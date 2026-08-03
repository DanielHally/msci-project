||| Implementation of DDCType-guided parsing

module DDC.Parse

import Decidable.Equality
import Data.Vect
import Data.Vect.Quantifiers

import public DDC.DSL
import public DDC.Error
import DDC.Util

%default total

||| Checks if an offset is past the end of a bit string
public export
eof : Binary -> Offset -> Bool
eof (len ** _) w = w >= len

||| 0 if 0, 1 if any other natural number
public export
pos : Nat -> Nat
pos 0 = 0
pos _ = 1

||| Parse binary data given a DDC type, bit string and offset
||| Corresponds to DDC's [[_]]P
-- TODO: totality
export
covering parse : (t : DDCType) -> (b : Binary) -> (w : Offset) -> (Offset, MkTy t)
parse UNIT b w = (w, MkResult () MkOk (MkSpan w w) ())
parse BOTTOM b w = (w, MkResult MkNone (MkFail 1) (MkSpan w w) ())
parse (BASE_TYPE _ _ decode) b w = decode b w
parse (DEPSUM t1 t2) b w =
    let
        -- Parse subcomponents
        (w', res1) = parse t1 b w
    in case res1.ec `decEq` OK of
        Yes _ =>
            let
                (w'', res2) = parse (t2 (stripMetadata t1 res1)) b w'

                (err ** prfRep) = calcError res1 res2

                res = MkResult {
                    rep = MkDepsumFull res1 res2,
                    err = err,
                    sp = (MkSpan res1.sp.begin res2.sp.end),
                    pdMisc = ()
                }
            in
                (w'', res)
        No _ => (w', MkResult (MkDepsumPartial res1) (MkFail 1) res1.sp ())
    where
        -- Combine the component errors with proof
        calcError :
            (res1 : MkTy t1) ->
            {auto 0 fstOk : IsOk res1} ->
            (res2 : MkTy $ t2 $ stripMetadata t1 res1) ->
            (err : Error ** StayedOk T_DEPSUM {tRep = Depsum t1 t2} err.ec (MkDepsumFull res1 {fstOk} res2))
        calcError res1 res2 =
            case decError res2.ec of
                ItIsOk _ => (MkOk ** DepsumWasOk)
                ItIsFail _ _ => (MkFail nerr ** WasntOk)
                ItIsErr _ _ => (MkErr nerr ** WasntOk)
            where
                nerr = pos res1.nerr + pos res2.nerr
parse (SUM t1 t2) b w =
    let
        (w', res1) = parse t1 b w
    in case res1.ec `decEq` OK of
        Yes _ =>
            (w', MkResult (Left res1) MkOk res1.sp () {prfRep=SumLeftWasOk})
        No _ =>
            let
                (w', res2) = parse t2 b w
            in case res2.ec `decEq` OK of
                Yes _ =>
                    (w', MkResult (Right res2) MkOk res2.sp () {prfRep=SumRightWasOk})
                No _ =>
                    (w', MkResult (Right res2) res2.err res2.sp ())
parse (INTERSECTION t1 t2) b w =
    let
        (w1, res1) = parse t1 b w
        (w2, res2) = parse t2 b w
        w' = max w1 w2
        (err ** prfRep) = calcError res1 res2
        res = MkResult {
            rep = (res1, res2),
            err = err,
            sp = MkSpan res1.sp.begin (max res1.sp.end res2.sp.end),
            pdMisc = ()
        }
    in
        (w', res)
    where
        -- Combine the component errors with proof
        -- Takes max_ec_nf, or FAIL when both elements failed
        calcError :
            (res1 : MkTy t1) ->
            (res2 : MkTy t2) ->
            (err : Error ** StayedOk T_INTERSECTION err.ec (res1, res2))
        calcError res1 res2 =
            case (decError res1.ec, decError res2.ec) of
                (ItIsOk _, ItIsOk _) => (MkOk ** IntersectionWasOk)
                (ItIsFail _ _, ItIsFail _ _) => (MkFail nerr ** WasntOk)
                _ => (MkErr nerr ** WasntOk)
            where
                nerr = pos res1.nerr + pos res2.nerr
parse (CONSTRAINED t e) b w =
    let
        (w', res) = parse t b w
    in case res.ec `decEq` OK of
        Yes _ =>
            case (e $ stripMetadata t res) `decEq` True of
                Yes _ =>
                    (w', MkResult (MkConstrainedMet res) MkOk res.sp ())
                No _ =>
                    let
                        (err ** prfRep) = calcLeftError res
                    in
                        (w', MkResult (MkConstrainedUnmet res) err res.sp ())
        No _ =>
            let
                (err ** prfRep) = calcLeftError res
            in
                (w', MkResult (MkConstrainedUnmet res) err res.sp ())
    where
        calcLeftError :
            (res : MkTy t) ->
            (err : Error ** StayedOk T_CONSTRAINED {tRep = Constrained t e} err.ec (MkConstrainedUnmet res))
        calcLeftError res =
            case decError res.ec of
                ItIsFail _ _ => (MkFail nerr ** WasntOk)
                _ => (MkErr nerr ** WasntOk)
            where
                nerr = 1 + pos res.nerr
parse (SEQUENCE tElem tSep mkSep termCon tTerm mkTerm) b w =
    let
        -- Initialise empty result
        res = MkResult (0 ** []) MkOk (MkSpan w w) 0
    in if isDone w res then
        -- 0-length sequence
        (w, res)
    else
        -- Parse 1 element and start loop
        let
            (wElem, resElem) = parse tElem b w
        in
            continue w wElem (resSeq res Nothing resElem)
    where
        -- TODO: Using T@(SEQUENCE ...) notation or a lowercase variable name fails type checking
        T = (SEQUENCE tElem tSep mkSep termCon tTerm mkTerm)

        -- Number of element errors (pdMisc)
        neerr : Result T_SEQUENCE _ SeqPdMisc -> Nat
        neerr res = res.pdMisc

        -- Check if the current representation is a complete list
        covering isDone : Offset -> (res : MkTy T) -> Bool
        isDone w res = case res.ec `decEq` OK of
            -- termCon requires a valid list
            No _ => True

            Yes _ => 
                -- No more data to read
                (eof b w) ||

                -- Termination condition met
                (termCon $ stripMetadata T res) ||

                -- Try parse terminator type
                let
                    (w', res') = parse tTerm b w
                in
                    res'.ec == OK

        calcError :
            (curRes : MkTy T) ->
            (newElem : MkTy tElem) ->
            (resSep : Maybe (MkTy tSep)) ->
            (newRep : RepTy T ** err : Error ** StayedOk T_SEQUENCE {tRep = RepTy T} err.ec newRep)
        calcError curRes newElem resSep = 
            case (curRes.ec `decEq` OK, decError newElem.ec, sepErr `decEq` 0) of
                (Yes _, ItIsOk isOk, Yes _) =>
                    (newRep ** MkOk ** SequenceWasOk {allOk = allOk ++ [isOk]})
                (_, ItIsFail _ _, _) =>
                    (newRep ** (MkFail nerr) ** WasntOk)
                (_, _, _) =>
                    (newRep ** (MkErr nerr) ** WasntOk)

                -- TODO: should separator errors actually change ec?
            where
                newRep : RepTy T
                newRep = (_ ** curRes.rep.snd ++ [newElem])

                -- If this is the first element with an error, raise error count by 1
                eerr : Nat
                eerr = if neerr curRes == 0 && newElem.nerr > 0 then 1 else 0

                -- Error count increases by 1 for each separator containing errors
                sepErr : Nat
                sepErr = case resSep of
                    Just resSep' => pos resSep'.nerr
                    Nothing => 0

                -- Increment error count by new separator and element errors
                nerr : Nat
                nerr = curRes.nerr + pos sepErr + eerr

                0 allOk : {auto 0 curOk : curRes.ec = OK} -> All IsOk curRes.rep.snd
                allOk = case shownOk curRes.prfRep of
                    WasntOk {contra} => void $ contra Refl
                    SequenceWasOk {allOk=allOk'} => allOk'

        -- Update a result with a new element and possibly separator
        resSeq : MkTy T -> Maybe (MkTy tSep) -> MkTy tElem -> MkTy T
        resSeq res resSep resElem =
            let
                (newRep ** err ** prfRep) = calcError res resElem resSep
            in
                MkResult {
                    rep = newRep,
                    err = err,
                    sp = MkSpan res.sp.begin resElem.sp.end,
                    pdMisc = (neerr res) + (pos resElem.nerr)
                }

        -- Check if done, parse another element and loop if not
        covering continue : Offset -> Offset -> MkTy T -> (Offset, MkTy T)
        continue w w' res =
            if w == w' || isDone w' res then
                (w', res)
            else
                let
                    (wSep, resSep) = parse tSep b w'
                    (wElem, resElem) = parse tElem b wSep
                in
                    continue w' wElem (resSeq res (Just resSep) resElem)
parse (COMPUTE {a} e) b w = (w, MkResult e MkOk (MkSpan w w) ())
parse (ABSORB t _) b w =
    let
        (w', res) = parse t b w
        res' = case res.ec `decEq` OK of
            Yes isOk =>
                MkResult (Right $ () `Element` res) MkOk res.sp () {prfRep=AbsorbWasOk}
            No _ =>
                MkResult (Left MkNone) res.err res.sp ()
    in
        (w', res')
parse (SCAN t) b w = try 0
    where
        calcError : 
            (i : Nat) ->
            (res : MkTy t) ->
            {auto 0 isOk : IsOk res} ->
            (err : Error ** StayedOk T_SCAN {tRep = ScanRep t} err.ec (Right res))
        calcError i res =
            let
                nerr = (pos i) + (pos res.nerr)
            in if nerr == 0 then
                (MkOk ** ScanWasOk {rep = Right res})
            else
                (MkErr nerr ** WasntOk)

        covering try : Offset -> (Offset, MkTy (SCAN t))
        try i =
            let
                (w', res) = parse t b (w+i)
            in case res.ec `decEq` OK of
                Yes _ =>
                    let
                        (err ** prfRep) = calcError i res
                        res' = MkResult (Right res) err (MkSpan w res.sp.end) (Right i)
                    in
                        (w', res')
                No _ =>
                    if eof b (w+i) then
                        (w', MkResult (Left MkNone) (MkFail 1) (MkSpan w w) (Left ()))
                    else
                        try (i+1)
