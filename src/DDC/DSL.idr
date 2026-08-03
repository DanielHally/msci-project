||| The domain-specific language for defining types
module DDC.DSL

import public Data.DPair
import public Data.Either
import public Data.Vect
import Derive.Eq
import Derive.Prelude

import public DDC.Binary
import public DDC.Error
import public DDC.Util

%language ElabReflection

%default total

{-
    Fundamental types
-}

||| An offset of a bit within a binary buffer
public export
Offset : Type
Offset = Nat

||| A range of bits specified by 2 offsets
public export
record Span where
    constructor MkSpan
    begin : Offset
    end : Offset

public export
implementation Show Span where
    show (MkSpan begin end) = "(" ++ show begin ++ ".." ++ show end ++ ")"

||| The singleton type None, indicating a failed parse
public export
data None = MkNone

%runElab derive "None" [Show]

{-
    Parse result data structure
-}

||| An indicator for the DDCType a result is created from
||| Used in place of raw DDCType values to help totality checker
public export
data DDCTag =
    T_UNIT |
    T_BOTTOM |
    T_BASE_TYPE |
    T_DEPSUM |
    T_SUM |
    T_INTERSECTION |
    T_CONSTRAINED |
    T_SEQUENCE |
    T_COMPUTE |
    T_ABSORB |
    T_SCAN

%runElab derive "DDCTag" [Show]

-- Forward declaration
public export data StayedOk : (tag : DDCTag) -> {tRep : Type} -> (ec : ErrorCode) -> (rep : tRep) -> Type

||| Result container for parsing of a DDCType
||| Contains both the representation and parse descriptor from the DDC
public export
record Result (tag : DDCTag) (tRep : Type) (tPdMisc : Type) where
    constructor MkResult

    ||| The representation of the value parsed
    rep : tRep

    ||| The number of errors from parsing this value
    err : Error

    ||| The range of bits this value came from
    sp : Span

    ||| Additional type-specific parse descriptor data
    pdMisc : tPdMisc

    ||| Proof that the err reflects rep
    ||| Either err is not OK, or all components of rep are OK
    {auto 0 prfRep : StayedOk tag (err.ec) rep}

||| Shorthand for a result's error code
public export
ec : Result _ _ _ -> ErrorCode
ec res = res.err.ec

||| Shorthand for a result's error code
public export
(.ec) : Result _ _ _ -> ErrorCode
(.ec) = ec

||| Shorthand for a result's error count
public export
nerr : Result _ _ _ -> Nat
nerr res = res.err.nerr

||| Shorthand for a result's error count
public export
(.nerr) : Result _ _ _ -> Nat
(.nerr) = nerr

||| Proof the error code of a result is OK
public export
IsOk : Result _ _ _ -> Type
IsOk res = res.ec = OK

{-
    Main DSL data structure
-}

||| The representation of a base type
||| Right t if successful, Left None if failed
public export
BaseRep : Type -> Type
BaseRep t = Either None t

||| Shorthand for the Result for a base type
public export
BaseResult : Type -> Type
BaseResult t = Result T_BASE_TYPE (BaseRep t) ()

||| A function converting a base type value to a bit string
public export
EncodeFn : Type -> Type
EncodeFn bType = bType -> Binary

||| A function converting a bit substring at a given offset into a base type value
||| Returns the end offset and the result of parsing
public export
DecodeFn : Type -> Type
DecodeFn bType = Binary -> Offset -> (Offset, BaseResult bType)

-- Forward declaration
public export data DDCType : Type

||| Inspect the category of a DDCType
public export
getTag : DDCType -> DDCTag

||| The host language representation type of a DDC type
||| Corresponds to DDC's [[_]]rep
public export
RepTy : DDCType -> Type

||| The type of data stored in a DDC type's parse descriptor in addition
||| to the child components' parse descriptors (which become part of the
||| representation due to Result)
||| Corresponds to DDC's [[_]]PD
public export
PdMiscTy : DDCType -> Type

||| The type given by parsing a DDCType
public export
MkTy : DDCType -> Type
MkTy t = Result (getTag t) (RepTy t) (PdMiscTy t)

||| The host-language representation of a successfully parsed DDCType, with all metadata removed
public export
RawTy : DDCType -> Type

||| A test on a parsed value for a constrained type
public export
Constraint : DDCType -> Type
Constraint t = RawTy t -> Bool

||| Shorthand for the raw representation of a constrained type
public export
ConstrainedRaw : (t : DDCType) -> (test : RawTy t -> Bool) -> Type 
ConstrainedRaw t test = Subset (RawTy t) (\x => test x = True)

||| Shorthand for the raw representation of a sequence type
public export
SeqRaw : DDCType -> Type
SeqRaw tElem = (n : Nat ** Vect n (RawTy tElem))

||| Shorthand for the representation of a sequence type
public export
SeqRep : DDCType -> Type
SeqRep tElem = (n : Nat ** Vect n (MkTy tElem))

||| Shorthand for the parse descriptor of a sequence type
public export
SeqPdMisc : Type
SeqPdMisc = Nat

||| Shorthand for the Result for a sequence type
public export
SeqResult : DDCType -> Type
SeqResult tElem = Result T_SEQUENCE (SeqRep tElem) SeqPdMisc

||| A termination condition for a sequence type
public export
TermCon : DDCType -> Type
TermCon tElem = SeqRaw tElem -> Bool

||| Function to decide a sequence separator value
public export
MkSep : (tElem : DDCType) -> (tSep : DDCType) -> Type
MkSep tElem tSep = SeqRaw tElem -> RawTy tSep

||| Function to decide a sequence terminator value
public export
MkTerm : (tElem : DDCType) -> (tTerm : DDCType) -> Type
MkTerm tElem tTerm = Binary -> SeqRaw tElem -> RawTy tTerm

||| The main DSL data structure for defining DDC types
public export
data DDCType : Type where
    ||| The empty type, length 0, always parses successfully
    UNIT : DDCType

    ||| Always fails to parse
    BOTTOM : DDCType

    ||| A type directly mapping to a bit string
    BASE_TYPE : (bType : Type) -> {auto _ : Show bType} -> (encodeFn : EncodeFn bType) -> (decodeFn : DecodeFn bType) -> DDCType

    ||| A sequenced pair of values where the latter may depend on the former
    ||| The second is only parsed if the first is successful
    DEPSUM : (t1 : DDCType) -> (t2 : RawTy t1 -> DDCType) -> DDCType

    ||| Data described by 1 of 2 types
    SUM : (t1 : DDCType) -> (t2 : DDCType) -> DDCType

    ||| Data described simultaneously by 2 types
    INTERSECTION : (t1 : DDCType) -> (t2 : DDCType) -> DDCType

    ||| A type with additional validation ran over its result
    CONSTRAINED : (t : DDCType) -> (test : Constraint t) -> DDCType

    ||| A consecutive sequence of values
    ||| @ tElem the element type
    ||| @ tSep the element separator type (may be unit)
    ||| @ mkSep the function to decide a separator when encoding
    ||| @ termCon the sequence termination condition (sequence ends if true)
    ||| @ tTerm the terminator type (sequence ends if parsed successfully)
    ||| @ mkTerm the function to decide a terminator when encoding
    SEQUENCE :  
        (tElem : DDCType) ->
        (tSep : DDCType) ->
        (mkSep : MkSep tElem tSep) ->
        (termCon : TermCon tElem) ->
        (tTerm : DDCType) ->
        (
            mkTerm : case getTag tTerm of
                T_BOTTOM => ()
                _ => MkTerm tElem tTerm
        ) ->
        DDCType

    -- RECURSIVE_TYPE

    ||| A value computed from existing data, not included in the binary directly
    COMPUTE : {a : Type} {- -> {auto _ : Show a} -} -> (expr : a) -> DDCType

    ||| A value parsed but not included in the output
    ABSORB : (t : DDCType) -> (mkVal : RawTy t) -> DDCType

    ||| Search forward until a value is parsed successfully
    SCAN : (t : DDCType) -> DDCType

||| Remove all parsing metadata from a successful Result
public export
stripMetadata : (t : DDCType) -> (res : MkTy t) -> {auto 0 isOk : IsOk res} -> RawTy t

||| Shorthand for the second item of Depsum's type
public export
DepsumRhs : (t1 : DDCType) -> (t2 : RawTy t1 -> DDCType) -> (fst : MkTy t1) -> {auto 0 fstOk : IsOk fst} -> Type
DepsumRhs {fstOk} t1 t2 fst = MkTy (t2 (stripMetadata {isOk=fstOk} t1 fst))

||| A dependent pair where the second item only exists if the first has no errors
public export
data Depsum : (t1 : DDCType) -> (t2 : RawTy t1 -> DDCType) -> Type where
    MkDepsumFull : (fst : MkTy t1) -> {auto 0 fstOk : IsOk fst} -> (snd : DepsumRhs t1 t2 fst) -> Depsum t1 t2
    MkDepsumPartial : (fst : MkTy t1) -> {auto 0 fstNotOk : Not (IsOk fst)} -> Depsum t1 t2 

||| Proof type showing Depsum contains both elements
public export
data DepsumFull : Depsum t1 t2 -> Type where
    DepsumIsFull : DepsumFull (MkDepsumFull {fstOk} x y)

public export
equivalentFulls : {x : Depsum _ _} -> (p1 : DepsumFull x) -> (p2 : DepsumFull x) -> p1 = p2
equivalentFulls DepsumIsFull DepsumIsFull = Refl

||| Helper to access the first element of a Depsum
public export
depsumFst : (ds : Depsum t1 t2) -> MkTy t1
depsumFst (MkDepsumFull x y) = x
depsumFst (MkDepsumPartial x) = x

||| Helper to access the first element of a Depsum
public export
(.fst) : (ds : Depsum t1 t2) -> MkTy t1
(.fst) = depsumFst

||| Alternate shorthand for the second item of Depsum's type
public export
DepsumRhs' :
    {t1 : DDCType} ->
    {t2 : RawTy t1 -> DDCType} ->
    (ds : Depsum t1 t2) ->
    {auto 0 fstOk : IsOk ds.fst} ->
    Type
DepsumRhs' {t1, t2} ds = DepsumRhs t1 t2 ds.fst

||| Helper to access the proof a full Depsum's first item is OK
public export
0 depsumFstOk : (ds : Depsum t1 t2) -> {auto 0 isFull : DepsumFull ds} -> IsOk ds.fst
depsumFstOk (MkDepsumFull x {fstOk} y) = fstOk

||| Helper to access the proof a full Depsum's first item is OK
public export
0 (.fstOk) : (ds : Depsum t1 t2) -> {auto 0 isFull : DepsumFull ds} -> IsOk ds.fst
(.fstOk) = depsumFstOk

||| Helper to access the second element of a Depsum
public export
depsumSnd : (ds : Depsum t1 t2) -> {auto 0 isFull : DepsumFull ds} -> DepsumRhs' ds {fstOk=ds.fstOk}
depsumSnd (MkDepsumFull x y) = y

||| Helper to access the second element of a Depsum
public export
(.snd) : (ds : Depsum t1 t2) -> {auto 0 isFull : DepsumFull ds} -> DepsumRhs' ds {fstOk=ds.fstOk}
(.snd) = depsumSnd

public export
decFull : (ds : Depsum t1 t2) -> Dec $ DepsumFull ds
decFull (MkDepsumFull x y) = Yes DepsumIsFull
decFull (MkDepsumPartial {fstNotOk} x) = No $ \DepsumIsFull impossible

||| Shorthand for the representation of a sum type
public export
SumRep : (t1 : DDCType) -> (t2 : DDCType) -> Type
SumRep t1 t2 = Either (MkTy t1) (MkTy t2)

||| Shorthand for the representation of an intersection type
public export
IntersectionRep : (t1 : DDCType) -> (t2 : DDCType) -> Type
IntersectionRep t1 t2 = (MkTy t1, MkTy t2)

public export
data Constrained : (t : DDCType) -> (test : RawTy t -> Bool) -> Type where
    MkConstrainedMet :
        (val : MkTy t) ->
        {auto 0 isOk : IsOk val} ->
        {auto 0 testPass : test (stripMetadata {isOk} t val) = True} ->
        Constrained t test
    MkConstrainedUnmet : (val : MkTy t) -> Constrained t test

public export
data ConstrainedMet : Constrained t test -> Type where
    ConstrainedIsMet : ConstrainedMet (MkConstrainedMet val {isOk, testPass})

public export
constrainedVal : Constrained t test -> MkTy t
constrainedVal (MkConstrainedMet val) = val
constrainedVal (MkConstrainedUnmet val) = val

public export
(.val) : Constrained t test -> MkTy t
(.val) = constrainedVal

public export
0 constrainedOk : (c : Constrained t test ) -> {auto 0 isMet : ConstrainedMet c} -> IsOk c.val
constrainedOk (MkConstrainedMet val {isOk}) = isOk

public export
0 (.isOk) : (c : Constrained t test) -> {auto 0 isMet : ConstrainedMet c} -> IsOk c.val
(.isOk) = constrainedOk

public export
0 constrainedTestPass :
    (c : Constrained t test ) ->
    {auto 0 isMet : ConstrainedMet c} ->
    test (stripMetadata {isOk=c.isOk} t c.val) = True
constrainedTestPass (MkConstrainedMet val {testPass}) = testPass

public export
0 (.testPass) :
    (c : Constrained t test ) ->
    {auto 0 isMet : ConstrainedMet c} ->
    test (stripMetadata {isOk=c.isOk} t c.val) = True
(.testPass) = constrainedTestPass

public export
AbsorbRep : DDCType -> Type
AbsorbRep t = Either None (() `Subset` const (MkTy t))

||| Shorthand for the representation of a constrained type
||| Right if the parse was successful, Left if not
public export
ScanRep : DDCType -> Type
ScanRep t = Either None (MkTy t)

getTag UNIT = T_UNIT
getTag BOTTOM = T_BOTTOM
getTag (BASE_TYPE _ _ _) = T_BASE_TYPE
getTag (DEPSUM _ _) = T_DEPSUM
getTag (SUM _ _) = T_SUM
getTag (INTERSECTION _ _) = T_INTERSECTION
getTag (CONSTRAINED _ _) = T_CONSTRAINED
getTag (SEQUENCE _ _ _ _ _ _) = T_SEQUENCE
getTag (COMPUTE _) = T_COMPUTE
getTag (ABSORB _ _) = T_ABSORB
getTag (SCAN _) = T_SCAN

RepTy UNIT = ()
RepTy BOTTOM = None
RepTy (BASE_TYPE t _ _) = BaseRep t
RepTy (DEPSUM t1 t2) = Depsum t1 t2
RepTy (SUM t1 t2) = SumRep t1 t2
RepTy (INTERSECTION t1 t2) = IntersectionRep t1 t2
RepTy (CONSTRAINED t test) = Constrained t test
RepTy (SEQUENCE tElem tSep mkSep termCon tTerm mkTerm) = SeqRep tElem
RepTy (COMPUTE {a} _) = a
RepTy (ABSORB t _) = AbsorbRep t
RepTy (SCAN t) = ScanRep t

PdMiscTy (SEQUENCE _ _ _ _ _ _) = SeqPdMisc
PdMiscTy (SCAN t) = Either () Nat
PdMiscTy _ = ()

RawTy UNIT = ()
RawTy BOTTOM = Void
RawTy (BASE_TYPE t _ _) = t
RawTy (DEPSUM t1 t2) = (x : (RawTy t1) ** RawTy (t2 x))
RawTy (SUM t1 t2) = Either (RawTy t1) (RawTy t2)
RawTy (INTERSECTION t1 t2) = (RawTy t1, RawTy t2)
RawTy (CONSTRAINED t test) = ConstrainedRaw t test
RawTy (SEQUENCE tElem tSep mkSep termCon tTerm mkTerm) = SeqRaw tElem
RawTy (COMPUTE {a} _) = a
RawTy (ABSORB t _) = ()
RawTy (SCAN t) = RawTy t

{-
    Proof over the data
-}

||| Proof that an error code accurately reflects a representation
||| Either the error code is not OK, or all components of the representation are OK
||| This means that if the outermost Result is OK, all children will be too
public export
data StayedOk : (tag : DDCTag) -> {tRep : Type} -> (ec : ErrorCode) -> (rep : tRep) -> Type where
    ||| ERR and FAIL may describe any representation
    WasntOk :
        {rep : tRep} ->
        {ec : ErrorCode} ->
        {auto 0 contra : Not (ec = OK)} ->
        StayedOk tag ec rep

    ||| Unit is always OK
    UnitWasOK :
        StayedOk T_UNIT OK ()

    ||| Base types are only OK if their representation is Right
    BaseWasOk :
        {rep : BaseRep t} ->
        {auto 0 isRight : IsRight rep} ->
        StayedOk T_BASE_TYPE OK rep

    ||| Dependent sums are only OK if both of their items are OK
    DepsumWasOk :
        {rep : Depsum t1 t2} ->
        {auto 0 isFull : DepsumFull rep} ->
        -- isFull implies IsOk rep.fst
        {auto 0 sndOk : IsOk rep.snd} ->
        StayedOk T_DEPSUM OK rep

    ||| A left sum is OK if its item is OK
    SumLeftWasOk :
        {rep : SumRep t1 t2} ->
        {auto 0 isLeft : IsLeft rep} ->
        {auto 0 leftOk : IsOk $ fromLeft rep} ->
        StayedOk T_SUM OK rep
    ||| A right sum is OK if its item is OK
    SumRightWasOk :
        {rep : SumRep t1 t2} ->
        {auto 0 isRight : IsRight rep} ->
        {auto 0 rightOk : IsOk $ fromRight rep} ->
        StayedOk T_SUM OK rep

    ||| Intersections are only OK if both of their items are OK
    IntersectionWasOk :
        {rep : IntersectionRep t1 t2} ->
        {auto 0 fstOk : IsOk (fst rep)} ->
        {auto 0 sndOk : IsOk (snd rep)} ->
        StayedOk T_INTERSECTION OK rep

    ||| Constrained types are only OK if their constraint is met (i.e. their
    ||| representation is Right) and their item is ok
    ConstrainedWasOk :
        {rep : Constrained t test} ->
        {auto 0 isMet : ConstrainedMet rep} ->
        -- isMet implies IsOk rep.val
        StayedOk T_CONSTRAINED OK rep

    ||| Sequences are only OK if every element is OK
    SequenceWasOk :
        {rep : (n : Nat ** Vect n (Result _ _ _))} ->
        {auto 0 allOk : All IsOk rep.snd} ->
        StayedOk T_SEQUENCE OK rep 

    ||| Compute is always OK
    ComputeWasOk : {rep : a} -> StayedOk T_COMPUTE OK rep

    ||| Absorb is only OK if its representation is Right
    AbsorbWasOk :
        {rep : AbsorbRep t} ->
        {auto 0 isRight : IsRight rep} ->
        {auto 0 rightOk : IsOk $ snd $ fromRight rep} ->
        StayedOk T_ABSORB OK rep

    ||| Scan is only OK if its item is OK
    ScanWasOk :
        {rep : ScanRep t} ->
        {auto 0 isRight : IsRight rep} ->
        {auto 0 rightOk : IsOk (fromRight rep)} ->
        StayedOk T_SCAN OK rep

||| Helper to narrow the error code of a StayedOk proof to rule out the WasntOk case
||| For some reason, doing this in-line wasn't working
public export
0 shownOk : {rep : a} -> {ec : ErrorCode} -> (0 stayedOk : StayedOk tag ec rep) -> {auto 0 isOk : ec = OK} -> StayedOk tag OK rep
shownOk stayedOk = rewrite sym isOk in stayedOk

{-
    Helpers for defining DDC base types
-}

||| Create a non-OK result for a base type
public export
BaseFail :
    {t : Type} ->
    (err : Error) -> {auto 0 prfEc : Not (err.ec = OK)} ->
    (sp : Span) ->
    BaseResult t
BaseFail err sp = MkResult (Left MkNone) err sp ()

||| Create an OK result for a base type
public export
BaseOk :
    {t : Type} ->
    (rep : t) ->
    (sp : Span) ->
    BaseResult t
BaseOk rep sp = MkResult (Right rep) MkOk sp ()

{-
    Helpers for accessing representations of OK results
-}

-- Unit is trivial to access

-- Bottom is trivial to access

||| Helper to access the representation of a base type when proven OK
public export
getBaseRep :
    (res : Result T_BASE_TYPE _ _) ->
    {auto 0 isOk : IsOk res} ->
    (RightTy res.rep)
getBaseRep res = fromRight res.rep where
    %hint
    0 isRight : IsRight res.rep
    isRight = case shownOk res.prfRep of
        WasntOk {contra} => void $ contra Refl
        BaseWasOk {isRight=isRight'} => isRight'

||| Helper to access the representation of a depsum type when proven OK
public export
getDepsumRep :
    (res : Result T_DEPSUM (Depsum t1 t2) _) ->
    {auto 0 isOk : IsOk res} ->
    (
        res1 : Subset (MkTy t1) IsOk **
        Subset (MkTy $ t2 $ stripMetadata {isOk=res1.snd} t1 (fst res1)) IsOk
    )
getDepsumRep res = (Element res.rep.fst res.rep.fstOk ** Element res.rep.snd sndOk) where
    %hint
    0 isFull : DepsumFull res.rep
    isFull = case shownOk res.prfRep of
        WasntOk {contra} => void $ contra Refl
        DepsumWasOk {isFull=isFull'} => isFull'

    0 sndOk : IsOk (depsumSnd res.rep)
    sndOk = case shownOk res.prfRep of
        WasntOk {contra} => void $ contra Refl
        DepsumWasOk {isFull=isFull', sndOk=sndOk'} =>
            rewrite equivalentFulls isFull isFull' in sndOk'

||| Helper to access the representation of an intersection type when proven OK
public export
getIntersectionRep :
    (res : Result T_INTERSECTION (Result t1 r1 p1, Result t2 r2 p2) _) ->
    {auto 0 isOk : IsOk res} ->
    (fst :
        Subset (Result t1 r1 p1) IsOk **
        Subset (Result t2 r2 p2) IsOk
    )
getIntersectionRep res = (fst res.rep `Element` fstOk ** snd res.rep `Element` sndOk) where
    0 fstOk : IsOk $ fst res.rep
    fstOk = case shownOk res.prfRep of
        WasntOk {contra} => void $ contra Refl
        IntersectionWasOk {fstOk=fstOk'} => fstOk'

    0 sndOk : IsOk $ snd res.rep
    sndOk = case shownOk res.prfRep of
        WasntOk {contra} => void $ contra Refl
        IntersectionWasOk {sndOk=sndOk'} => sndOk'

||| Helper to access the representation of a sum type when proven OK
public export
getSumRep :
    (res : Result T_SUM (Either (Result t1 r1 p1) (Result t2 r2 p2)) _) ->
    {auto 0 isOk : IsOk res} ->
    Either
        (Subset (Result t1 r1 p1) IsOk)
        (Subset (Result t2 r2 p2) IsOk)
getSumRep res = case decEither res.rep of
        Left isLeft => Left $ fromLeft res.rep `Element` leftOk
        Right isRight => Right $ fromRight res.rep `Element` rightOk
    where
        0 leftOk : {auto 0 isLeft : IsLeft res.rep} -> IsOk $ fromLeft res.rep
        leftOk = case shownOk res.prfRep of
            WasntOk {contra} => void $ contra Refl
            SumLeftWasOk {isLeft=isLeft', leftOk=leftOk'} => rewrite equivalentLefts isLeft isLeft' in leftOk'
            SumRightWasOk {isRight} => void $ eitherNotBoth res.rep isLeft isRight

        0 rightOk : {auto 0 isRight : IsRight res.rep} -> IsOk $ fromRight res.rep
        rightOk = case shownOk res.prfRep of
            WasntOk {contra} => void $ contra Refl
            SumLeftWasOk {isLeft} => void $ eitherNotBoth res.rep isLeft isRight
            SumRightWasOk {isRight=isRight', rightOk=rightOk'} => rewrite equivalentRights isRight isRight' in rightOk'

||| Helper to access the representation of a constrained type when proven OK
public export
getConstrainedRep :
    {t : DDCType} ->
    {test : RawTy t -> Bool} ->
    (res : Result T_CONSTRAINED (Constrained t test) _) ->
    {auto 0 isOk : IsOk res} ->
    Subset (MkTy t) $ \x => (isOk : IsOk x ** test (stripMetadata {isOk} t x) = True)
getConstrainedRep {t} res = res.rep.val `Element` (res.rep.isOk ** res.rep.testPass) where
    %hint
    0 isMet : ConstrainedMet res.rep
    isMet = case shownOk res.prfRep of
        WasntOk {contra} => void $ contra Refl
        ConstrainedWasOk {isMet=isMet'} => isMet'

||| Helper to access the representation of a sequence type when proven OK
public export
getSequenceRep :
    (res : Result T_SEQUENCE (n : Nat ** Vect n (Result t1 r1 p1)) _) ->
    {auto 0 isOk : IsOk res} ->
    Subset (n : Nat ** Vect n (Result t1 r1 p1)) (\x => All IsOk x.snd)
getSequenceRep res = (res.rep.fst ** res.rep.snd) `Element` allOk where
    0 allOk : All IsOk res.rep.snd
    allOk = case shownOk res.prfRep of
        WasntOk {contra} => void $ contra Refl
        SequenceWasOk {allOk=allOk'} => allOk'

-- Compute is trivial to access

||| Helper to access the representation of an absorb type when proven OK
public export
getAbsorbRep :
    (res : Result T_ABSORB (Either None (() `Subset` const (Result _ _ _))) _) ->
    {auto 0 isOk : IsOk res} ->
    ()
getAbsorbRep res = fst (fromRight res.rep) where
    %hint
    0 isRight : IsRight res.rep
    isRight = case shownOk res.prfRep of
        WasntOk {contra} => void $ contra Refl
        AbsorbWasOk {isRight=isRight'} => isRight'

||| Helper to access the representation of a scan type when proven OK
public export
getScanRep :
    (res : Result T_SCAN (Either None (Result t1 r1 p1)) _) ->
    {auto 0 isOk : IsOk res} ->
    Subset (Result t1 r1 p1) IsOk
getScanRep res = fromRight res.rep `Element` rightOk where
    %hint
    0 isRight : IsRight res.rep
    isRight = case shownOk res.prfRep of
        WasntOk {contra} => void $ contra Refl
        ScanWasOk {isRight=isRight'} => isRight'

    0 rightOk : IsOk $ fromRight res.rep
    rightOk = case shownOk res.prfRep of
        WasntOk {contra} => void $ contra Refl
        ScanWasOk {isRight=isRight', rightOk=rightOk'} =>
            rewrite equivalentRights isRight isRight' in rightOk'


stripMetadata UNIT res = res.rep
stripMetadata BOTTOM res = void $
    case shownOk res.prfRep of
        WasntOk {contra=contra'} => contra' Refl
stripMetadata (BASE_TYPE _ _ _) res = getBaseRep res
stripMetadata (DEPSUM t1 t2) res =
    let
        (Element x xOk ** Element y yOk) = getDepsumRep res
    in
        (stripMetadata t1 x ** stripMetadata (t2 $ stripMetadata t1 x) y)
stripMetadata (SUM t1 t2) res = case getSumRep res of
    Left (rep `Element` isOk) => Left (stripMetadata t1 rep)
    Right (rep `Element` isOk) => Right (stripMetadata t2 rep)
stripMetadata (INTERSECTION t1 t2) res =
    let
        (x `Element` xOk ** y `Element` yOk) = getIntersectionRep res
    in
        (stripMetadata t1 x, stripMetadata t2 y)
stripMetadata (CONSTRAINED t e) res =
    let
        x `Element` prf = getConstrainedRep res
    in
        stripMetadata {isOk=prf.fst} t x `Element` prf.snd
stripMetadata (SEQUENCE tElem _ _ _ _ _) res =
    let
        (_ ** xs) `Element` prfs = getSequenceRep res
        xs' = mapPrf xs prfs
    in
        (_ ** map (\(x `Element` isOk) => stripMetadata tElem x) xs')
stripMetadata (COMPUTE _) res = res.rep
stripMetadata (ABSORB _ _) res = getAbsorbRep res
stripMetadata (SCAN t) res =
    let
        x `Element` xOk = getScanRep res
    in
        stripMetadata t x

public export
mkUnitSep : VectAndLength _ -> RawTy UNIT
mkUnitSep _ = ()

public export
noTermCon : _ -> Bool
noTermCon _ = False
