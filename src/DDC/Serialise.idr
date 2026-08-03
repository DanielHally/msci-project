module DDC.Serialise

import public DDC.DSL

%default total

empty : VectAndLength a
empty = vectAndLength []

||| Encode an instance of a given DDC type to a bit string
public export
serialise : (t : DDCType) -> RawTy t -> Binary
serialise UNIT rep = empty
serialise BOTTOM rep impossible
serialise (BASE_TYPE _ encode _) rep = encode rep
serialise (DEPSUM t1 t2) (x ** y) =
    let
        (_ ** x') = serialise t1 x
        (_ ** y') = serialise (t2 x) y
    in
        (_ ** x' ++ y')
serialise (SUM t1 t2) (Left rep) = serialise t1 rep
serialise (SUM t1 t2) (Right rep) = serialise t2 rep
serialise (INTERSECTION t1 t2) (rep1, rep2) =
    let
        (len1 ** x) = serialise t1 rep1
        (len2 ** y) = serialise t2 rep2
    in if len1 >= len2 then
        (len1 ** x)
    else
        (len2 ** y)
serialise (CONSTRAINED t test) rep = serialise t rep.fst
serialise (SEQUENCE tElem tSep mkSep termCon tTerm mkTerm) rep@(_ ** l) = continue l empty empty where
    serialiseTerm :
        (acc : Binary) ->
        (prev : SeqRaw tElem) ->
        Binary
    serialiseTerm acc' prev' = the Binary $
        -- Don't need to emit terminator if termination condition met; would go unparsed
        if termCon rep then empty

        -- The compiler can only solve the constraint between tTerm and mkTerm if
        -- each DDCType is invidiually tested; a wildcard for non-bottom doesn't
        -- work
        else case tTerm of
            BOTTOM => empty
            UNIT => serialise tTerm $ mkTerm acc' prev'
            BASE_TYPE _ _ _ => serialise tTerm $ mkTerm acc' prev'
            DEPSUM _ _ => serialise tTerm $ mkTerm acc' prev'
            SUM _ _ => serialise tTerm $ mkTerm acc' prev'
            INTERSECTION _ _ => serialise tTerm $ mkTerm acc' prev'
            CONSTRAINED _ _ => serialise tTerm $ mkTerm acc' prev'
            SEQUENCE _ _ _ _ _ _ => serialise tTerm $ mkTerm acc' prev'
            COMPUTE _ => serialise tTerm $ mkTerm acc' prev'
            ABSORB _ _ => serialise tTerm $ mkTerm acc' prev'
            SCAN _ => serialise tTerm $ mkTerm acc' prev'

    continue : (xs : Vect n (RawTy tElem)) -> (prev : SeqRaw tElem) -> (acc : Binary) -> Binary
    continue [] _ acc = acc ++ serialiseTerm empty empty
    continue [x] prev acc =
        let
            elem = serialise tElem x
            prev' = prev ++ [x]
            acc' = acc ++ elem
            term = serialiseTerm acc' prev'
        in
            acc ++ elem ++ term
    continue (x::xs) (_ ** prevXs) (len ** acc) =
        let
            (n ** elem) = serialise tElem x
            prevXs' = vectAndLength $ prevXs ++ [x]
            (_ ** sep) = serialise tSep $ mkSep prevXs'
        in
            continue xs prevXs' (_ ** acc ++ elem ++ sep)
serialise (COMPUTE expr) rep = empty
serialise (ABSORB t mkVal) _ = serialise t mkVal
serialise (SCAN t) rep = serialise t rep
