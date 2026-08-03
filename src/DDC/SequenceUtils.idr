module DDC.SequenceUtils

import public DDC.BaseTypes
import public DDC.DSL
import public DDC.Syntax

-- This could be much nicer if proof of TermCon was preserved
public export
ARRAY : DDCType -> Nat -> DDCType
ARRAY t n = SEQUENCE t UNIT mkUnitSep (\x => x.fst == n) BOTTOM ()
            # \(len ** _) => len == n

public export
MkArray : {n : Nat} -> Vect n (RawTy t) -> RawTy (ARRAY t n)
MkArray {n} v = (_ ** v) `Element` (equalNatId n)

public export
UNTIL_EOF : DDCType -> DDCType
UNTIL_EOF t = SEQUENCE t UNIT mkUnitSep (const False) BOTTOM ()

public export
WITH_BYTES : DDCType -> Nat -> DDCType
WITH_BYTES t n = t .& ARRAY Buint8 n

public export
not : DDCType -> DDCType
not t = (t .+ UNIT) # isRight

public export
mkNotTerm : MkTerm tElem (not tElem)
mkNotTerm _ _ = Right () `Element` Refl
