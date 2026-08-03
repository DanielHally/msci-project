||| Helper DSL Syntax

module DDC.Syntax

import public DDC.DSL

%default total

||| Define bind as a dependent sum, allowing do notation to be used
public export
(>>=) : (x : DDCType) -> (y : RawTy x -> DDCType) -> DDCType
(>>=) = DEPSUM

||| Define bind as a dependent sum, allowing do notation to be used
-- Unlike Idris 1, >> must be manually defined too
public export
(>>) : DDCType -> DDCType -> DDCType
a >> b = a >>= \_ => b

||| Define .+ as SUM
||| + has wrong bracket direction
public export
(.+) : DDCType -> DDCType -> DDCType
(.+) = SUM

-- TODO: check precedence
public export
infixr 5 .+

||| Define .& as INTERSECTION
||| & on isn't permitted, while .&. like Data.Bits has wrong bracket direction
public export
(.&) : DDCType -> DDCType -> DDCType
(.&) = INTERSECTION

-- TODO: check precedence
public export
infixr 5 .&

public export
(#) : (t : DDCType) -> (test : Constraint t) -> DDCType
(#) = CONSTRAINED

-- TODO: nicer syntax for other types?
