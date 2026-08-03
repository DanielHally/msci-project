{-
    The MIT License (MIT)

    Copyright (c) 2014 Simon Fowler
    Copyright (c) 2026 Daniel Hally

    Permission is hereby granted, free of charge, to any person obtaining a copy of
    this software and associated documentation files (the "Software"), to deal in
    the Software without restriction, including without limitation the rights to
    use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
    the Software, and to permit persons to whom the Software is furnished to do so,
    subject to the following conditions:

    The above copyright notice and this permission notice shall be included in all
    copies or substantial portions of the Software.

    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
    IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
    FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
    COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
    IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
    CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
-}

module PacketLang.DSL

import public Data.Bits
import public Data.Monoid.Exponentiation
import public Data.So
import public Data.Vect
import public Decidable.Decidable
import public Decidable.Equality

import public PacketLang.Bounded
import public PacketLang.BaseTypes
import public DDC

%default total

public export
data Proposition : Type

public export
propTy : Proposition -> Type

public export
data Both : Proposition -> Proposition -> Type where
    MkBoth : (propTy a) ->
        (propTy b) ->
        Both a b

public export
data Proposition : Type where
    P_EQ : DecEq a => a -> a -> Proposition
    P_BOOL : Bool -> Proposition
    P_AND : Proposition -> Proposition -> Proposition
    P_OR : Proposition -> Proposition -> Proposition

propTy (P_EQ x y) = x=y
propTy (P_BOOL b) = So b
propTy (P_AND s t) = Both s t
propTy (P_OR s t) = Either (propTy s) (propTy t)

public export
data Chunk : Type

public export
bit : (w : Nat) -> {auto 0 p : So (w > 0)} -> Chunk

public export
data Chunk : Type where
    Bit : (width : Nat) -> (0 p : So (width > 0)) -> Chunk
    CBool : Chunk
    CString : Chunk
    LString : Nat -> Chunk
    Prop : (P : Proposition) -> Chunk
    Decodable :
        (n : Nat) ->
        {auto 0 p : So (n > 0)} -> -- Not in original
        (t : Type) ->
        {auto _ : Show t} -> -- Not in original
        (Bounded n -> Maybe t) ->
        (t -> Bounded n) ->
        Chunk

bit w {p} = Bit w p

-- TODO: base type?
public export
unmarshalProp : (p : Proposition) -> Maybe (propTy p)
unmarshalProp (P_EQ x y) = case decEq x y of
    (Yes p) => Just p
    (No p) =>  Nothing
unmarshalProp (P_BOOL b) = case choose b of
    Left p_yes => Just p_yes
    Right _ => Nothing
unmarshalProp (P_AND prop1 prop2) = do
    p1 <- unmarshalProp prop1
    p2 <- unmarshalProp prop2
    Just (MkBoth p1 p2)
unmarshalProp (P_OR p1 p2) = maybe
    (
        maybe
            Nothing
            (\p2' => Just (Right p2'))
            (unmarshalProp p2)
    )
    (\p1' => Just (Left p1'))
    (unmarshalProp p1)

public export
chunkToDDC : Chunk -> DDCType
chunkToDDC (Bit width p) = Bbit width p
chunkToDDC CBool = Bcbool
chunkToDDC CString = Pstring "\0"
chunkToDDC (LString i) = Pstring_FW i
chunkToDDC (Prop p) = COMPUTE (unmarshalProp p) # isJust -- DDC constraints are much weaker, just prove = True
chunkToDDC (Decodable n t f g) = Bdecodable n t f g

public export
chunkTy : Chunk -> Type
chunkTy = RawTy . chunkToDDC

public export
data PacketLang : Type

public export
toDDC : PacketLang -> DDCType

public export
mkTy : PacketLang -> Type
mkTy pl = RawTy $ toDDC pl

public export
data PacketLang : Type where
    CHUNK : (c : Chunk) -> PacketLang
    IF :
        (test : Bool) ->
        (yes : PacketLang) ->
        (no : PacketLang) ->
        PacketLang
    (//) : PacketLang -> PacketLang -> PacketLang
    LIST : PacketLang -> PacketLang
    LISTN : (n : Nat) -> PacketLang -> PacketLang
    NULL : PacketLang
    (>>=) : (p : PacketLang) -> (mkTy p -> PacketLang) -> PacketLang

-- Seems to be no longer implicit in Idris 2
public export
infixl 5 //

toDDC (CHUNK c) = chunkToDDC c
toDDC (IF test yes no) = if test then toDDC yes else toDDC no
toDDC (x // y) = toDDC x .+ toDDC y
toDDC (LIST x) = SEQUENCE (toDDC x) UNIT mkUnitSep (const False) (not $ toDDC x) (mkNotTerm)
toDDC (LISTN n x) = ARRAY (toDDC x) n
toDDC NULL = UNIT
toDDC (p >>= f) = DEPSUM (toDDC p) (toDDC . f)

-- chunkTy (Bit w p) = Bounded w
-- chunkTy CString = String
-- chunkTy (LString i) = String
-- chunkTy (Prop p) = propTy p
-- chunkTy (CBool) = Bool
-- chunkTy (Decodable n t encode_fn decode_fn) = t

-- mkTy (CHUNK c) = chunkTy c
-- mkTy (IF x t e) = if x then (mkTy t) else (mkTy e)
-- mkTy (l // r) = Either (mkTy l) (mkTy r)
-- mkTy (LIST x) = List (mkTy x)
-- mkTy (LISTN n a) = Vect n (mkTy a)
-- mkTy NULL = ()
-- mkTy (c >>= k) = (x ** mkTy (k x))
