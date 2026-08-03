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

module PacketLang.BaseTypes

import PacketLang.Bounded
import DDC

%default total

public export
bitsToBounded : {width : Nat} -> (v : Vect width Bool) -> Bounded width
bitsToBounded v = BInt (impl 0 v) (believe_me Oh) where
    impl : Int -> Vect n Bool -> Int
    impl acc [] = acc
    impl acc (x::xs) =
        let
            b = the Int $ if x then 1 else 0
            acc' = (acc `shiftL` 1) + b
        in
            impl acc' xs

public export
boundedToBits : {width : Nat} -> Bounded width -> Vect width Bool
boundedToBits {width} (BInt x _ ) = reverse $ impl width x where
    impl : (n : Nat) -> (x : Int) -> Vect n Bool
    impl Z _ = []
    impl (S k) x =
        let
            b = testBit x 0
            x' = x `shiftR` 1
        in
            (b :: impl k x')

public export
Bbit : (width : Nat) -> (0 p : So $ width > 0) -> DDCType
Bbit width p = BASE_TYPE (Bounded width) encode decode where
    encode : (Bounded width) -> Binary
    encode = vectAndLength . boundedToBits 

    decode : Binary -> Offset -> (Offset, BaseResult $ Bounded width)
    decode (len ** b) w =
        case w' `isLTE` len of
            Yes prf =>
                let
                    val = bitsToBounded $ slice w width b {prf}
                in
                    (w', BaseOk val (MkSpan w w'))
            No _ => (w, BaseFail (MkFail 1) (MkSpan w w))
        where
            w' = w + width

public export
Bcbool : DDCType
Bcbool = BASE_TYPE Bool encode decode where
    encode : Bool -> Binary
    encode b = vectAndLength [b]

    decode : Binary -> Offset -> (Offset, BaseResult Bool)
    decode (len ** b) w =
        case w `isLT` len of
            Yes prf =>
                let
                    val = index (natToFinLT w) b
                in
                    (w', BaseOk val (MkSpan w w'))
            No _ => (w, BaseFail (MkFail 1) (MkSpan w w))
        where
            w' = w + 1

public export
Bdecodable :
    (n : Nat) ->
    {auto 0 p : So (n > 0)} ->
    (t : Type) ->
    {auto _ : Show t} ->
    (Bounded n -> Maybe t) ->
    (t -> Bounded n) ->
    DDCType
Bdecodable n t decode encode = BASE_TYPE t encode' decode' where
    encode' : t -> Binary
    encode' = vectAndLength . boundedToBits . encode

    decode' : Binary -> Offset -> (Offset, BaseResult t)
    decode' b w = assert_total $ -- Otherwise chunkTy would fail
        let
            (w', res) = parse (Bbit n p) b w
            res' = case res.ec `decEq` OK of
                Yes _ => case decode $ getBaseRep res of
                    Just x => BaseOk x res.sp
                    Nothing => BaseFail (MkFail 1) res.sp
                No _ => BaseFail res.err res.sp
        in 
            (w', res')
