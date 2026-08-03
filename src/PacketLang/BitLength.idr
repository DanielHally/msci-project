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

module PacketLang.BitLength

import public PacketLang.DSL

%default total

public export
Length : Type
Length = Nat

public export
bitLength : (pl : PacketLang) -> mkTy pl -> Length

public export
listLength : (pl : PacketLang) -> List (mkTy pl) -> Length
listLength pl [] = 0
listLength pl (x :: xs) = bitLength pl x + (listLength pl xs)

public export
vectLength : (pl : PacketLang) -> Vect n (mkTy pl) -> Length
vectLength pl [] = 0
vectLength pl (x :: xs) = bitLength pl x + (vectLength pl xs)

public export
chunkLength : (c : Chunk) -> chunkTy c -> Length
chunkLength (Bit w p) _ = w
chunkLength CBool _ = 1
chunkLength CString str = 8 * (length str + 1)
chunkLength (LString len) str = 8 * len
chunkLength (Decodable n _ _ _) _ = n
chunkLength (Prop _) p = 0

bitLength (CHUNK c) x = chunkLength c x
bitLength (IF True yes _) x = bitLength yes x
bitLength (IF False _ no) x = bitLength no x
bitLength (y // z) x = either (\l_x => bitLength y l_x)
    (\r_x => bitLength z r_x) x
bitLength (LIST pl) x = vectLength pl x.snd -- listLength pl x
bitLength (LISTN n pl) x = vectLength pl x.fst.snd -- vectLength pl x
bitLength NULL _ = 0
bitLength (c >>= k) (a ** b) = bitLength c a + bitLength (k a) b
