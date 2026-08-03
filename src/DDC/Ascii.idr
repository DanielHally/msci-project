||| Strings constrained to ASCII characters, and some helper functions for them
||| 
||| Based on https://idris-community.github.io/idris2-tutorial/Tutorial/Prim/Refined.html
|||
||| BSD 3-Clause License
|||
||| Copyright (c) 2021, Stefan Höck
||| Copyright (c) 2025, Idris Community (Unoffical)
||| All rights reserved.
|||
||| Redistribution and use in source and binary forms, with or without
||| modification, are permitted provided that the following conditions are met:
|||
||| 1. Redistributions of source code must retain the above copyright notice, this
||| list of conditions and the following disclaimer.
|||
||| 2. Redistributions in binary form must reproduce the above copyright notice,
||| this list of conditions and the following disclaimer in the documentation
||| and/or other materials provided with the distribution.
|||
||| 3. Neither the name of the copyright holder nor the names of its
||| contributors may be used to endorse or promote products derived from
||| this software without specific prior written permission.
|||
||| THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
||| AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
||| IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
||| DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
||| FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
||| DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
||| SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
||| CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
||| OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
||| OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

module DDC.Ascii

import Data.String
import public Data.Vect
import Decidable.Equality

%default total

public export
isAsciiChar : Char -> Bool
isAsciiChar c = ord c <= 127

public export
isAsciiString : String -> Bool
isAsciiString = all isAsciiChar . unpack

public export
record Ascii where
  constructor MkAscii
  value : String
  0 prf : isAsciiString value = True

public export
fromString : (s : String) -> {auto 0 prf : isAsciiString s = True} -> Ascii
fromString s = MkAscii s prf

public export
ascii : String -> Maybe Ascii
ascii x = case isAsciiString x `decEq` True of
  Yes prf   => Just $ MkAscii x prf
  No contra => Nothing

public export
0 allAppend :  (f : Char -> Bool)
            -> (s1,s2 : String)
            -> (p1 : all f (unpack s1) = True)
            -> (p2 : all f (unpack s2) = True)
            -> all f (unpack (s1 ++ s2)) = True
allAppend f s1 s2 p1 p2 = believe_me $ Refl {x = True}

public export
(++) : Ascii -> Ascii -> Ascii
MkAscii s1 p1 ++ MkAscii s2 p2 = MkAscii (s1 ++ s2) (allAppend isAsciiChar s1 s2 p1 p2)

public export
0 allReverse :  (f : Char -> Bool)
             -> (s : String)
             -> (p : all f (unpack s1) = True)
             -> all f (unpack (reverse s)) = True
allReverse f s p = believe_me $ Refl {x = True}

public export
reverse : Ascii -> Ascii
reverse (MkAscii s p) = MkAscii (reverse s) (allReverse isAsciiChar s p)

public export
0 allSubstr :  (f : Char -> Bool)
            -> (s : String)
            -> (p : all f (unpack s1) = True)
            -> all f (unpack (substr x y s)) = True
allSubstr f s p = believe_me $ Refl {x = True}

public export
substr : (index : Nat) -> (len : Nat) -> (subject : Ascii) -> Ascii
substr s e (MkAscii subj p) = MkAscii (substr s e subj) (allSubstr isAsciiChar subj p)

public export
0 allReplicate :  (f : Char -> Bool)
            -> (c : Char)
            -> (p : f c = True)
            -> all f (unpack (replicate n c)) = True
allReplicate f c p = believe_me $ Refl {x = True}

public export
replicate : Nat -> (c : Char) -> {auto 0 prf : isAsciiChar c = True} -> Ascii
replicate n c = MkAscii (replicate n c) (allReplicate isAsciiChar c prf)

public export
length : Ascii -> Nat
length = length . value

public export
unpack : Ascii -> List Char
unpack = unpack . value

public export
drop : (n : Nat) -> (input : Ascii) -> Ascii
drop n str = substr n (length str) str

public export
dropLast : (n : Nat) -> (input : Ascii) -> Ascii
dropLast n str = reverse (drop n (reverse str))

public export
isSuffixOf : Ascii -> Ascii -> Bool
isSuffixOf s1 s2 = isSuffixOf s1.value s2.value

public export
implementation Show Ascii where
    show = show . value

public export
implementation Eq Ascii where
    a == b = a.value == b.value

||| Vect version of unpack
public export
unpackVect : Ascii -> (n ** Vect n Char)
unpackVect x = (_ ** fromList $ unpack x)
