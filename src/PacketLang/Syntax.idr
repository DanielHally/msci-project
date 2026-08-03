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

module PacketLang.Syntax

import public Data.So

import public PacketLang.Bounded
import public PacketLang.DSL

%default total

public export
(##) : (fst : a) -> p fst -> DPair a p
(##) = MkDPair

public export
infixr 5 ##

-- Seems to be no longer implicit in Idris 2
public export
(>>) : PacketLang -> PacketLang -> PacketLang
(c >> k) = c >>= const k

public export
bits : (n : Nat) -> {auto 0 p : So (n > 0)} -> PacketLang
bits n {p} = CHUNK $ bit n {p}

public export
check : Bool -> PacketLang
check b = CHUNK $ Prop $ P_BOOL b

public export
cstring : PacketLang
cstring = CHUNK CString

public export
lstring : Nat -> PacketLang
lstring n = CHUNK $ LString n

public export
bool : PacketLang
bool = CHUNK CBool

public export
null : PacketLang
null = NULL

public export
decodable :
    (n : Nat) ->
    {auto 0 p : So (n > 0)} ->
    (t : Type) ->
    {auto _ : Show t} ->
    (Bounded n -> Maybe t) ->
    (t -> Bounded n) ->
    PacketLang
decodable n ty fn1 fn2 = CHUNK $ Decodable n ty fn1 fn2

public export
listn : (n : Nat) -> PacketLang -> PacketLang
listn = LISTN

public export
list : PacketLang -> PacketLang
list = LIST

public export
p_if : 
    (test : Bool) ->
    (yes : PacketLang) ->
    (no : PacketLang) ->
    PacketLang
p_if = IF

public export
p_either : PacketLang -> PacketLang -> PacketLang
p_either = (//)

public export
prop : Proposition -> PacketLang
prop p = CHUNK $ Prop p

public export
prop_bool : Bool -> Proposition
prop_bool = P_BOOL

public export
prop_eq : DecEq a => a -> a -> Proposition
prop_eq = P_EQ

public export
prop_and : Proposition -> Proposition -> Proposition
prop_and = P_AND

public export
prop_or : Proposition -> Proposition -> Proposition
prop_or = P_OR
