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

import PacketLang

%default total

--------
-- IF --
--------

ifTest : PacketLang
ifTest = with PacketLang do
    flag <- bool
    p_if flag cstring (bits 8) -- p_if syntax macro not possible in Idris 2

ifTestInst1 : (mkTy Main.ifTest)
ifTestInst1 = (True ## "Flag was set")

ifTestInst2 : (mkTy Main.ifTest)
ifTestInst2 = (False ## (BInt 100 Oh))

showIfTest : (mkTy Main.ifTest) -> String
showIfTest (True ** str) = "True, str: "++ str.value -- Can't pattern match on ##, need .value for Ascii
showIfTest (False ** (BInt x oh)) = "False, int: "++ (show x)

-- The first test can be done at compile time
test_if1 : showIfTest Main.ifTestInst1 = "True, str: Flag was set"
test_if1 = Refl

-- Integer show uses primitives so the second test can't be proven at compile time

----------
-- (//) --
----------

eitherTest : PacketLang
eitherTest = innerTestLang1 // innerTestLang2
    where
        innerTestLang1 : PacketLang
        innerTestLang1 = do
            cstring
            cstring

        innerTestLang2 : PacketLang
        innerTestLang2 = bits 8

eitherTestInst1 : (mkTy Main.eitherTest)
eitherTestInst1 = (Left ("hello" ## "world"))

eitherTestInst2 : (mkTy Main.eitherTest)
eitherTestInst2 = (Right (BInt 21 Oh))

showEitherTest : (mkTy Main.eitherTest) -> String
showEitherTest (Left (s1 ** s2)) = "Left, s1: " ++ s1.value ++ ", s2: " ++ s2.value
showEitherTest (Right (BInt x oh)) = "Right, int: " ++ (show x)

test_show1 : showEitherTest Main.eitherTestInst1 = "Left, s1: hello, s2: world"
test_show1 = Refl

-- Second test again uses integer show primitive

----------
-- LIST --
----------

{-
    (Note: The LIST constructor is greedy, and as such will accept anything that it matches. For
    this reason, we use a slightly more complex packet speciﬁcation in this test, to ensure that the
    data that follows is not subsumed).
-}

innerListStruct : PacketLang
innerListStruct = do
    b1 <- (bits 8)
    check ((val b1) < 10)

-- x : Bounded 8 **
-- Subset (Maybe (So (x < 10))) (So $ isJust x)

listTest : PacketLang
listTest = with PacketLang do
    list innerListStruct
    cstring

-- x : (n : Nat ** Vect n (mkTy Main.innerListStruct)) **
-- Ascii

listTestInst : (mkTy Main.listTest)
listTestInst = (
        vectAndLength [
            ((BInt 1 Oh) ## propPassed),
            ((BInt 2 Oh) ## propPassed),
            ((BInt 3 Oh) ## propPassed)
        ]
        ## "hello"
    )
    where
        -- The representations of propositions are much less elegant than the original Oh
        propPassed : Subset (Maybe (So True)) (\x => isJust x = True)
        propPassed = Element (Just Oh) Refl

showListTest : (mkTy Main.listTest) -> String
showListTest ((_ ** xs) ** s) =
    "List: " ++ (show $ map fst xs) ++ ", s: " ++ s.value

-- Again needs integer show

-----------
-- LISTN --
-----------

listNTest : PacketLang
listNTest = with PacketLang do
    listn 5 cstring
    bits 8

-- x : Subset (n : Nat ** Vect n Ascii) (\x => (let (len ** _) = x in len == 5) = True) **
-- Bounded 8

listNTestInst : (mkTy Main.listNTest)
listNTestInst =
    (
        vectAndLength [
            "This",
            "is",
            "another",
            "PacketLang",
            "test"
        ]
        `Element`
        Refl
    )
    ##
    (BInt 5 Oh)

-- Can't explicitly say Oh
-- Ugly ARRAY
showListNTest : (mkTy Main.listNTest) -> String
showListNTest ((_ ** xs) `Element` _ ** (BInt n _)) = "ListN: " ++
    (show xs) ++ ", int: " ++ (show n)

-- Again needs integer show

----------
-- P_EQ --
----------

eqTest : PacketLang
eqTest = with PacketLang do
    x1 <- bits 8
    x2 <- bits 8
    prop (prop_eq (val x1) (val x2))

eqTestInst : (mkTy Main.eqTest)
eqTestInst = ((BInt 5 Oh) ## (BInt 5 Oh) ## propPassed) where
    propPassed : Subset (Maybe (the Int 5 = 5)) (\x => isJust x = True)
    propPassed = Element (Just Refl) Refl

showEqTest : (mkTy Main.eqTest) -> String
showEqTest (n ** m ** p) =
    "Int1: " ++ (show $ val n) ++ ", " ++ "Int2: " ++ (show $ val m) ++ ", refl"

-- Again needs integer show

------------
-- P_BOOL --
------------

boolTest : PacketLang
boolTest = with PacketLang do
    b1 <- bool
    check b1

boolTestInst : (mkTy Main.boolTest)
boolTestInst = (True ## propPassed) where
    propPassed : Subset (Maybe (So True)) (\x => isJust x = True)
    propPassed = Just Oh `Element` Refl

showBoolTest : (mkTy Main.boolTest) -> String
showBoolTest (b ** _) = "Bool test, " ++ (show b)

test_bool : showBoolTest Main.boolTestInst = "Bool test, True"
test_bool = Refl

-----------
-- P_AND --
-----------

andTest : PacketLang
andTest = with PacketLang do
    b1 <- bool
    b2 <- bool
    prop (prop_and (prop_bool b1) (prop_bool b2))

andTestInst : (mkTy Main.andTest)
andTestInst = (True ## True ## propPassed) where
    propPassed : Subset (Maybe (Both (P_BOOL True) (P_BOOL True))) (\x => isJust x = True)
    propPassed = Just (MkBoth Oh Oh) `Element` Refl

-- Original was simpler due to all cases being directly proven impossible
showAndTest : (mkTy Main.andTest) -> String
showAndTest (True ** True ** (Just (MkBoth Oh Oh) `Element` _)) = "And test passed"
showAndTest (True ** False ** (Just (MkBoth Oh contra) `Element` _)) = absurd contra
showAndTest (False ** _ ** (Just (MkBoth contra _) `Element` _)) = absurd contra

test_and : showAndTest Main.andTestInst = "And test passed"
test_and = Refl

----------
-- P_OR --
----------

orTest : PacketLang
orTest = with PacketLang do
    b1 <- bool
    b2 <- bool
    prop (prop_or (prop_bool b1) (prop_bool b2))

orTestInst1 : (mkTy Main.orTest)
orTestInst1 = (True ## False ## propPassed) where
    propPassed : Subset (Maybe (Either (So True) (So False))) (\x => isJust x = True)
    propPassed = Just (Left Oh) `Element` Refl

orTestInst2 : (mkTy Main.orTest)
orTestInst2 = (False ## True ## propPassed) where
    propPassed : Subset (Maybe (Either (So False) (So True))) (\x => isJust x = True)
    propPassed = Just (Right Oh) `Element` Refl

-- Should be possible to reduce this to 3 cases, but compiler claims not covering
showOrTest : (mkTy Main.orTest) -> String
showOrTest (b1@True ** b2@True ** Just (Left Oh) `Element` _) =
    "Left, b1: " ++ show b1 ++ ", b2: " ++ show b2
showOrTest (b1@True ** b2@False ** Just (Left Oh) `Element` _) =
    "Left, b1: " ++ show b1 ++ ", b2: " ++ show b2
showOrTest (b1@False ** b2@True ** Just (Right Oh) `Element` _) =
    "Right, b1: " ++ (show b1) ++ ", b2: " ++ (show b2)
showOrTest (b1@True ** b2@True ** Just (Right Oh) `Element` _) =
    "Right, b1: " ++ (show b1) ++ ", b2: " ++ (show b2)
showOrTest (False ** False ** Just (Left contra) `Element` _) = absurd contra
showOrTest (False ** False ** Just (Right contra) `Element` _) = absurd contra


test_or1 : showOrTest Main.orTestInst1 = "Left, b1: True, b2: False"
test_or1 = Refl

test_or2 : showOrTest Main.orTestInst2 = "Right, b1: False, b2: True"
test_or2 = Refl

----------
-- Main --
----------

testEq : String -> String -> String
testEq a b =
    if a == b then
        "passed - " ++ a
    else
        "failed - (" ++ a ++ ") != (" ++ b ++ ")"

main : IO ()
main = do
    putStr "IF 1: "
    putStrLn $ showIfTest ifTestInst1 `testEq` "True, str: Flag was set"
    putStr "IF 2: "
    putStrLn $ showIfTest ifTestInst2 `testEq` "False, int: 100"

    putStr "(//) 1: "
    putStrLn $ showEitherTest eitherTestInst1 `testEq` "Left, s1: hello, s2: world"
    putStr "(//) 2: "
    putStrLn $ showEitherTest eitherTestInst2 `testEq` "Right, int: 21"
    
    putStr "LIST: "
    putStrLn $ showListTest listTestInst `testEq` "List: [1, 2, 3], s: hello"

    putStr "LISTN: "
    putStrLn $ showListNTest listNTestInst `testEq` "ListN: [\"This\", \"is\", \"another\", \"PacketLang\", \"test\"], int: 5"

    putStr "P_EQ: "
    putStrLn $ showEqTest eqTestInst `testEq` "Int1: 5, Int2: 5, refl"

    putStr "P_BOOL: "
    putStrLn $ showBoolTest boolTestInst `testEq`"Bool test, True"

    putStr "P_AND: "
    putStrLn $ showAndTest andTestInst `testEq` "And test passed" 

    putStr "P_OR 1: "
    putStrLn $ showOrTest orTestInst1 `testEq` "Left, b1: True, b2: False"
    putStr "P_OR 2: "
    putStrLn $ showOrTest orTestInst2 `testEq` "Right, b1: False, b2: True"
