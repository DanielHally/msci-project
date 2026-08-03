||| Miscellaneous utility functions not directly tied to the DDC

module DDC.Util

import public Data.Bits
import public Data.DPair
import public Data.Either
import public Data.Nat
import public Data.String
import public Data.Vect
import public Data.Vect.Quantifiers

%default total

||| Commutated version of plusMinunsLte
public export
plusMinusLte' : (a : Nat) -> (b : Nat) -> (prf : a `LTE` b) -> a + (b `minus` a) = b
plusMinusLte' a b prf = rewrite plusCommutative a (b `minus` a) in
                        rewrite plusMinusLte a b prf in
                        Refl
public export
VectAndLength : Type -> Type
VectAndLength a = (n ** Vect n a)

public export
vectAndLength : {n : Nat} -> Vect n a -> (n ** Vect n a)
vectAndLength v = (n ** v)

public export
asVectAndLength : List a -> VectAndLength a
asVectAndLength l = (_ ** fromList l)

public export
(++) : VectAndLength a -> VectAndLength a -> VectAndLength a
(n ** xs) ++ (m ** ys) = (n+m ** xs ++ ys)

namespace VectAndLength'
    public export
    (++) : {m : Nat} -> VectAndLength a -> Vect m a -> VectAndLength a
    (n ** xs) ++ ys = (n+m ** xs ++ ys)

-- This form is easier to prove internally, but less convenient for callers to prove
-- TODO: this can probably be 1 function?
public export
slice' : (start : Nat) -> (n : Nat) -> Vect (start + (n + m)) a -> Vect n a
slice' start n v = take n $ drop start v

||| Takes exactly `n` elements starting at index `start` of a `Vect`
||| Requires proof that this isn't out of bounds
public export
slice : {len : Nat} -> (start : Nat) -> (n : Nat) -> Vect len a -> {auto 0 prf : start+n `LTE` len} -> Vect n a
slice start n v = slice' {m} start n (lenSumPrf v)
    where
        m : Nat
        m = len `minus` (start + n)

        -- slice' requires len in the form start + (n + m)
        -- TODO: it should be possible to write this with m
        lenSumPrf : Vect len a -> Vect (start + (n + (len `minus` (start + n)))) a
        lenSumPrf v =
            -- Correct bracket direction
            rewrite plusAssociative start n (len `minus` (start + n)) in 

            -- start+n <= len allows for m=len `minus` (start + n)
            -- in len = start + n + m
            rewrite plusMinusLte' (start + n) len prf in
            v

||| Vect version of Prelude pack
public export
packVect : Vect n Char -> String
packVect = pack . toList

||| Vect version of Prelude unpack
public export
unpackVect : String -> (n ** Vect n Char)
unpackVect = asVectAndLength . unpack

public export
RightTy : {t: Type} -> Either _ t -> Type
RightTy {t} _ = t

public export
mapPrf : {Prf : a -> Type} -> (xs : Vect n a) -> (0 _ : All Prf xs) -> Vect n (Subset a Prf)
mapPrf [] Nil = []
mapPrf (x :: xs) (p :: ps) = (x `Element` p) :: mapPrf xs ps

public export
indented : Nat -> String -> String
indented n s = replicate (n*4) ' ' ++ s

||| Unlines without a trailing \n
public export
unlines' : List String -> String
unlines' [] = ""
unlines' (x::xs) = impl x xs where
    impl : String -> List String -> String
    impl acc [] = acc
    impl acc (x::xs) = impl (acc ++ "\n" ++ x) xs

public export
decEither : (e : Either a b) -> Either (IsLeft e) (IsRight e)
decEither e = case e of
    Left _ => Left $ ItIsLeft
    Right _ => Right $ ItIsRight

public export
eitherNotBoth : (e : Either a b) -> IsLeft e -> IsRight e -> Void
eitherNotBoth (Right _) ItIsLeft ItIsRight impossible

public export
equivalentLefts : {x : Either _ _} -> (p1 : IsLeft x) -> (p2 : IsLeft x) -> p1 = p2
equivalentLefts ItIsLeft ItIsLeft = Refl

public export
equivalentRights : {x : Either _ _} -> (p1 : IsRight x) -> (p2 : IsRight x) -> p1 = p2
equivalentRights ItIsRight ItIsRight = Refl

public export
equalNatId : (n : Nat) -> equalNat n n = True
equalNatId Z = Refl
equalNatId (S x) = equalNatId x

public export
vectZeroToN : (n : Nat) -> Vect n Bits32
vectZeroToN n = iter n 0 where
    iter : (n : Nat) -> Bits32 -> Vect n Bits32
    iter Z x = []
    iter (S k) x = x :: iter k (x+1)

||| Idris has no in-built cast from Bits8 to Fin 256
||| Restrict is used here to avoid proofs; the mod case will never happen since Bits8 <= 255
public export
bits8ToFin : Bits8 -> Fin 256
bits8ToFin x = restrict 255 $ cast x

||| For any non-zero x, x - 1 + 1 = x
public export
succMinusOne : (x : Nat) -> {auto prf : IsSucc x} -> x = S (x `minus` 1)
succMinusOne Z impossible
succMinusOne (S x) = rewrite minusZeroRight x in Refl

||| Easier to prove call signature for Data.Fin.last
public export
last' : (x : Nat) -> {auto prf : IsSucc x} -> Fin x
last' x = rewrite succMinusOne x in last {n=x `minus` 1}

||| Extension fo FiniteBits for a fixed-range integer
public export
interface (FiniteBits a, Cast Integer a, Cast a Integer) => FiniteBitsInteger a where
    signed : Bool
    bitSizeNonZero : IsSucc $ bitSize {a}

public export
implementation FiniteBitsInteger Bits8 where
    signed = False
    bitSizeNonZero = ItIsSucc

public export
implementation FiniteBitsInteger Bits16 where
    signed = False
    bitSizeNonZero = ItIsSucc

public export
implementation FiniteBitsInteger Bits32 where
    signed = False
    bitSizeNonZero = ItIsSucc

public export
implementation FiniteBitsInteger Bits64 where
    signed = False
    bitSizeNonZero = ItIsSucc

public export
implementation FiniteBitsInteger Int8 where
    signed = True
    bitSizeNonZero = ItIsSucc

public export
implementation FiniteBitsInteger Int16 where
    signed = True
    bitSizeNonZero = ItIsSucc

public export
implementation FiniteBitsInteger Int32 where
    signed = True
    bitSizeNonZero = ItIsSucc

public export
implementation FiniteBitsInteger Int64 where
    signed = True
    bitSizeNonZero = ItIsSucc

public export
msb : FiniteBitsInteger a => Index {a}
msb = bitsToIndex $ last' (bitSize {a}) {prf=bitSizeNonZero {a}}

public export
minValue : FiniteBitsInteger a => Integer
minValue =
    if signed {a} then
        cast {from=a} $ setBit zeroBits msb
    else
        cast {from=a} zeroBits

public export
maxValue : FiniteBitsInteger a => Integer
maxValue =
    if signed {a} then
        cast {from=a} $ clearBit oneBits msb
    else
        cast {from=a} oneBits

||| Cast an integer to a FiniteBitsInteger only if it will fit
public export
safeBitsCast : FiniteBitsInteger a => Integer -> Maybe a
safeBitsCast x = do
    guard $ x >= minValue {a} && x <= maxValue {a}
    pure (cast x)

||| Convert a number string to a FiniteBits
public export
parseFiniteBits : FiniteBitsInteger a => String -> Maybe a
parseFiniteBits str = parseInteger str >>= safeBitsCast

||| Proof of identity for Eq Char
public export
charEqId : intToBool (prim__eq_Char x x) = True
charEqId = believe_me $ Refl {x=True} -- required, is primitive

