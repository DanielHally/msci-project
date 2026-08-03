||| Utilities for bit manipulation

module DDC.Binary

import public Data.Bits
import Data.Buffer
import public Data.Vect
import Decidable.Equality
import public System.File

import public DDC.Util

%default total

||| A bit string
public export
Binary : Type
Binary = VectAndLength Bool

||| Inverse of Data.Bits.asBitVector
export
fromBitVector : FiniteBits a => Vect (bitSize {a}) Bool -> a
fromBitVector bits =
    let
        -- Build list of bit indices
        indices = Data.Fin.List.allFins (bitSize {a})

        -- Filter only for set bits
        indices' = filter (flip index bits) indices
    in
        foldl setBit (zeroBits {a}) (bitsToIndex <$> indices')

||| Data.Bits.asBitVector but with MSB -> LSB ordering
export
asBinary : FiniteBits a => a -> Vect (bitSize {a}) Bool
asBinary = reverse . asBitVector

||| fromBitVector but with MSB -> LSB ordering
export
fromBinary : FiniteBits a => Vect (bitSize {a}) Bool -> a
fromBinary = fromBitVector . reverse

||| asBinary for an ASCII character
-- TODO: enforce ASCII
export
charAsBinary : Char -> Vect 8 Bool
charAsBinary x = asBinary $ cast {to=Bits8} x

||| fromBinary for an ASCII character
export
charFromBinary : Vect 8 Bool -> Char
charFromBinary x = cast {to=Char} $ fromBinary {a=Bits8} x

||| Try to read the bits of a file
export
covering readFileBits :(path : String) -> IO (Either FileError Binary)
readFileBits path = do
    -- Try load file
    Right buf <- createBufferFromFile path
        | Left err => pure $ Left err

    -- Convert contents to Binary
    contents <- bufferData' buf
    let contents' = fromList contents
    pure . Right . vectAndLength . concat $ map asBinary contents'

export
stringToBinary : String -> Binary
stringToBinary s =
    let
        (_ ** chars) = unpackVect s
    in
        vectAndLength . concat $ map charAsBinary chars

public export
compareBinary : Binary -> Binary -> Bool
compareBinary (al ** a) (bl ** b) =
    case al `decEq` bl of
        Yes prf => a == (rewrite prf in b)
        No _ => False
