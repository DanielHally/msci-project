||| Some example base type implementations that may be useful

module DDC.BaseTypes

import public Data.Bits

import public DDC.Ascii
import public DDC.Binary
import public DDC.DSL
import DDC.Error
import DDC.Parse
import DDC.Util

%default total

||| An ASCII character
-- TODO: enforce ASCII
public export
Pchar : DDCType
Pchar = BASE_TYPE Char encode decode where
    encode : Char -> Binary
    encode = vectAndLength . charAsBinary

    decode : Binary -> Offset -> (Offset, BaseResult Char)
    decode (len ** b) w =
        case w' `isLTE` len of
            Yes _ =>
                let
                    bits = slice w 8 b
                    val = charFromBinary bits
                in
                    (w', BaseOk val (MkSpan w w'))
            No _ =>
                (w, BaseFail (MkFail 1) (MkSpan w w))
        where
            w' = w+8

encodeString : Ascii -> Binary
encodeString s =
    let
        (_ ** s') = unpackVect s
        encoded = Data.Vect.concat $ map charAsBinary s'
    in
        (_ ** encoded)

||| An ASCII string with a terminator substring
public export
Pstring : Ascii -> DDCType
Pstring s = BASE_TYPE Ascii encode decode where
    encode : Ascii -> Binary
    encode x = encodeString (x ++ s)

    decode' : Binary -> Offset -> Offset -> Ascii -> (Offset, BaseResult Ascii)
    decode' (len ** b) w w' acc = assert_total $ -- TODO: totality - w' is strictly increasing
        case w'+8 `isLTE` len of
            Yes prf =>
                let
                    bits = slice w' 8 b
                    char = charFromBinary bits
                in case ascii (pack [char]) of
                    Just char' =>
                        let
                            acc' = acc ++ char'
                        in if isSuffixOf s acc' then
                            (w'+8, BaseOk (dropLast (length s) acc') (MkSpan w (w'+8)))
                        else
                            decode' (len ** b) w (w' + 8) acc'
                    Nothing =>
                            (w', BaseFail (MkFail 1) (MkSpan w w'))
            No _ =>
                    (w', BaseFail (MkFail 1) (MkSpan w w'))

    decode : Binary -> Offset -> (Offset, BaseResult Ascii)
    decode b w = decode' b w w ""

||| Variant of Pstring that does not move the file cursor past the terminator and
||| does not error on EOF
public export
Pstring_Alt : Ascii -> DDCType
Pstring_Alt s = BASE_TYPE Ascii encode decode where
    encode : Ascii -> Binary
    encode x = encodeString (x ++ s)

    decode' : Binary -> Offset -> Offset -> Ascii -> (Offset, BaseResult Ascii)
    decode' (len ** b) w w' acc = assert_total $ -- TODO: totality - w' is strictly increasing
        case w'+8 `isLTE` len of
            Yes prf =>
                let
                    bits = slice w' 8 b
                    char = charFromBinary bits
                in case ascii (pack [char]) of
                    Just char' =>
                        let
                            acc' = acc ++ char'
                        in if isSuffixOf s acc' then
                            let
                                w'' = (w'+8) `minus` (length s * 8)
                                acc'' = dropLast (length s) acc'
                            in
                                (w'', BaseOk acc'' (MkSpan w w''))
                        else
                            decode' (len ** b) w (w' + 8) acc'
                    Nothing =>
                            (w', BaseFail (MkFail 1) (MkSpan w w'))
            No _ =>
                    (w', BaseOk acc (MkSpan w w'))

    decode : Binary -> Offset -> (Offset, BaseResult Ascii)
    decode b w = decode' b w w ""

||| A fixed width string
public export
Pstring_FW : Nat -> DDCType
Pstring_FW n = BASE_TYPE Ascii encode decode where
    encode : Ascii -> Binary
    encode s =
        let
            len = length s.value
            s' = if len < n then
                    s ++ (replicate (n `minus` len) '\0')
                else
                    substr 0 n s
        in
            encodeString s'

    decode' : Binary -> Offset -> Offset -> Ascii -> (Offset, BaseResult Ascii)
    decode' (len ** b) w w' acc = assert_total $ -- TODO: totality - w' is strictly increasing
        case w'+8 `isLTE` len of -- TODO: this check may be movable to wrapper function as length is fixed
            Yes _ =>
                let
                    bits = slice w' 8 b
                    char = charFromBinary bits
                in case ascii (pack [char]) of
                    Just char' =>
                        let
                            acc' = acc ++ char'
                        in if length acc' >= n then
                            -- TODO: trim padding?
                            (w'+8, BaseOk acc' (MkSpan w (w'+8)))
                        else
                            decode' (len ** b) w (w' + 8) acc'
                    Nothing =>
                        (w', BaseFail (MkFail 1) (MkSpan w w'))
            No _ =>
                (w', BaseFail (MkFail 1) (MkSpan w w'))

    decode : Binary -> Offset -> (Offset, BaseResult Ascii)
    decode b w = decode' b w w ""

||| Any type implementing the FiniteBitsInteger interface, parsed from ASCII digits
public export
PfiniteBitsInteger : (a : Type) -> {auto _ : Show a} -> {auto _ : FiniteBitsInteger a} -> DDCType
PfiniteBitsInteger a = BASE_TYPE a encode decode
    where
        encode : a -> Binary
        encode s = encodeString $ MkAscii (show s) showIntAscii where
            -- Can't do proofs over the primitive integer show functions
            showIntAscii : isAsciiString (show s) = True
            showIntAscii = believe_me $ Refl {x=True}

        decode : Binary -> Offset -> (Offset, BaseResult a)
        decode b w = iter [] b w where
            finalize : List Char -> Offset -> (Offset, BaseResult a)
            finalize acc w' = case parseFiniteBits (pack acc) of
                    Just x => (w', BaseOk x (MkSpan w w'))
                    Nothing => (w', BaseFail (MkErr 1) (MkSpan w w'))

            iter : List Char -> Binary -> Offset -> (Offset, BaseResult a)
            iter acc b w' = assert_total $ -- TODO: totality - w' is strictly increasing
                let
                    (w'', res) = parse Pchar b w'
                in case res.ec `decEq` OK of
                    Yes _ =>
                        let
                            newChar = stripMetadata Pchar res
                        in if isDigit newChar || (signed {a} && newChar == '-') then
                            iter (acc ++ [newChar]) b w''
                        else
                            finalize acc w'
                    No _ => finalize acc w'

public export
Puint64 : DDCType
Puint64 = PfiniteBitsInteger Bits64

public export
Puint32 : DDCType
Puint32 = PfiniteBitsInteger Bits32

public export
Puint16 : DDCType
Puint16 = PfiniteBitsInteger Bits16

public export
Puint8 : DDCType
Puint8 = PfiniteBitsInteger Bits8

public export
Pint64 : DDCType
Pint64 = PfiniteBitsInteger Int64

public export
Pint32 : DDCType
Pint32 = PfiniteBitsInteger Int32

public export
Pint16 : DDCType
Pint16 = PfiniteBitsInteger Int16

public export
Pint8 : DDCType
Pint8 = PfiniteBitsInteger Int8

||| Any type representable by fixed-length binary, implementing the FiniteBits interface
||| Default big-endian, TODO allow little-endian
public export
finiteBitsBaseType : (a : Type) -> {auto _ : Show a} -> {auto _ : FiniteBits a} -> DDCType
finiteBitsBaseType a = BASE_TYPE a encode decode where
    encode : a -> Binary
    encode = vectAndLength . asBinary

    decode : Binary -> Offset -> (Offset, BaseResult a)
    decode (len ** b) w =
        case w + bitSize `isLTE` len of
            Yes prf =>
                let
                    val = fromBinary $ slice w bitSize b {prf}
                    w' = w + bitSize {a}
                in
                    (w', BaseOk val (MkSpan w w'))
            No _ => (w, BaseFail (MkFail 1) (MkSpan w w))

public export
Buint64 : DDCType
Buint64 = finiteBitsBaseType Bits64

public export
Buint32 : DDCType
Buint32 = finiteBitsBaseType Bits32

public export
Buint16 : DDCType
Buint16 = finiteBitsBaseType Bits16

public export
Buint8 : DDCType
Buint8 = finiteBitsBaseType Bits8

public export
Bint64 : DDCType
Bint64 = finiteBitsBaseType Int64

public export
Bint32 : DDCType
Bint32 = finiteBitsBaseType Int32

public export
Bint16 : DDCType
Bint16 = finiteBitsBaseType Int16

public export
Bint8 : DDCType
Bint8 = finiteBitsBaseType Int8

public export
Ip : Type
Ip = (Bits8, Bits8, Bits8, Bits8)

public export
Bip : DDCType
Bip = BASE_TYPE Ip encode decode
    where
        encode : Ip -> Binary
        encode (m, n, o, p) =
            vectAndLength $ asBinary m ++ asBinary n ++ asBinary o ++ asBinary p

        decode : Binary -> Offset -> (Offset, BaseResult Ip)
        decode (len ** b) w =
            case w + 32 `isLTE` len of
                Yes _ =>
                    let
                        dat = slice w 32 b
                        [m, n, o, p] = kSplits 4 8 dat
                        val = (fromBinary m, fromBinary n, fromBinary o, fromBinary p)
                        w' = w + 32
                    in
                        (w', BaseOk val (MkSpan w w'))
                No _ => (w, BaseFail (MkFail 1) (MkSpan w w))
