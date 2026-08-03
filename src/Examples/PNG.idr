import DDC

import Data.Vect.Quantifiers
import Derive.Prelude
import Derive.Eq
import Derive.Show

%language ElabReflection

%default total

||| A four-byte unsigned integer limited to the range 0 to 2^31-1
pngUint32 : DDCType
pngUint32 = Buint32 # (<= 0x7fffffff)

||| "Each byte of a chunk type is restricted to the hexadecimal values 41 to 5A and 61 to 7A.
||| These correspond to the uppercase and lowercase ISO 646 [ISO646] letters (A-Z and a-z)"
data IsChunkChar : Char -> Type where
    IsLowercase : {auto prf : isLower c = True} -> IsChunkChar c
    IsUppercase : {auto prf : isUpper c = True} -> IsChunkChar c

||| Proof that c can't be a valid PNG chunk type character if it's neither a-z nor A-Z
isNotChunkChar :
    (c : Char) ->
    (contra1 : Not (isLower c = True)) ->
    (contra2 : Not (isUpper c = True)) ->
    Not $ IsChunkChar c
isNotChunkChar c contra1 contra2 (IsLowercase {prf}) = void $ contra1 prf
isNotChunkChar c contra1 contra2 (IsUppercase {prf}) = void $ contra2 prf

||| Decision property for if c is a valid PNG chunk type character
isChunkChar : (c : Char) -> Dec $ IsChunkChar c
isChunkChar c = do
    let No contra1 = isLower c `decEq` True
        | Yes prf => Yes IsLowercase

    let No contra2 = isUpper c `decEq` True
        | Yes prf => Yes IsUppercase
    
    No $ isNotChunkChar c contra1 contra2

ChunkName : Type
ChunkName = Subset (Vect 4 Char) (All IsChunkChar)

||| Type descriptor of a PNG chunk
data ChunkType =
    CT_IHDR |
    CT_PLTE |
    CT_IDAT |
    CT_IEND |
    CT_UNKNOWN (Subset (Vect 4 Char) (All IsChunkChar))

%runElab derive "ChunkType" [Show,Eq]

fromChunkName : ChunkName -> ChunkType
fromChunkName (['I', 'H', 'D', 'R'] `Element` _) = CT_IHDR
fromChunkName (['P', 'L', 'T', 'E'] `Element` _) = CT_PLTE
fromChunkName (['I', 'D', 'A', 'T'] `Element` _) = CT_IDAT
fromChunkName (['I', 'E', 'N', 'D'] `Element` _) = CT_IEND
fromChunkName name = CT_UNKNOWN name

toChunkName : ChunkType -> ChunkName
toChunkName CT_IHDR = (['I', 'H', 'D', 'R'] `Element` [IsUppercase, IsUppercase, IsUppercase, IsUppercase])
toChunkName CT_PLTE = (['P', 'L', 'T', 'E'] `Element` [IsUppercase, IsUppercase, IsUppercase, IsUppercase])
toChunkName CT_IDAT = (['I', 'D', 'A', 'T'] `Element` [IsUppercase, IsUppercase, IsUppercase, IsUppercase])
toChunkName CT_IEND = (['I', 'E', 'N', 'D'] `Element` [IsUppercase, IsUppercase, IsUppercase, IsUppercase])
toChunkName (CT_UNKNOWN name) = name

||| DDCType for ChunkType
BchunkType : DDCType
BchunkType = (BASE_TYPE ChunkType encode decode) where
    raw : DDCType
    raw = (ARRAY Pchar 4)

    encode : ChunkType -> Binary
    encode ty = serialise raw $ MkArray (toChunkName ty).fst

    decode : Binary -> Offset -> (Offset, BaseResult ChunkType)
    decode b w =
        let
            -- Parse underlying chars
            (w', res) = assert_total $ parse raw b w
            Yes isOk = res.ec `decEq` OK
                | No _ => (w', BaseFail (MkFail 1) res.sp)
            (4 ** name) `Element` _ = stripMetadata raw res

            -- Check chars are in bounds
            Yes charsInRange = all isChunkChar name
                | No _ => (w', BaseFail (MkFail 1) res.sp)

            -- Convert to enum
            rep = fromChunkName (name `Element` charsInRange)
        in
            (w', BaseOk rep res.sp)

||| Pre-calculated table for CRC algorithm
crcTable : Vect 256 Bits32
crcTable = map crcByte $ vectZeroToN 256 where
    iter : Nat -> Bits32 -> Bits32
    iter 0 c = c
    iter (S k) c =
        let
            c' = if testBit c 0 then
                    0xedb88320 `xor` (c `shiftR` 1)
                 else
                    c `shiftR` 1
        in
            iter k c'

    crcByte : Bits32 -> Bits32
    crcByte c = iter 8 c

||| Update a CRC with a further set of bytes
update_crc : (crc : Bits32) -> (buf : Vect n Bits8) -> Bits32
update_crc = foldl iter where
    iter : Bits32 -> Bits8 -> Bits32
    iter c buf_n =
        let
            idx = bits8ToFin $ cast c `xor` buf_n
        in
            index idx crcTable `xor` shiftR c 8

||| Calculate CRC as specified by PNG spec
calcCrc : Vect n Bits8 -> Bits32
calcCrc buf = update_crc 0xffffffff buf `xor` 0xffffffff

data ColorType =
    GREYSCALE | -- 0
    TRUECOLOR | -- 2
    INDEXED_COLOR | -- 3
    GREYSCALE_ALPHA | -- 4
    TRUECOLOR_ALPHA  -- 6

%runElab derive "ColorType" [Show, Eq]

ColorTypeId : Type
ColorTypeId = Bits8

fromId : ColorTypeId -> Maybe ColorType
fromId 0 = Just GREYSCALE
fromId 2 = Just TRUECOLOR
fromId 3 = Just INDEXED_COLOR
fromId 4 = Just GREYSCALE_ALPHA
fromId 6 = Just TRUECOLOR_ALPHA
fromId _ = Nothing

toId : ColorType -> ColorTypeId
toId GREYSCALE = 0
toId TRUECOLOR = 2
toId INDEXED_COLOR = 3
toId GREYSCALE_ALPHA = 4
toId TRUECOLOR_ALPHA = 6

BcolorType : DDCType
BcolorType = (BASE_TYPE ColorType encode decode) where
    raw : DDCType
    raw = Buint8

    encode : ColorType -> Binary
    encode ty = serialise raw $ toId ty

    decode : Binary -> Offset -> (Offset, BaseResult ColorType)
    decode b w =
        let
            (w', res) = assert_total $ parse raw b w
            Yes isOk = res.ec `decEq` OK
                | No _ => (w', BaseFail (MkFail 1) res.sp)
            tyId = stripMetadata raw res

        in case fromId tyId of
            Just ty => (w', BaseOk ty res.sp)
            Nothing => (w', BaseFail (MkFail 1) res.sp)

bitDepthsForColorType : ColorType -> List Bits8
bitDepthsForColorType GREYSCALE = [1, 2, 4, 8, 16]
bitDepthsForColorType TRUECOLOR = [8, 16]
bitDepthsForColorType INDEXED_COLOR = [1, 2, 4, 8]
bitDepthsForColorType GREYSCALE_ALPHA = [8, 16]
bitDepthsForColorType TRUECOLOR_ALPHA = [8, 16]

ihdrChunk : DDCType
ihdrChunk = with DDCType do
    width <- pngUint32 # (> 0) . fst
    height <- pngUint32 # (> 0) . fst
    bitDepth <- Buint8
    colorType <- BcolorType # \colorType => elem bitDepth (bitDepthsForColorType colorType)
    compressionMethod <- Buint8
    filterMethod <- Buint8
    Buint8 -- interlaceMethod

IhdrChunk : Type
IhdrChunk = RawTy ihdrChunk

namespace IhdrChunk
    public export
    (.colorType) : IhdrChunk -> ColorType
    (.colorType) (width ** height ** bitDepth ** (colorType `Element` _) ** _) = colorType

||| Determine the body DDCType for a PNG chunk based on its type
chunkBodyTy : ChunkType -> DDCType
chunkBodyTy CT_IHDR = ihdrChunk
chunkBodyTy _ = UNIT -- Unknown chunk type

||| One chunk of a PNG file
chunk : DDCType
chunk = with DDCType do
    -- Can't do pattern match tuple syntax here

    -- RawTy does not resolve if pattern matching in do block
    length <- pngUint32
    -- Encoding these is not ideal, COMPUTE would make it even worse
    chunkType <- BchunkType `WITH_BYTES` 4
    -- Nothing enforces that chunkBodyTy isn't > length
    body <- chunkBodyTy (fst chunkType) `WITH_BYTES` (cast length.fst)
    Buint32 # (== calcCrc ((snd chunkType).fst.snd ++ (snd body).fst.snd))

-- This existing significantly slows compile times
Chunk : Type
Chunk = RawTy chunk

namespace Chunk
    public export
    (.chunkType) : Chunk -> ChunkType
    (.chunkType) c = fst c.snd.fst

    public export
    (.body) : (c : Chunk) -> RawTy (chunkBodyTy c.chunkType)
    (.body) c = fst c.snd.snd.fst

chunkType : Chunk -> ChunkType
chunkType (length ** ty ** _) = fst ty

data OrderConstraint =
    FIRST |
    LAST |
    CONSECUTIVE |
    BEFORE ChunkType |
    AFTER ChunkType

%runElab derive "OrderConstraint" [Show]

data QuantityConstraint =
    ONE_OR_MORE |
    ONE |
    ZERO |
    ZERO_OR_ONE |
    ZERO_OR_MORE

%runElab derive "QuantityConstraint" [Show]

record ChunkRule where
    constructor MkChunkRule
    ty : ChunkType
    order : List OrderConstraint
    quantity : QuantityConstraint
    excluded : List ChunkType

implementation Show ChunkRule where
    show (MkChunkRule ty order quantity excluded) =
        "ChunkRule " ++
        packVect (toChunkName ty).fst ++ " " ++
        show order ++ " " ++
        show quantity ++ " " ++
        show excluded


chunkRules : ColorType -> List ChunkRule
chunkRules colorType = [
    MkChunkRule CT_IHDR [FIRST] ONE [],
    MkChunkRule CT_PLTE [BEFORE CT_IDAT] (plteCount colorType) [],
    MkChunkRule CT_IDAT [CONSECUTIVE] ONE_OR_MORE [],
    MkChunkRule CT_IEND [LAST] ONE []
]
    where
        plteCount : ColorType -> QuantityConstraint
        plteCount GREYSCALE = ZERO
        plteCount GREYSCALE_ALPHA = ZERO
        plteCount INDEXED_COLOR = ONE
        plteCount _ = ZERO_OR_ONE

validOrderConstraint : ChunkType -> Vect n Chunk -> OrderConstraint -> Bool
validOrderConstraint ty chunks FIRST = case chunks of
    (c::cs) => chunkType c == ty
    [] => False
validOrderConstraint ty chunks LAST {n} = case chunks of
    (c::cs) => chunkType (Data.Vect.last (c::cs)) == ty
    [] => False
validOrderConstraint ty chunks CONSECUTIVE = iter False False chunks where
    iter : Bool -> Bool -> Vect m Chunk -> Bool
    iter _ _ [] = True
    iter runStarted runEnded (c::cs) =
        if chunkType c == ty then
            if runEnded then False
            else iter True False cs
        else
            if runStarted then iter True True cs
            else iter False False cs
validOrderConstraint tyX chunks (BEFORE tyY) = iter 0 Nothing Nothing chunks where
    iter : (i : Nat) -> (latestX : Maybe Nat) -> (earliestY : Maybe Nat) -> Vect m Chunk -> Bool
    iter i latestX earliestY [] = case (latestX, earliestY) of
        (Just x, Just y) => x < y
        _ => True
    iter i latestX earliestY (c::cs) =
        let
            latestX' =
                if chunkType c == tyX then
                    Just i
                else
                    latestX
            earliestY' =
                case (isJust earliestY, chunkType c == tyY) of
                    (True, _) => earliestY
                    (False, True) => Just i
                    (False, False) => Nothing
        in
            iter (i+1) latestX' earliestY' cs
validOrderConstraint tyX chunks (AFTER tyY) = iter 0 Nothing Nothing chunks where
    iter : (i : Nat) -> (earliestX : Maybe Nat) -> (latestY : Maybe Nat) -> Vect m Chunk -> Bool
    iter i earliestX latestY [] = case (earliestX, latestY) of
        (Just x, Just y) => x > y
        _ => True
    iter i earliestX latestY (c::cs) =
        let
            earliestX' =
                case (isJust earliestX, chunkType c == tyX) of
                    (True, _) => earliestX
                    (False, True) => Just i
                    (False, False) => Nothing
            latestY' =
                if chunkType c == tyY then
                    Just i
                else
                    latestY
        in
            iter (i+1) earliestX' latestY' cs

-- TODO: fcTL

validQuantityConstraint : ChunkType -> Vect n Chunk -> QuantityConstraint -> Bool
validQuantityConstraint ty chunks constraint =
    let
        (n ** _) = filter ((== ty) . chunkType) chunks
    in case constraint of
        ONE_OR_MORE => n >= 1
        ONE => n == 1
        ZERO => n == 0
        ZERO_OR_ONE => n == 0 || n == 1
        ZERO_OR_MORE => n >= 0

validExcluded : ChunkType -> Vect n Chunk -> ChunkType -> Bool
validExcluded ty chunks excluded = not $ any ((== excluded) . chunkType) chunks

findIHDR : Vect n Chunk -> Maybe IhdrChunk
findIHDR = iter Nothing where
    iter : Maybe IhdrChunk -> Vect m Chunk -> Maybe IhdrChunk
    iter acc [] = acc
    iter acc (c :: cs) = case c of
        (_ ** ((CT_IHDR, _) ** _)) => 
            let
                body : IhdrChunk
                body = c.body
            in case acc of
                Nothing => iter (Just body) cs
                Just _ => Nothing -- Multiple IHDR chunks is invalid
        _ => iter acc cs

validChunkRule : Vect n Chunk -> ChunkRule -> Bool
validChunkRule cs rule =
    all (validOrderConstraint rule.ty cs) rule.order &&
    validQuantityConstraint rule.ty cs rule.quantity &&
    all (validExcluded rule.ty cs) rule.excluded
validChunkSet : VectAndLength Chunk -> Bool
validChunkSet (_ ** cs) = case findIHDR cs of
    Just ihdr => all (validChunkRule cs) (chunkRules ihdr.colorType)
    Nothing => False

||| A PNG file
png : DDCType
png = with DDCType do
    -- signature
    ARRAY Buint8 8 # \((8 ** vals) `Element` _) => vals == [0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]

    UNTIL_EOF chunk # validChunkSet

-- Could add constraints on chunks here

covering showChunks : IO ()
showChunks = do
    Right dat <- readFileBits "small.png"
        | Left err => putStrLn "Failed"

    let (_, res) = parse png dat 0
    printLn res.ec

    let Yes _ = decFull res.rep
        | No _ => printLn "Failed"
    let chunks' = res.rep.snd.rep.val

    let Yes _ = chunks'.ec `decEq` OK
        | No _ => printLn "Failed"
    let (n ** chunks) = stripMetadata (UNTIL_EOF chunk) chunks'

    putStrLn . unlines . toList $ map (show . chunkType) chunks

covering roundTrip : IO ()
roundTrip = do
    Right dat <- readFileBits "small.png"
        | Left err => putStrLn "Failed"

    let (_, res) = parse png dat 0
    printLn res.ec

    let Yes _ = res.ec `decEq` OK
        | No _ => putStrLn "Failed"
    let rep = stripMetadata png res

    let dat' = serialise png rep

    let Yes _ = fst dat `decEq` fst dat'
        | No _ => putStrLn "Different lengths"

    printLn dat'
    printLn $ compareBinary dat dat'

-- Unpacking lambdas break type inference

{-
https://en.wikipedia.org/wiki/BMP_file_format
https://en.wikipedia.org/wiki/Pcap
https://en.wikipedia.org/wiki/ICO_(file_format)
https://en.wikipedia.org/wiki/JPEG
https://www.w3.org/TR/png-3/#5DataRep
-}
