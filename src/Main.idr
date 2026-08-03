import DDC

import Data.String

%default total

covering parsePackToml : (t : DDCType) -> IO (Either FileError (MkTy t))
parsePackToml t = do
    Right dat <- readFileBits "pack.toml"
        | Left err => pure $ Left err
    printLn dat

    -- Parse the whole file as a char sequence
    let (_, res) = parse t dat 0

    -- Print parse descriptor info
    putStrLn $ "Error code:" ++ show res.ec
    putStrLn $ "Error count:" ++ show res.nerr
    putStrLn $ "Span:" ++ show res.sp
    -- putStrLn $ "pdMisc:" ++ show res.pdMisc

    pure $ Right res

asciiFile : DDCType
asciiFile = SEQUENCE Pchar UNIT mkUnitSep noTermCon BOTTOM ()

covering printPackToml : IO ()
printPackToml = do
    Right res <- parsePackToml asciiFile
        | Left err => printLn err

    let Yes _ = res.ec `decEq` OK
        | No _ => printLn "Failed"

    -- Convert char sequence to string and print
    let (len ** contents) = stripMetadata asciiFile res
    printLn $ packVect contents

    putStrLn ""

    -- Check round-trip
    printLn "Re-decode:"
    let reencode = serialise asciiFile (len ** contents)
    let (w', res') = parse asciiFile reencode 0
    let Yes _ = res'.ec `decEq` OK
        | No _ => printLn "Failed"

    let (len' ** contents') = stripMetadata asciiFile res'
    printLn $ packVect contents'
    printLn $ toList contents == toList contents'

line : DDCType
line = Pstring "\n"

covering printPackTomlFirstLine : IO ()
printPackTomlFirstLine = do
    Right res <- parsePackToml line
        | Left err => printLn err 

    printLn res.rep

willFail : DDCType
willFail = Pstring "this string does not exist in the file"

covering printPackTomlFail : IO ()
printPackTomlFail = do
    Right res <- parsePackToml willFail
        | Left err => printLn err 

    printLn res.rep

covering printPackTomlStringOfFive : IO ()
printPackTomlStringOfFive = do
    Right res <- parsePackToml (Pstring_FW 5)
        | Left err => printLn err 

    printLn res.rep

covering printPackTomlIntersection : IO ()
printPackTomlIntersection = do
    Right res <- parsePackToml (Buint32 .& Bint16)
        | Left err => printLn err

    case res.ec `decEq` OK of 
        Yes _ => do
            let (x `Element` xIsOk ** y `Element` yIsOk) = getIntersectionRep res
            putStr "x is "
            printLn $ getBaseRep x
            putStr "y is "
            printLn $ getBaseRep y
        No _ => pure ()

covering pairOfUints : DDCType
pairOfUints = with DDCType do
    Buint32
    Buint32

covering printPackTomlDepsum : IO ()
printPackTomlDepsum = do
    Right res <- parsePackToml pairOfUints
        | Left err => printLn err

    case res.ec `decEq` OK of 
        Yes _ => do
            let (Element x xIsOk ** Element y yIsOk) = getDepsumRep res
            putStr "x is "
            printLn $ getBaseRep x
            putStr "y is "
            printLn $ getBaseRep y
        No _ => pure ()

depsumTest : DDCType
depsumTest = with DDCType do
    -- len `Element` _ <- CONSTRAINED (Pstring ".") (\s => length s > 0)
    -- let len' = cast $ fromMaybe 0 (parseInteger len.value)
    len <- Pstring "." # (>0) . length
    let len' = cast $ fromMaybe 0 (parseInteger len.fst.value)
    Pstring_FW len'
    Pchar .& Pstring "."

covering printDepsumTest : IO ()
printDepsumTest = do
    let binary = stringToBinary "5.1234567."

    putStr "Binary: "
    printLn binary
    putStrLn ""

    let (w', res) = parse depsumTest binary 0
    -- Print parse descriptor info
    putStrLn $ "Error code:" ++ show res.ec
    putStrLn $ "Error count:" ++ show res.nerr
    putStrLn $ "Span:" ++ show res.sp
    -- putStrLn $ "pdMisc:" ++ show res.pdMisc

    putStrLn $ showResult {t=depsumTest} res ++ "\n"

    Yes isOk <- pure $ res.ec `decEq` OK
        | No _ => putStrLn "Failed"

    let (x ** s ** c) = stripMetadata depsumTest res

    putStrLn "Results:"
    printLn x
    printLn s
    printLn c
    putStrLn ""

    let reencode = serialise depsumTest (x ** s ** c)

    putStr "Re-encode:"
    printLn reencode
    putStrLn ""

    let (x' ** s' ** c') = stripMetadata depsumTest res

    putStrLn "Re-decode results:"
    printLn x'
    printLn s'
    printLn c'

{-
-------------
-- Testing --
-------------

random : DDCType
random = with DDCType do
    unit
    bottom
    length <- Puint32
    text <- Pstring_FW $ cast length.rep
    inter <- Puint32 .& Pstring " " .& Puint32
    let (a, inter') = inter.rep
    let (b, c) = inter'.rep
    byteSize <- COMPUTE $ cast length.rep * 8
    unit

random2 : DDCType
random2 = with DDCType do
    Pstring " "
    Pstring_FW 5
    unit
    bottom
    Puint32

basic : DDCType
basic = with DDCType do
    len <- Puint32
    Pstring_FW $ cast len.rep

covering parseBasic : MkTy DDC.basic
parseBasic = snd $ parse basic "4abcdef" 0

--------------------

{- Implementation of a snippet from the DDC paper -}

getdomain : Ip -> String
getdomain (a, b, c, d) = case a of
    207 => "edu"
    _ => "com"

S : String -> DDCType
S str = CONSTRAINED (Pstring_FW 1) (\s => s.rep == str)

authid_t : DDCType
authid_t = (S "-") + Pstring(" ")

response_t : Nat -> DDCType
response_t x = CONSTRAINED (Puint16_FW x) (\y => 100 <= y.rep && y.rep <= 600)

entry_t : DDCType
entry_t = with DDCType do
    client <- Pip
    S " "
    remoteid <- authid_t
    S " "
    response <- response_t 3
    COMPUTE (getdomain client.rep == "edu")

weblog : DDCType
weblog = SEQUENCE entry_t (S "\n") (\_ => False) bottom

exampleLog : String
exampleLog = "207.136.97.49 - 200\n213.120.12.10 - 200"

covering exampleLogRes : MkTy DDC.weblog
exampleLogRes = snd $ parse weblog exampleLog 0

covering firstIp : Maybe String
firstIp = do
    let (n ** entries) = exampleLogRes.rep
    idx <- integerToFin 0 n
    let firstEntry = (index idx entries).rep
    let firstIp = firstEntry.fst.rep
    pure $ show firstIp
-}

AbsorbRoundTrip : DDCType
AbsorbRoundTrip = with DDCType do
    x <- Pchar
    ABSORB (Pchar # (== x)) (x `Element` charEqId)
    Pchar

inst : RawTy AbsorbRoundTrip
inst = ('a' ** () ** 'b')

covering absorbRoundTrip : IO ()
absorbRoundTrip = do
    let x = serialise AbsorbRoundTrip inst
    printLn x
    let (_, res) = parse AbsorbRoundTrip x 0
    putStrLn $ showResult {t=AbsorbRoundTrip} res

boundedString : DDCType
boundedString = do
    len <- Buint32
    Pstring_FW (cast len)

serialiseExample : Binary
serialiseExample = serialise boundedString (5 ** "12345")

covering parseExample : IO ()
parseExample = do
    let (_, res) = parse boundedString serialiseExample 0

    let Yes _ = res.ec `decEq` OK
        | No _ => putStrLn "Parse failed"

    let (len ** msg) = stripMetadata boundedString res
    putStrLn $ (show len) ++ " length message: " ++ msg.value

append : Vect m a -> Vect n a -> Vect (m + n) a
append [] ys = ?ys
append (x::xs) ys = x :: (append xs ys)

covering fakeProof: 1 = 2
fakeProof = fakeProof

CharX : DDCType
CharX = ABSORB (Pstring "\0" # (== "x")) ("x" `Element` Refl)

ScanRoundTrip : DDCType
ScanRoundTrip = do
    SEQUENCE CharX UNIT mkUnitSep noTermCon (not CharX) (mkNotTerm {tElem=CharX})
    SCAN CharX -- Scan >0 is ERR

badData : Binary
badData = vectAndLength $ [
    False,  True,  True,  True,  True, False, False, False,
    False,  True,  True,  True,  True, False, False, False,
    False, False, False, False, False, False, False, False,
    False,  True,  True,  True,  True, False, False, False
]

covering scanRoundTrip : IO ()
scanRoundTrip = do
    let (_, res) = parse ScanRoundTrip badData 0
    putStrLn $ showResult {t=ScanRoundTrip} res
    printLn res.ec

IntersectionRoundTrip : DDCType
IntersectionRoundTrip = Buint8 .& Buint16

intersectionData : Binary
intersectionData = vectAndLength $ [
    False, False, False, False, False, False, False, False,
    False, False, False, False, False, False, False, True
]

covering intersectionRoundTrip : IO ()
intersectionRoundTrip = do
    let (_, res) = parse IntersectionRoundTrip intersectionData 0
    -- putStrLn $ showResult {t=IntersectionRoundTrip} res
    
    let Yes _ = res.ec `decEq` OK
        | No _ => putStrLn "Failed 1"

    let raw = stripMetadata IntersectionRoundTrip res
    printLn raw

    let data' = serialise IntersectionRoundTrip raw
    printLn data'

    let (_, res') = parse IntersectionRoundTrip data' 0
    putStrLn $ showResult {t=IntersectionRoundTrip} res'
    printLn res'.ec

covering intersectionRoundTrip2 : IO ()
intersectionRoundTrip2 = do
    let dat = serialise IntersectionRoundTrip (1, 2)
    let (_, res) = parse IntersectionRoundTrip dat 0   
    putStrLn $ showResult {t=IntersectionRoundTrip} res
    printLn res.ec
