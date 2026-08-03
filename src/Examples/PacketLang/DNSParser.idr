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

import Examples.PacketLang.DNS

%default total

DNSReference : Type
DNSReference = Int

total data DNSParseError = NonexistentRef Int
                   | BadCode
                   | InternalError String
                   | PayloadUnimplemented

implementation Show DNSParseError where
    show (NonexistentRef i) = "Bad reference: " ++ show i
    show BadCode = "Bad code"
    show (InternalError s) = "Internal error: " ++ s
    show PayloadUnimplemented = "Payload unimplemented"

record DNSState where
    constructor MkDNSState
    blob : ()
    labelCache : List (Position, List DomainFragment)
    pcktLen : Length

packAndMap : Vect n (Bounded 8) -> String
packAndMap xs = packVect $ map (chr . val) xs

unmarshalLabel : (mkTy Examples.PacketLang.DNS.dnsLabel) -> DomainFragment
unmarshalLabel (tagc ** len ** prf ** xs) = packAndMap xs.fst.snd

covering unmarshalReference' : Binary -> Position -> Maybe (List DomainFragment)
unmarshalReference' pckt pos = do
  let res = unmarshal' pckt pos dnsLabels
  case res of
    Just ((lbls ** (Left nt)), res_len) => Just $ toList $ map unmarshalLabel lbls.snd
    Just ((lbls ** (Right (_ ** ref))), res_len) =>
        let
            res = toList $ map unmarshalLabel lbls.snd
            rest = assert_total $ unmarshalReference' pckt (intToNat $ (val ref) * 8) -- TODO intToNat, assert_total
        in 
            [| Just res ++ rest |]
    Nothing => Nothing

covering unmarshalReference : Binary -> DNSReference -> Maybe (List DomainFragment)
unmarshalReference b ref = unmarshalReference' b (intToNat $ ref * 8) -- TODO intToNat

parseDNSHeader : (mkTy Examples.PacketLang.DNS.dnsHeader) -> DNSHeader
parseDNSHeader (ident ** qr ** opcode ** aa ** tc ** rd ** 
                ra ** z ** z_prf ** ans_auth ** nonauth_accept ** resp) = 
  MkDNSHeader (val ident) qr opcode aa tc rd ra ans_auth nonauth_accept resp
  
covering decodeReference : Binary -> DNSReference -> Either DNSParseError (List DomainFragment)
decodeReference b ref =
    let
        -- Cache removed
        unmarshal_res = unmarshalReference b ref
    in maybe
        (Left $ NonexistentRef ref) 
        (\frags => Right frags)
        unmarshal_res

covering decodeLabels : Binary -> (mkTy Examples.PacketLang.DNS.dnsLabels) -> Either DNSParseError (List DomainFragment)
decodeLabels b (lbls ** (Left null_term)) = Right $ toList $ map unmarshalLabel lbls.snd
decodeLabels b (lbls ** (Right (_ ** ref))) =
    let
        decoded_lbls = toList $ map unmarshalLabel lbls.snd
        ref_lbls = decodeReference b (val ref)
    in either
        (\err => Left err)
        (\r_lbls => Right $ decoded_lbls ++ r_lbls)
        ref_lbls

covering decodeDomain : Binary -> (mkTy Examples.PacketLang.DNS.dnsDomain) -> Either DNSParseError (List DomainFragment)
decodeDomain b (Left (_ ** ref)) = decodeReference b (val ref)
decodeDomain b (Right encoded_lbls) = decodeLabels b encoded_lbls

covering parseDNSQuestion : Binary -> (mkTy Examples.PacketLang.DNS.dnsQuestion) -> Either DNSParseError DNSQuestion
parseDNSQuestion b (encoded_domain ** qt ** qc) =
    let
        decoded_domain = decodeDomain b encoded_domain
    in case decoded_domain of
        Left err => Left err
        Right decoded_domain' => 
            Right (MkDNSQuestion decoded_domain' qt qc)

decodeIP : Binary -> (mkTy Examples.PacketLang.DNS.dnsIP) -> SocketAddress
decodeIP b (i1 ** i2 ** i3 ** i4) = 
  IPv4Addr (val i1) (val i2) (val i3) (val i4)

-- decodeNone : (mkTy Examples.PacketLang.DNS.null) -> ()
-- decodeNone _ = ()

covering decodeDomainPayload : Binary -> (mkTy Examples.PacketLang.DNS.dnsDomain) -> Either DNSParseError (DNSPayload DNSDomain)
decodeDomainPayload b dom_pl =
    let
        domain = decodeDomain b dom_pl
    in case domain of
        Left err => Left err
        Right domain' => Right (DNSDomainPayload domain')

getPayloadRel : (pl_ty : DNSPayloadType) ->
              (ty : DNSType) -> 
              (cls : DNSClass) -> 
              Either DNSParseError (DNSPayloadRel ty cls pl_ty)
getPayloadRel DNSIPv4 DNSTypeA DNSClassIN = Right DNSPayloadRelIP
getPayloadRel DNSIPv6 DNSTypeAAAA DNSClassIN = Right DNSPayloadRelIP6
getPayloadRel DNSDomain DNSTypeCNAME DNSClassIN = Right DNSPayloadRelCNAME
getPayloadRel DNSDomain DNSTypeNS DNSClassIN = Right DNSPayloadRelNS
getPayloadRel DNSSOA DNSTypeSOA DNSClassIN = Right DNSPayloadRelSOA
getPayloadRel _ _ _ = Left PayloadUnimplemented

payloadType : DNSType -> DNSClass -> Either DNSParseError DNSPayloadType
payloadType DNSTypeA DNSClassIN = Right DNSIPv4
payloadType DNSTypeAAAA DNSClassIN = Right DNSIPv6
payloadType DNSTypeNS DNSClassIN =  Right DNSDomain
payloadType DNSTypeCNAME DNSClassIN = Right DNSDomain
payloadType DNSTypeSOA DNSClassIN = Right DNSSOA
payloadType _ _ = Left PayloadUnimplemented

covering decodeSOAPayload : Binary -> (mkTy Examples.PacketLang.DNS.dnsSOA) -> Either DNSParseError (DNSPayload DNSSOA)
decodeSOAPayload b (mn ** rn ** ser ** ref ** ret ** exp ** min) =
    let
        mn' = decodeDomain b mn
        rn' = decodeDomain b rn
    in case (mn', rn') of
        (Right mn'', Right rn'') =>
            Right (DNSSOAPayload (MkSOA mn'' rn'' (val ser) (val ref) 
                (val ret)  (val exp)  (val min)))
        (Left err, _) => Left err
        (_, Left err) => Left err

covering decodePayload : Binary -> (pl_rel : DNSPayloadRel ty cl pl_ty) ->
                (mkTy (Examples.PacketLang.DNS.dnsPayloadLang ty cl)) ->
                Either DNSParseError (DNSPayload pl_ty)
decodePayload b DNSPayloadRelIP ip_pl = Right (DNSIPv4Payload (decodeIP b ip_pl))
decodePayload b DNSPayloadRelCNAME dom_pl = decodeDomainPayload b dom_pl
decodePayload b DNSPayloadRelNS dom_pl = decodeDomainPayload b dom_pl
decodePayload b DNSPayloadRelSOA soa_pl = decodeSOAPayload b soa_pl
decodePayload b _ _ = Left (PayloadUnimplemented)

covering parseDNSRecord : Binary -> (mkTy Examples.PacketLang.DNS.dnsRR) ->
                 Either DNSParseError DNSRecord
parseDNSRecord b (encoded_domain ** ty ** cls ** ttl ** len ** payload ** prf) =
    let
        ttl' = val ttl
        domain = (decodeDomain b encoded_domain)
    in case (payloadType ty cls) of
        Left err => Left err
        Right pl_ty =>
            case (domain, getPayloadRel pl_ty ty cls) of
                (Left err, _) => Left err
                (_, Left err) => Left err
                (Right domain', Right pl_rel) =>
                    case decodePayload b pl_rel payload of
                        Left err => Left err
                        Right decoded_pl' => 
                            Right (MkDNSRecord domain' ty cls (val ttl) pl_rel decoded_pl')

-- Ugly hack, since records aren't of the same type and therefore we can't 
-- use sequence. Also proves to the TC that the lengths are as stated.
sequenceRecords : 
               Vect n (Either DNSParseError DNSRecord) -> 
               Vect m (Either DNSParseError DNSRecord) -> 
               Vect l (Either DNSParseError DNSRecord) -> 
               Either DNSParseError (Vect n DNSRecord, Vect m DNSRecord, Vect l DNSRecord)
sequenceRecords v1 v2 v3 = do
    v1' <- sequence v1
    v2' <- sequence v2
    v3' <- sequence v3
    pure (v1', v2', v3')

covering parseDNSPacket :
    Binary ->
    (mkTy Examples.PacketLang.DNS.dns) ->  
    Either DNSParseError DNSPacket
parseDNSPacket
    b
    (
        hdr **
        qdcount **
        ancount **
        nscount ** 
        arcount **
        ((_ ** qs) `Element` _) ** -- Significantly faster than using .fst.snd later
        ((_ ** as) `Element` _) **
        ((_ ** auths) `Element` _) **
        ((_ ** additionals) `Element` _)
    ) =
    let
        hdr' = parseDNSHeader hdr
        n_qdcount = intToNat $ val qdcount
        n_ancount = intToNat $ val ancount
        n_nscount = intToNat $ val nscount
        n_arcount = intToNat $ val arcount
        qs' = map (parseDNSQuestion b) qs
        -- sequence results in TC not terminating
        -- let qs_ = sequence qs'
        qs'' = sequence qs' 
        as' = map (parseDNSRecord b) as
        auths' = map (parseDNSRecord b) auths
        additionals' = map (parseDNSRecord b) additionals
        records = sequenceRecords as' auths' additionals'
        -- Now, see if everything was successful!
    in case (qs'', records) of
        (Right qs''', Right (as'', auths'', additionals'')) =>
            Right (MkDNS hdr' _ _ _ _ qs''' as'' auths'' additionals'')
        -- Record parsing may throw an error
        (Left err, _) => Left err
        (_, Left err) => Left err
        -- Nothing = bad code
        _ => Left BadCode

covering parseDNS : Binary -> (mkTy Examples.PacketLang.DNS.dns) -> Either DNSParseError DNSPacket
parseDNS = parseDNSPacket

{-
data DNSEncodeError = OutOfBoundsError Nat Nat
                    | ProofConstructionError String
                    | LengthMismatchError Nat Nat
                    | UnsupportedPayloadType 
                    | InternalEncodeError String

implementation Show DNSEncodeError where
  show (OutOfBoundsError n1 n2) = "Out of bounds: " ++ (show n1) ++ ", " ++ (show n2) 
  show (ProofConstructionError s) = "Proof construction error: " ++ s
  show (LengthMismatchError n1 n2) = "Length mismatch: " ++ (show n1) ++ ", " ++ (show n2)
  show UnsupportedPayloadType = "Unsupported payload type"
  show (InternalEncodeError s) = "Internal error: " ++ s

-- Our old friend... Might be a better way of doing this
lemma_vect_len : {x : Nat} -> (y : Nat) -> Vect x a -> Either DNSEncodeError (Vect y a)
lemma_vect_len {x} y xs with (decEq x y)
  lemma_vect_len {x} x xs | (Yes Refl) = Right xs
  lemma_vect_len {x} y _  | (No _) = Left $ LengthMismatchError x y

---encodeVectLen : (n : Nat) -> Bounded

lemma_vect : (y : Bounded m) -> (xs : Vect n a) -> Either DNSEncodeError (Vect (intToNat (val y)) a )
lemma_vect b xs = lemma_vect_len (intToNat (val b)) xs  

isBounded : (bound : Nat) -> Nat -> Either DNSEncodeError (Bounded bound)
isBounded b n = 
  case choose (i_n < (pow 2 b)) of
      Left yes => Right (BInt i_n yes)
      Right _ => Left $ OutOfBoundsError b n
  where i_n : Int 
        i_n = natToInt n


zeroBit : Bounded 1
zeroBit = BInt 0 Oh

oneBit : Bounded 1
oneBit = BInt 1 Oh 

charToBits8 : Char -> Bounded 8
charToBits8 c = BInt (ord c) (believe_me Oh) -- Premise

encodeString : String -> (n ** (Vect n (Bounded 8)))
encodeString str = 
  let unpacked_string = map charToBits8 (unpack str) in
  let vect_string = fromList unpacked_string in
  (_ ** vect_string)

mkTagCheck0 : (mkTy Examples.PacketLang.DNS.(tagCheck 0))
mkTagCheck0 = let zbit = zeroBit in
              (zbit ## zbit ## Refl ## Refl)

mkTagCheck1 : (mkTy Examples.PacketLang.DNS.(tagCheck 1))
mkTagCheck1 = let onebit = oneBit in
              (onebit ## onebit ## Refl ## Refl)

nullT : (mkTy Examples.PacketLang.DNS.nullterm)
nullT = (b0 ## Oh)
  where b0 : Bounded 8
        b0 = BInt 0 Oh


encodeDomainFragment : DomainFragment -> Either DNSEncodeError (mkTy Examples.PacketLang.DNS.dnsLabel)
encodeDomainFragment frag = with Monad do
  let (len ** vect_string) = encodeString frag
  encoded_len <- isBounded 6 len
  case choose ((val encoded_len) /= 0) of
    Left prf => 
      (lemma_vect encoded_len vect_string) >>= \encoded_string' =>
        Right (mkTagCheck0 ** encoded_len ** prf ** encoded_string') 
    Right _ => Left $ ProofConstructionError "Length of encoded domain fragment may not be zero"

encodeDomain : List DomainFragment -> Either DNSEncodeError (mkTy Examples.PacketLang.DNS.dnsDomain)
encodeDomain xs = with Monad do
  xs <- sequence $ map encodeDomainFragment xs
  return (Right (xs ## (Left nullT)))


encodeQuestion : DNSQuestion -> Either DNSEncodeError (mkTy Examples.PacketLang.DNS.dnsQuestion)
encodeQuestion (MkDNSQuestion qnames ty cls) = with Monad do
  dom <- encodeDomain qnames 
  return (dom ## ty ## cls)  

encodeHeader : DNSHeader -> Either DNSEncodeError (mkTy Examples.PacketLang.DNS.dnsHeader) 
encodeHeader (MkDNSHeader hdr_id query op auth trunc rd ra aa naa resp) = with Monad do
  b_id <- isBounded 16 (intToNat hdr_id)
  Right (b_id ## query ## op ## auth ## trunc ## rd ## 
        ra ## False ## Oh ## aa ## naa ## resp)

encodeIP : DNSPayload DNSIPv4 -> Either DNSEncodeError (mkTy Examples.PacketLang.DNS.dnsIP)
encodeIP (DNSIPv4Payload (IPv4Addr i1 i2 i3 i4)) = with Monad do
  i1' <- isBounded 8 (intToNat i1)
  i2' <- isBounded 8 (intToNat i2)
  i3' <- isBounded 8 (intToNat i3)
  i4' <- isBounded 8 (intToNat i4)
  return (i1' ## i2' ## i3' ## i4')
-- TODO: If we parameterised SocketAddress over its type, we wouldn't have to do this.
encodeIP _ = Left $ InternalEncodeError "Attempted to encode ipv6 address using ipv4 function"


encodeSOA : DNSSoA -> Either DNSEncodeError (mkTy Examples.PacketLang.DNS.dnsSOA)
encodeSOA soa = do
  mname <- encodeDomain (dnsSOAMName soa)
  rname <- encodeDomain (dnsSOARName soa)
  serial <- isBounded 32 (intToNat $ dnsSOASerial soa)
  refresh <- isBounded 32 (intToNat $ dnsSOASerial soa)
  retry <- isBounded 32 (intToNat $ dnsSOASerial soa)
  expire <- isBounded 32 (intToNat $ dnsSOASerial soa)
  minimum <- isBounded 32 (intToNat $ dnsSOASerial soa)
  return $ (mname ## rname ## serial ## refresh ## retry ## expire ## minimum)

encodePayload : (rel : DNSPayloadRel ty cls pl_ty) -> 
                (payload : DNSPayload pl_ty) ->
                Either DNSEncodeError (mkTy Examples.PacketLang.DNS.(dnsPayloadLang ty cls))
--encodePayload {ty_code} {cls_code} rel ty_rel cls_rel = ?mv
encodePayload DNSPayloadRelIP payload = encodeIP payload
encodePayload DNSPayloadRelIP6 payload = Left UnsupportedPayloadType
encodePayload DNSPayloadRelCNAME (DNSDomainPayload payload) = encodeDomain payload
encodePayload DNSPayloadRelNS (DNSDomainPayload payload) = encodeDomain payload
encodePayload DNSPayloadRelSOA (DNSSOAPayload payload) = encodeSOA payload
encodePayload _ _ = Left UnsupportedPayloadType

{-
payloadLength : (rel : DNSPayloadRel ty cls pl_ty) ->
                (payload : (mkTy Examples.PacketLang.DNS.(dnsPayloadLang ty cls))) ->
                Either DNSEncodeError Int
payloadLength DNSPayloadRelIP pl = Right $ bitLength _ pl

payloadLength DNSPayloadRelIP6 pl = Left UnsupportedPayloadType
payloadLength DNSPayloadRelCNAME pl = encodeDomain payload
payloadLength DNSPayloadRelNS pl = encodeDomain payload
payloadLength _ _ = Left UnsupportedPayloadType
-}
encodeRR : DNSRecord -> Either DNSEncodeError (mkTy Examples.PacketLang.DNS.dnsRR)
encodeRR (MkDNSRecord name ty cls ttl rel pl) = with Monad do
  dom <- encodeDomain name
  b_ttl <- isBounded 32 (intToNat ttl)
  encoded_pl <- encodePayload rel pl
  let pl_len = (bitLength (dnsPayloadLang ty cls) encoded_pl) `div` 8
  b_len <- isBounded 16 (intToNat pl_len) 
  case decEq (val b_len) (bitLength (dnsPayloadLang ty cls) encoded_pl `div` 8) of
    Yes p =>
      Right (dom ## ty ## cls ## b_ttl ## b_len ## encoded_pl ## p)
    No _ => Left $ ProofConstructionError "Length field not equal to payload length"

encodeDNS : DNSPacket -> Either DNSEncodeError (mkTy Examples.PacketLang.DNS.dns) -- Maybe (mkTy Examples.PacketLang.DNS.dns)
encodeDNS (MkDNS hdr qc ac nsc arc qs as auths ars) = with Monad do
    encoded_hdr <- encodeHeader hdr
    b_qc <- isBounded 16 qc
    b_ac <- isBounded 16 ac
    b_nsc <- isBounded 16 nsc
    b_arc <- isBounded 16 arc 
    qs' <- sequence $ map encodeQuestion qs
    as' <- sequence $ map encodeRR as
    auths' <- sequence $ map encodeRR auths
    ars' <- sequence $ map encodeRR ars
    qs'' <- lemma_vect b_qc qs'
    as'' <- lemma_vect b_ac as'
    auths'' <- lemma_vect b_nsc auths' 
    ars'' <- lemma_vect b_arc ars' 
    return (encoded_hdr ## b_qc ## b_ac ## b_nsc ## b_arc ## qs'' ## as'' ## auths'' ## ars'')
 

-- Simple wrapper function to allow us to create a DNS request
mkDNSRequest : Int -> 
               List DomainFragment -> 
               DNSQType -> 
               DNSQClass -> 
               DNSPacket
mkDNSRequest req_id dom_frags qt qc = MkDNS hdr 1 0 0 0 [q] [] [] []
  where hdr = (MkDNSHeader req_id False QUERY False False 
              True True False False DNSResponseNoError)
        q = (MkDNSQuestion dom_frags qt qc)
-- runInit [(MkDNSState ptr [] len)] (parseDNSPacket pckt)

-}

covering main : IO ()
main = do
    Right dat <- readFileBits "DNS.bin"
        | Left err => printLn err

    let Just (res, _) = unmarshal' dat 0 dns   
        | Nothing => putStrLn "Unmarshal failed"

    let Right parsed = parseDNS dat res
        | Left err => printLn err

    printLn parsed

    let serial = marshal dns res
    printLn $ compareBinary dat serial
