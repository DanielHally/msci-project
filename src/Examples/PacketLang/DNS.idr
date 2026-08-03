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

module Examples.PacketLang.DNS

import public PacketLang

import public Examples.PacketLang.DNSCodes
import public Examples.PacketLang.Util

%default total

public export
data DNSQuestion : Type where
    MkDNSQuestion :
        (dnsQNames : List DomainFragment) ->
        (dnsQQType : DNSQType) ->
        (dnsQQClass : DNSQClass) ->
        DNSQuestion

public export
implementation Show DNSQuestion where
    show (MkDNSQuestion qns qqt qqc) =
        "DNS Question: \n" ++ 
        "DNS QNames: \n" ++ (show qns) ++ "\n" ++
        "DNS QType: \n" ++ (show qqt) ++ "\n" ++
        "DNS QClass: \n" ++ (show qqc) ++ "\n"

public export
data DNSRecord : Type where
    MkDNSRecord :
        (dnsRRName : List DomainFragment) ->
        (dnsRRType : DNSType) ->
        (dnsRRClass : DNSClass) ->
        (dnsRRTTL : Int) ->
        (dnsRRRel : DNSPayloadRel dnsRRType dnsRRClass pl_ty) -> 
        (dnsRRPayload : DNSPayload pl_ty) ->
        DNSRecord

public export
implementation Show DNSRecord where
    show (MkDNSRecord name ty cls ttl rel pl) = "DNS Record: \n" ++
        "DNS RR Name: " ++ (show name) ++ "\n" ++
        "DNS RR Type: " ++ (show ty) ++ "\n" ++
        "DNS RR Class: " ++ (show cls) ++ "\n" ++
        "DNS RR TTL: " ++ (show ttl) ++ "\n" ++
        "DNS RR Payload: " ++ (showPayload rel pl) ++ "\n"

public export
record DNSHeader where
    constructor MkDNSHeader
    dnsHdrId : Int
    dnsHdrIsQuery : Bool
    dnsHdrOpcode : DNSHdrOpcode
    dnsHdrIsAuthority : Bool
    dnsHdrIsTruncated : Bool
    dnsHdrRecursionDesired : Bool
    dnsHdrRecursionAvailable : Bool
    dnsAnswerAuthenticated : Bool
    dnsNonAuthAcceptable : Bool
    dnsHdrResponse : DNSResponse

public export
implementation Show DNSHeader where
  show (MkDNSHeader hdr_id query op auth trunc rd ra aa naa resp) = 
    "DNS Header\n" ++ 
    "ID : " ++ (show hdr_id) ++ "\n" ++ 
    "Is query? : " ++ (show query) ++ "\n" ++ 
    "Opcode : " ++ (show op) ++ "\n" ++ 
    "Is authority? : " ++ (show auth) ++ "\n" ++ 
    "Is truncated? : " ++ (show trunc) ++ "\n" ++
    "Is recursion desired? : " ++ (show rd) ++ "\n" ++
    "Is recursion available? : " ++ (show ra) ++ "\n" ++
    "Is answer authenticated? : " ++ (show aa) ++ "\n" ++
    "Is non-authenticated data acceptable? : " ++ (show naa) ++ "\n" ++
    "Response : " ++ (show resp) ++ "\n"

public export
record DNSPacket where
    constructor MkDNS
    dnsPcktHeader : DNSHeader
    dnsPcktQDCount : Nat
    dnsPcktANCount : Nat
    dnsPcktNSCount : Nat
    dnsPcktARCount : Nat
    dnsPcktQuestions : Vect dnsPcktQDCount DNSQuestion
    dnsPcktAnswers : Vect dnsPcktANCount DNSRecord
    dnsPcktAuthorities : Vect dnsPcktNSCount DNSRecord
    dnsPcktAdditionals : Vect dnsPcktARCount DNSRecord

public export
implementation Show DNSPacket where
    show (MkDNS hdr qdc anc nsc arc qs as auths adds) = 
        "DNS Packet: " ++ "\n" ++
        "Header: " ++ (show hdr) ++ "\n" ++
        "QD Count: " ++ (show qdc) ++ "\n" ++
        "AN Count: " ++ (show anc) ++ "\n" ++
        "NS Count: " ++ (show nsc) ++ "\n" ++
        "AR Count: " ++ (show arc) ++ "\n" ++
        "Questions: " ++ (show qs) ++ "\n" ++
        "Answers: " ++ (show as) ++ "\n" ++
        "Authorities: " ++ (show auths) ++ "\n" ++
        "Additionals: " ++ (show adds) ++ "\n"

public export
nullterm : PacketLang
nullterm = with PacketLang do 
    nt <- bits 8
    check ((val nt) == 0)

public export
validRespCode : Int -> Bool
validRespCode i = i >= 0 && i <= 5

public export
tagCheck : Int -> PacketLang
tagCheck i = do
    tag1 <- bits 1
    tag2 <- bits 1
    let v1 = val tag1
    let v2 = val tag2
    prop (prop_eq v1 i)
    prop (prop_eq v2 i)

public export
dnsReference : PacketLang
dnsReference = do
    tagCheck 1
    bits 14

public export
dnsLabel : PacketLang
dnsLabel = do
    tagCheck 0
    len <- bits 6
    let vl = (val len)
    prf <- check (vl /= 0)
    listn (intToNat vl) (bits 8)

public export
dnsLabels : PacketLang
dnsLabels = do
    list dnsLabel
    nullterm // dnsReference

public export
dnsDomain : PacketLang
dnsDomain = dnsReference // dnsLabels

public export
dnsQuestion : PacketLang
dnsQuestion = do
    dnsDomain
    decodable 16 DNSQType dnsCodeToQType dnsQTypeToCode
    decodable 16 DNSQClass dnsCodeToQClass dnsQClassToCode

public export
dnsIP : PacketLang
dnsIP = with PacketLang do
    bits 8
    bits 8
    bits 8
    bits 8

public export
dnsSOA : PacketLang
dnsSOA = with PacketLang do
    mname <- dnsDomain 
    rname <- dnsDomain
    serial <- bits 32
    refresh <- bits 32
    retry <- bits 32
    expire <- bits 32
    bits 32

public export
dnsPayloadLang : DNSType -> DNSClass -> PacketLang
dnsPayloadLang DNSTypeA DNSClassIN = dnsIP
dnsPayloadLang DNSTypeAAAA DNSClassIN = null 
dnsPayloadLang DNSTypeNS DNSClassIN = dnsDomain
dnsPayloadLang DNSTypeCNAME DNSClassIN = dnsDomain
dnsPayloadLang DNSTypeSOA DNSClassIN = dnsSOA
dnsPayloadLang _ _ = null

public export
dnsHeader : PacketLang
dnsHeader = with PacketLang do
    ident <- bits 16
    qr <- bool
    opcode <- decodable 4 DNSHdrOpcode dnsCodeToOpcode dnsOpcodeToCode
    aa <- bool
    tc <- bool
    rd <- bool
    ra <- bool
    z <- bool
    check (not z)
    ans_auth <- bool
    auth_acceptable <- bool
    decodable 4 DNSResponse dnsCodeToResponse dnsResponseToCode

public export
dnsRR : PacketLang
dnsRR = with PacketLang do 
    domain <- dnsDomain
    ty <- decodable 16 DNSType dnsCodeToType' dnsTypeToCode'
    cls <- decodable 16 DNSClass dnsCodeToClass' dnsClassToCode' 
    ttl <- bits 32
    len <- bits 16
    let pl_lang = dnsPayloadLang ty cls
    pl_data <- pl_lang
    let data_len = (bitLength pl_lang pl_data) `div` 8
    prop (prop_eq (val len) (cast data_len))

public export
dns : PacketLang
dns = with PacketLang do
    header <- dnsHeader
    qdcount <- bits 16
    ancount <- bits 16
    nscount <- bits 16
    arcount <- bits 16
    questions <- listn (intToNat $ val qdcount) dnsQuestion
    answers <- listn (intToNat $ val ancount) dnsRR
    authorities <- listn (intToNat $ val nscount) dnsRR
    listn (intToNat $ val arcount) dnsRR

covering main : IO ()
main = do
    Right dat <- readFileBits "DNS.bin"
        | Left err => printLn err

    let (_, res) = parse (toDDC dns) dat 0
    putStrLn $ showResult {t=toDDC dns} res
    printLn res.ec
