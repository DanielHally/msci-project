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

-- This file is unchanged from the original outside of Idris 2 adjustments

module Examples.PacketLang.DNSCodes

import public Network.Socket -- For SocketAddress

import public PacketLang

public export
data DNSHdrOpcode = QUERY | IQUERY | STATUS

public export
implementation Show DNSHdrOpcode where
    show QUERY = "QUERY"
    show IQUERY = "IQUERY"
    show STATUS = "STATUS"

public export
dnsCodeToOpcode : Bounded 4 -> Maybe DNSHdrOpcode
dnsCodeToOpcode (BInt 0 Oh) = Just QUERY
dnsCodeToOpcode (BInt 1 Oh) = Just IQUERY
dnsCodeToOpcode (BInt 2 Oh) = Just STATUS
dnsCodeToOpcode _ = Nothing

public export
dnsOpcodeToCode : DNSHdrOpcode -> Bounded 4
dnsOpcodeToCode QUERY = BInt 0 Oh
dnsOpcodeToCode IQUERY = BInt 1 Oh
dnsOpcodeToCode STATUS = BInt 2 Oh

public export
data DNSClass = DNSClassIN

public export
implementation Show DNSClass where
    show DNSClassIN = "IN"

public export
data DNSClassRel : Int -> DNSClass -> Type where
    DNSClassRelIN : DNSClassRel 1 DNSClassIN

public export
dnsClassRel : (code : Int) -> (cls : DNSClass) -> Maybe (DNSClassRel code cls)
dnsClassRel 1 DNSClassIN = Just DNSClassRelIN
dnsClassRel _ _ = Nothing 

public export
dnsCodeToClass : (code : Int) -> Maybe DNSClass
dnsCodeToClass 1 = Just DNSClassIN
dnsCodeToClass _ = Nothing

public export
dnsClassToCode : DNSClass -> Int
dnsClassToCode DNSClassIN = 1

public export
dnsCodeToClass' : Bounded 16 -> Maybe DNSClass
dnsCodeToClass' (BInt 1 Oh) = Just DNSClassIN
dnsCodeToClass' _ = Nothing

public export
dnsClassToCode' : DNSClass -> Bounded 16
dnsClassToCode' DNSClassIN = BInt 1 Oh

public export
data DNSQClass = DNSQClassIN
               | DNSQClassANY
               | DNSQClassCS
               | DNSQClassCH
               | DNSQClassHS

public export
implementation Show DNSQClass where
    show DNSQClassIN = "IN"
    show DNSQClassANY = "ANY"
    show DNSQClassCS = "CS"
    show DNSQClassCH = "CH"
    show DNSQClassHS = "HS"

public export
dnsCodeToQClass : (Bounded 16) -> Maybe DNSQClass
dnsCodeToQClass (BInt 1 Oh) = Just DNSQClassIN
dnsCodeToQClass (BInt 2 Oh) = Just DNSQClassCS
dnsCodeToQClass (BInt 3 Oh) = Just DNSQClassCH
dnsCodeToQClass (BInt 4 Oh) = Just DNSQClassHS
dnsCodeToQClass (BInt 255 Oh) = Just DNSQClassANY
dnsCodeToQClass _ = Nothing

public export
dnsQClassToCode : DNSQClass -> Bounded 16
dnsQClassToCode DNSQClassIN = BInt 1 Oh
dnsQClassToCode DNSQClassCS = BInt 2 Oh
dnsQClassToCode DNSQClassCH = BInt 3 Oh
dnsQClassToCode DNSQClassHS = BInt 4 Oh
dnsQClassToCode DNSQClassANY = BInt 255 Oh

public export
A_VAL : Int
A_VAL = 1

public export
NS_VAL : Int
NS_VAL = 2

public export
CNAME_VAL : Int
CNAME_VAL = 5

public export
AAAA_VAL : Int
AAAA_VAL = 28

public export
IN_VAL : Int
IN_VAL = 1

public export
SOA_VAL : Int
SOA_VAL = 6

public export
data DNSType = DNSTypeA
             | DNSTypeNS
             | DNSTypeCNAME
             | DNSTypeNULL
             | DNSTypePTR
             | DNSTypeMX
             | DNSTypeTXT
             | DNSTypeAAAA
             | DNSTypeSOA

public export
implementation Show DNSType where
    show DNSTypeA = "A"
    show DNSTypeNS = "NA"
    show DNSTypeCNAME = "CNAME"
    show DNSTypeNULL = "NULL"
    show DNSTypePTR = "PTR"
    show DNSTypeMX = "MX"
    show DNSTypeTXT = "TXT"
    show DNSTypeAAAA = "AAAA"
    show DNSTypeSOA = "SOA"

public export
data DNSQType = DNSQTypeAXFR
              | DNSQTypeMAILB
              | DNSQTypeMAILA
              | DNSQTypeALL
              | DNSQTypeA
              | DNSQTypeNS
              | DNSQTypeCNAME
              | DNSQTypeNULL
              | DNSQTypePTR
              | DNSQTypeMX
              | DNSQTypeTXT
              | DNSQTypeAAAA
              | DNSQTypeSOA

public export
implementation Show DNSQType where
    show DNSQTypeAXFR = "AXFR"
    show DNSQTypeMAILA = "MAILA"
    show DNSQTypeMAILB = "MAILB"
    show DNSQTypeALL = "ALL"
    show DNSQTypeA = "A"
    show DNSQTypeNS = "NA"
    show DNSQTypeCNAME = "CNAME"
    show DNSQTypeNULL = "NULL"
    show DNSQTypePTR = "PTR"
    show DNSQTypeMX = "MX"
    show DNSQTypeTXT = "TXT"
    show DNSQTypeAAAA = "AAAA"
    show DNSQTypeSOA = "SOA"

public export
data DNSTypeRel : Int -> DNSType -> Type where
    DNSTypeRelA : DNSTypeRel 1 DNSTypeA 
    DNSTypeRelNS : DNSTypeRel NS_VAL DNSTypeNS
    DNSTypeRelCNAME : DNSTypeRel CNAME_VAL DNSTypeCNAME
    DNSTypeRelNULL : DNSTypeRel 10 DNSTypeNULL
    DNSTypeRelPTR : DNSTypeRel 12 DNSTypePTR
    DNSTypeRelMX : DNSTypeRel 15 DNSTypeMX
    DNSTypeRelTXT : DNSTypeRel 16 DNSTypeTXT
    DNSTypeRelAAAA : DNSTypeRel AAAA_VAL DNSTypeAAAA

public export
data DNSQTypeRel : Int -> DNSQType -> Type where
    DNSQTypeRelA : DNSQTypeRel 1 DNSQTypeA 
    DNSQTypeRelNS : DNSQTypeRel NS_VAL DNSQTypeNS
    DNSQTypeRelCNAME : DNSQTypeRel CNAME_VAL DNSQTypeCNAME
    DNSQTypeRelNULL : DNSQTypeRel 10 DNSQTypeNULL
    DNSQTypeRelPTR : DNSQTypeRel 12 DNSQTypePTR
    DNSQTypeRelMX : DNSQTypeRel 15 DNSQTypeMX
    DNSQTypeRelTXT : DNSQTypeRel 16 DNSQTypeTXT
    DNSQTypeRelAAAA : DNSQTypeRel AAAA_VAL DNSQTypeAAAA
    DNSQTypeRelAXFR : DNSQTypeRel 252 DNSQTypeAXFR
    DNSQTypeRelMAILB : DNSQTypeRel 253 DNSQTypeMAILB
    DNSQTypeRelMAILA : DNSQTypeRel 254 DNSQTypeMAILA
    DNSQTypeRelALL : DNSQTypeRel 255 DNSQTypeALL

public export
dnsTypeToCode' : DNSType -> Bounded 16
dnsTypeToCode' DNSTypeA = (BInt 1 Oh)
dnsTypeToCode' DNSTypeNS = (BInt 2 Oh) 
dnsTypeToCode' DNSTypeCNAME = (BInt 5 Oh)
dnsTypeToCode' DNSTypeNULL = (BInt 10 Oh)
dnsTypeToCode' DNSTypePTR = (BInt 12 Oh)
dnsTypeToCode' DNSTypeMX = (BInt 15 Oh)
dnsTypeToCode' DNSTypeTXT = (BInt 16 Oh)
dnsTypeToCode' DNSTypeAAAA = (BInt 28 Oh)
dnsTypeToCode' DNSTypeSOA = (BInt 6 Oh)

public export
dnsTypeToCode : DNSType -> Int
dnsTypeToCode DNSTypeA = 1
dnsTypeToCode DNSTypeNS = 2
dnsTypeToCode DNSTypeCNAME = 5
dnsTypeToCode DNSTypeNULL = 10
dnsTypeToCode DNSTypePTR = 12
dnsTypeToCode DNSTypeMX = 15
dnsTypeToCode DNSTypeTXT = 16
dnsTypeToCode DNSTypeAAAA = 28
dnsTypeToCode DNSTypeSOA = 6

public export
dnsCodeToType' : (Bounded 16) -> Maybe DNSType
dnsCodeToType' (BInt 1 Oh) = Just DNSTypeA
dnsCodeToType' (BInt 2 Oh) = Just DNSTypeNS
dnsCodeToType' (BInt 5 Oh) = Just DNSTypeCNAME
dnsCodeToType' (BInt 6 Oh) = Just DNSTypeSOA
dnsCodeToType' (BInt 10 Oh) = Just DNSTypeNULL
dnsCodeToType' (BInt 12 Oh) = Just DNSTypePTR
dnsCodeToType' (BInt 15 Oh) = Just DNSTypeMX
dnsCodeToType' (BInt 16 Oh) = Just DNSTypeTXT
dnsCodeToType' (BInt 28 Oh) = Just DNSTypeAAAA
dnsCodeToType' (BInt _ _) = Nothing

public export
dnsCodeToType : (code : Int) -> Maybe DNSType
dnsCodeToType 1 = Just DNSTypeA
dnsCodeToType 2 = Just DNSTypeNS
dnsCodeToType 5 = Just DNSTypeCNAME
dnsCodeToType 10 = Just DNSTypeNULL
dnsCodeToType 12 = Just DNSTypePTR
dnsCodeToType 15 = Just DNSTypeMX
dnsCodeToType 16 = Just DNSTypeTXT
dnsCodeToType 28 = Just DNSTypeAAAA
dnsCodeToType _ = Nothing

public export
dnsCodeToQType : Bounded 16 -> Maybe DNSQType
dnsCodeToQType (BInt 1 Oh) = Just DNSQTypeA
dnsCodeToQType (BInt 2 Oh) = Just DNSQTypeNS
dnsCodeToQType (BInt 5 Oh) = Just DNSQTypeCNAME
dnsCodeToQType (BInt 10 Oh) = Just DNSQTypeNULL
dnsCodeToQType (BInt 12 Oh) = Just DNSQTypePTR
dnsCodeToQType (BInt 15 Oh) = Just DNSQTypeMX
dnsCodeToQType (BInt 16 Oh) = Just DNSQTypeTXT
dnsCodeToQType (BInt 28 Oh) = Just DNSQTypeAAAA
dnsCodeToQType (BInt 252 Oh) = Just DNSQTypeAXFR
dnsCodeToQType (BInt 253 Oh) = Just DNSQTypeMAILB
dnsCodeToQType (BInt 254 Oh) = Just DNSQTypeMAILA
dnsCodeToQType (BInt 255 Oh) = Just DNSQTypeALL
dnsCodeToQType _ = Nothing

public export
dnsQTypeToCode : DNSQType -> Bounded 16
dnsQTypeToCode DNSQTypeA = (BInt 1 Oh)
dnsQTypeToCode DNSQTypeNS = (BInt 2 Oh)
dnsQTypeToCode DNSQTypeCNAME = (BInt 5 Oh)
dnsQTypeToCode DNSQTypeNULL = (BInt 10 Oh)
dnsQTypeToCode DNSQTypePTR = (BInt 12 Oh)
dnsQTypeToCode DNSQTypeMX = (BInt 15 Oh)
dnsQTypeToCode DNSQTypeTXT = (BInt 16 Oh)
dnsQTypeToCode DNSQTypeAAAA = (BInt 28 Oh)
dnsQTypeToCode DNSQTypeAXFR = (BInt 252 Oh)
dnsQTypeToCode DNSQTypeMAILB = (BInt 253 Oh)
dnsQTypeToCode DNSQTypeMAILA = (BInt 254 Oh)
dnsQTypeToCode DNSQTypeALL = (BInt 255 Oh)
dnsQTypeToCode DNSQTypeSOA = (BInt 6 Oh)

public export
data DNSResponse = DNSResponseNoError
                 | DNSResponseFormatError
                 | DNSResponseServerError
                 | DNSResponseNameError
                 | DNSResponseNotImplementedError
                 | DNSResponseRefusedError

public export
implementation Show DNSResponse where
    show DNSResponseNoError = "No error"
    show DNSResponseFormatError = "Format error"
    show DNSResponseServerError = "Server error"
    show DNSResponseNameError = "Name error"
    show DNSResponseNotImplementedError = "Not implemented error"
    show DNSResponseRefusedError = "Refused error"

public export
dnsCodeToResponse : Bounded 4 -> Maybe DNSResponse
dnsCodeToResponse (BInt 0 Oh) = Just DNSResponseNoError
dnsCodeToResponse (BInt 1 Oh) = Just DNSResponseFormatError
dnsCodeToResponse (BInt 2 Oh) = Just DNSResponseServerError
dnsCodeToResponse (BInt 3 Oh) = Just DNSResponseNameError
dnsCodeToResponse (BInt 4 Oh) = Just DNSResponseNotImplementedError
dnsCodeToResponse (BInt 5 Oh) = Just DNSResponseRefusedError
dnsCodeToResponse _ = Nothing

public export
dnsResponseToCode : DNSResponse -> Bounded 4
dnsResponseToCode DNSResponseNoError = BInt 0 Oh
dnsResponseToCode DNSResponseFormatError = BInt 1 Oh
dnsResponseToCode DNSResponseServerError = BInt 2 Oh
dnsResponseToCode DNSResponseNameError = BInt 3 Oh
dnsResponseToCode DNSResponseNotImplementedError = BInt 4 Oh
dnsResponseToCode DNSResponseRefusedError = BInt 5 Oh

public export
DomainFragment : Type
DomainFragment = String

public export
record DNSSoA where
    constructor MkSOA
    dnsSOAMName : List DomainFragment
    dnsSOARName : List DomainFragment
    dnsSOASerial : Int
    dnsSOARefresh : Int
    dnsSOARetry : Int
    dnsSOAExpire : Int
    dnsSOAMinimum : Int

public export
implementation Show DNSSoA where
  show soa =
    "DNS Start of Authority: \n" ++ 
    "MName: " ++ (show $ dnsSOAMName soa) ++ "\n" ++
    "RName: " ++ (show $ dnsSOARName soa) ++ "\n" ++
    "Serial: " ++ (show $ dnsSOASerial soa) ++ "\n" ++
    "Refresh: " ++ (show $ dnsSOARefresh soa) ++ "\n" ++
    "Retry: " ++ (show $ dnsSOARetry soa) ++ "\n" ++
    "Expire: " ++ (show $ dnsSOAExpire soa) ++ "\n" ++
    "Minimum: " ++ (show $ dnsSOAMinimum soa) ++ "\n" 

public export
data DNSPayloadType = DNSIPv4 | DNSIPv6 | DNSDomain | DNSSOA

public export
data DNSPayload : DNSPayloadType -> Type where
  DNSIPv4Payload : SocketAddress -> DNSPayload DNSIPv4 
  DNSIPv6Payload : SocketAddress -> DNSPayload DNSIPv6
  DNSDomainPayload : List DomainFragment -> DNSPayload DNSDomain
  DNSSOAPayload : DNSSoA -> DNSPayload DNSSOA

public export
data DNSPayloadRel : DNSType -> DNSClass -> DNSPayloadType -> Type where
  DNSPayloadRelIP : DNSPayloadRel DNSTypeA DNSClassIN DNSIPv4
  DNSPayloadRelIP6 : DNSPayloadRel DNSTypeAAAA DNSClassIN DNSIPv6
  DNSPayloadRelCNAME : DNSPayloadRel DNSTypeCNAME DNSClassIN DNSDomain
  DNSPayloadRelNS : DNSPayloadRel DNSTypeNS DNSClassIN DNSDomain
  DNSPayloadRelSOA : DNSPayloadRel DNSTypeSOA DNSClassIN DNSSOA

public export
showPayload : (DNSPayloadRel rrt rrc pl_ty) -> DNSPayload pl_ty -> String
showPayload DNSPayloadRelIP (DNSIPv4Payload addr) = "IPv4: " ++ (show addr)
showPayload DNSPayloadRelIP6 (DNSIPv6Payload addr) = "IPv6 " ++ (show addr)
showPayload DNSPayloadRelCNAME (DNSDomainPayload dom) = "Domain: " ++ show dom
showPayload DNSPayloadRelNS (DNSDomainPayload dom) = "Domain: " ++ show dom
showPayload DNSPayloadRelSOA (DNSSOAPayload soa) = "SOA: " ++ show soa
