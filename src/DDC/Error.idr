||| Types for parser error handling

module DDC.Error

import public Decidable.Equality
import Derive.Eq
import Derive.Prelude

%language ElabReflection

%default total

||| Error codes
||| @ OK successful parse
||| @ ERR successful parse with semantic errors
||| @ FAIL syntactic errors
public export
data ErrorCode = OK | ERR | FAIL

%runElab derive "ErrorCode" [Eq,Show]

public export
implementation DecEq ErrorCode where
    decEq OK OK = Yes Refl
    decEq ERR ERR = Yes Refl
    decEq FAIL FAIL = Yes Refl
    decEq OK ERR = No (\Refl impossible)
    decEq OK FAIL = No (\Refl impossible)
    decEq ERR OK = No (\Refl impossible)
    decEq ERR FAIL = No (\Refl impossible)
    decEq FAIL OK = No (\Refl impossible)
    decEq FAIL ERR = No (\Refl impossible)

%hint
public export
errNotOk : Not (ERR = OK)
errNotOk Refl impossible

%hint
public export
failNotOk : Not (FAIL = OK)
failNotOk Refl impossible

||| An error code along with an error count if appropriate
public export
data Error : Type where
    MkOk : Error
    MkErr : (nerr : Nat) -> Error
    MkFail : (nerr : Nat) -> Error

%runElab derive "Error" [Show]

||| Alternate constructor for errors
public export
MkError : (ec : ErrorCode) -> (nerr : Nat) -> {prf : Either (Not (ec = OK)) (nerr = 0)}  -> Error
MkError OK 0 = MkOk
MkError OK (S k) {prf} = case prf of
    Left prf' => void $ prf' Refl
    Right prf' => absurd prf'
MkError ERR nerr = MkOk
MkError FAIL nerr = MkOk

||| The error code of an error
public export
ec : Error -> ErrorCode
ec MkOk = OK
ec (MkErr _) = ERR
ec (MkFail _) = FAIL

||| The error code of an error
public export
(.ec) : Error -> ErrorCode
(.ec) = ec

||| The error count of an error
public export
nerr : Error -> Nat
nerr MkOk = 0
nerr (MkErr n) = n
nerr (MkFail n) = n

||| The error count of an error
public export
(.nerr) : Error -> Nat
(.nerr) = nerr

||| Provable check for an error code being OK
public export
data DecError : (ec : ErrorCode) -> Type where
    ItIsOk : {ec : ErrorCode} -> (prf : ec = OK) -> DecError ec
    ItIsErr : {ec : ErrorCode} -> (prf : ec = ERR) -> (prf' : Not (ec = OK)) -> DecError ec
    ItIsFail : {ec : ErrorCode} -> (prf : ec = FAIL) -> (prf' : Not (ec = OK))  -> DecError ec

||| Provable check for an error code being OK
public export
decError : (ec : ErrorCode) -> DecError ec
decError OK = ItIsOk Refl
decError ERR = ItIsErr Refl (\Refl impossible)
decError FAIL = ItIsFail Refl (\Refl impossible)
