module DDC.Show

import public DDC.DSL

%default total

-- Dependence on t means this can't be implemented by the normal interface
public export
showResult : {t : DDCType} -> (res : MkTy t) -> String
showResult = showResult' 0 where
    showResult' : (indent : Nat) -> {t : DDCType} -> (res : MkTy t) -> String
    showResult' {t=UNIT} indent (MkResult rep err sp pdMisc) =
        unlines' [
            indented indent "Result T_UNIT",
            indented indent $ show err,
            indented indent $ show sp,
            indented indent $ show rep
        ]
    showResult' {t=BOTTOM} indent (MkResult rep err sp pdMisc) =
        unlines' [
            indented indent "Result T_BOTTOM",
            indented indent $ show err,
            indented indent $ show sp,
            indented indent $ show rep
        ]
    showResult' {t=BASE_TYPE _ _ _} indent (MkResult rep err sp pdMisc) =
        unlines' [
            indented indent "Result T_BASE_TYPE",
            indented indent $ show err,
            indented indent $ show sp,
            indented indent $ show rep
        ]
    showResult' {t=DEPSUM _ _} indent (MkResult rep err sp pdMisc) =
        unlines' $ [
            indented indent "Result T_DEPSUM",
            indented indent $ show err,
            indented indent $ show sp
        ] ++ case rep of
            MkDepsumFull fst snd => [
                showResult' (indent+1) fst,
                indented indent "**",
                showResult' (indent) snd
            ]
            MkDepsumPartial fst => [
                showResult' (indent+1) fst,
                indented indent "**",
                indented indent "<skipped>"
            ]
    showResult' {t=SUM _ _} indent (MkResult rep err sp pdMisc) =
        unlines' $ [
            indented indent "Result T_SUM",
            indented indent $ show err,
            indented indent $ show sp
        ] ++ case rep of
            Left rep => [
                indented indent "Left",
                showResult' (indent+1) rep
            ]
            Right rep => [
                indented indent "Right",
                showResult' (indent+1) rep
            ]
    showResult' {t=INTERSECTION _ _} indent (MkResult rep err sp pdMisc) =
        unlines' [
            indented indent "Result T_INTERSECTION",
            indented indent "Right",
            indented indent $ show err,
            indented indent $ show sp,
            showResult' (indent+1) (fst rep),
            indented indent "+",
            showResult' (indent+1) (snd rep)
        ]
    showResult' {t=CONSTRAINED _ _} indent (MkResult rep err sp pdMisc) =
        unlines' $ [
            indented indent "Result T_CONSTRAINED",
            indented indent $ show err,
            indented indent $ show sp
        ] ++ case rep of
            MkConstrainedMet rep => [
                indented indent "MkConstrainedMet",
                showResult' (indent+1) rep
            ]
            MkConstrainedUnmet rep => [
                indented indent "MkConstrainedUnmet",
                showResult' (indent+1) rep
            ]
    showResult' {t=SEQUENCE _ _ _ _ _ _} indent (MkResult rep err sp pdMisc) =
        unlines' [
            indented indent "Result T_SEQUENCE",
            indented indent $ show err,
            indented indent $ show sp,
            unlines' $
                intersperse (indented indent ",") $
                toList $
                map (showResult' (indent+1)) rep.snd
        ]
    showResult' {t=COMPUTE _} indent (MkResult rep err sp pdMisc) =
        unlines' [
            indented indent "Result T_COMPUTE",
            indented indent $ show err,
            indented indent $ show sp,
            indented indent $ "<compute>" -- show rep
        ]
    showResult' {t=ABSORB _ _} indent (MkResult rep err sp pdMisc) =
        unlines' [
            indented indent "Result T_ABSORB",
            indented indent $ show err,
            indented indent $ show sp,
            indented indent (case rep of
                Left _ =>  "<absorb fail>"
                Right _ => "<absorb>"
            )
        ]
    showResult' {t=SCAN _} indent (MkResult rep err sp pdMisc) =
        unlines' $ [
            indented indent "Result T_SCAN",
            indented indent $ show err,
            indented indent $ show sp
        ] ++ case rep of
            Left _ => [
                indented indent "<scan failed>"
            ]
            Right rep => [
                indented indent "Right",
                showResult' (indent+1) rep
            ]
