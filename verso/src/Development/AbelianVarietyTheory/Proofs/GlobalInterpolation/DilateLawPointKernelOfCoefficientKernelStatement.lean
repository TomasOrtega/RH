import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DilateLawPointKernelOfCoefficientKernel
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfPointKernelLiftL
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FDilateLawPointKernelOfCoefficientKernel.lean&line=107#L107)
-/
theorem _root_.GlobalTheory.T.dilateLaw_pointKernel_of_coefficientKernel : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Built.Dat.KerDil k → K.DilLaw := by
  first | exact @GlobalTheory.LvT.Built.DilPass.dilLaw_of_kerDil | exact GlobalTheory.LvT.Built.DilPass.dilLaw_of_kerDil | (intros; apply GlobalTheory.LvT.Built.DilPass.dilLaw_of_kerDil <;> assumption)
