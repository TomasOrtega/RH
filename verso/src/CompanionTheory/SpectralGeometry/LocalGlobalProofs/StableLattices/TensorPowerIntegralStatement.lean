import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TensorPowerIntegral
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.ZuckTens.okTens | exact GlobalTheory.CompanionTheory.ZuckTens.okTens | (intros; apply GlobalTheory.CompanionTheory.ZuckTens.okTens <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.TensorPowerIntegral : OKTens := by
  first | exact @GlobalTheory.CompanionTheory.ZuckTens.okTens | exact GlobalTheory.CompanionTheory.ZuckTens.okTens | (intros; apply GlobalTheory.CompanionTheory.ZuckTens.okTens <;> assumption)
