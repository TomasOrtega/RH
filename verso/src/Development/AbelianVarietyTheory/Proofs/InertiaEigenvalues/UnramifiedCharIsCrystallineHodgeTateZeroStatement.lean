import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedCharIsCrystallineHodgeTateZero
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnramifiedChar.isCrys_and_multV_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUnramifiedCharIsCrystallineHodgeTateZero.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.unramifiedChar_isCrystalline_hodgeTate_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ), Continuous (fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → (∀ g ∈ IK K, μ g = 1) → IsCrys (P.PD K) (charRep μ) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = 0 then 1 else 0 := by
  first | exact @GlobalTheory.UnramifiedChar.isCrys_and_multV_eq | exact GlobalTheory.UnramifiedChar.isCrys_and_multV_eq | (intros; apply GlobalTheory.UnramifiedChar.isCrys_and_multV_eq <;> assumption)
