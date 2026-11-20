import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCochainOfDeRhamCoboundary
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FContinuousCochainOfDeRhamCoboundary.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.continuous_cochain_of_deRham_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ (k : ℕ) (x : Fin k → V ⊗[ℚ_[l]] P.R.BdR) (β : Fin k → ↥(GK K) → ℚ_[l]), (∀ i, Continuous (β i)) → ∀ (x' : V ⊗[ℚ_[l]] P.R.BdR) (f : ↥(GK K) → V), (∀ g, f g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = ∑ i, β i g • x i + (actVdR (P.PD K) ρ g x' - x')) → Continuous f := by
  first | exact @GlobalTheory.ContDR.cont_dR | exact GlobalTheory.ContDR.cont_dR | (intros; apply GlobalTheory.ContDR.cont_dR <;> assumption)
