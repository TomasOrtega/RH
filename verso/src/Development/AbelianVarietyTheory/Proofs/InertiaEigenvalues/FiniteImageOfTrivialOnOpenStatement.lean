import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteImageOfTrivialOnOpen
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GK.finite_image_of_trivial_on_open` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFiniteImageOfTrivialOnOpen.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.finite_image_of_trivial_on_inf_isOpen : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (Q : Type) [Group Q] (ρ : ↥(GK K) →* Q) (J H : Subgroup ↥(GK K)), IsOpen (H : Set ↥(GK K)) → (∀ g ∈ J, g ∈ H → ρ g = 1) → (ρ '' (J : Set ↥(GK K))).Finite := by
  first | exact @GlobalTheory.GK.finite_image_of_trivial_on_open | exact GlobalTheory.GK.finite_image_of_trivial_on_open | (intros; apply GlobalTheory.GK.finite_image_of_trivial_on_open <;> assumption)
