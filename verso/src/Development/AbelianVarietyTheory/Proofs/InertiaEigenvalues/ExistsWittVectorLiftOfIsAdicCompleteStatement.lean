import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittVectorLiftOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsWittVectorLiftOfIsAdicComplete.lean&line=153#L153)
-/
theorem _root_.GlobalTheory.T.exists_wittVector_lift_of_isAdicComplete' : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [CommRing k] [CharP k l] [PerfectRing k l] (C : Type) [CommRing C] (J : Ideal C), (l : C) ∈ J → IsAdicComplete J C → ∀ ψ : k →+* C ⧸ J, ∃ ω : WittVector l k →+* C, ∀ w, Ideal.Quotient.mk J (ω w) = ψ (w.coeff 0) := by
  first | exact @GlobalTheory.exists_wittVector_lift_of_isAdicComplete | exact GlobalTheory.exists_wittVector_lift_of_isAdicComplete | (intros; apply GlobalTheory.exists_wittVector_lift_of_isAdicComplete <;> assumption)
