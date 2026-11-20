import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorRingHomEqOfSubMem
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWittVectorRingHomEqOfSubMem.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.wittVector_ringHom_eq_of_sub_mem' : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [CommRing k] [CharP k l] [PerfectRing k l] (C : Type) [CommRing C] (J : Ideal C), (l : C) ∈ J → IsHausdorff J C → ∀ ω ω' : WittVector l k →+* C, (∀ w, ω w - ω' w ∈ J) → ω = ω' := by
  first | exact @GlobalTheory.wittVector_ringHom_eq_of_sub_mem | exact GlobalTheory.wittVector_ringHom_eq_of_sub_mem | (intros; apply GlobalTheory.wittVector_ringHom_eq_of_sub_mem <;> assumption)
