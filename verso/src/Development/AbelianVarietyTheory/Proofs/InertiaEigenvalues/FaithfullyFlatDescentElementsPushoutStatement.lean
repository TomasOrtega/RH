import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FaithfullyFlatDescentElementsPushout
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BSP.ff_descent_elem_pushout` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFaithfullyFlatDescentElementsPushout.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.faithfullyFlat_descent_elements_pushout : ∀ (A B D : Type) [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (p q : B →+* D), f.FaithfullyFlat → CategoryTheory.IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom f) (CommRingCat.ofHom p) (CommRingCat.ofHom q) → Function.Injective f ∧ ∀ b, p b = q b → b ∈ f.range := by
  first | exact @GlobalTheory.BSP.ff_descent_elem_pushout | exact GlobalTheory.BSP.ff_descent_elem_pushout | (intros; apply GlobalTheory.BSP.ff_descent_elem_pushout <;> assumption)
