import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderTranslationInvariant
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.BT.HopfTranslate.translate_mem_of_isHopfOrder` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FHopfOrderTranslationInvariant.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.hopf_order_translation_invariant : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (A : Subalgebra R (T → R)), IsHopfOrder A → ∀ f ∈ A, ∀ t, (fun h => f (t * h)) ∈ A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.HopfTranslate.translate_mem_of_isHopfOrder | exact GlobalTheory.CompanionTheory.Ar.BT.HopfTranslate.translate_mem_of_isHopfOrder | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.HopfTranslate.translate_mem_of_isHopfOrder <;> assumption)
