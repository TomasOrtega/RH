import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrSubOfIsIrrSubMap
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FAbsIrrSubOfIsIrrSubMap.lean&line=116#L116)
-/
theorem _root_.GlobalTheory.T.absIrrSub_of_isIrrSub_span_map : ∀ {k Γ L : Type} [Field k] [Group Γ] [Field L] [IsAlgClosed L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)), IsInv ρ W → IsIrrSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))) → AbsIrrSub ρ W := by
  first | exact @GlobalTheory.AbsIrrOfAlgClosed.absIrrSub_of_isIrrSub_map | exact GlobalTheory.AbsIrrOfAlgClosed.absIrrSub_of_isIrrSub_map | (intros; apply GlobalTheory.AbsIrrOfAlgClosed.absIrrSub_of_isIrrSub_map <;> assumption)
