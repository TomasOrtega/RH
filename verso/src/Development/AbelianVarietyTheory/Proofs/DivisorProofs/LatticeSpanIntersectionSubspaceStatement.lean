import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpanIntersectionSubspace
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLatticeSpanIntersectionSubspace.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.lattice_span_intersection_subspace : ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (E : Submodule (𝓞 K) (Fin r → K)) (V : Submodule K (Fin r → K)), Submodule.span K (E : Set (Fin r → K)) = ⊤ → Submodule.span K ((E ⊓ V.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin r → K)) : Set (Fin r → K)) = V := by
  first | exact @GlobalTheory.span_cut | exact GlobalTheory.span_cut | (intros; apply GlobalTheory.span_cut <;> assumption)
