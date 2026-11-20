import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpanInfRationalSubspaceIntegersExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentIdealSmulMemSpanRational
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.span_inf_span_eq_span_inf_of_rational` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLatticeSpanInfRationalSubspaceIntegersExt.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.lattice_span_inf_rational_subspace_integers_ext : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (n : ℕ) (M : Submodule (𝓞 K) (Fin n → K)) (W : Submodule K (Fin n → K)), Submodule.span (𝓞 L) ((fun x i => algebraMap K L (x i)) '' (M : Set (Fin n → K))) ⊓ (Submodule.span L ((fun x i => algebraMap K L (x i)) '' (W : Set (Fin n → K)))).restrictScalars (𝓞 L) = Submodule.span (𝓞 L) ((fun x i => algebraMap K L (x i)) '' ((M ⊓ W.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) := by
  first | exact @GlobalTheory.span_inf_span_eq_span_inf_of_rational | exact GlobalTheory.span_inf_span_eq_span_inf_of_rational | (intros; apply GlobalTheory.span_inf_span_eq_span_inf_of_rational <;> assumption)
