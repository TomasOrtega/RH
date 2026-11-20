import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewTangentReduction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
open Matrix GlobalTheory.SUCong
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SUCong.skewTr_eq_reduced` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSkewTangentReduction.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.skew_tangent_reduction : ∀ {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (S : Subring A) (σ : A →+* A) (H : Matrix n n A) (ϖ : A) (τ : Res S ϖ →+* Res S ϖ), ϖ ∈ S → (∀ s ∈ S, σ s ∈ S) → (∀ i j, H i j ∈ S) → (∀ a ∈ S, τ (red S ϖ a) = red S ϖ (σ a)) → skewTr S σ H ϖ = {Y : Matrix n n (Res S ϖ) | Formalism.UG.cT τ Y * H.map (red S ϖ) + H.map (red S ϖ) * Y = 0 ∧ Y.trace = 0} := by
  first | exact @GlobalTheory.SUCong.skewTr_eq_reduced | exact GlobalTheory.SUCong.skewTr_eq_reduced | (intros; apply GlobalTheory.SUCong.skewTr_eq_reduced <;> assumption)
