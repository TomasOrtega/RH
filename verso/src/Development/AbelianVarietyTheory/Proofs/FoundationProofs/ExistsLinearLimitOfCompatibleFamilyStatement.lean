import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLinearLimitOfCompatibleFamily
import GroundTheory.PAdicHodge.AxLemma
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_linear_limit_of_compatible_family` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsLinearLimitOfCompatibleFamily.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.exists_linearMap_limit_of_compatible_approximations : ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] (B : Submodule ℤ_[l] M) (R : ℕ → M → PadicAlgCl l → Prop) (C : ℝ),
  (∀ n, ∀ b ∈ B, ∃ x, R n b x) →
  (∀ n, ∀ b ∈ B, ∀ x y, R (n + 1) b x → R n b y → ‖x - y‖ ≤ C * ‖((l : ℕ) : PadicAlgCl l) ^ n‖) →
  (∀ n, ∀ b ∈ B, ∀ b' ∈ B, ∀ (a a' : ℤ_[l]) (x x' : PadicAlgCl l), R n b x → R n b' x' →
    R n (a • b + a' • b') (((a.appr n : ℕ) : PadicAlgCl l) * x + ((a'.appr n : ℕ) : PadicAlgCl l) * x')) →
  ∃ L : TensorProduct ℤ_[l] (PadicAlgCl l) M →ₗ[PadicAlgCl l] ℂ_[l], ∀ n, ∀ b ∈ B, ∀ x, R n b x →
    ‖(x : ℂ_[l]) - L (1 ⊗ₜ[ℤ_[l]] b)‖ ≤ C * ‖((l : ℕ) : PadicAlgCl l) ^ n‖ := by
  first | exact @GlobalTheory.exists_linear_limit_of_compatible_family | exact GlobalTheory.exists_linear_limit_of_compatible_family | (intros; apply GlobalTheory.exists_linear_limit_of_compatible_family <;> assumption)
