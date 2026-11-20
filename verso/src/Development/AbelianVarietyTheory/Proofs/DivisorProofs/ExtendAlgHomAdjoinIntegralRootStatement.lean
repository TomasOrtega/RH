import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendAlgHomAdjoinIntegralRoot
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.extend_alg_hom_adjoin_integral_root` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExtendAlgHomAdjoinIntegralRoot.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_algHom_adjoin_extend_of_isIntegral_root : ∀ (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω] [Algebra k Ω] (R : Subalgebra k F) [IsIntegrallyClosed R] (θ : F), IsIntegral R θ → ∀ (ev : R →ₐ[k] Ω) (r : Ω), Polynomial.eval₂ (ev : R →+* Ω) r (minpoly R θ) = 0 → ∃ ψ : Algebra.adjoin k (insert θ (R : Set F)) →ₐ[k] Ω, ∀ (x : F) (hx : x ∈ R) (hx' : x ∈ Algebra.adjoin k (insert θ (R : Set F))), ψ ⟨x, hx'⟩ = ev ⟨x, hx⟩ := by
  first | exact @GlobalTheory.extend_alg_hom_adjoin_integral_root | exact GlobalTheory.extend_alg_hom_adjoin_integral_root | (intros; apply GlobalTheory.extend_alg_hom_adjoin_integral_root <;> assumption)
