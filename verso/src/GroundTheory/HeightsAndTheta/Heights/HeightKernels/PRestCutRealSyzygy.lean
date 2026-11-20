import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem RestCutRealSyzygy.flagIntegral_zero (f N : ℕ) : RestTerms.flagIntegral f N 0 = 0 := by
  simp [RestTerms.flagIntegral]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses repeatedly using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem RestCutRealSyzygy.proof (h₁ : RestTerms.RestTermWellDefined.Statement)
    (h₂ : RestCutPsiFlag.Statement) : RestCutRealSyzygy.Statement := by
  intro f N R hR m hm1 hmN τ G hG
  apply KRest.eq_zero_of_forall_psi
  intro ψ
  rw [(h₂ f N).2 ψ, KRest.psiPoly_map_mul]
  set Rψ : ℕ → Fin f → RestTerms.RootRing f N := fun l σ => KRest.psiPoly ψ (R l σ) with hRψ
  have hsyz : RestTerms.IsPowerSumDecomposition f N 0 Rψ := by
    have h0 := congrArg (KRest.psiPoly ψ) hR
    rw [map_zero, map_sum] at h0
    simp_rw [map_sum, KRest.psiPoly_map_mul] at h0
    exact h0.symm
  have hzero : RestTerms.IsPowerSumDecomposition f N 0 (fun _ _ => 0) := by
    simp [RestTerms.IsPowerSumDecomposition]
  have h := h₁ f N 0 Rψ (fun _ _ => 0) hsyz hzero m hm1 hmN τ G hG
  simp only [RestTerms.restTerm, mul_zero, RestCutRealSyzygy.flagIntegral_zero] at h
  have hm : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  exact (mul_eq_zero.mp h).resolve_left hm

end GroundTheory.Heights₂.Heights
