import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Both sides reduce to the same expression.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem cosetTrace_fixed_props : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (N : Subgroup G) [Fintype (G ⧸ N)], ∀ z ∈ Fix L N, (∀ g : G, g • cosetTrace N z = cosetTrace N z) ∧ (v z ≤ 1 → v (cosetTrace N z) ≤ 1) ∧ ∀ e : L, (∀ g : G, g • e = e) → cosetTrace N (e * z) = e * cosetTrace N z := by
  intro L _ v G _ _ hv N _ z hz
  have hfix : ∀ n : G, n ∈ N → n • z = z := fun n hn => hz ⟨n, hn⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g
    unfold cosetTrace
    rw [Finset.smul_sum]
    have key : ∀ q : G ⧸ N, g • q.out • z = (g • q).out • z := by
      intro q
      have h1 : (QuotientGroup.mk (g * q.out) : G ⧸ N) = g • q := by
        conv_rhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have h2 : ((g • q).out)⁻¹ * (g * q.out) ∈ N := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq', h1]
      have h3 : g * q.out = (g • q).out * (((g • q).out)⁻¹ * (g * q.out)) := by group
      rw [smul_smul, h3, mul_smul, hfix _ h2]
    simp_rw [key]
    exact Equiv.sum_comp (MulAction.toPerm g) (fun q : G ⧸ N => q.out • z)
  · intro hz1
    unfold cosetTrace
    apply Valuation.map_sum_le
    intro q _
    rw [hv]; exact hz1
  · intro e he
    unfold cosetTrace
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [smul_mul', he]

end GlobalTheory.AlmostEt
