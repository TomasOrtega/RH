import Formalism.LagrangeIdealLifts.Statement

noncomputable section

namespace Formalism.LIFT

open Polynomial

/- English proof (translation)
Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem prod_X_sub_C_dvd_of_injOn {R : Type} [CommRing R] [IsDomain R] {ι : Type}
    (S : Finset ι) (c : ι → R) (hc : Set.InjOn c S) (G : R[X])
    (hG : ∀ a ∈ S, G.eval (c a) = 0) : (∏ a ∈ S, (X - C (c a))) ∣ G := by
  classical
  by_cases hG0 : G = 0
  · rw [hG0]
    exact dvd_zero _
  have hle : S.val.map c ≤ G.roots := by
    rw [Multiset.le_iff_subset (Multiset.Nodup.map_on (fun a ha b hb hab => hc ha hb hab) S.nodup)]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
    exact (Polynomial.mem_roots hG0).mpr (hG a ha)
  calc (∏ a ∈ S, (X - C (c a))) = ((S.val.map c).map fun x => X - C x).prod := by
        rw [Multiset.map_map]
        rfl
    _ ∣ (G.roots.map fun x => X - C x).prod :=
        Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hle)
    _ ∣ G := Polynomial.prod_multiset_X_sub_C_dvd G

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem lagrangian_ideal_holds : LagrangeIdeal := by
  intro R _ _ ℓ ι _ S₁ S₂ c w hdisj hw
  set N := S₁.sup fun a => (∑ b ∈ S₂, w a b) + ∑ a' ∈ S₁.erase a, w a a' with hN
  by_cases hℓN : ℓ ^ N = 0
  · rw [hℓN, map_zero]
    exact Ideal.zero_mem _
  have hleN : ∀ a ∈ S₁, (∑ a' ∈ S₁.erase a, w a a') + ∑ b ∈ S₂, w a b ≤ N := by
    intro a ha
    rw [add_comm]
    exact Finset.le_sup (f := fun a => (∑ b ∈ S₂, w a b) + ∑ a' ∈ S₁.erase a, w a a') ha
  have hval : ∀ a ∈ S₁, ∃ u : R,
      ℓ ^ N = ((∏ a' ∈ S₁.erase a, (c a - c a')) * ∏ b ∈ S₂, (c a - c b)) * u := by
    intro a ha
    have hassoc : Associated ((∏ a' ∈ S₁.erase a, (c a - c a')) * ∏ b ∈ S₂, (c a - c b))
        (ℓ ^ ((∑ a' ∈ S₁.erase a, w a a') + ∑ b ∈ S₂, w a b)) := by
      rw [pow_add, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
      refine Associated.mul_mul (Associated.prod _ _ _ fun a' ha' => ?_) (Associated.prod _ _ _ fun b hb => ?_)
      · exact hw a ha a' (Finset.mem_union_left _ (Finset.mem_of_mem_erase ha'))
          (Finset.ne_of_mem_erase ha').symm
      · refine hw a ha b (Finset.mem_union_right _ hb) ?_
        intro hab
        subst hab
        exact Finset.disjoint_left.mp hdisj ha hb
    exact (hassoc.dvd_iff_dvd_left).mpr (pow_dvd_pow ℓ (hleN a ha))
  choose! u hu using hval
  have hinj : Set.InjOn c S₁ := by
    intro a ha a' ha' heq
    by_contra hne
    have hw' : w a a' ≤ N := le_trans (Finset.single_le_sum (f := fun x => w a x)
      (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨Ne.symm hne, ha'⟩)) (le_trans (Nat.le_add_right _ _) (hleN a ha))
    have hpow : ℓ ^ w a a' ≠ 0 := by
      intro h0
      apply hℓN
      rw [← Nat.add_sub_cancel' hw', pow_add, h0, zero_mul]
    have := (hw a ha a' (Finset.mem_union_left _ ha') hne).ne_zero_iff.mpr hpow
    exact this (by rw [heq, sub_self])
  set F : R[X] := ∑ a ∈ S₁, C (u a) * ∏ a' ∈ S₁.erase a, (X - C (c a')) with hF
  have hQ : (∏ a ∈ S₁, (X - C (c a))) ∣ F * ∏ b ∈ S₂, (X - C (c b)) - C (ℓ ^ N) := by
    apply prod_X_sub_C_dvd_of_injOn S₁ c hinj
    intro a ha
    rw [eval_sub, eval_mul, eval_C, hF, eval_finset_sum, Finset.sum_eq_single a]
    · simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X]
      rw [hu a ha]
      ring
    · intro a₀ _ hne
      rw [eval_mul, eval_prod, Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hne, ha⟩)
        (by simp), mul_zero]
    · intro h
      exact absurd ha h
  obtain ⟨k, hk⟩ := hQ
  have hC : C (ℓ ^ N) = F * ∏ b ∈ S₂, (X - C (c b)) - (∏ a ∈ S₁, (X - C (c a))) * k := by
    rw [← hk]
    ring
  rw [hC]
  refine Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span ?_))
    (Ideal.mul_mem_right _ _ (Ideal.subset_span ?_))
  · simp
  · simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem lagrangian_ideal_integral_holds : LagrangeIdealInt := by
  intro ℓ _ R _ _ S₁ S₂ c hdisj hw
  exact lagrangian_ideal_holds R (ℓ : R) ℤ S₁ S₂ c (fun a b => padicValInt ℓ (a - b)) hdisj hw

end Formalism.LIFT
