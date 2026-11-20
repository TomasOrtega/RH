import Mathlib

namespace GlobalTheory

open Polynomial

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem norm_multiset_sum_le_of_forall_le_ultrametric {K : Type} [NormedField K]
    [IsUltrametricDist K] (m : Multiset K) {C : ℝ} (hC : 0 ≤ C) (h : ∀ x ∈ m, ‖x‖ ≤ C) :
    ‖m.sum‖ ≤ C := by
  induction m using Multiset.induction_on with
  | empty => simpa using hC
  | cons a s ih =>
    rw [Multiset.sum_cons]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact h a (Multiset.mem_cons_self _ _)
    · exact ih fun x hx => h x (Multiset.mem_cons_of_mem hx)

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem norm_multiset_prod_le_pow_card_of_forall_le {K : Type} [NormedField K]
    (m : Multiset K) {B : ℝ} (h : ∀ x ∈ m, ‖x‖ ≤ B) :
    ‖m.prod‖ ≤ B ^ Multiset.card m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ']
    have ha := h a (Multiset.mem_cons_self _ _)
    exact mul_le_mul ha (ih fun x hx => h x (Multiset.mem_cons_of_mem hx)) (norm_nonneg _)
      ((norm_nonneg _).trans ha)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem norm_coeff_natDegree_sub_le_pow_of_roots_le (K : Type) [NormedField K]
    [IsUltrametricDist K] [IsAlgClosed K] (Q : Polynomial K) (hQ : Q.Monic) (B : ℝ)
    (hB : ∀ r : K, Q.IsRoot r → ‖r‖ ≤ B) (i : ℕ) (hi : i ≤ Q.natDegree) :
    ‖Q.coeff (Q.natDegree - i)‖ ≤ B ^ i := by
  have hcard : Multiset.card Q.roots = Q.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hroot : ∀ r ∈ Q.roots, ‖r‖ ≤ B := fun r hr => hB r (isRoot_of_mem_roots hr)
  have hBi : 0 ≤ B ^ i := by
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp
    · have : 0 < Multiset.card Q.roots := by omega
      obtain ⟨r, hr⟩ := Multiset.card_pos_iff_exists_mem.1 this
      exact pow_nonneg ((norm_nonneg _).trans (hroot r hr)) _
  rw [Polynomial.coeff_eq_esymm_roots_of_card hcard (Nat.sub_le _ _), hQ.leadingCoeff,
    Nat.sub_sub_self hi, one_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Multiset.esymm]
  refine norm_multiset_sum_le_of_forall_le_ultrametric _ hBi ?_
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hx
  obtain ⟨hle, hc⟩ := Multiset.mem_powersetCard.1 ht
  rw [← hc]
  exact norm_multiset_prod_le_pow_card_of_forall_le t fun y hy =>
    hroot y (Multiset.mem_of_le hle hy)

end GlobalTheory
