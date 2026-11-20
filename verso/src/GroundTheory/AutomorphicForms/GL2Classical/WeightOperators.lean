import Mathlib

open Complex

namespace GroundTheory.Automorphic

namespace GL2Classical

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {Rr Ll Jj : Module.End ℂ E}

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem J_pow_apply (hJR : Jj * Rr - Rr * Jj = (2 * I) • Rr) {κ : ℂ} {t : E} (ht : Jj t = κ • t) (j : ℕ) :
    Jj ((Rr ^ j) t) = (κ + 2 * I * j) • (Rr ^ j) t := by
  induction j with
  | zero => simpa using ht
  | succ j ih =>
    have h1 : Jj (Rr ((Rr ^ j) t)) = Rr (Jj ((Rr ^ j) t)) + (2 * I) • Rr ((Rr ^ j) t) := by
      have := congrArg (fun F : Module.End ℂ E => F ((Rr ^ j) t)) hJR
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at this
      rw [← this]
      abel
    rw [pow_succ', Module.End.mul_apply, h1, ih, map_smul, ← add_smul]
    congr 1
    push_cast
    ring

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Normalize the expressions using the abelian group laws. Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem L_pow_succ_apply (hJR : Jj * Rr - Rr * Jj = (2 * I) • Rr) (hLR : Ll * Rr - Rr * Ll = (4 * I) • Jj)
    {κ : ℂ} {t : E} (ht : Jj t = κ • t) (hL : Ll t = 0) (j : ℕ) :
    Ll ((Rr ^ (j + 1)) t) = (4 * I * (j + 1) * (κ + I * j)) • (Rr ^ j) t := by
  have hcomm : ∀ v, Ll (Rr v) = Rr (Ll v) + (4 * I) • Jj v := by
    intro v
    have := congrArg (fun F : Module.End ℂ E => F v) hLR
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [← this]
    abel
  induction j with
  | zero =>
    rw [pow_one, hcomm, hL, map_zero, zero_add, ht, smul_smul, pow_zero, Module.End.one_apply]
    congr 1
    push_cast
    ring
  | succ j ih =>
    rw [pow_succ' Rr (j + 1), Module.End.mul_apply, hcomm, ih, map_smul, J_pow_apply hJR ht, smul_smul]
    have e : Rr ((Rr ^ j) t) = (Rr ^ (j + 1)) t := by rw [pow_succ', Module.End.mul_apply]
    rw [e, ← add_smul]
    congr 1
    push_cast
    ring

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.
-/
theorem L_pow_R_pow_apply (hJR : Jj * Rr - Rr * Jj = (2 * I) • Rr) (hLR : Ll * Rr - Rr * Ll = (4 * I) • Jj)
    {κ : ℂ} {t : E} (ht : Jj t = κ • t) (hL : Ll t = 0) (j : ℕ) :
    (Ll ^ j) ((Rr ^ j) t) = (∏ m ∈ Finset.range j, (4 * I * (m + 1) * (κ + I * m))) • t := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ Ll j, Module.End.mul_apply, L_pow_succ_apply hJR hLR ht hL, map_smul, ih, smul_smul,
      Finset.prod_range_succ, mul_comm]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Check the signs of the components of the expression. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem prod_ne_zero_of_pos {k : ℤ} (hk : 0 < k) (j : ℕ) :
    (∏ m ∈ Finset.range j, (4 * I * (m + 1) * (I * k + I * m))) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro m _
  have h1 : (4 * I * (m + 1) : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
    (by exact_mod_cast Nat.succ_ne_zero m)
  have h2 : (I * k + I * m : ℂ) ≠ 0 := by
    rw [← mul_add]
    refine mul_ne_zero I_ne_zero ?_
    have : (0 : ℝ) < (k : ℝ) + m := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      positivity
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  exact mul_ne_zero h1 h2

/- English proof (translation)
Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem mem_of_sum_mem_of_eigen {W : Submodule ℂ E} (hW : ∀ v ∈ W, Jj v ∈ W) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) : ∀ (v : ι → E) (μ : ι → ℂ), (∀ i ∈ s, Jj (v i) = μ i • v i) → Set.InjOn μ s →
      ∑ i ∈ s, v i ∈ W → ∀ i ∈ s, v i ∈ W := by
  induction s using Finset.induction_on with
  | empty => intro v μ _ _ _ i hi; simp at hi
  | insert a s ha ih =>
    intro v μ hv hμ hsum
    rw [Finset.sum_insert ha] at hsum

    have hJs : ∑ i ∈ s, (μ i - μ a) • v i ∈ W := by
      have h1 : Jj (v a + ∑ i ∈ s, v i) - μ a • (v a + ∑ i ∈ s, v i) ∈ W :=
        sub_mem (hW _ hsum) (Submodule.smul_mem _ _ hsum)
      have e : Jj (v a + ∑ i ∈ s, v i) - μ a • (v a + ∑ i ∈ s, v i) = ∑ i ∈ s, (μ i - μ a) • v i := by
        rw [map_add, map_sum, hv a (Finset.mem_insert_self a s), smul_add, Finset.smul_sum]
        rw [Finset.sum_congr rfl fun i hi => hv i (Finset.mem_insert_of_mem hi)]
        simp only [sub_smul, Finset.sum_sub_distrib]
        abel
      rwa [e] at h1
    have hs' := ih (fun i => (μ i - μ a) • v i) μ
      (fun i hi => by rw [map_smul, hv i (Finset.mem_insert_of_mem hi), smul_comm])
      (hμ.mono (Finset.coe_subset.2 (Finset.subset_insert a s))) hJs
    have hvs : ∀ i ∈ s, v i ∈ W := by
      intro i hi
      have hne : μ i - μ a ≠ 0 := sub_ne_zero.2 fun h =>
        ha (hμ (Finset.mem_insert_of_mem hi) (Finset.mem_insert_self a s) h ▸ hi)
      have := Submodule.smul_mem W (μ i - μ a)⁻¹ (hs' i hi)
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · have := sub_mem hsum (Submodule.sum_mem W hvs)
      rwa [add_sub_cancel_right] at this
    · exact hvs i hi

end GL2Classical

end GroundTheory.Automorphic
