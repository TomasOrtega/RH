import Mathlib

open Finset Complex Polynomial

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2

def tp (n : ℕ) (z : Fin n → ℂ) : ℂ[X] := ∏ i, (X - C (z i))

/- English proof (translation)
Unfold `tp`. Conclude with `(natDegree_prod_le _ _).trans (by simp [natDegree_X_sub_C])`.
-/
theorem tp_natDeg (n : ℕ) (z : Fin n → ℂ) : (tp n z).natDegree ≤ n := by
  unfold tp
  exact (natDegree_prod_le _ _).trans (by simp [natDegree_X_sub_C])

/- English proof (translation)
Simplify using `[tp, eval_prod]`.
-/
theorem tp_eval (n : ℕ) (z : Fin n → ℂ) (x : ℂ) : (tp n z).eval x = ∏ i, (x - z i) := by
  simp [tp, eval_prod]

/- English proof (translation)
The claim follows from `eval_eq_sum_range' (Nat.lt_succ_of_le (tp_natDeg n z)) x`.
-/
theorem tp_eval_sum (n : ℕ) (z : Fin n → ℂ) (x : ℂ) :
    (tp n z).eval x = ∑ a ∈ range (n + 1), (tp n z).coeff a * x ^ a :=
  eval_eq_sum_range' (Nat.lt_succ_of_le (tp_natDeg n z)) x

/- English proof (translation)
Use `set s : Multiset ℂ := Finset.univ.val.map z with hs`. Establish `hcard : Multiset.card s = n` using `by simp [hs]`. Establish `htp : tp n z = (s.map fun t => X - C t).prod`. Rewrite using `[tp, Finset.prod_eq_multiset_prod, hs, Multiset.map_map]`. Both sides reduce to the same expression.

Establish `hprod : ∀ t : Multiset ℂ, (∀ x ∈ t, ‖x‖ ≤ 1) → ‖t.prod‖ ≤ 1`. Introduce `t`. Proceed by induction on `t using Multiset.induction_on with`. Consider the case `empty => intro _`. Simplify using the standard rewrite rules.

Consider the case `cons x t ih`. Introduce `h`. Rewrite using `[Multiset.prod_cons, norm_mul]`. Conclude with `mul_le_one₀ (h x (Multiset.mem_cons_self x t)) (norm_nonneg _) (ih fun y hy => h y (Multiset.mem_cons_of_mem hy))`. Establish `hmem : ∀ t ∈ s, ‖t‖ ≤ 1`.

Introduce `t ht`. Rewrite `ht` using `[hs, Multiset.mem_map]`. Take `⟨i, _, rfl⟩` from `ht`. Conclude with `hz i`. Rewrite using `[htp, Multiset.prod_X_sub_C_coeff s (by rw [hcard]; exact ha), hcard, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, ← Nat.choose_symm ha, Multiset.esymm]`.

Combine the equalities or inequalities in the displayed calculation. Use `Multiset.sum_map_le_sum_map _ _ fun t ht => hprod t fun x hx => hmem x ?_` and prove the remaining obligations. Conclude with `Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).1 hx`. Use `_ = n.choose (n - a) := by simp [Multiset.card_powersetCard, hcard]`.
-/
theorem tp_coeff_norm (n : ℕ) (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (a : ℕ) (ha : a ≤ n) :
    ‖(tp n z).coeff a‖ ≤ n.choose a := by
  classical
  set s : Multiset ℂ := Finset.univ.val.map z with hs
  have hcard : Multiset.card s = n := by simp [hs]
  have htp : tp n z = (s.map fun t => X - C t).prod := by
    rw [tp, Finset.prod_eq_multiset_prod, hs, Multiset.map_map]
    rfl
  have hprod : ∀ t : Multiset ℂ, (∀ x ∈ t, ‖x‖ ≤ 1) → ‖t.prod‖ ≤ 1 := by
    intro t
    induction t using Multiset.induction_on with
    | empty => intro _; simp
    | cons x t ih =>
      intro h
      rw [Multiset.prod_cons, norm_mul]
      exact mul_le_one₀ (h x (Multiset.mem_cons_self x t)) (norm_nonneg _)
        (ih fun y hy => h y (Multiset.mem_cons_of_mem hy))
  have hmem : ∀ t ∈ s, ‖t‖ ≤ 1 := by
    intro t ht
    rw [hs, Multiset.mem_map] at ht
    obtain ⟨i, _, rfl⟩ := ht
    exact hz i
  rw [htp, Multiset.prod_X_sub_C_coeff s (by rw [hcard]; exact ha), hcard, norm_mul, norm_pow,
    norm_neg, norm_one, one_pow, one_mul, ← Nat.choose_symm ha, Multiset.esymm]
  calc ‖((s.powersetCard (n - a)).map Multiset.prod).sum‖
      ≤ (((s.powersetCard (n - a)).map Multiset.prod).map norm).sum := norm_multiset_sum_le _
    _ = ((s.powersetCard (n - a)).map fun t => ‖t.prod‖).sum := by rw [Multiset.map_map]; rfl
    _ ≤ ((s.powersetCard (n - a)).map fun _ => (1 : ℝ)).sum := by
        refine Multiset.sum_map_le_sum_map _ _ fun t ht => hprod t fun x hx => hmem x ?_
        exact Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).1 hx
    _ = n.choose (n - a) := by simp [Multiset.card_powersetCard, hcard]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem tp_sum_norm (n : ℕ) (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ∑ a ∈ range (n + 1), ‖(tp n z).coeff a‖ ≤ 2 ^ n := by
  calc ∑ a ∈ range (n + 1), ‖(tp n z).coeff a‖ ≤ ∑ a ∈ range (n + 1), (n.choose a : ℝ) :=
        Finset.sum_le_sum fun a ha => tp_coeff_norm n z hz a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))
    _ = 2 ^ n := by exact_mod_cast Nat.sum_range_choose n

/- English proof (translation)
Establish `h1 : ∏ i, (1 - z i * ζ) = ζ ^ n * (tp n z).eval ζ⁻¹`. Rewrite using `[tp_eval, ← Fin.prod_const n ζ, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_sub, mul_inv_cancel₀ hζ]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h1, tp_eval_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations. Establish `ha' : a ≤ n` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)`. Rewrite using `[inv_pow, pow_sub₀ _ hζ ha']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tp_rev (n : ℕ) (z : Fin n → ℂ) (ζ : ℂ) (hζ : ζ ≠ 0) :
    ∏ i, (1 - z i * ζ) = ∑ a ∈ range (n + 1), (tp n z).coeff a * ζ ^ (n - a) := by
  have h1 : ∏ i, (1 - z i * ζ) = ζ ^ n * (tp n z).eval ζ⁻¹ := by
    rw [tp_eval, ← Fin.prod_const n ζ, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_sub, mul_inv_cancel₀ hζ]
    ring
  rw [h1, tp_eval_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  rw [inv_pow, pow_sub₀ _ hζ ha']
  ring

/- English proof (translation)
Rewrite using `[← tp_eval_sum, tp_eval]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)`.
-/
theorem tp_root (n : ℕ) (z : Fin n → ℂ) (i : Fin n) :
    ∑ a ∈ range (n + 1), (tp n z).coeff a * z i ^ a = 0 := by
  rw [← tp_eval_sum, tp_eval]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)

end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
