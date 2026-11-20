import Mathlib

universe u_1

namespace GlobalTheory.RootNormPowerBound

open Polynomial

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih`. Rewrite using `[Multiset.card_cons, pow_succ, Multiset.map_cons, Multiset.prod_cons, eval_mul, norm_mul, mul_comm]`. Establish `ha : c ≤ ‖eval x (X - C a)‖`.

Rewrite using `[eval_sub, eval_X, eval_C, norm_sub_rev]`. Conclude with `hs a (Multiset.mem_cons_self a s)`. Conclude with `mul_le_mul ha (ih fun t ht => hs t (Multiset.mem_cons_of_mem ht)) (pow_nonneg hc _) (norm_nonneg _)`.
-/
theorem pow_card_le_norm_eval_prod {K : Type u_1} [NormedField K] (x : K) (c : ℝ) (hc : 0 ≤ c)
    (s : Multiset K) (hs : ∀ a ∈ s, c ≤ ‖a - x‖) :
    c ^ Multiset.card s ≤ ‖Polynomial.eval x (s.map fun a => X - C a).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.card_cons, pow_succ, Multiset.map_cons, Multiset.prod_cons, eval_mul, norm_mul, mul_comm]
    have ha : c ≤ ‖eval x (X - C a)‖ := by
      rw [eval_sub, eval_X, eval_C, norm_sub_rev]
      exact hs a (Multiset.mem_cons_self a s)
    exact mul_le_mul ha (ih fun t ht => hs t (Multiset.mem_cons_of_mem ht)) (pow_nonneg hc _)
      (norm_nonneg _)

/- English proof (translation)
Establish `hsp : p.Splits` using `IsAlgClosed.splits p`. Establish `hcard` using `hsp.natDegree_eq_card_roots`. Establish `hne : p.roots ≠ 0`. Introduce `h`. Rewrite `hcard` using `[h, Multiset.card_zero]`.

Use linear arithmetic over natural numbers and integers. Take `⟨b, hb, hmin⟩` from `Multiset.exists_min_image (fun a => ‖a - x‖) hne`. Use `⟨b, hb, ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [hsp.eq_prod_roots]`. Rewrite using `[eval_mul, eval_C, norm_mul, hcard]`.

Conclude with `mul_le_mul_of_nonneg_left (pow_card_le_norm_eval_prod x _ (norm_nonneg _) _ hmin) (norm_nonneg _)`.
-/
theorem exists_root_norm_sub_pow_le {K : Type u_1} [inst : NormedField K] [IsAlgClosed K]
    (p : Polynomial K) (hp : (0 : ℕ) < Polynomial.natDegree p) (x : K) :
    ∃ b ∈ Polynomial.roots p,
      ‖Polynomial.leadingCoeff p‖ * ‖b - x‖ ^ Polynomial.natDegree p ≤ ‖Polynomial.eval x p‖ := by
  have hsp : p.Splits := IsAlgClosed.splits p
  have hcard := hsp.natDegree_eq_card_roots
  have hne : p.roots ≠ 0 := by
    intro h
    rw [h, Multiset.card_zero] at hcard
    omega
  obtain ⟨b, hb, hmin⟩ := Multiset.exists_min_image (fun a => ‖a - x‖) hne
  refine ⟨b, hb, ?_⟩
  conv_rhs => rw [hsp.eq_prod_roots]
  rw [eval_mul, eval_C, norm_mul, hcard]
  exact mul_le_mul_of_nonneg_left (pow_card_le_norm_eval_prod x _ (norm_nonneg _) _ hmin) (norm_nonneg _)

end GlobalTheory.RootNormPowerBound
