import Mathlib

namespace GlobalTheory.RootNormBound

open Polynomial

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih`. Rewrite using `[Multiset.card_cons, pow_succ, Multiset.map_cons, Multiset.prod_cons, norm_mul, mul_comm]`. Establish `ha : ε ≤ ‖(0 : ℂ) - a‖`.

Rewrite using `[zero_sub, norm_neg]`. Conclude with `hs a (Multiset.mem_cons_self a s)`. Conclude with `mul_le_mul ha (ih fun t ht => hs t (Multiset.mem_cons_of_mem ht)) (pow_nonneg hε _) (norm_nonneg _)`.
-/
theorem pow_card_le_norm_prod {ε : ℝ} (hε : 0 ≤ ε) (s : Multiset ℂ)
    (hs : ∀ t ∈ s, ε ≤ ‖t‖) :
    ε ^ Multiset.card s ≤ ‖(s.map (fun a => (0 : ℂ) - a)).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.card_cons, pow_succ, Multiset.map_cons, Multiset.prod_cons, norm_mul, mul_comm]
    have ha : ε ≤ ‖(0 : ℂ) - a‖ := by
      rw [zero_sub, norm_neg]
      exact hs a (Multiset.mem_cons_self a s)
    exact mul_le_mul ha (ih fun t ht => hs t (Multiset.mem_cons_of_mem ht)) (pow_nonneg hε _)
      (norm_nonneg _)

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `hsp : h.Splits` using `IsAlgClosed.splits h`. Establish `hne0 : h ≠ 0` using `hm.ne_zero`. Establish `key` using `pow_card_le_norm_prod hε h.roots fun t ht => hne t ((mem_roots hne0).1 ht)`.

Rewrite `key` using `[← hsp.eval_eq_prod_roots_of_monic hm 0, ← coeff_zero_eq_eval_zero, ← hsp.natDegree_eq_card_roots]`. Conclude with `absurd hc (not_lt.2 key)`.
-/
theorem exists_root_norm_lt {h : Polynomial ℂ} (hm : h.Monic) {ε : ℝ} (hε : 0 ≤ ε)
    (hc : ‖h.coeff 0‖ < ε ^ h.natDegree) : ∃ t : ℂ, h.IsRoot t ∧ ‖t‖ < ε := by
  by_contra hne
  push Not at hne
  have hsp : h.Splits := IsAlgClosed.splits h
  have hne0 : h ≠ 0 := hm.ne_zero
  have key := pow_card_le_norm_prod hε h.roots fun t ht => hne t ((mem_roots hne0).1 ht)
  rw [← hsp.eval_eq_prod_roots_of_monic hm 0, ← coeff_zero_eq_eval_zero,
    ← hsp.natDegree_eq_card_roots] at key
  exact absurd hc (not_lt.2 key)

end GlobalTheory.RootNormBound
