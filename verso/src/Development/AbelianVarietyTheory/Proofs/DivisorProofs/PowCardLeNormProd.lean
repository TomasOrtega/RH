import Mathlib

namespace GlobalTheory.RootNormLowerBound

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih`. Establish `ha` using `h a (Multiset.mem_cons_self a s)`. Establish `ih'` using `ih fun t ht => h t (Multiset.mem_cons_of_mem ht)`.

Rewrite using `[Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, norm_mul, norm_neg, pow_succ, mul_comm (ε ^ Multiset.card s)]`. Conclude with `mul_le_mul ha ih' (by positivity) (norm_nonneg _)`.
-/
theorem pow_card_le_norm_prod {ε : ℝ} (hε : 0 < ε) (s : Multiset ℂ)
    (h : ∀ t ∈ s, ε ≤ ‖t‖) : ε ^ Multiset.card s ≤ ‖(s.map (fun a => -a)).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha := h a (Multiset.mem_cons_self a s)
    have ih' := ih fun t ht => h t (Multiset.mem_cons_of_mem ht)
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, norm_mul, norm_neg, pow_succ,
      mul_comm (ε ^ Multiset.card s)]
    exact mul_le_mul ha ih' (by positivity) (norm_nonneg _)

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Establish `hall : ∀ t ∈ F.roots, ε ≤ ‖t‖` using `fun t ht => le_of_not_gt fun hlt => hcon ⟨t, (Polynomial.mem_roots hF.ne_zero).1 ht, hlt⟩`. Establish `h1` using `pow_card_le_norm_prod hε F.roots hall`. Establish `hc : F.coeff 0 = (F.roots.map fun a => -a).prod`. Rewrite using `[(IsAlgClosed.splits F).coeff_zero_eq_prod_roots_of_monic hF, Multiset.prod_map_neg, IsAlgClosed.card_roots_eq_natDegree]`.

Rewrite `h1` using `[IsAlgClosed.card_roots_eq_natDegree, ← hc]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_root_norm_lt {F : Polynomial ℂ} (hF : Polynomial.Monic F) {ε : ℝ}
    (hε : (0 : ℝ) < ε) (h0 : ‖Polynomial.coeff F (0 : ℕ)‖ < ε ^ Polynomial.natDegree F) :
    ∃ (t : ℂ), Polynomial.IsRoot F t ∧ ‖t‖ < ε := by
  by_contra hcon
  have hall : ∀ t ∈ F.roots, ε ≤ ‖t‖ := fun t ht =>
    le_of_not_gt fun hlt => hcon ⟨t, (Polynomial.mem_roots hF.ne_zero).1 ht, hlt⟩
  have h1 := pow_card_le_norm_prod hε F.roots hall
  have hc : F.coeff 0 = (F.roots.map fun a => -a).prod := by
    rw [(IsAlgClosed.splits F).coeff_zero_eq_prod_roots_of_monic hF, Multiset.prod_map_neg,
      IsAlgClosed.card_roots_eq_natDegree]
  rw [IsAlgClosed.card_roots_eq_natDegree, ← hc] at h1
  linarith

end GlobalTheory.RootNormLowerBound
