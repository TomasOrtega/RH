import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.GaussianMomentRecurrence

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def hC (c : ℝ) (p q : ℕ) : ℂ := if p = q then (p.factorial : ℂ) * (2 * c : ℂ) ^ p else 0

def wC (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : ℂ := ∏ a, ∏ i, hC c (s (a, i, false)) (s (a, i, true))

/- English proof (translation)
Unfold `hC`. Distinguish the cases in `h : p = q`. Substitute `h` using the available equality. Both sides reduce to the same expression. Rewrite using `[if_neg h, if_neg (Ne.symm h)]`.
-/
theorem hC_comm (c : ℝ) (p q : ℕ) : hC c p q = hC c q p := by
  unfold hC; by_cases h : p = q
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

/- English proof (translation)
Break down `q with _ | q` into its components or cases. Simplify using `[hC]`. Simplify using `only [hC, Nat.add_sub_cancel, Nat.add_right_cancel_iff] split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[Nat.factorial_succ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem hC_rel (c : ℝ) (p q : ℕ) : hC c (p + 1) q = (2 * c : ℂ) * (q : ℂ) * hC c p (q - 1) := by
  rcases q with _ | q
  · simp [hC]
  · simp only [hC, Nat.add_sub_cancel, Nat.add_right_cancel_iff]
    split_ifs with h
    · subst h; rw [Nat.factorial_succ]; push_cast; ring
    · simp

/- English proof (translation)
Unfold `contr wC`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Establish `: (∏ a, ∏ i, hC c (s (a, i, false)) (s (a, i, true))) = if ∀ a i, s (a, i, false) = s (a, i, true) then ∏ a, ∏ i, (((s (a, i, false)).factorial : ℂ) * (2 * c : ℂ) ^ (s (a, i, false))) else 0`. Simplify using `only [hC, Finset.prod_ite_zero, Finset.mem_univ, true_implies]`. Rewrite using `[this]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem contr_eq (c : ℝ) (p : PX m n) : contr c p = ∑ s ∈ p.support, p.coeff s * wC c s := by
  unfold contr wC
  refine Finset.sum_congr rfl fun s _ => ?_
  have : (∏ a, ∏ i, hC c (s (a, i, false)) (s (a, i, true))) =
      if ∀ a i, s (a, i, false) = s (a, i, true) then
        ∏ a, ∏ i, (((s (a, i, false)).factorial : ℂ) * (2 * c : ℂ) ^ (s (a, i, false))) else 0 := by
    simp only [hC, Finset.prod_ite_zero, Finset.mem_univ, true_implies]
  rw [this]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[contr_eq]`. Use `Finset.sum_subset hS fun s _ hs => ?_` and prove the remaining obligations. Rewrite using `[notMem_support_iff.1 hs, zero_mul]`.
-/
theorem contr_eq_of_subset (c : ℝ) (p : PX m n) (S : Finset (Fin m × Fin n × Bool →₀ ℕ)) (hS : p.support ⊆ S) :
    contr c p = ∑ s ∈ S, p.coeff s * wC c s := by
  rw [contr_eq]
  refine Finset.sum_subset hS fun s _ hs => ?_
  rw [notMem_support_iff.1 hs, zero_mul]

/- English proof (translation)
Rewrite using `[contr_eq_of_subset c (p + q) (p.support ∪ q.support) support_add, contr_eq_of_subset c p (p.support ∪ q.support) Finset.subset_union_left, contr_eq_of_subset c q (p.support ∪ q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_add, add_mul]`.
-/
theorem contr_add (c : ℝ) (p q : PX m n) : contr c (p + q) = contr c p + contr c q := by
  classical
  rw [contr_eq_of_subset c (p + q) (p.support ∪ q.support) support_add,
    contr_eq_of_subset c p (p.support ∪ q.support) Finset.subset_union_left,
    contr_eq_of_subset c q (p.support ∪ q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_add, add_mul]

/- English proof (translation)
Rewrite using `[contr_eq_of_subset c _ {s} support_monomial_subset, Finset.sum_singleton, coeff_monomial, if_pos rfl]`.
-/
theorem contr_monomial (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (r : ℂ) : contr c (monomial s r) = r * wC c s := by
  classical
  rw [contr_eq_of_subset c _ {s} support_monomial_subset, Finset.sum_singleton, coeff_monomial, if_pos rfl]

/- English proof (translation)
Rewrite using `[← monomial_zero', contr_monomial]`. Simplify using `[wC, hC]`.
-/
theorem contr_C (c : ℝ) (r : ℂ) : contr c (C r : PX m n) = r := by
  rw [← monomial_zero', contr_monomial]
  simp [wC, hC]

/- English proof (translation)
Unfold `wC`. Rewrite using `[← Fintype.prod_prod_type' (f := fun a i => hC c (s (a, i, false)) (s (a, i, true)))]`. Conclude with `(Finset.mul_prod_erase _ (fun x : Fin m × Fin n => hC c (s (x.1, x.2, false)) (s (x.1, x.2, true))) (Finset.mem_univ (a, i))).symm`.
-/
theorem wC_split (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (i : Fin n) :
    wC c s = hC c (s (a, i, false)) (s (a, i, true)) *
      ∏ x ∈ Finset.univ.erase (a, i), hC c (s (x.1, x.2, false)) (s (x.1, x.2, true)) := by
  unfold wC
  rw [← Fintype.prod_prod_type' (f := fun a i => hC c (s (a, i, false)) (s (a, i, true)))]
  exact (Finset.mul_prod_erase _ (fun x : Fin m × Fin n => hC c (s (x.1, x.2, false)) (s (x.1, x.2, true)))
    (Finset.mem_univ (a, i))).symm

/- English proof (translation)
Take `⟨a, i, b⟩` from `k`. Rewrite using `[wC_split c _ a i, wC_split c _ a i]`. Establish `hrest : ∏ x ∈ Finset.univ.erase (a, i), hC c ((Finsupp.single (a, i, b) 1 + u : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, false)) ((Finsupp.single (a, i, b) 1 + u : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, true)) = ∏ x ∈ Finset.univ.erase (a, i), hC c ((u - Finsupp.single (flip (a, i, b …`. Use `Finset.prod_congr rfl fun x hx => ?_` and prove the remaining obligations. Establish `hx'` using `(Finset.mem_erase.1 hx).1`.

Establish `key : ∀ b', (Finsupp.single (a, i, b) 1 + u : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, b') = (u - Finsupp.single (flip (a, i, b)) 1 : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, b')`. Introduce `b'`. Establish `h1 : (a, i, b) ≠ (x.1, x.2, b')` using `fun h => hx' (by`. Use `congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h` as an intermediate fact. Simplify using `at this`.

Conclude with `this.symm)`. Establish `h2 : flip (a, i, b) ≠ (x.1, x.2, b')` using `fun h => hx' (by`. Use `congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h` as an intermediate fact. Simplify using `[flip] at this`. Conclude with `this.symm)`.

Simplify using `only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, if_neg h1, if_neg h2, tsub_zero, zero_add]`. Rewrite using `[key false, key true]`. Rewrite using `[hrest, ← mul_assoc]`. Use `congr 1`. Establish `e1 : (a, i, true) ≠ (a, i, false)` using `by simp`.

Consider the cases of `b`. Simplify using `only [flip, Bool.not_false, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]`. Rewrite using `[add_comm]`. Conclude with `hC_rel c _ _`. Simplify using `only [flip, Bool.not_true, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]`.

Rewrite using `[hC_comm c (u (a, i, false)), hC_comm c (u (a, i, false) - 1), add_comm]`. Conclude with `hC_rel c _ _`.
-/
theorem wC_rel (c : ℝ) (u : Fin m × Fin n × Bool →₀ ℕ) (k : Fin m × Fin n × Bool) :
    wC c (Finsupp.single k 1 + u) = (2 * c : ℂ) * (u (flip k) : ℂ) * wC c (u - Finsupp.single (flip k) 1) := by
  obtain ⟨a, i, b⟩ := k
  rw [wC_split c _ a i, wC_split c _ a i]
  have hrest : ∏ x ∈ Finset.univ.erase (a, i), hC c ((Finsupp.single (a, i, b) 1 + u : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, false))
        ((Finsupp.single (a, i, b) 1 + u : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, true)) =
      ∏ x ∈ Finset.univ.erase (a, i), hC c ((u - Finsupp.single (flip (a, i, b)) 1 : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, false))
        ((u - Finsupp.single (flip (a, i, b)) 1 : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, true)) := by
    refine Finset.prod_congr rfl fun x hx => ?_
    have hx' := (Finset.mem_erase.1 hx).1
    have key : ∀ b', (Finsupp.single (a, i, b) 1 + u : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, b') = (u - Finsupp.single (flip (a, i, b)) 1 : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, b') := by
      intro b'
      have h1 : (a, i, b) ≠ (x.1, x.2, b') := fun h => hx' (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simp at this; exact this.symm)
      have h2 : flip (a, i, b) ≠ (x.1, x.2, b') := fun h => hx' (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simp [flip] at this; exact this.symm)
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
        if_neg h1, if_neg h2, tsub_zero, zero_add]
    rw [key false, key true]
  rw [hrest, ← mul_assoc]
  congr 1
  have e1 : (a, i, true) ≠ (a, i, false) := by simp
  cases b
  · simp only [flip, Bool.not_false, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [add_comm]
    exact hC_rel c _ _
  · simp only [flip, Bool.not_true, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [hC_comm c (u (a, i, false)), hC_comm c (u (a, i, false) - 1), add_comm]
    exact hC_rel c _ _

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on' with`. Consider the case `monomial u r`. Establish `hX : (X k : PX m n) * monomial u r = monomial (Finsupp.single k 1 + u) r`. Rewrite using `[X, monomial_mul, one_mul]`. Rewrite using `[hX, pderiv_monomial, contr_monomial, contr_monomial, wC_rel]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `add P Q hP hQ => rw [mul_add, contr_add, hP, hQ, map_add, contr_add, mul_add]`.
-/
theorem contr_X_mul (c : ℝ) (k : Fin m × Fin n × Bool) (p : PX m n) :
    contr c (X k * p) = (2 * c : ℂ) * contr c (pderiv (flip k) p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial u r =>
    have hX : (X k : PX m n) * monomial u r = monomial (Finsupp.single k 1 + u) r := by
      rw [X, monomial_mul, one_mul]
    rw [hX, pderiv_monomial, contr_monomial, contr_monomial, wC_rel]
    ring
  | add P Q hP hQ => rw [mul_add, contr_add, hP, hQ, map_add, contr_add, mul_add]

end PositivityTheory.Rg.Sw.LC
