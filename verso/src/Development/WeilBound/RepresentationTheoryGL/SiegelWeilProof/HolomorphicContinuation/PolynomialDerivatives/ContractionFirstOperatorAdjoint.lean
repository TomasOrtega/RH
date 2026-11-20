import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PartialDerivZeroSecondFamily

noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC

namespace CoreC

open PositivityTheory.Rg.Sw G

variable {m n : ℕ}

/- English proof (translation)
Establish `h1` using `T1 ε (c := c) (k := (a, i, false)) (by simp [inF1, ha]) (partial_deriv_mem_first_family ε (b, i, false) hh) hg`. Establish `h2` using `T2 ε (c := c) (k := (b, i, false)) (by simp [inF1, hb]) hh (partial_deriv_mem_second_family ε (a, i, true) hg)`. Simplify using `only [pE_apply, Bool.not_false] at h1 h2`. Rewrite using `[h1, h2]`.
-/
theorem tA (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {a b : Fin m} (ha : ε a = true) (hb : ε b = true) (i : Fin n)
    {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (X (a, i, false) * pderiv (b, i, false) h * g) = contr c (h * (X (b, i, true) * pderiv (a, i, true) g)) := by
  have h1 := T1 ε (c := c) (k := (a, i, false)) (by simp [inF1, ha]) (partial_deriv_mem_first_family ε (b, i, false) hh) hg
  have h2 := T2 ε (c := c) (k := (b, i, false)) (by simp [inF1, hb]) hh (partial_deriv_mem_second_family ε (a, i, true) hg)
  simp only [pE_apply, Bool.not_false] at h1 h2
  rw [h1, h2]

/- English proof (translation)
Establish `h1` using `T1 ε (c := c) (k := (b, i, true)) (by simp [inF1, hb]) (partial_deriv_mem_first_family ε (a, i, true) hh) hg`. Establish `h2` using `T2 ε (c := c) (k := (a, i, true)) (by simp [inF1, ha]) hh (partial_deriv_mem_second_family ε (b, i, false) hg)`. Simplify using `only [pE_apply, Bool.not_true] at h1 h2`. Rewrite using `[h1, h2]`.
-/
theorem tB (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {a b : Fin m} (ha : ε a = false) (hb : ε b = false) (i : Fin n)
    {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (X (b, i, true) * pderiv (a, i, true) h * g) = contr c (h * (X (a, i, false) * pderiv (b, i, false) g)) := by
  have h1 := T1 ε (c := c) (k := (b, i, true)) (by simp [inF1, hb]) (partial_deriv_mem_first_family ε (a, i, true) hh) hg
  have h2 := T2 ε (c := c) (k := (a, i, true)) (by simp [inF1, ha]) hh (partial_deriv_mem_second_family ε (b, i, false) hg)
  simp only [pE_apply, Bool.not_true] at h1 h2
  rw [h1, h2]

/- English proof (translation)
Establish `hbT : inF1 ε (b, i, true)` using `by simp [inF1, hb]`. Establish `h1` using `T1 ε (c := c) (k := (a, i, false)) (by simp [inF1, ha]) (variable_mul_mem_first_family ε hbT hh) hg`. Establish `h2` using `T1 ε (c := c) (k := (b, i, true)) hbT hh (partial_deriv_mem_second_family ε (a, i, true) hg)`. Simplify using `only [pE_apply, Bool.not_false, Bool.not_true] at h1 h2`. Rewrite using `[mul_assoc (X (a, i, false)), h1, h2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem tC (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {a b : Fin m} (ha : ε a = true) (hb : ε b = false) (i : Fin n)
    {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (X (a, i, false) * X (b, i, true) * h * g) =
      ((2 * c : ℝ) : ℂ) ^ 2 * contr c (h * pderiv (b, i, false) (pderiv (a, i, true) g)) := by
  have hbT : inF1 ε (b, i, true) := by simp [inF1, hb]
  have h1 := T1 ε (c := c) (k := (a, i, false)) (by simp [inF1, ha]) (variable_mul_mem_first_family ε hbT hh) hg
  have h2 := T1 ε (c := c) (k := (b, i, true)) hbT hh (partial_deriv_mem_second_family ε (a, i, true) hg)
  simp only [pE_apply, Bool.not_false, Bool.not_true] at h1 h2
  rw [mul_assoc (X (a, i, false)), h1, h2]; ring

/- English proof (translation)
Establish `hbT : ¬ inF1 ε (b, i, true)` using `by simp [inF1, hb]`. Establish `h1` using `T2 ε (c := c) (k := (b, i, false)) (by simp [inF1, hb]) (partial_deriv_mem_first_family ε (a, i, true) hh) hg`. Establish `h2` using `T2 ε (c := c) (k := (a, i, true)) (by simp [inF1, ha]) hh (variable_mul_mem_second_family ε hbT hg)`. Simplify using `only [pE_apply, Bool.not_false, Bool.not_true] at h1 h2`. Rewrite using `[pow_two, mul_assoc, h1, h2, mul_assoc]`.
-/
theorem tD (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {a b : Fin m} (ha : ε a = false) (hb : ε b = true) (i : Fin n)
    {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    ((2 * c : ℝ) : ℂ) ^ 2 * contr c (pderiv (b, i, false) (pderiv (a, i, true) h) * g) =
      contr c (h * (X (a, i, false) * X (b, i, true) * g)) := by
  have hbT : ¬ inF1 ε (b, i, true) := by simp [inF1, hb]
  have h1 := T2 ε (c := c) (k := (b, i, false)) (by simp [inF1, hb]) (partial_deriv_mem_first_family ε (a, i, true) hh) hg
  have h2 := T2 ε (c := c) (k := (a, i, true)) (by simp [inF1, ha]) hh (variable_mul_mem_second_family ε hbT hg)
  simp only [pE_apply, Bool.not_false, Bool.not_true] at h1 h2
  rw [pow_two, mul_assoc, h1, h2, mul_assoc]

/- English proof (translation)
Establish `hc2 : ((2 * c : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (by positivity : (2 * c) ≠ 0)`. Unfold `D1 D2`. Distinguish the cases in `hab : ε a = ε b`. Rewrite using `[if_pos hab, if_pos hab]`. Consider the cases of `ha : ε a`.

Establish `hb : ε b = false` using `by rw [← hab, ha]`. Simplify using `only [Bool.false_eq_true, if_false]`. Rewrite using `[Finset.sum_mul, contr_sum, mul_neg, contr_neg, Finset.mul_sum, contr_sum, neg_neg]`. Conclude with `Finset.sum_congr rfl fun i _ => tB ε hc ha hb i hh hg`. Establish `hb : ε b = true` using `by rw [← hab, ha]`.

Simplify using `only [if_true]`. Rewrite using `[neg_mul, contr_neg, Finset.sum_mul, contr_sum, Finset.mul_sum, contr_sum]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => tA ε hc ha hb i hh hg`. Rewrite using `[if_neg hab, if_neg hab]`.

Consider the cases of `ha : ε a`. Apply the tactic sequence `have hb : ε b = true := by cases h' : ε b <;> simp_all`. Simplify using `only [Bool.false_eq_true, if_false]`. Rewrite using `[smul_mul_assoc, contr_smul, Finset.sum_mul, contr_sum, mul_smul_comm, contr_smul, Finset.mul_sum _ _ h, contr_sum]`. Repeatedly rewrite using `[← tD ε hc ha hb _ hh hg]`.

Rewrite using `[← Finset.mul_sum]`. Move the coercions through the operations in `at hc2 ⊢`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `have hb : ε b = false := by cases h' : ε b <;> simp_all`. Simplify using `only [if_true]`.

Rewrite using `[smul_mul_assoc, contr_smul, Finset.sum_mul, contr_sum, mul_smul_comm, contr_smul, Finset.mul_sum _ _ h, contr_sum]`. Repeatedly rewrite using `[tC ε hc ha hb _ hh hg]`. Rewrite using `[← Finset.mul_sum]`. Move the coercions through the operations in `at hc2 ⊢`. Clear the denominators using the available nonvanishing facts.
-/
theorem contraction_first_operator_adjoint (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (a b : Fin m) {h g : PX m n} (hh : h ∈ F1 ε)
    (hg : g ∈ F2 ε) : contr c (D1 ε c a b h * g) = -contr c (h * D2 ε c a b g) := by
  have hc2 : ((2 * c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * c) ≠ 0)
  unfold D1 D2
  by_cases hab : ε a = ε b
  · rw [if_pos hab, if_pos hab]
    cases ha : ε a
    · have hb : ε b = false := by rw [← hab, ha]
      simp only [Bool.false_eq_true, if_false]
      rw [Finset.sum_mul, contr_sum, mul_neg, contr_neg, Finset.mul_sum, contr_sum, neg_neg]
      exact Finset.sum_congr rfl fun i _ => tB ε hc ha hb i hh hg
    · have hb : ε b = true := by rw [← hab, ha]
      simp only [if_true]
      rw [neg_mul, contr_neg, Finset.sum_mul, contr_sum, Finset.mul_sum, contr_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => tA ε hc ha hb i hh hg
  · rw [if_neg hab, if_neg hab]
    cases ha : ε a
    · have hb : ε b = true := by cases h' : ε b <;> simp_all
      simp only [Bool.false_eq_true, if_false]
      rw [smul_mul_assoc, contr_smul, Finset.sum_mul, contr_sum, mul_smul_comm, contr_smul, Finset.mul_sum _ _ h,
        contr_sum]
      simp_rw [← tD ε hc ha hb _ hh hg]
      rw [← Finset.mul_sum]
      push_cast at hc2 ⊢
      field_simp
    · have hb : ε b = false := by cases h' : ε b <;> simp_all
      simp only [if_true]
      rw [smul_mul_assoc, contr_smul, Finset.sum_mul, contr_sum, mul_smul_comm, contr_smul, Finset.mul_sum _ _ h,
        contr_sum]
      simp_rw [tC ε hc ha hb _ hh hg]
      rw [← Finset.mul_sum]
      push_cast at hc2 ⊢
      field_simp

end CoreC

end PositivityTheory.Rg.Sw.LC
