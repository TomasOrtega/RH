import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

noncomputable section

open UpperHalfPlane hiding I
open MeasureTheory Complex CongruenceSubgroup Filter Topology NumberField IsDedekindDomain
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped MatrixGroups ModularForm Modular ComplexConjugate Real ArithmeticFunction.Moebius NumberTheorySymbols

namespace Ad3.S

namespace PLB

/- English proof (translation)
Establish `h1 : HasDerivAt (fun w : ℂ => b + w) 1 (t : ℂ)` using `(hasDerivAt_id' (x := (t : ℂ))).const_add b`. Establish `h3` using `(h1.cpow_const (c := c) h).comp_ofReal`. Rewrite `h3` using `[mul_one, ← hd]`. Conclude with `h3`.
-/
lemma hd_add (b c d : ℂ) (hd : d = c - 1) {t : ℝ} (h : b + t ∈ Complex.slitPlane) :
    HasDerivAt (fun t : ℝ => (b + t) ^ c) (c * (b + t) ^ d) t := by
  have h1 : HasDerivAt (fun w : ℂ => b + w) 1 (t : ℂ) := (hasDerivAt_id' (x := (t : ℂ))).const_add b
  have h3 := (h1.cpow_const (c := c) h).comp_ofReal
  rw [mul_one, ← hd] at h3
  exact h3

/- English proof (translation)
Establish `h1 : HasDerivAt (fun w : ℂ => b - w) (-1) (t : ℂ)` using `(hasDerivAt_id' (x := (t : ℂ))).const_sub b`. Establish `h3` using `(h1.cpow_const (c := c) h).comp_ofReal`. Rewrite `h3` using `[mul_neg_one, ← hd]`. Conclude with `h3`.
-/
lemma hd_sub (b c d : ℂ) (hd : d = c - 1) {t : ℝ} (h : b - t ∈ Complex.slitPlane) :
    HasDerivAt (fun t : ℝ => (b - t) ^ c) (-(c * (b - t) ^ d)) t := by
  have h1 : HasDerivAt (fun w : ℂ => b - w) (-1) (t : ℂ) := (hasDerivAt_id' (x := (t : ℂ))).const_sub b
  have h3 := (h1.cpow_const (c := c) h).comp_ofReal
  rw [mul_neg_one, ← hd] at h3
  exact h3

/- English proof (translation)
Establish `hK0 : 0 ≤ K` using `le_trans (norm_nonneg _) (hK 0 ⟨le_rfl, zero_le_one⟩)`. Establish `b1 : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖h' t‖ ≤ K`. Introduce `t ht`. Use `norm_image_sub_le_of_norm_deriv_le_segment' (f := h') (f' := h'') (C := K) (fun x hx => (d2 x hx).hasDerivWithinAt) (fun x hx => hK x (Set.Ico_subset_Icc_self hx)) t ht` as an intermediate fact. Rewrite `this` using `[h0, sub_zero]`.

Use polynomial arithmetic with `[ht.1, ht.2]`. Conclude with `norm_image_sub_le_of_norm_deriv_le_segment_01' (fun x hx => (d1 x hx).hasDerivWithinAt) (fun x hx => b1 x (Set.Ico_subset_Icc_self hx))`.
-/
lemma mvt2 {h h' h'' : ℝ → ℂ} {K : ℝ}
    (d1 : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt h (h' t) t)
    (d2 : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt h' (h'' t) t)
    (h0 : h' 0 = 0) (hK : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖h'' t‖ ≤ K) : ‖h 1 - h 0‖ ≤ K := by
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0 ⟨le_rfl, zero_le_one⟩)
  have b1 : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖h' t‖ ≤ K := by
    intro t ht
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := h') (f' := h'') (C := K)
      (fun x hx => (d2 x hx).hasDerivWithinAt) (fun x hx => hK x (Set.Ico_subset_Icc_self hx)) t ht
    rw [h0, sub_zero] at this
    nlinarith [ht.1, ht.2]
  exact norm_image_sub_le_of_norm_deriv_le_segment_01' (fun x hx => (d1 x hx).hasDerivWithinAt)
    (fun x hx => b1 x (Set.Ico_subset_Icc_self hx))

/- English proof (translation)
The claim follows from `Complex.norm_cpow_eq_rpow_re_of_pos hy c`.
-/
lemma norm_re (y : ℝ) (hy : 0 < y) (c : ℂ) : ‖(y : ℂ) ^ c‖ = y ^ c.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hy c

/- English proof (translation)
Establish `mm : ∀ t ∈ Set.Icc (0:ℝ) 1, (x : ℂ) + 1 - t ∈ Complex.slitPlane`. Introduce `t ht`. Rewrite using `[show (x : ℂ) + 1 - t = ((x + 1 - t : ℝ) : ℂ) by push_cast; ring]`. Conclude with `Complex.ofReal_mem_slitPlane.2 (by linarith [ht.2])`. Establish `mp : ∀ t ∈ Set.Icc (0:ℝ) 1, (x : ℂ) + 1 + t ∈ Complex.slitPlane`.

Introduce `t ht`. Rewrite using `[show (x : ℂ) + 1 + t = ((x + 1 + t : ℝ) : ℂ) by push_cast; ring]`. Conclude with `Complex.ofReal_mem_slitPlane.2 (by linarith [ht.1])`. Establish `key` using `mvt2 (h := fun t : ℝ => ((x : ℂ) + 1 - t) ^ (-s) + ((x : ℂ) + 1 + t) ^ (-s)) (h' := fun t : ℝ => -(-s * ((x : ℂ) + 1 - t) ^ (-s - 1)) + -s * ((x : ℂ) + 1 + t) ^ (-s - 1)) (h'' := fun t : ℝ => -s * (-s - 1) * (((x : ℂ) + 1 - t) ^ (-s - 2) + ((x : ℂ) + 1 + t) ^ (-s - 2))) (K := ‖s‖ …`. Establish `e : ((x:ℂ) + 1 - ((1:ℝ):ℂ)) ^ (-s) + ((x:ℂ) + 1 + ((1:ℝ):ℂ)) ^ (-s) - (((x:ℂ) + 1 - ((0:ℝ):ℂ)) ^ (-s) + ((x:ℂ) + 1 + ((0:ℝ):ℂ)) ^ (-s)) = (x : ℂ) ^ (-s) - 2 * ((x : ℂ) + 1) ^ (-s) + ((x : ℂ) + 2) ^ (-s)`.

Rewrite using `[Complex.ofReal_one, Complex.ofReal_zero, add_sub_cancel_right, sub_zero, add_zero, add_assoc, one_add_one_eq_two]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← e]`. Conclude with `key`. Introduce `t ht`.

Use `((hd_sub _ (-s) (-s - 1) (by ring) (mm t ht)).add (hd_add _ (-s) (-s - 1) (by ring) (mp t ht))).congr_deriv ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Introduce `t ht`. Use `(((hd_sub _ (-s - 1) (-s - 2) (by ring) (mm t ht)).const_mul (-s)).neg.add ((hd_add _ (-s - 1) (-s - 2) (by ring) (mp t ht)).const_mul (-s))).congr_deriv ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Introduce `t ht`. Establish `e1 : ‖((x : ℂ) + 1 - t) ^ (-s - 2)‖ ≤ x ^ (-s.re - 2)`. Rewrite using `[show (x : ℂ) + 1 - t = ((x + 1 - t : ℝ) : ℂ) by push_cast; ring, norm_re _ (by linarith [ht.2])]`. Establish `: (-s - 2).re = -s.re - 2` using `by simp`.

Rewrite using `[this]`. Conclude with `Real.rpow_le_rpow_of_nonpos hx (by linarith [ht.2]) (by linarith)`. Establish `e2 : ‖((x : ℂ) + 1 + t) ^ (-s - 2)‖ ≤ x ^ (-s.re - 2)`. Rewrite using `[show (x : ℂ) + 1 + t = ((x + 1 + t : ℝ) : ℂ) by push_cast; ring, norm_re _ (by linarith [ht.1])]`. Establish `: (-s - 2).re = -s.re - 2` using `by simp`.

Rewrite using `[this]`. Conclude with `Real.rpow_le_rpow_of_nonpos hx (by linarith [ht.1]) (by linarith)`. Establish `e3 : ‖-s - 1‖ = ‖s + 1‖` using `by rw [show -s - 1 = -(s + 1) by ring, norm_neg]`. Rewrite using `[norm_mul, norm_mul, norm_neg, e3]`. Use `gcongr`.

Combine the equalities or inequalities in the displayed calculation.
-/
lemma second_difference_cpow_bound (x : ℝ) (hx : 0 < x) (s : ℂ) (hs : -2 ≤ s.re) :
    ‖(x : ℂ) ^ (-s) - 2 * ((x : ℂ) + 1) ^ (-s) + ((x : ℂ) + 2) ^ (-s)‖ ≤
      ‖s‖ * ‖s + 1‖ * (2 * x ^ (-s.re - 2)) := by
  have mm : ∀ t ∈ Set.Icc (0:ℝ) 1, (x : ℂ) + 1 - t ∈ Complex.slitPlane := by
    intro t ht
    rw [show (x : ℂ) + 1 - t = ((x + 1 - t : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_mem_slitPlane.2 (by linarith [ht.2])
  have mp : ∀ t ∈ Set.Icc (0:ℝ) 1, (x : ℂ) + 1 + t ∈ Complex.slitPlane := by
    intro t ht
    rw [show (x : ℂ) + 1 + t = ((x + 1 + t : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_mem_slitPlane.2 (by linarith [ht.1])
  have key := mvt2 (h := fun t : ℝ => ((x : ℂ) + 1 - t) ^ (-s) + ((x : ℂ) + 1 + t) ^ (-s))
    (h' := fun t : ℝ => -(-s * ((x : ℂ) + 1 - t) ^ (-s - 1)) + -s * ((x : ℂ) + 1 + t) ^ (-s - 1))
    (h'' := fun t : ℝ => -s * (-s - 1) * (((x : ℂ) + 1 - t) ^ (-s - 2) + ((x : ℂ) + 1 + t) ^ (-s - 2)))
    (K := ‖s‖ * ‖s + 1‖ * (2 * x ^ (-s.re - 2))) ?_ ?_ ?_ ?_
  · have e : ((x:ℂ) + 1 - ((1:ℝ):ℂ)) ^ (-s) + ((x:ℂ) + 1 + ((1:ℝ):ℂ)) ^ (-s) -
        (((x:ℂ) + 1 - ((0:ℝ):ℂ)) ^ (-s) + ((x:ℂ) + 1 + ((0:ℝ):ℂ)) ^ (-s)) =
        (x : ℂ) ^ (-s) - 2 * ((x : ℂ) + 1) ^ (-s) + ((x : ℂ) + 2) ^ (-s) := by
      rw [Complex.ofReal_one, Complex.ofReal_zero, add_sub_cancel_right, sub_zero, add_zero, add_assoc,
        one_add_one_eq_two]
      ring
    rw [← e]
    exact key
  · intro t ht
    refine ((hd_sub _ (-s) (-s - 1) (by ring) (mm t ht)).add (hd_add _ (-s) (-s - 1) (by ring) (mp t ht))).congr_deriv ?_
    ring
  · intro t ht
    refine (((hd_sub _ (-s - 1) (-s - 2) (by ring) (mm t ht)).const_mul (-s)).neg.add
      ((hd_add _ (-s - 1) (-s - 2) (by ring) (mp t ht)).const_mul (-s))).congr_deriv ?_
    ring
  · simp
  · intro t ht
    have e1 : ‖((x : ℂ) + 1 - t) ^ (-s - 2)‖ ≤ x ^ (-s.re - 2) := by
      rw [show (x : ℂ) + 1 - t = ((x + 1 - t : ℝ) : ℂ) by push_cast; ring, norm_re _ (by linarith [ht.2])]
      have : (-s - 2).re = -s.re - 2 := by simp
      rw [this]
      exact Real.rpow_le_rpow_of_nonpos hx (by linarith [ht.2]) (by linarith)
    have e2 : ‖((x : ℂ) + 1 + t) ^ (-s - 2)‖ ≤ x ^ (-s.re - 2) := by
      rw [show (x : ℂ) + 1 + t = ((x + 1 + t : ℝ) : ℂ) by push_cast; ring, norm_re _ (by linarith [ht.1])]
      have : (-s - 2).re = -s.re - 2 := by simp
      rw [this]
      exact Real.rpow_le_rpow_of_nonpos hx (by linarith [ht.1]) (by linarith)
    have e3 : ‖-s - 1‖ = ‖s + 1‖ := by rw [show -s - 1 = -(s + 1) by ring, norm_neg]
    rw [norm_mul, norm_mul, norm_neg, e3]
    gcongr
    calc _ ≤ ‖((x : ℂ) + 1 - t) ^ (-s - 2)‖ + ‖((x : ℂ) + 1 + t) ^ (-s - 2)‖ := norm_add_le _ _
      _ ≤ _ := by linarith

/- English proof (translation)
Establish `mp : ∀ t ∈ Set.Icc (0:ℝ) 1, (x : ℂ) + t ∈ Complex.slitPlane`. Introduce `t ht`. Rewrite using `[show (x : ℂ) + t = ((x + t : ℝ) : ℂ) by push_cast; ring]`. Conclude with `Complex.ofReal_mem_slitPlane.2 (by linarith [ht.1])`. Establish `key` using `mvt2 (h := fun t : ℝ => ((x : ℂ) + t) ^ (1 - s) - (x : ℂ) ^ (1 - s) + (t : ℂ) / 2 * ((s - 1) * (x : ℂ) ^ (-s) + (s - 1) * ((x : ℂ) + t) ^ (-s))) (h' := fun t : ℝ => 1 / 2 * ((s - 1) * (x : ℂ) ^ (-s) - (s - 1) * ((x : ℂ) + t) ^ (-s)) + (t : ℂ) / 2 * ((s - 1) * (-s * ((x : ℂ) + t) …`.

Establish `e : ((x : ℂ) + ((1:ℝ):ℂ)) ^ (1 - s) - (x : ℂ) ^ (1 - s) + ((1:ℝ):ℂ) / 2 * ((s - 1) * (x : ℂ) ^ (-s) + (s - 1) * ((x : ℂ) + ((1:ℝ):ℂ)) ^ (-s)) - (((x : ℂ) + ((0:ℝ):ℂ)) ^ (1 - s) - (x : ℂ) ^ (1 - s) + ((0:ℝ):ℂ) / 2 * ((s - 1) * (x : ℂ) ^ (-s) + (s - 1) * ((x : ℂ) + ((0:ℝ):ℂ)) ^ (-s …`. Rewrite using `[Complex.ofReal_one, Complex.ofReal_zero, add_zero]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← e]`. Conclude with `key`.

Introduce `t ht`. Use `(((hd_add _ (1 - s) (-s) (by ring) (mp t ht)).sub_const ((x : ℂ) ^ (1 - s))).add (((hasDerivAt_id' (x := t)).ofReal_comp.div_const 2).mul (((hd_add _ (-s) (-s - 1) (by ring) (mp t ht)).const_mul (s - 1)).const_add ((s - 1) * (x : ℂ) ^ (-s))))).congr_deriv ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `t ht`.

Use `(((((hd_add _ (-s) (-s - 1) (by ring) (mp t ht)).const_mul (s - 1)).const_sub ((s - 1) * (x : ℂ) ^ (-s))).const_mul (1 / 2)).add (((hasDerivAt_id' (x := t)).ofReal_comp.div_const 2).mul (((hd_add _ (-s - 1) (-s - 2) (by ring) (mp t ht)).const_mul (-s)).const_mul (s - 1)))).congr_ …` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Introduce `t ht`.

Establish `e1 : ‖((x : ℂ) + t) ^ (-s - 2)‖ ≤ x ^ (-s.re - 2)`. Rewrite using `[show (x : ℂ) + t = ((x + t : ℝ) : ℂ) by push_cast; ring, norm_re _ (by linarith [ht.1])]`. Establish `: (-s - 2).re = -s.re - 2` using `by simp`. Rewrite using `[this]`. Conclude with `Real.rpow_le_rpow_of_nonpos hx (by linarith [ht.1]) (by linarith)`.

Establish `e3 : ‖-s - 1‖ = ‖s + 1‖` using `by rw [show -s - 1 = -(s + 1) by ring, norm_neg]`. Establish `e4 : ‖(t : ℂ) / 2‖ ≤ 1 / 2`. Rewrite using `[norm_div, Complex.norm_real, Real.norm_of_nonneg ht.1, Complex.norm_two]`. Combine the linear relations using `[ht.2]`. Rewrite using `[norm_mul, norm_mul, norm_mul, norm_mul, norm_neg, e3]`.

Use `gcongr`.
-/
lemma trap_bound (x : ℝ) (hx : 0 < x) (s : ℂ) (hs : -2 ≤ s.re) :
    ‖(s - 1) / 2 * ((x : ℂ) ^ (-s) + ((x : ℂ) + 1) ^ (-s)) - ((x : ℂ) ^ (1 - s) - ((x : ℂ) + 1) ^ (1 - s))‖ ≤
      1 / 2 * (‖s - 1‖ * (‖s‖ * (‖s + 1‖ * x ^ (-s.re - 2)))) := by
  have mp : ∀ t ∈ Set.Icc (0:ℝ) 1, (x : ℂ) + t ∈ Complex.slitPlane := by
    intro t ht
    rw [show (x : ℂ) + t = ((x + t : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_mem_slitPlane.2 (by linarith [ht.1])
  have key := mvt2 (h := fun t : ℝ => ((x : ℂ) + t) ^ (1 - s) - (x : ℂ) ^ (1 - s) +
      (t : ℂ) / 2 * ((s - 1) * (x : ℂ) ^ (-s) + (s - 1) * ((x : ℂ) + t) ^ (-s)))
    (h' := fun t : ℝ => 1 / 2 * ((s - 1) * (x : ℂ) ^ (-s) - (s - 1) * ((x : ℂ) + t) ^ (-s)) +
      (t : ℂ) / 2 * ((s - 1) * (-s * ((x : ℂ) + t) ^ (-s - 1))))
    (h'' := fun t : ℝ => (t : ℂ) / 2 * ((s - 1) * (-s * ((-s - 1) * ((x : ℂ) + t) ^ (-s - 2)))))
    (K := 1 / 2 * (‖s - 1‖ * (‖s‖ * (‖s + 1‖ * x ^ (-s.re - 2))))) ?_ ?_ ?_ ?_
  · have e : ((x : ℂ) + ((1:ℝ):ℂ)) ^ (1 - s) - (x : ℂ) ^ (1 - s) +
        ((1:ℝ):ℂ) / 2 * ((s - 1) * (x : ℂ) ^ (-s) + (s - 1) * ((x : ℂ) + ((1:ℝ):ℂ)) ^ (-s)) -
        (((x : ℂ) + ((0:ℝ):ℂ)) ^ (1 - s) - (x : ℂ) ^ (1 - s) +
        ((0:ℝ):ℂ) / 2 * ((s - 1) * (x : ℂ) ^ (-s) + (s - 1) * ((x : ℂ) + ((0:ℝ):ℂ)) ^ (-s))) =
        (s - 1) / 2 * ((x : ℂ) ^ (-s) + ((x : ℂ) + 1) ^ (-s)) - ((x : ℂ) ^ (1 - s) - ((x : ℂ) + 1) ^ (1 - s)) := by
      rw [Complex.ofReal_one, Complex.ofReal_zero, add_zero]
      ring
    rw [← e]
    exact key
  · intro t ht
    refine (((hd_add _ (1 - s) (-s) (by ring) (mp t ht)).sub_const ((x : ℂ) ^ (1 - s))).add
      (((hasDerivAt_id' (x := t)).ofReal_comp.div_const 2).mul
        (((hd_add _ (-s) (-s - 1) (by ring) (mp t ht)).const_mul (s - 1)).const_add
          ((s - 1) * (x : ℂ) ^ (-s))))).congr_deriv ?_
    push_cast
    ring
  · intro t ht
    refine (((((hd_add _ (-s) (-s - 1) (by ring) (mp t ht)).const_mul (s - 1)).const_sub
      ((s - 1) * (x : ℂ) ^ (-s))).const_mul (1 / 2)).add
      (((hasDerivAt_id' (x := t)).ofReal_comp.div_const 2).mul
        (((hd_add _ (-s - 1) (-s - 2) (by ring) (mp t ht)).const_mul (-s)).const_mul (s - 1)))).congr_deriv ?_
    push_cast
    ring
  · simp
  · intro t ht
    have e1 : ‖((x : ℂ) + t) ^ (-s - 2)‖ ≤ x ^ (-s.re - 2) := by
      rw [show (x : ℂ) + t = ((x + t : ℝ) : ℂ) by push_cast; ring, norm_re _ (by linarith [ht.1])]
      have : (-s - 2).re = -s.re - 2 := by simp
      rw [this]
      exact Real.rpow_le_rpow_of_nonpos hx (by linarith [ht.1]) (by linarith)
    have e3 : ‖-s - 1‖ = ‖s + 1‖ := by rw [show -s - 1 = -(s + 1) by ring, norm_neg]
    have e4 : ‖(t : ℂ) / 2‖ ≤ 1 / 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ht.1, Complex.norm_two]
      linarith [ht.2]
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_neg, e3]
    gcongr

def v (k : ℕ) (s : ℂ) : ℂ := ((k : ℂ) + 1) ^ (-s)
def W (k : ℕ) (s : ℂ) : ℂ := ((k : ℂ) + 1) ^ (1 - s)
def D (k : ℕ) (s : ℂ) : ℂ := v k s - 2 * v (k + 1) s + v (k + 2) s
def E (k : ℕ) (s : ℂ) : ℂ := (s - 1) / 2 * (v k s + v (k + 1) s) - (W k s - W (k + 1) s)

/- English proof (translation)
Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma cast1 (k : ℕ) : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
/- English proof (translation)
Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma cast2 (k : ℕ) : (((k + 1 : ℕ) : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) + 1 := by push_cast; ring
/- English proof (translation)
Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma cast3 (k : ℕ) : (((k + 2 : ℕ) : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) + 2 := by push_cast; ring

/- English proof (translation)
Use `second_difference_cpow_bound ((k : ℝ) + 1) (by positivity) s hs` as an intermediate fact. Unfold `D v`. Rewrite using `[cast1, cast2, cast3]`. Conclude with `this`.
-/
lemma D_bound (k : ℕ) (s : ℂ) (hs : -2 ≤ s.re) :
    ‖D k s‖ ≤ ‖s‖ * ‖s + 1‖ * (2 * ((k : ℝ) + 1) ^ (-s.re - 2)) := by
  have := second_difference_cpow_bound ((k : ℝ) + 1) (by positivity) s hs
  unfold D v
  rw [cast1, cast2, cast3]
  exact this

/- English proof (translation)
Use `trap_bound ((k : ℝ) + 1) (by positivity) s hs` as an intermediate fact. Unfold `E v W`. Rewrite using `[cast1, cast2]`. Conclude with `this`.
-/
lemma E_bound (k : ℕ) (s : ℂ) (hs : -2 ≤ s.re) :
    ‖E k s‖ ≤ 1 / 2 * (‖s - 1‖ * (‖s‖ * (‖s + 1‖ * ((k : ℝ) + 1) ^ (-s.re - 2)))) := by
  have := trap_bound ((k : ℝ) + 1) (by positivity) s hs
  unfold E v W
  rw [cast1, cast2]
  exact this

/- English proof (translation)
Unfold `v`. Rewrite using `[cast1, norm_re _ (by positivity)]`. Simplify using the standard rewrite rules.
-/
lemma nv (k : ℕ) (s : ℂ) : ‖v k s‖ = ((k : ℝ) + 1) ^ (-s.re) := by
  unfold v
  rw [cast1, norm_re _ (by positivity)]
  simp

/- English proof (translation)
Unfold `W`. Rewrite using `[cast1, norm_re _ (by positivity)]`. Simplify using the standard rewrite rules.
-/
lemma nW (k : ℕ) (s : ℂ) : ‖W k s‖ = ((k : ℝ) + 1) ^ (1 - s.re) := by
  unfold W
  rw [cast1, norm_re _ (by positivity)]
  simp

/- English proof (translation)
The claim follows from `((summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 hp)).congr fun k => by simp`.
-/
lemma sumr (p : ℝ) (hp : p < -1) : Summable fun k : ℕ => ((k : ℝ) + 1) ^ p :=
  ((summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 hp)).congr fun k => by simp

/- English proof (translation)
Establish `h2 : ‖s + 1‖ ≤ 1 + ‖s‖` using `by have := norm_add_le s 1; rw [norm_one] at this; linarith`. Establish `h0 : 0 ≤ ‖s‖` using `norm_nonneg _`. Use polynomial arithmetic with `[mul_le_mul h2 h2 (norm_nonneg _) (by linarith), mul_le_mul_of_nonneg_left h2 h0]`.
-/
lemma poly2 (s : ℂ) : ‖s‖ * ‖s + 1‖ ≤ (1 + ‖s‖) ^ 3 := by
  have h2 : ‖s + 1‖ ≤ 1 + ‖s‖ := by have := norm_add_le s 1; rw [norm_one] at this; linarith
  have h0 : 0 ≤ ‖s‖ := norm_nonneg _
  nlinarith [mul_le_mul h2 h2 (norm_nonneg _) (by linarith), mul_le_mul_of_nonneg_left h2 h0]

/- English proof (translation)
Establish `h1 : ‖s - 1‖ ≤ 1 + ‖s‖` using `by have := norm_sub_le s 1; rw [norm_one] at this; linarith`. Establish `h2 : ‖s + 1‖ ≤ 1 + ‖s‖` using `by have := norm_add_le s 1; rw [norm_one] at this; linarith`. Establish `h0 : 0 ≤ ‖s‖` using `norm_nonneg _`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul h1 _ (by positivity) (by positivity)` to reduce the goal to its premises.

Conclude with `mul_le_mul (by linarith) h2 (norm_nonneg _) (by positivity)`. Use `_ = _ := by ring`.
-/
lemma poly3 (s : ℂ) : ‖s - 1‖ * (‖s‖ * ‖s + 1‖) ≤ (1 + ‖s‖) ^ 3 := by
  have h1 : ‖s - 1‖ ≤ 1 + ‖s‖ := by have := norm_sub_le s 1; rw [norm_one] at this; linarith
  have h2 : ‖s + 1‖ ≤ 1 + ‖s‖ := by have := norm_add_le s 1; rw [norm_one] at this; linarith
  have h0 : 0 ≤ ‖s‖ := norm_nonneg _
  calc ‖s - 1‖ * (‖s‖ * ‖s + 1‖) ≤ (1 + ‖s‖) * ((1 + ‖s‖) * (1 + ‖s‖)) := by
        apply mul_le_mul h1 _ (by positivity) (by positivity)
        exact mul_le_mul (by linarith) h2 (norm_nonneg _) (by positivity)
    _ = _ := by ring

/- English proof (translation)
Establish `h` using `hs.hasSum.tendsto_sum_nat`. Simplify using `only [Finset.sum_range_sub'] at h`. Establish `h2 : Tendsto (fun n => F 0 - F n) atTop (𝓝 (F 0 - 0))` using `hF.const_sub _`. Rewrite `h2` using `[sub_zero]`. Conclude with `tendsto_nhds_unique h h2`.
-/
lemma tele (F : ℕ → ℂ) (hF : Tendsto F atTop (𝓝 0)) (hs : Summable fun n => F n - F (n + 1)) :
    ∑' n, (F n - F (n + 1)) = F 0 := by
  have h := hs.hasSum.tendsto_sum_nat
  simp only [Finset.sum_range_sub'] at h
  have h2 : Tendsto (fun n => F 0 - F n) atTop (𝓝 (F 0 - 0)) := hF.const_sub _
  rw [sub_zero] at h2
  exact tendsto_nhds_unique h h2

/- English proof (translation)
Establish `sm : ∀ (g u : ℕ → ℂ), (∀ n, ‖g n‖ ≤ B) → Summable (fun n => ‖u n‖) → Summable fun n => g n * u n`. Introduce `g u hg hu`. Use `Summable.of_norm_bounded (hu.mul_left B) (fun n => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hg n) (norm_nonneg _)`.

Establish `hw1 : Summable fun n => ‖w (n + 1)‖` using `(summable_nat_add_iff 1).2 hw`. Establish `s1` using `sm (fun n => A (n + 1)) w (fun n => hA _) hw`. Establish `s2` using `sm A w hA hw`. Establish `s3` using `sm (fun n => A (n + 1)) (fun n => w (n + 1)) (fun n => hA _) hw1`. Establish `e1 : ∑' n, A n * w n = ∑' n, A (n + 1) * w (n + 1)`.

Rewrite using `[s2.tsum_eq_zero_add, hA0, zero_mul, zero_add]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma abel (A w : ℕ → ℂ) (B : ℝ) (hA0 : A 0 = 0) (hA : ∀ n, ‖A n‖ ≤ B) (hw : Summable fun n => ‖w n‖) :
    ∑' n, (A (n + 1) - A n) * w n = ∑' n, A (n + 1) * (w n - w (n + 1)) := by
  have sm : ∀ (g u : ℕ → ℂ), (∀ n, ‖g n‖ ≤ B) → Summable (fun n => ‖u n‖) → Summable fun n => g n * u n := by
    intro g u hg hu
    refine Summable.of_norm_bounded (hu.mul_left B) (fun n => ?_)
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hg n) (norm_nonneg _)
  have hw1 : Summable fun n => ‖w (n + 1)‖ := (summable_nat_add_iff 1).2 hw
  have s1 := sm (fun n => A (n + 1)) w (fun n => hA _) hw
  have s2 := sm A w hA hw
  have s3 := sm (fun n => A (n + 1)) (fun n => w (n + 1)) (fun n => hA _) hw1
  have e1 : ∑' n, A n * w n = ∑' n, A (n + 1) * w (n + 1) := by
    rw [s2.tsum_eq_zero_add, hA0, zero_mul, zero_add]
  calc ∑' n, (A (n + 1) - A n) * w n = ∑' n, (A (n + 1) * w n - A n * w n) := by congr 1; ext n; ring
    _ = ∑' n, A (n + 1) * w n - ∑' n, A n * w n := s1.tsum_sub s2
    _ = ∑' n, A (n + 1) * w n - ∑' n, A (n + 1) * w (n + 1) := by rw [e1]
    _ = ∑' n, (A (n + 1) * w n - A (n + 1) * w (n + 1)) := (s1.tsum_sub s3).symm
    _ = _ := by congr 1; ext n; ring

/- English proof (translation)
Introduce `s₀ hs₀`. Establish `hs₀' : -1 < s₀.re` using `hs₀`. Set `U : Set ℂ` to `{s | (s₀.re - 1) / 2 < s.re} ∩ Metric.ball 0 (‖s₀‖ + 1)`. Establish `hU : IsOpen U` using `(isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball`. Establish `hmem : s₀ ∈ U` using `⟨by show (s₀.re - 1) / 2 < s₀.re; linarith, by rw [Metric.mem_ball, dist_zero_right]; linarith⟩`.

Establish `hd : DifferentiableOn ℂ (fun s => ∑' k, F k s) U`. Use `differentiableOn_tsum_of_summable_norm (u := fun k => A * (1 + (‖s₀‖ + 1)) ^ 3 * ((k : ℝ) + 1) ^ (-((s₀.re - 1) / 2) - 2)) ((sumr _ (by linarith)).mul_left _) (fun k => (hF k).differentiableOn) hU ?_` and prove the remaining obligations. Introduce `k s hs`. Establish `h1 : (s₀.re - 1) / 2 < s.re` using `hs.1`. Establish `h2 : ‖s‖ < ‖s₀‖ + 1`.

Use `hs.2` as an intermediate fact. Rewrite `this` using `[Metric.mem_ball, dist_zero_right]`. Conclude with `this`. Use `(hb k s (by linarith)).trans ?_` and prove the remaining obligations. Establish `h3 : ((k : ℝ) + 1) ^ (-s.re - 2) ≤ ((k : ℝ) + 1) ^ (-((s₀.re - 1) / 2) - 2)` using `Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]) (by linarith)`.

Establish `h4 : (1 + ‖s‖) ^ 3 ≤ (1 + (‖s₀‖ + 1)) ^ 3` using `by gcongr`. Use `gcongr`. Conclude with `(hd.differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt`.
-/
lemma diff_tsum (F : ℕ → ℂ → ℂ) (A : ℝ) (hA : 0 ≤ A) (hF : ∀ k, Differentiable ℂ (F k))
    (hb : ∀ k s, -1 < s.re → ‖F k s‖ ≤ A * (1 + ‖s‖) ^ 3 * ((k : ℝ) + 1) ^ (-s.re - 2)) :
    DifferentiableOn ℂ (fun s => ∑' k, F k s) (HP (-1)) := by
  intro s₀ hs₀
  have hs₀' : -1 < s₀.re := hs₀
  let U : Set ℂ := {s | (s₀.re - 1) / 2 < s.re} ∩ Metric.ball 0 (‖s₀‖ + 1)
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hmem : s₀ ∈ U := ⟨by show (s₀.re - 1) / 2 < s₀.re; linarith,
    by rw [Metric.mem_ball, dist_zero_right]; linarith⟩
  have hd : DifferentiableOn ℂ (fun s => ∑' k, F k s) U := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun k => A * (1 + (‖s₀‖ + 1)) ^ 3 * ((k : ℝ) + 1) ^ (-((s₀.re - 1) / 2) - 2))
      ((sumr _ (by linarith)).mul_left _) (fun k => (hF k).differentiableOn) hU ?_
    intro k s hs
    have h1 : (s₀.re - 1) / 2 < s.re := hs.1
    have h2 : ‖s‖ < ‖s₀‖ + 1 := by
      have := hs.2; rw [Metric.mem_ball, dist_zero_right] at this; exact this
    refine (hb k s (by linarith)).trans ?_
    have h3 : ((k : ℝ) + 1) ^ (-s.re - 2) ≤ ((k : ℝ) + 1) ^ (-((s₀.re - 1) / 2) - 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]) (by linarith)
    have h4 : (1 + ‖s‖) ^ 3 ≤ (1 + (‖s₀‖ + 1)) ^ 3 := by gcongr
    gcongr
  exact (hd.differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[← ih]`. Establish `h1 : ∑ j ∈ Finset.range (q + 1), f (n + j + 1) = ∑ j ∈ Finset.range q, f (n + j + 1) + f (n + q + 1)` using `Finset.sum_range_succ _ _`.

Establish `h2 : ∑ j ∈ Finset.range (q + 1), f (n + j + 1) = ∑ j ∈ Finset.range q, f (n + (j + 1) + 1) + f (n + 0 + 1)` using `Finset.sum_range_succ' _ _`. Establish `h3 : f (n + q + 1) = f (n + 0 + 1)`. Rewrite using `[add_zero, show n + q + 1 = (n + 1) + q by ring, hper]`. Establish `h4 : ∀ j, f (n + 1 + j + 1) = f (n + (j + 1) + 1)` using `fun j => by congr 1; ring`. Simplify using `only [h4]`.

Take the linear combination `h1 - h2 + h3`.
-/
lemma sum_shift (q : ℕ) (f : ℕ → ℂ) (hper : ∀ n, f (n + q) = f n) (n : ℕ) :
    ∑ j ∈ Finset.range q, f (n + j + 1) = ∑ j ∈ Finset.range q, f (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← ih]
    have h1 : ∑ j ∈ Finset.range (q + 1), f (n + j + 1) = ∑ j ∈ Finset.range q, f (n + j + 1) + f (n + q + 1) :=
      Finset.sum_range_succ _ _
    have h2 : ∑ j ∈ Finset.range (q + 1), f (n + j + 1) =
        ∑ j ∈ Finset.range q, f (n + (j + 1) + 1) + f (n + 0 + 1) := Finset.sum_range_succ' _ _
    have h3 : f (n + q + 1) = f (n + 0 + 1) := by
      rw [add_zero, show n + q + 1 = (n + 1) + q by ring, hper]
    have h4 : ∀ j, f (n + 1 + j + 1) = f (n + (j + 1) + 1) := fun j => by congr 1; ring
    simp only [h4]
    linear_combination h1 - h2 + h3

/- English proof (translation)
Establish `hq' : (q : ℂ) ≠ 0` using `by exact_mod_cast hq.ne'`. Establish `hB : 0 ≤ B` using `le_trans (norm_nonneg _) (hb 0)`. Establish `hsum : ∀ r : ℕ, ‖∑ j ∈ Finset.range r, f (j + 1)‖ ≤ B * r`. Introduce `r`. Proceed by induction on `r with`.

Consider the case `zero => simp`. Consider the case `succ r ih`. Rewrite using `[Finset.sum_range_succ]`. Use `push_cast`. Combine the linear relations using `[norm_add_le (∑ j ∈ Finset.range r, f (j + 1)) (f (r + 1)), hb (r + 1)]`.

Use `set m : ℂ := (∑ j ∈ Finset.range q, f (j + 1)) / q with hm`. Establish `hmB : ‖m‖ ≤ B`. Rewrite using `[hm, norm_div, Complex.norm_natCast, div_le_iff₀ (by exact_mod_cast hq)]`. Conclude with `hsum q`. Use `set P : ℕ → ℂ := fun n => ∑ j ∈ Finset.range n, (f (j + 1) - m) with hPdef`.

Establish `hz : ∀ n, ∑ j ∈ Finset.range q, (f (n + j + 1) - m) = 0`. Introduce `n`. Rewrite using `[Finset.sum_sub_distrib, sum_shift q f hper n, Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Establish `: (q : ℂ) * m = ∑ j ∈ Finset.range q, f (j + 1)` using `by rw [hm]; field_simp`. Rewrite using `[this, sub_self]`.

Establish `hPq : ∀ n, P (n + q) = P n`. Introduce `n`. Simplify using `only [hPdef, Finset.sum_range_add]`. Rewrite using `[add_eq_left]`. Simplify `hz n` using `only [add_assoc]`.

Establish `hPk : ∀ r k, P (r + q * k) = P r`. Introduce `r k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [show r + q * (k + 1) = (r + q * k) + q by ring, hPq, ih]`.

Establish `hPs : ∀ n, P (n + 1) = P n + (f (n + 1) - m)` using `fun n => Finset.sum_range_succ _ _`. Establish `hPr : ∀ r : ℕ, ‖P r‖ ≤ 2 * B * r`. Introduce `r`. Proceed by induction on `r with`. Consider the case `zero => simp [hPdef]`.

Consider the case `succ r ih`. Rewrite using `[hPs]`. Use `push_cast`. Establish `h1` using `norm_add_le (P r) (f (r + 1) - m)`. Establish `h2` using `norm_sub_le (f (r + 1)) m`.

Establish `h3` using `hb (r + 1)`. Use the polynomial consequences of the given equalities and inequalities. Use `⟨m, P, hmB, by simp [hPdef], hPs, hPq, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[← Nat.mod_add_div n q, hPk]`. Establish `: n % q ≤ q` using `(Nat.mod_lt n hq).le`.

Conclude with `(hPr _).trans (by gcongr)`.
-/
lemma prim (q : ℕ) (hq : 0 < q) (f : ℕ → ℂ) (B : ℝ) (hper : ∀ n, f (n + q) = f n) (hb : ∀ n, ‖f n‖ ≤ B) :
    ∃ (m : ℂ) (P : ℕ → ℂ), ‖m‖ ≤ B ∧ P 0 = 0 ∧ (∀ n, P (n + 1) = P n + (f (n + 1) - m)) ∧
      (∀ n, P (n + q) = P n) ∧ ∀ n, ‖P n‖ ≤ 2 * B * q := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (hb 0)
  have hsum : ∀ r : ℕ, ‖∑ j ∈ Finset.range r, f (j + 1)‖ ≤ B * r := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      rw [Finset.sum_range_succ]; push_cast
      linarith [norm_add_le (∑ j ∈ Finset.range r, f (j + 1)) (f (r + 1)), hb (r + 1)]
  set m : ℂ := (∑ j ∈ Finset.range q, f (j + 1)) / q with hm
  have hmB : ‖m‖ ≤ B := by
    rw [hm, norm_div, Complex.norm_natCast, div_le_iff₀ (by exact_mod_cast hq)]
    exact hsum q
  set P : ℕ → ℂ := fun n => ∑ j ∈ Finset.range n, (f (j + 1) - m) with hPdef
  have hz : ∀ n, ∑ j ∈ Finset.range q, (f (n + j + 1) - m) = 0 := by
    intro n
    rw [Finset.sum_sub_distrib, sum_shift q f hper n, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : (q : ℂ) * m = ∑ j ∈ Finset.range q, f (j + 1) := by rw [hm]; field_simp
    rw [this, sub_self]
  have hPq : ∀ n, P (n + q) = P n := by
    intro n
    simp only [hPdef, Finset.sum_range_add]
    rw [add_eq_left]
    simpa only [add_assoc] using hz n
  have hPk : ∀ r k, P (r + q * k) = P r := by
    intro r k
    induction k with
    | zero => simp
    | succ k ih => rw [show r + q * (k + 1) = (r + q * k) + q by ring, hPq, ih]
  have hPs : ∀ n, P (n + 1) = P n + (f (n + 1) - m) := fun n => Finset.sum_range_succ _ _
  have hPr : ∀ r : ℕ, ‖P r‖ ≤ 2 * B * r := by
    intro r
    induction r with
    | zero => simp [hPdef]
    | succ r ih =>
      rw [hPs]; push_cast
      have h1 := norm_add_le (P r) (f (r + 1) - m)
      have h2 := norm_sub_le (f (r + 1)) m
      have h3 := hb (r + 1)
      nlinarith
  refine ⟨m, P, hmB, by simp [hPdef], hPs, hPq, fun n => ?_⟩
  rw [← Nat.mod_add_div n q, hPk]
  have : n % q ≤ q := (Nat.mod_lt n hq).le
  exact (hPr _).trans (by gcongr)

/- English proof (translation)
The claim follows from `(sumr (-s.re) (by linarith)).congr (fun k => (nv k s).symm)`.
-/
lemma hv_sum (s : ℂ) (hs : 1 < s.re) : Summable fun k => ‖v k s‖ :=
  (sumr (-s.re) (by linarith)).congr (fun k => (nv k s).symm)

/- English proof (translation)
Establish `hv` using `hv_sum s hs`. Establish `hv'` using `hv.of_norm`. Establish `hv1 : Summable fun k => v (k + 1) s` using `(summable_nat_add_iff 1).2 hv'`. Establish `hE : Summable fun k => E k s`. Use `Summable.of_norm_bounded ((sumr (-s.re - 2) (by linarith)).mul_left (1 / 2 * (‖s - 1‖ * (‖s‖ * ‖s + 1‖)))) (fun k => ?_)` and prove the remaining obligations.

Use `(E_bound k s (by linarith)).trans (le_of_eq ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hvv : Summable fun k => (s - 1) / 2 * (v k s + v (k + 1) s)` using `(hv'.add hv1).mul_left _`. Establish `hWs : Summable fun k => W k s - W (k + 1) s` using `(hvv.sub hE).congr (fun k => by unfold E; ring)`. Establish `hWt : Tendsto (fun k => W k s) atTop (𝓝 0)`.

Rewrite using `[tendsto_zero_iff_norm_tendsto_zero]`. Simplify using `only [nW]`. Establish `h1 : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop` using `Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop`. Establish `h2 : (fun k : ℕ => ((k : ℝ) + 1) ^ (1 - s.re)) = (fun x : ℝ => x ^ (-(s.re - 1))) ∘ (fun k : ℕ => (k : ℝ) + 1)`. Use extensionality with `k`.

Simplify using `only [Function.comp_apply, neg_sub]`. Rewrite using `[h2]`. Conclude with `(tendsto_rpow_neg_atTop (by linarith)).comp h1`. Establish `e1 : ∑' k, (W k s - W (k + 1) s) = 1`. Rewrite using `[tele (fun k => W k s) hWt hWs]`.

Simplify using `[W]`. Establish `e2 : ∑' k, v k s = 1 + ∑' k, v (k + 1) s`. Rewrite using `[hv'.tsum_eq_zero_add]`. Simplify using `[v]`. Establish `e3 : ∑' k, E k s = (s - 1) / 2 * (∑' k, v k s + ∑' k, v (k + 1) s) - 1`.

Simplify using `only [E]`. Rewrite using `[hvv.tsum_sub hWs, tsum_mul_left, hv'.tsum_add hv1, e1]`. Rewrite using `[e3, e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma zeta_id (s : ℂ) (hs : 1 < s.re) : 1 + (s - 1) / 2 + ∑' k, E k s = (s - 1) * ∑' k, v k s := by
  have hv := hv_sum s hs
  have hv' := hv.of_norm
  have hv1 : Summable fun k => v (k + 1) s := (summable_nat_add_iff 1).2 hv'
  have hE : Summable fun k => E k s := by
    refine Summable.of_norm_bounded
      ((sumr (-s.re - 2) (by linarith)).mul_left (1 / 2 * (‖s - 1‖ * (‖s‖ * ‖s + 1‖)))) (fun k => ?_)
    refine (E_bound k s (by linarith)).trans (le_of_eq ?_)
    ring
  have hvv : Summable fun k => (s - 1) / 2 * (v k s + v (k + 1) s) := (hv'.add hv1).mul_left _
  have hWs : Summable fun k => W k s - W (k + 1) s :=
    (hvv.sub hE).congr (fun k => by unfold E; ring)
  have hWt : Tendsto (fun k => W k s) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [nW]
    have h1 : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h2 : (fun k : ℕ => ((k : ℝ) + 1) ^ (1 - s.re)) =
        (fun x : ℝ => x ^ (-(s.re - 1))) ∘ (fun k : ℕ => (k : ℝ) + 1) := by
      ext k; simp only [Function.comp_apply, neg_sub]
    rw [h2]
    exact (tendsto_rpow_neg_atTop (by linarith)).comp h1
  have e1 : ∑' k, (W k s - W (k + 1) s) = 1 := by
    rw [tele (fun k => W k s) hWt hWs]; simp [W]
  have e2 : ∑' k, v k s = 1 + ∑' k, v (k + 1) s := by
    rw [hv'.tsum_eq_zero_add]; simp [v]
  have e3 : ∑' k, E k s = (s - 1) / 2 * (∑' k, v k s + ∑' k, v (k + 1) s) - 1 := by
    simp only [E]
    rw [hvv.tsum_sub hWs, tsum_mul_left, hv'.tsum_add hv1, e1]
  rw [e3, e2]
  ring

/- English proof (translation)
Establish `hv` using `hv_sum s hs`. Establish `hv'` using `hv.of_norm`. Establish `hv1 : Summable fun k => v (k + 1) s` using `(summable_nat_add_iff 1).2 hv'`. Establish `hvn1 : Summable fun k => ‖v (k + 1) s‖` using `hv1.norm`. Establish `hdv : Summable fun k => ‖v k s - v (k + 1) s‖` using `Summable.of_nonneg_of_le (f := fun k => ‖v k s‖ + ‖v (k + 1) s‖) (fun _ => norm_nonneg _) (fun k => norm_sub_le (v k s) (v (k + 1) s)) (hv.add hvn1)`.

Establish `a1` using `abel S (fun k => v k s) B1 hS0 hSb hv`. Establish `a2` using `abel T (fun k => v k s - v (k + 1) s) B2 hT0 hTb hdv`. Establish `e1 : ∑' k, (Φ (k + 1) - m) * v k s = ∑' k, (S (k + 1) - S k) * v k s`. Use `congr 1`. Use extensionality with `k`.

Rewrite using `[hS k]`. Expand and normalize the polynomial expressions, which then agree. Establish `sA : Summable fun k => m₂ * (v k s - v (k + 1) s)` using `(hv'.sub hv1).mul_left _`. Establish `sB : Summable fun k => (T (k + 1) - T k) * (v k s - v (k + 1) s)`. Use `Summable.of_norm_bounded (hdv.mul_left (2 * B2)) (fun k => ?_)` and prove the remaining obligations.

Rewrite using `[norm_mul]`. Use `mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)` and prove the remaining obligations. Combine the linear relations using `[norm_sub_le (T (k + 1)) (T k), hTb (k + 1), hTb k]`. Establish `e2 : ∑' k, S (k + 1) * (v k s - v (k + 1) s) = ∑' k, (m₂ * (v k s - v (k + 1) s) + (T (k + 1) - T k) * (v k s - v (k + 1) s))`. Use `congr 1`.

Use extensionality with `k`. Rewrite using `[hT k]`. Expand and normalize the polynomial expressions, which then agree. Establish `e3 : ∑' k, (v k s - v (k + 1) s) = 1`. Rewrite using `[hv'.tsum_sub hv1, hv'.tsum_eq_zero_add]`.

Simplify using `[v]`. Rewrite using `[e1, a1, e2, sA.tsum_add sB, tsum_mul_left, e3, a2, mul_one]`. Use `congr 1`. Use `congr 1`. Use extensionality with `k`.

Simplify using `only [D, show k + 1 + 1 = k + 2 from rfl]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma per_id (Φ : ℕ → ℂ) (m m₂ : ℂ) (S T : ℕ → ℂ) (B1 B2 : ℝ) (hS0 : S 0 = 0)
    (hS : ∀ n, S (n + 1) = S n + (Φ (n + 1) - m)) (hT0 : T 0 = 0)
    (hT : ∀ n, T (n + 1) = T n + (S (n + 1) - m₂))
    (hSb : ∀ n, ‖S n‖ ≤ B1) (hTb : ∀ n, ‖T n‖ ≤ B2) (s : ℂ) (hs : 1 < s.re) :
    ∑' k, (Φ (k + 1) - m) * v k s = m₂ + ∑' k, T (k + 1) * D k s := by
  have hv := hv_sum s hs
  have hv' := hv.of_norm
  have hv1 : Summable fun k => v (k + 1) s := (summable_nat_add_iff 1).2 hv'
  have hvn1 : Summable fun k => ‖v (k + 1) s‖ := hv1.norm
  have hdv : Summable fun k => ‖v k s - v (k + 1) s‖ :=
    Summable.of_nonneg_of_le (f := fun k => ‖v k s‖ + ‖v (k + 1) s‖) (fun _ => norm_nonneg _)
      (fun k => norm_sub_le (v k s) (v (k + 1) s)) (hv.add hvn1)
  have a1 := abel S (fun k => v k s) B1 hS0 hSb hv
  have a2 := abel T (fun k => v k s - v (k + 1) s) B2 hT0 hTb hdv
  have e1 : ∑' k, (Φ (k + 1) - m) * v k s = ∑' k, (S (k + 1) - S k) * v k s := by
    congr 1; ext k; rw [hS k]; ring
  have sA : Summable fun k => m₂ * (v k s - v (k + 1) s) := (hv'.sub hv1).mul_left _
  have sB : Summable fun k => (T (k + 1) - T k) * (v k s - v (k + 1) s) := by
    refine Summable.of_norm_bounded (hdv.mul_left (2 * B2)) (fun k => ?_)
    rw [norm_mul]; refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    linarith [norm_sub_le (T (k + 1)) (T k), hTb (k + 1), hTb k]
  have e2 : ∑' k, S (k + 1) * (v k s - v (k + 1) s) =
      ∑' k, (m₂ * (v k s - v (k + 1) s) + (T (k + 1) - T k) * (v k s - v (k + 1) s)) := by
    congr 1; ext k; rw [hT k]; ring
  have e3 : ∑' k, (v k s - v (k + 1) s) = 1 := by
    rw [hv'.tsum_sub hv1, hv'.tsum_eq_zero_add]; simp [v]
  rw [e1, a1, e2, sA.tsum_add sB, tsum_mul_left, e3, a2, mul_one]
  congr 1; congr 1; ext k
  simp only [D, show k + 1 + 1 = k + 2 from rfl]
  ring

/- English proof (translation)
Establish `e : ∀ k : ℕ, LSeries.term Φ s (k + 1) = Φ (k + 1) * v k s`. Introduce `k`. Rewrite using `[LSeries.term_of_ne_zero (Nat.succ_ne_zero k), v, Complex.cpow_neg, div_eq_mul_inv]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `h1 : Summable fun n => LSeries.term Φ s n`. Rewrite using `[← summable_nat_add_iff 1]`. Simplify `h` using `only [e]`. Rewrite using `[LSeries, h1.tsum_eq_zero_add]`. Simplify using `only [LSeries.term_zero, zero_add, e]`.
-/
lemma lser_eq (Φ : ℕ → ℂ) (s : ℂ) (h : Summable fun k : ℕ => Φ (k + 1) * v k s) :
    LSeries Φ s = ∑' k, Φ (k + 1) * v k s := by
  have e : ∀ k : ℕ, LSeries.term Φ s (k + 1) = Φ (k + 1) * v k s := by
    intro k
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero k), v, Complex.cpow_neg, div_eq_mul_inv]
    push_cast; ring
  have h1 : Summable fun n => LSeries.term Φ s n := by
    rw [← summable_nat_add_iff 1]; simpa only [e] using h
  rw [LSeries, h1.tsum_eq_zero_add]
  simp only [LSeries.term_zero, zero_add, e]

/- English proof (translation)
Unfold `v`. Conclude with `differentiable_neg.const_cpow (Or.inl (Nat.cast_add_one_ne_zero k))`.
-/
lemma vdiff (k : ℕ) : Differentiable ℂ (fun s => v k s) := by
  unfold v
  exact differentiable_neg.const_cpow (Or.inl (Nat.cast_add_one_ne_zero k))

/- English proof (translation)
Unfold `W`. Conclude with `(differentiable_id.const_sub 1).const_cpow (Or.inl (Nat.cast_add_one_ne_zero k))`.
-/
lemma Wdiff (k : ℕ) : Differentiable ℂ (fun s => W k s) := by
  unfold W
  exact (differentiable_id.const_sub 1).const_cpow (Or.inl (Nat.cast_add_one_ne_zero k))

/- English proof (translation)
Unfold `D`. Conclude with `((vdiff k).sub ((vdiff (k + 1)).const_mul 2)).add (vdiff (k + 2))`.
-/
lemma Ddiff (k : ℕ) : Differentiable ℂ (fun s => D k s) := by
  unfold D
  exact ((vdiff k).sub ((vdiff (k + 1)).const_mul 2)).add (vdiff (k + 2))

/- English proof (translation)
Unfold `E`. Conclude with `(((differentiable_id.sub_const 1).div_const 2).mul ((vdiff k).add (vdiff (k + 1)))).sub ((Wdiff k).sub (Wdiff (k + 1)))`.
-/
lemma Ediff (k : ℕ) : Differentiable ℂ (fun s => E k s) := by
  unfold E
  exact (((differentiable_id.sub_const 1).div_const 2).mul ((vdiff k).add (vdiff (k + 1)))).sub
    ((Wdiff k).sub (Wdiff (k + 1)))

end PLB

/- English proof (translation)
Take `⟨K0, hK0⟩ : ∃ K0 : ℝ, HasSum (fun k : ℕ => ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ))) K0` from `⟨_, (PLB.sumr _ (by norm_num)).hasSum⟩`. Establish `hK0n : 0 ≤ K0` using `hK0.nonneg (fun k => by positivity)`. Use `⟨4 + 9 * K0, fun q Φ hq hper hb => ?_⟩` and prove the remaining obligations. Take `⟨m, S, hm, hS0, hS, hSper, hSb⟩` from `PLB.prim q hq Φ 1 hper hb`. Take `⟨m₂, T, hm₂, hT0, hT, -, hTb⟩` from `PLB.prim q hq S (2 * 1 * q) hSper hSb`.

Establish `hQ : (1 : ℝ) ≤ q` using `by exact_mod_cast hq`. Establish `hTb' : ∀ n, ‖T n‖ ≤ 4 * (q : ℝ) ^ 2` using `fun n => (hTb n).trans (le_of_eq (by ring))`. Establish `d1 : DifferentiableOn ℂ (fun s => ∑' k, T (k + 1) * PLB.D k s) (HP (-1))`. Use `PLB.diff_tsum _ (8 * (q : ℝ) ^ 2) (by positivity) (fun k => (PLB.Ddiff k).const_mul _) (fun k s hs => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Combine the equalities or inequalities in the displayed calculation. Establish `d2 : DifferentiableOn ℂ (fun s => ∑' k, PLB.E k s) (HP (-1))`. Use `PLB.diff_tsum _ (1 / 2) (by norm_num) PLB.Ediff (fun k s hs => ?_)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `⟨fun s => (s - 1) * (m₂ + ∑' k, T (k + 1) * PLB.D k s) + m * (1 + (s - 1) / 2 + ∑' k, PLB.E k s), ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `((differentiableOn_id.sub_const 1).mul (d1.const_add m₂)).add (((((differentiableOn_id.sub_const 1).div_const 2).const_add 1).add d2).const_mul m)`. Introduce `s hs`. Establish `hv` using `PLB.hv_sum s hs`. Establish `hΦv : Summable fun k => Φ (k + 1) * PLB.v k s`. Use `Summable.of_norm_bounded hv (fun k => ?_)` and prove the remaining obligations.

Rewrite using `[norm_mul]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (hb _)`. Establish `hmv : Summable fun k => (Φ (k + 1) - m) * PLB.v k s`. Use `Summable.of_norm_bounded (hv.mul_left 2) (fun k => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Use `mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)` and prove the remaining obligations. Combine the linear relations using `[norm_sub_le (Φ (k + 1)) m, hb (k + 1)]`. Establish `e : ∑' k, Φ (k + 1) * PLB.v k s = m * ∑' k, PLB.v k s + ∑' k, (Φ (k + 1) - m) * PLB.v k s`. Rewrite using `[← tsum_mul_left, ← (hv.of_norm.mul_left m).tsum_add hmv]`. Use `congr 1`.

Use extensionality with `k`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only`. Rewrite using `[PLB.lser_eq Φ s hΦv, e, PLB.per_id Φ m m₂ S T _ _ hS0 hS hT0 hT hSb hTb s hs, PLB.zeta_id s hs]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `s hs`. Establish `hR : 1 ≤ 1 + ‖s‖` using `by linarith [norm_nonneg s]`. Establish `hexp : ∀ k : ℕ, ((k : ℝ) + 1) ^ (-s.re - 2) ≤ ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ))` using `fun k => Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]) (by linarith)`. Establish `hX : ‖∑' k, T (k + 1) * PLB.D k s‖ ≤ 8 * (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 3 * K0`. Use `tsum_of_norm_bounded (hK0.mul_left (8 * (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 3)) (fun k => ?_)` and prove the remaining obligations.

Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Conclude with `mul_le_mul (PLB.poly2 s) (by linarith [hexp k]) (by positivity) (by positivity)`. Use `_ = _ := by ring`.

Establish `hY : ‖∑' k, PLB.E k s‖ ≤ 1 / 2 * (1 + ‖s‖) ^ 3 * K0`. Use `tsum_of_norm_bounded (hK0.mul_left (1 / 2 * (1 + ‖s‖) ^ 3)) (fun k => ?_)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul _ (hexp k) (by positivity) (by positivity)` to reduce the goal to its premises. Conclude with `mul_le_mul_of_nonneg_left (PLB.poly3 s) (by norm_num)`.

Establish `h1 : ‖s - 1‖ ≤ 1 + ‖s‖` using `by have := norm_sub_le s 1; rw [norm_one] at this; linarith`. Establish `h2 : ‖m₂ + ∑' k, T (k + 1) * PLB.D k s‖ ≤ 2 * q + 8 * (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 3 * K0`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Combine the linear relations using `[hm₂]`. Establish `h3 : ‖1 + (s - 1) / 2 + ∑' k, PLB.E k s‖ ≤ 1 + (1 + ‖s‖) / 2 + 1 / 2 * (1 + ‖s‖) ^ 3 * K0`.

Establish `e : ‖(s - 1) / 2‖ = ‖s - 1‖ / 2` using `by rw [norm_div, Complex.norm_two]`. Establish `t1` using `norm_add_le (1 + (s - 1) / 2) (∑' k, PLB.E k s)`. Establish `t2` using `norm_add_le (1 : ℂ) ((s - 1) / 2)`. Rewrite `t2` using `[norm_one, e]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `f1 : (q : ℝ) ≤ (q : ℝ) ^ 2` using `by nlinarith`. Establish `f2 : 1 + ‖s‖ ≤ (1 + ‖s‖) ^ 4` using `le_self_pow₀ hR (by norm_num)`. Establish `f3 : (1 + ‖s‖) ^ 3 ≤ (1 + ‖s‖) ^ 4` using `pow_le_pow_right₀ hR (by norm_num)`. Establish `f4 : (1 : ℝ) ≤ (q : ℝ) ^ 2` using `one_le_pow₀ hQ`. Establish `f5 : (1 : ℝ) ≤ (1 + ‖s‖) ^ 4` using `one_le_pow₀ hR`.

Establish `g1 : (q : ℝ) * (1 + ‖s‖) ≤ (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 4` using `mul_le_mul f1 f2 (by positivity) (by positivity)`. Establish `g2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 4` using `one_le_mul_of_one_le_of_one_le f4 f5`. Establish `g3 : 1 + ‖s‖ ≤ (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 4`. Combine the equalities or inequalities in the displayed calculation. Establish `g4 : (1 + ‖s‖) ^ 3 * K0 ≤ (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 4 * K0`.

Apply `mul_le_mul_of_nonneg_right _ hK0n` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `g5 : 0 ≤ (1 + ‖s‖) ^ 3 * K0` using `by positivity`. Use `show ‖(s - 1) * (m₂ + ∑' k, T (k + 1) * PLB.D k s) + m * (1 + (s - 1) / 2 + ∑' k, PLB.E k s)‖ ≤ _`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[norm_mul, norm_mul]`. Use `_ ≤ (1 + ‖s‖) * (2 * q + 8 * (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 3 * K0) + 1 * (1 + (1 + ‖s‖) / 2 + 1 / 2 * (1 + ‖s‖) ^ 3 * K0) := add_le_add (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) (mul_le_mul hm h3 (norm_nonneg _) zero_le_one)`. Use `_ ≤ (4 + 9 * K0) * (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 4 := by nlinarith`.
-/
theorem lB_of : LB := by
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℝ, HasSum (fun k : ℕ => ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ))) K0 :=
    ⟨_, (PLB.sumr _ (by norm_num)).hasSum⟩
  have hK0n : 0 ≤ K0 := hK0.nonneg (fun k => by positivity)
  refine ⟨4 + 9 * K0, fun q Φ hq hper hb => ?_⟩
  obtain ⟨m, S, hm, hS0, hS, hSper, hSb⟩ := PLB.prim q hq Φ 1 hper hb
  obtain ⟨m₂, T, hm₂, hT0, hT, -, hTb⟩ := PLB.prim q hq S (2 * 1 * q) hSper hSb
  have hQ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hTb' : ∀ n, ‖T n‖ ≤ 4 * (q : ℝ) ^ 2 := fun n => (hTb n).trans (le_of_eq (by ring))
  have d1 : DifferentiableOn ℂ (fun s => ∑' k, T (k + 1) * PLB.D k s) (HP (-1)) := by
    refine PLB.diff_tsum _ (8 * (q : ℝ) ^ 2) (by positivity) (fun k => (PLB.Ddiff k).const_mul _)
      (fun k s hs => ?_)
    rw [norm_mul]
    calc ‖T (k + 1)‖ * ‖PLB.D k s‖ ≤ (4 * (q : ℝ) ^ 2) * (‖s‖ * ‖s + 1‖ * (2 * ((k : ℝ) + 1) ^ (-s.re - 2))) :=
          mul_le_mul (hTb' _) (PLB.D_bound k s (by linarith)) (norm_nonneg _) (by positivity)
      _ ≤ (4 * (q : ℝ) ^ 2) * ((1 + ‖s‖) ^ 3 * (2 * ((k : ℝ) + 1) ^ (-s.re - 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (PLB.poly2 s) (by positivity)) (by positivity)
      _ = _ := by ring
  have d2 : DifferentiableOn ℂ (fun s => ∑' k, PLB.E k s) (HP (-1)) := by
    refine PLB.diff_tsum _ (1 / 2) (by norm_num) PLB.Ediff (fun k s hs => ?_)
    calc ‖PLB.E k s‖ ≤ 1 / 2 * (‖s - 1‖ * (‖s‖ * (‖s + 1‖ * ((k : ℝ) + 1) ^ (-s.re - 2)))) :=
          PLB.E_bound k s (by linarith)
      _ = 1 / 2 * (‖s - 1‖ * (‖s‖ * ‖s + 1‖)) * ((k : ℝ) + 1) ^ (-s.re - 2) := by ring
      _ ≤ 1 / 2 * (1 + ‖s‖) ^ 3 * ((k : ℝ) + 1) ^ (-s.re - 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (PLB.poly3 s) (by norm_num)) (by positivity)
  refine ⟨fun s => (s - 1) * (m₂ + ∑' k, T (k + 1) * PLB.D k s) + m * (1 + (s - 1) / 2 + ∑' k, PLB.E k s),
    ?_, ?_, ?_⟩
  · exact ((differentiableOn_id.sub_const 1).mul (d1.const_add m₂)).add
      (((((differentiableOn_id.sub_const 1).div_const 2).const_add 1).add d2).const_mul m)
  · intro s hs
    have hv := PLB.hv_sum s hs
    have hΦv : Summable fun k => Φ (k + 1) * PLB.v k s := by
      refine Summable.of_norm_bounded hv (fun k => ?_)
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hb _)
    have hmv : Summable fun k => (Φ (k + 1) - m) * PLB.v k s := by
      refine Summable.of_norm_bounded (hv.mul_left 2) (fun k => ?_)
      rw [norm_mul]; refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      linarith [norm_sub_le (Φ (k + 1)) m, hb (k + 1)]
    have e : ∑' k, Φ (k + 1) * PLB.v k s = m * ∑' k, PLB.v k s + ∑' k, (Φ (k + 1) - m) * PLB.v k s := by
      rw [← tsum_mul_left, ← (hv.of_norm.mul_left m).tsum_add hmv]
      congr 1; ext k; ring
    dsimp only
    rw [PLB.lser_eq Φ s hΦv, e, PLB.per_id Φ m m₂ S T _ _ hS0 hS hT0 hT hSb hTb s hs, PLB.zeta_id s hs]
    ring
  · intro s hs
    have hR : 1 ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
    have hexp : ∀ k : ℕ, ((k : ℝ) + 1) ^ (-s.re - 2) ≤ ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := fun k =>
      Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]) (by linarith)
    have hX : ‖∑' k, T (k + 1) * PLB.D k s‖ ≤ 8 * (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 3 * K0 := by
      refine tsum_of_norm_bounded (hK0.mul_left (8 * (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 3)) (fun k => ?_)
      rw [norm_mul]
      calc ‖T (k + 1)‖ * ‖PLB.D k s‖ ≤ (4 * (q : ℝ) ^ 2) * (‖s‖ * ‖s + 1‖ * (2 * ((k : ℝ) + 1) ^ (-s.re - 2))) :=
            mul_le_mul (hTb' _) (PLB.D_bound k s (by linarith)) (norm_nonneg _) (by positivity)
        _ ≤ (4 * (q : ℝ) ^ 2) * ((1 + ‖s‖) ^ 3 * (2 * ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul (PLB.poly2 s) (by linarith [hexp k]) (by positivity) (by positivity)
        _ = _ := by ring
    have hY : ‖∑' k, PLB.E k s‖ ≤ 1 / 2 * (1 + ‖s‖) ^ 3 * K0 := by
      refine tsum_of_norm_bounded (hK0.mul_left (1 / 2 * (1 + ‖s‖) ^ 3)) (fun k => ?_)
      calc ‖PLB.E k s‖ ≤ 1 / 2 * (‖s - 1‖ * (‖s‖ * (‖s + 1‖ * ((k : ℝ) + 1) ^ (-s.re - 2)))) :=
            PLB.E_bound k s (by linarith)
        _ = 1 / 2 * (‖s - 1‖ * (‖s‖ * ‖s + 1‖)) * ((k : ℝ) + 1) ^ (-s.re - 2) := by ring
        _ ≤ 1 / 2 * (1 + ‖s‖) ^ 3 * ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
            apply mul_le_mul _ (hexp k) (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left (PLB.poly3 s) (by norm_num)
    have h1 : ‖s - 1‖ ≤ 1 + ‖s‖ := by have := norm_sub_le s 1; rw [norm_one] at this; linarith
    have h2 : ‖m₂ + ∑' k, T (k + 1) * PLB.D k s‖ ≤ 2 * q + 8 * (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 3 * K0 := by
      refine (norm_add_le _ _).trans ?_
      linarith [hm₂]
    have h3 : ‖1 + (s - 1) / 2 + ∑' k, PLB.E k s‖ ≤ 1 + (1 + ‖s‖) / 2 + 1 / 2 * (1 + ‖s‖) ^ 3 * K0 := by
      have e : ‖(s - 1) / 2‖ = ‖s - 1‖ / 2 := by rw [norm_div, Complex.norm_two]
      have t1 := norm_add_le (1 + (s - 1) / 2) (∑' k, PLB.E k s)
      have t2 := norm_add_le (1 : ℂ) ((s - 1) / 2)
      rw [norm_one, e] at t2
      linarith
    have f1 : (q : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
    have f2 : 1 + ‖s‖ ≤ (1 + ‖s‖) ^ 4 := le_self_pow₀ hR (by norm_num)
    have f3 : (1 + ‖s‖) ^ 3 ≤ (1 + ‖s‖) ^ 4 := pow_le_pow_right₀ hR (by norm_num)
    have f4 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := one_le_pow₀ hQ
    have f5 : (1 : ℝ) ≤ (1 + ‖s‖) ^ 4 := one_le_pow₀ hR
    have g1 : (q : ℝ) * (1 + ‖s‖) ≤ (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 4 := mul_le_mul f1 f2 (by positivity) (by positivity)
    have g2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 4 := one_le_mul_of_one_le_of_one_le f4 f5
    have g3 : 1 + ‖s‖ ≤ (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 4 := by
      calc 1 + ‖s‖ = 1 * (1 + ‖s‖) := by ring
        _ ≤ _ := mul_le_mul f4 f2 (by positivity) (by positivity)
    have g4 : (1 + ‖s‖) ^ 3 * K0 ≤ (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 4 * K0 := by
      apply mul_le_mul_of_nonneg_right _ hK0n
      calc (1 + ‖s‖) ^ 3 = 1 * (1 + ‖s‖) ^ 3 := by ring
        _ ≤ _ := mul_le_mul f4 f3 (by positivity) (by positivity)
    have g5 : 0 ≤ (1 + ‖s‖) ^ 3 * K0 := by positivity
    show ‖(s - 1) * (m₂ + ∑' k, T (k + 1) * PLB.D k s) + m * (1 + (s - 1) / 2 + ∑' k, PLB.E k s)‖ ≤ _
    calc _ ≤ ‖(s - 1) * (m₂ + ∑' k, T (k + 1) * PLB.D k s)‖ + ‖m * (1 + (s - 1) / 2 + ∑' k, PLB.E k s)‖ :=
          norm_add_le _ _
      _ = ‖s - 1‖ * ‖m₂ + ∑' k, T (k + 1) * PLB.D k s‖ + ‖m‖ * ‖1 + (s - 1) / 2 + ∑' k, PLB.E k s‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ (1 + ‖s‖) * (2 * q + 8 * (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 3 * K0) +
          1 * (1 + (1 + ‖s‖) / 2 + 1 / 2 * (1 + ‖s‖) ^ 3 * K0) :=
          add_le_add (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) (mul_le_mul hm h3 (norm_nonneg _) zero_le_one)
      _ ≤ (4 + 9 * K0) * (q : ℝ) ^ 2 * (1 + ‖s‖) ^ 4 := by nlinarith

end Ad3.S

end
