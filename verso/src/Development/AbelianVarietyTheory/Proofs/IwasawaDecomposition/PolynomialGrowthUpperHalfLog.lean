import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UpperGrowth

open Complex
open scoped ComplexConjugate

noncomputable def qf (w : ℂ) : ℝ := (1 + ‖w‖ ^ 2) / w.im

/- English proof (translation)
Unfold `qf`. Check the signs of the components of the expression.
-/
theorem qf_nonneg {w : ℂ} (hw : 0 < w.im) : 0 ≤ qf w := by
  unfold qf; positivity

/- English proof (translation)
Unfold `qf`. Rewrite using `[le_div_iff₀ hw]`. Establish `h1` using `mul_le_mul_of_nonneg_left (Complex.im_le_norm w) (norm_nonneg w)`. Use polynomial arithmetic with `[norm_nonneg w, sq_nonneg (‖w‖ - 1)]`.
-/
theorem norm_le_qf {w : ℂ} (hw : 0 < w.im) : ‖w‖ ≤ qf w := by
  unfold qf
  rw [le_div_iff₀ hw]
  have h1 := mul_le_mul_of_nonneg_left (Complex.im_le_norm w) (norm_nonneg w)
  nlinarith [norm_nonneg w, sq_nonneg (‖w‖ - 1)]

/- English proof (translation)
Establish `e : u - conj v = (u - v) + (v - conj v)` using `by ring`. Rewrite using `[e]`. Use `(norm_add_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Complex.sub_conj, norm_mul, Complex.norm_I, _root_.mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]`.
-/
theorem norm_sub_conj_le (u v : ℂ) (hv : 0 < v.im) : ‖u - conj v‖ ≤ ‖u - v‖ + 2 * v.im := by
  have e : u - conj v = (u - v) + (v - conj v) := by ring
  rw [e]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [Complex.sub_conj, norm_mul, Complex.norm_I, _root_.mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith)]

/- English proof (translation)
Use `set d := ‖u - v‖ with hd`. Use `set K := 2 / (1 - r) with hK`. Establish `h1r : 0 < 1 - r` using `by linarith`. Establish `hK1 : K - 1 = (1 + r) / (1 - r)` using `by rw [hK]; field_simp; ring`. Establish `hKge : 1 ≤ K` using `by rw [hK, le_div_iff₀ h1r]; linarith`.

Establish `e1` using `norm_sub_conj_le u v hv`. Establish `e2 : ‖u - conj v‖ ≤ d + 2 * u.im`. Establish `: u - conj v = -conj (v - conj u)` using `by simp`. Rewrite using `[this, norm_neg, Complex.norm_conj]`. Establish `h'` using `norm_sub_conj_le v u hu`.

Rewrite `h'` using `[norm_sub_rev v u, ← hd]`. Then use the resulting hypothesis. Establish `hdv : d ≤ (K - 1) * v.im`. Rewrite using `[hK1, div_mul_eq_mul_div, le_div_iff₀ h1r]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left e1 hr0]`. Establish `hdu : d ≤ (K - 1) * u.im`.

Rewrite using `[hK1, div_mul_eq_mul_div, le_div_iff₀ h1r]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left e2 hr0]`. Establish `him : v.im ≤ K * u.im`. Establish `: v.im - u.im ≤ d`. Use `Complex.im_le_norm (v - u)` as an intermediate fact.

Rewrite `this` using `[norm_sub_rev]`. Simplify using `using this`. Use the polynomial consequences of the given equalities and inequalities. Establish `hn : ‖u‖ ≤ K * ‖v‖`. Establish `h1 : ‖u‖ ≤ ‖v‖ + d`.

Use `norm_add_le v (u - v)` as an intermediate fact. Simplify using `using this`. Establish `h2` using `mul_le_mul_of_nonneg_left (Complex.im_le_norm v) (by linarith : 0 ≤ K - 1)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hsq : 1 + ‖u‖ ^ 2 ≤ K ^ 2 * (1 + ‖v‖ ^ 2)`.

Establish `: ‖u‖ ^ 2 ≤ (K * ‖v‖) ^ 2` using `pow_le_pow_left₀ (norm_nonneg _) hn 2`. Use polynomial arithmetic with `[sq_nonneg K, sq_nonneg ‖v‖]`. Establish `hprod : (1 + ‖u‖ ^ 2) * v.im ≤ (K ^ 2 * (1 + ‖v‖ ^ 2)) * (K * u.im)` using `mul_le_mul hsq him hv.le (by positivity)`. Unfold `qf`. Rewrite using `[div_le_iff₀ hu, ← mul_div_assoc, div_mul_eq_mul_div, le_div_iff₀ hv]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem qf_le {u v : ℂ} {r : ℝ} (hu : 0 < u.im) (hv : 0 < v.im) (hr0 : 0 ≤ r) (hr : r < 1)
    (h : ‖u - v‖ ≤ r * ‖u - conj v‖) : qf u ≤ (2 / (1 - r)) ^ 3 * qf v := by
  set d := ‖u - v‖ with hd
  set K := 2 / (1 - r) with hK
  have h1r : 0 < 1 - r := by linarith
  have hK1 : K - 1 = (1 + r) / (1 - r) := by rw [hK]; field_simp; ring
  have hKge : 1 ≤ K := by rw [hK, le_div_iff₀ h1r]; linarith
  have e1 := norm_sub_conj_le u v hv
  have e2 : ‖u - conj v‖ ≤ d + 2 * u.im := by
    have : u - conj v = -conj (v - conj u) := by simp
    rw [this, norm_neg, Complex.norm_conj]
    have h' := norm_sub_conj_le v u hu
    rwa [norm_sub_rev v u, ← hd] at h'
  have hdv : d ≤ (K - 1) * v.im := by
    rw [hK1, div_mul_eq_mul_div, le_div_iff₀ h1r]
    nlinarith [mul_le_mul_of_nonneg_left e1 hr0]
  have hdu : d ≤ (K - 1) * u.im := by
    rw [hK1, div_mul_eq_mul_div, le_div_iff₀ h1r]
    nlinarith [mul_le_mul_of_nonneg_left e2 hr0]
  have him : v.im ≤ K * u.im := by
    have : v.im - u.im ≤ d := by
      have := Complex.im_le_norm (v - u)
      rw [norm_sub_rev] at this
      simpa using this
    nlinarith
  have hn : ‖u‖ ≤ K * ‖v‖ := by
    have h1 : ‖u‖ ≤ ‖v‖ + d := by
      have := norm_add_le v (u - v)
      simpa using this
    have h2 := mul_le_mul_of_nonneg_left (Complex.im_le_norm v) (by linarith : 0 ≤ K - 1)
    nlinarith
  have hsq : 1 + ‖u‖ ^ 2 ≤ K ^ 2 * (1 + ‖v‖ ^ 2) := by
    have : ‖u‖ ^ 2 ≤ (K * ‖v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg K, sq_nonneg ‖v‖]
  have hprod : (1 + ‖u‖ ^ 2) * v.im ≤ (K ^ 2 * (1 + ‖v‖ ^ 2)) * (K * u.im) :=
    mul_le_mul hsq him hv.le (by positivity)
  unfold qf
  rw [div_le_iff₀ hu, ← mul_div_assoc, div_mul_eq_mul_div, le_div_iff₀ hv]
  nlinarith

end GlobalTheory.UpperGrowth

namespace GlobalTheory.UpperGrowth

open Complex
open scoped ComplexConjugate

/- English proof (translation)
Establish `h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1` using `Metric.mem_ball_self one_pos`. Establish `hζb : ζ ∈ Metric.ball (0 : ℂ) 1` using `mem_ball_zero_iff.mpr hζ`. Use `set c := f 0 with hcdef`. Establish `hc : 0 < c.im` using `hpos 0 h0`. Establish `hne : ∀ z ∈ Metric.ball (0 : ℂ) 1, f z - conj c ≠ 0`.

Introduce `z hz h`. Use `congrArg Complex.im h` as an intermediate fact. Simplify using `at this`. Combine the linear relations using `[hpos z hz]`. Establish `hle : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z - c‖ ≤ ‖f z - conj c‖`.

Introduce `z hz`. Establish `hz'` using `hpos z hz`. Use `(pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_` and prove the remaining obligations. Rewrite using `[Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]`. Simplify using the standard rewrite rules.

Use polynomial arithmetic with `[mul_pos hz' hc]`. Use `set g : ℂ → ℂ := fun z => (f z - c) / (f z - conj c) with hg`. Establish `hdg : DifferentiableOn ℂ g (Metric.ball 0 1)` using `(hd.sub_const c).div (hd.sub_const _) hne`. Establish `hmaps : Set.MapsTo g (Metric.ball 0 1) (Metric.closedBall 0 1)`. Introduce `z hz`.

Rewrite using `[mem_closedBall_zero_iff, hg, norm_div]`. Conclude with `div_le_one_of_le₀ (hle z hz) (norm_nonneg _)`. Establish `hg0 : g 0 = 0` using `by simp [hg, hcdef]`. Establish `key` using `Complex.norm_le_norm_of_mapsTo_ball hdg hmaps hg0 hζ`. Establish `key' : ‖f ζ - c‖ ≤ ‖ζ‖ * ‖f ζ - conj c‖`.

Rewrite `key` using `[hg, norm_div, div_le_iff₀ (norm_pos_iff.mpr (hne ζ hζb))]`. Conclude with `key`. Conclude with `qf_le (hpos ζ hζb) hc (norm_nonneg _) hζ key'`.
-/
theorem qf_ball {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hpos : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 < (f z).im) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    qf (f ζ) ≤ (2 / (1 - ‖ζ‖)) ^ 3 * qf (f 0) := by
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self one_pos
  have hζb : ζ ∈ Metric.ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hζ
  set c := f 0 with hcdef
  have hc : 0 < c.im := hpos 0 h0
  have hne : ∀ z ∈ Metric.ball (0 : ℂ) 1, f z - conj c ≠ 0 := by
    intro z hz h
    have := congrArg Complex.im h
    simp at this
    linarith [hpos z hz]
  have hle : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z - c‖ ≤ ‖f z - conj c‖ := by
    intro z hz
    have hz' := hpos z hz
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp
    nlinarith [mul_pos hz' hc]
  set g : ℂ → ℂ := fun z => (f z - c) / (f z - conj c) with hg
  have hdg : DifferentiableOn ℂ g (Metric.ball 0 1) :=
    (hd.sub_const c).div (hd.sub_const _) hne
  have hmaps : Set.MapsTo g (Metric.ball 0 1) (Metric.closedBall 0 1) := by
    intro z hz
    rw [mem_closedBall_zero_iff, hg, norm_div]
    exact div_le_one_of_le₀ (hle z hz) (norm_nonneg _)
  have hg0 : g 0 = 0 := by simp [hg, hcdef]
  have key := Complex.norm_le_norm_of_mapsTo_ball hdg hmaps hg0 hζ
  have key' : ‖f ζ - c‖ ≤ ‖ζ‖ * ‖f ζ - conj c‖ := by
    rw [hg, norm_div, div_le_iff₀ (norm_pos_iff.mpr (hne ζ hζb))] at key
    exact key
  exact qf_le (hpos ζ hζb) hc (norm_nonneg _) hζ key'

/- English proof (translation)
Use `(qf_ball hd hpos hζ).trans (mul_le_mul_of_nonneg_right ?_ (qf_nonneg (hpos 0 (Metric.mem_ball_self one_pos))))` and prove the remaining obligations. Establish `: 0 ≤ 2 / (1 - ‖ζ‖)` using `div_nonneg (by norm_num) (by linarith)`. Conclude with `pow_le_pow_left₀ this hM 3`.
-/
theorem qf_ball_le {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hpos : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 < (f z).im) {ζ : ℂ} (hζ : ‖ζ‖ < 1) {M : ℝ}
    (hM : 2 / (1 - ‖ζ‖) ≤ M) : qf (f ζ) ≤ M ^ 3 * qf (f 0) := by
  refine (qf_ball hd hpos hζ).trans (mul_le_mul_of_nonneg_right ?_ (qf_nonneg (hpos 0 (Metric.mem_ball_self one_pos))))
  have : 0 ≤ 2 / (1 - ‖ζ‖) := div_nonneg (by norm_num) (by linarith)
  exact pow_le_pow_left₀ this hM 3

noncomputable def cay (ζ : ℂ) : ℂ := (ζ - 1) / (ζ + 1)

/- English proof (translation)
Introduce `h`. Establish `: ζ = -1` using `by linear_combination h`. Simplify using `[this] at hζ`.
-/
theorem cay_ne {ζ : ℂ} (hζ : ζ ∈ Metric.ball (0 : ℂ) 1) : ζ + 1 ≠ 0 := by
  intro h
  have : ζ = -1 := by linear_combination h
  simp [this] at hζ

/- English proof (translation)
Establish `h1` using `cay_ne hζ`. Establish `hn : 0 < Complex.normSq (ζ + 1)` using `Complex.normSq_pos.mpr h1`. Establish `hζ' : ζ.re ^ 2 + ζ.im ^ 2 < 1`. Establish `h2 : ‖ζ‖ < 1` using `by simpa using hζ`. Establish `h3 : ‖ζ‖ ^ 2 < 1` using `by nlinarith [norm_nonneg ζ]`.

Rewrite `h3` using `[Complex.sq_norm, Complex.normSq_apply]`. Use the polynomial consequences of the given equalities and inequalities. Unfold `cay`. Rewrite using `[Complex.div_re, ← add_div, div_lt_iff₀ hn, Complex.normSq_apply]`. Simplify using the standard rewrite rules.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem cay_re {ζ : ℂ} (hζ : ζ ∈ Metric.ball (0 : ℂ) 1) : (cay ζ).re < 0 := by
  have h1 := cay_ne hζ
  have hn : 0 < Complex.normSq (ζ + 1) := Complex.normSq_pos.mpr h1
  have hζ' : ζ.re ^ 2 + ζ.im ^ 2 < 1 := by
    have h2 : ‖ζ‖ < 1 := by simpa using hζ
    have h3 : ‖ζ‖ ^ 2 < 1 := by nlinarith [norm_nonneg ζ]
    rw [Complex.sq_norm, Complex.normSq_apply] at h3
    nlinarith
  unfold cay
  rw [Complex.div_re, ← add_div, div_lt_iff₀ hn, Complex.normSq_apply]
  simp
  nlinarith

/- English proof (translation)
The claim follows from `DifferentiableOn.div (by fun_prop) (by fun_prop) fun _ h => cay_ne h`.
-/
theorem cay_diff : DifferentiableOn ℂ cay (Metric.ball 0 1) :=
  DifferentiableOn.div (by fun_prop) (by fun_prop) fun _ h => cay_ne h

/- English proof (translation)
Simplify using `[cay]`.
-/
theorem cay_zero : cay 0 = -1 := by simp [cay]

/- English proof (translation)
Establish `h : 1 - z ≠ 0`. Introduce `e`. Use `congrArg Complex.re e` as an intermediate fact. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Unfold `cay`. Establish `h2 : (1 + z) / (1 - z) + 1 = 2 / (1 - z)` using `by field_simp; ring`. Rewrite using `[h2]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cay_inv {z : ℂ} (hz : z.re < 0) : cay ((1 + z) / (1 - z)) = z := by
  have h : 1 - z ≠ 0 := by
    intro e; have := congrArg Complex.re e; simp at this; linarith
  unfold cay
  have h2 : (1 + z) / (1 - z) + 1 = 2 / (1 - z) := by field_simp; ring
  rw [h2]
  field_simp
  ring

/- English proof (translation)
Use `set A := ‖1 + z‖ with hA`. Use `set B := ‖1 - z‖ with hB`. Establish `hAB : B ^ 2 - A ^ 2 = -4 * z.re`. Rewrite using `[hA, hB, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Establish `hA0 : 0 ≤ A` using `norm_nonneg _`. Establish `hB0 : 0 < B`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Establish `h0 : B = 0` using `le_antisymm hc (norm_nonneg _)`. Rewrite `hAB` using `[h0]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hlt : A < B` using `by nlinarith`. Establish `hBz : B ≤ 1 + ‖z‖`.

Rewrite using `[hB]; exact (norm_sub_le _ _).trans (by simp)`. Establish `hq : ‖(1 + z) / (1 - z)‖ = A / B` using `by rw [norm_div]`. Rewrite using `[hq]`. Establish `hlt1 : A / B < 1` using `(div_lt_one hB0).mpr hlt`. Use `⟨hlt1, ?_⟩` and prove the remaining obligations.

Establish `e : 1 - A / B = (B - A) / B` using `by field_simp`. Rewrite using `[e, div_div_eq_mul_div, div_le_iff₀ (by linarith)]`. Establish `h1 : 1 ≤ 2 * B * (B - A)` using `by nlinarith`. Establish `h2 : B ^ 2 ≤ (1 + ‖z‖) ^ 2` using `pow_le_pow_left₀ hB0.le hBz 2`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right h2 (by linarith : (0:ℝ) ≤ B - A)]`.
-/
theorem cay_bound {z : ℂ} (hz : z.re ≤ -1 / 2) :
    ‖(1 + z) / (1 - z)‖ < 1 ∧ 2 / (1 - ‖(1 + z) / (1 - z)‖) ≤ 4 * (1 + ‖z‖) ^ 2 := by
  set A := ‖1 + z‖ with hA
  set B := ‖1 - z‖ with hB
  have hAB : B ^ 2 - A ^ 2 = -4 * z.re := by
    rw [hA, hB, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp; ring
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 < B := by
    by_contra hc
    push_neg at hc
    have h0 : B = 0 := le_antisymm hc (norm_nonneg _)
    rw [h0] at hAB
    nlinarith
  have hlt : A < B := by nlinarith
  have hBz : B ≤ 1 + ‖z‖ := by
    rw [hB]; exact (norm_sub_le _ _).trans (by simp)
  have hq : ‖(1 + z) / (1 - z)‖ = A / B := by rw [norm_div]
  rw [hq]
  have hlt1 : A / B < 1 := (div_lt_one hB0).mpr hlt
  refine ⟨hlt1, ?_⟩
  have e : 1 - A / B = (B - A) / B := by field_simp
  rw [e, div_div_eq_mul_div, div_le_iff₀ (by linarith)]
  have h1 : 1 ≤ 2 * B * (B - A) := by nlinarith
  have h2 : B ^ 2 ≤ (1 + ‖z‖) ^ 2 := pow_le_pow_left₀ hB0.le hBz 2
  nlinarith [mul_le_mul_of_nonneg_right h2 (by linarith : (0:ℝ) ≤ B - A)]

/- English proof (translation)
Rewrite `h` using `[Complex.norm_exp]`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h1` using `Real.exp_lt_exp.mpr hc`. Establish `h2` using `Real.add_one_le_exp (-1 / 2 : ℝ)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem re_le_of_exp {z : ℂ} (h : ‖Complex.exp z‖ ≤ 1 / 2) : z.re ≤ -1 / 2 := by
  rw [Complex.norm_exp] at h
  by_contra hc
  push_neg at hc
  have h1 := Real.exp_lt_exp.mpr hc
  have h2 := Real.add_one_le_exp (-1 / 2 : ℝ)
  linarith

end GlobalTheory.UpperGrowth

namespace GlobalTheory.UpperGrowth

open Complex

/- English proof (translation)
Simplify using `only [logDom, Set.mem_setOf_eq] at hp ⊢`. Introduce `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `using hz`.

Rewrite using `[Function.update_of_ne hk]`. Conclude with `hp k`.
-/
theorem upd_mem {n a : ℕ} {p : Fin n → ℂ} (hp : p ∈ logDom n a) (i : Fin n) {z : ℂ}
    (hz : if (i : ℕ) < a then z.re < 0 else ‖z‖ < 1) : Function.update p i z ∈ logDom n a := by
  simp only [logDom, Set.mem_setOf_eq] at hp ⊢
  intro k
  by_cases hk : k = i
  · subst hk; simpa using hz
  · rw [Function.update_of_ne hk]; exact hp k

/- English proof (translation)
The claim follows from `hF.comp (fun z _ => (hasFDerivAt_update p z).differentiableAt.differentiableWithinAt) (fun z hz => upd_mem hp i (hD z hz))`.
-/
theorem upd_diff {n a : ℕ} {F : (Fin n → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (logDom n a))
    {p : Fin n → ℂ} (hp : p ∈ logDom n a) (i : Fin n) {D : Set ℂ}
    (hD : ∀ z ∈ D, if (i : ℕ) < a then z.re < 0 else ‖z‖ < 1) :
    DifferentiableOn ℂ (fun z => F (Function.update p i z)) D :=
  hF.comp (fun z _ => (hasFDerivAt_update p z).differentiableAt.differentiableWithinAt)
    (fun z hz => upd_mem hp i (hD z hz))

end GlobalTheory.UpperGrowth

namespace GlobalTheory

open GlobalTheory.UpperGrowth in

/- English proof (translation)
Introduce `n a F hF hpos`. Use `set s₀ : Fin n → ℂ := fun k => if (k : ℕ) < a then -1 else 0 with hs₀`. Use `⟨64 ^ n * qf (F s₀), 6 * n, fun s hs hse _ => ?_⟩` and prove the remaining obligations. Use `set P : ℕ → Fin n → ℂ := fun j k => if (k : ℕ) < j then s k else s₀ k with hP`. Establish `hs' : ∀ k : Fin n, if (k : ℕ) < a then (s k).re < 0 else ‖s k‖ < 1`.

Simplify `hs` using `[logDom]`. Establish `hs₀' : ∀ k : Fin n, if (k : ℕ) < a then (s₀ k).re < 0 else ‖s₀ k‖ < 1`. Apply the tactic sequence `intro k; simp only [hs₀]; split_ifs <;> norm_num`. Establish `hs₀mem : s₀ ∈ logDom n a` using `by simpa [logDom] using hs₀'`. Establish `hPmem : ∀ j, P j ∈ logDom n a`.

Introduce `j`. Simplify using `only [logDom, Set.mem_setOf_eq]`. Introduce `k`. Distinguish the cases in `hk : (k : ℕ) < j`. Establish `e : P j k = s k` using `if_pos hk`.

Rewrite using `[e]`. Conclude with `hs' k`. Establish `e : P j k = s₀ k` using `if_neg hk`. Rewrite using `[e]`. Conclude with `hs₀' k`.

Establish `hco : ∀ k : Fin n, ‖logExp a s k‖ ≤ 1 / 2` using `fun k => (norm_le_pi_norm (logExp a s) k).trans hse`. Establish `hsk : ∀ k : Fin n, ‖s k‖ ≤ ‖s‖` using `fun k => norm_le_pi_norm s k`. Use `set M : ℝ := 4 * (1 + ‖s‖) ^ 2 with hMdef`. Establish `hM1 : 1 ≤ M`. Establish `: 1 ≤ (1 + ‖s‖) ^ 2` using `one_le_pow₀ (by linarith [norm_nonneg s])`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `step : ∀ j, qf (F (P (j + 1))) ≤ M ^ 3 * qf (F (P j))`. Introduce `j`. Distinguish the cases in `hj : j < n`. Use `set i : Fin n := ⟨j, hj⟩ with hi`.

Establish `hPi : P (j + 1) = Function.update (P j) i (s i)`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i`. Rewrite using `[hk, Function.update_self]`. Conclude with `if_pos (show (i : ℕ) < j + 1 by simp [hi])`.

Rewrite using `[Function.update_of_ne hk]`. Establish `hkj : (k : ℕ) ≠ j` using `fun h => hk (Fin.ext h)`. Establish `e : ((k : ℕ) < j + 1 ↔ (k : ℕ) < j)` using `by omega`. Simplify using `only [hP, e]`. Establish `hPj : Function.update (P j) i (s₀ i) = P j`.

Rewrite using `[Function.update_eq_self_iff]`. Establish `hn : ¬ ((i : ℕ) < j)` using `by simp [hi]`. Conclude with `(if_neg hn).symm`. Distinguish the cases in `ha : j < a`. Establish `hai : (i : ℕ) < a` using `ha`.

Establish `hre : (s i).re ≤ -1 / 2`. Apply `re_le_of_exp` to reduce the goal to its premises. Use `hco i` as an intermediate fact. Simplify `this` using `[logExp, hai]`. Take `⟨hζ, hMb⟩` from `cay_bound hre`.

Establish `hdf : DifferentiableOn ℂ (fun ζ => F (Function.update (P j) i (cay ζ))) (Metric.ball 0 1)` using `(upd_diff hF (hPmem j) i (D := {z | z.re < 0}) (fun z hz => by simpa [hai] using hz)).comp cay_diff (fun ζ hζ => cay_re hζ)`. Establish `hposf : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 < (F (Function.update (P j) i (cay z))).im` using `fun z hz => hpos _ (upd_mem (hPmem j) i (by simpa [hai] using cay_re hz))`. Establish `key` using `qf_ball_le hdf hposf hζ (M := M) (hMb.trans (by rw [hMdef]; gcongr; exact hsk i))`. Establish `hsi : (s i).re < 0` using `by simpa [hai] using hs' i`. Establish `e0 : s₀ i = -1` using `by simp [hs₀, hai]`.

Simplify using `only [cay_inv hsi, cay_zero] at key`. Rewrite `key` using `[← e0, hPj]`. Rewrite using `[hPi]`. Conclude with `key`. Establish `hai : ¬ (i : ℕ) < a` using `ha`.

Establish `hle : ‖s i‖ ≤ 1 / 2`. Use `hco i` as an intermediate fact. Simplify `this` using `[logExp, hai]`. Establish `hζ : ‖s i‖ < 1` using `by linarith`. Establish `hdf : DifferentiableOn ℂ (fun ζ => F (Function.update (P j) i ζ)) (Metric.ball 0 1)` using `upd_diff hF (hPmem j) i (fun z hz => by simpa [hai] using hz)`.

Establish `hposf : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 < (F (Function.update (P j) i z)).im` using `fun z hz => hpos _ (upd_mem (hPmem j) i (by simpa [hai] using hz))`. Establish `hMb : 2 / (1 - ‖s i‖) ≤ M`. Rewrite using `[div_le_iff₀ (by linarith)]`. Establish `: 1 ≤ (1 + ‖s‖) ^ 2` using `one_le_pow₀ (by linarith [norm_nonneg s])`. Use the polynomial consequences of the given equalities and inequalities.

Establish `key` using `qf_ball_le hdf hposf hζ hMb`. Establish `e0 : s₀ i = 0` using `by simp [hs₀, hai]`. Rewrite `key` using `[← e0, hPj, ← hPi]`. Conclude with `key`. Establish `e : P (j + 1) = P j`.

Use function extensionality and compare the values at `k`. Establish `e : ((k : ℕ) < j + 1 ↔ (k : ℕ) < j)` using `by have := k.isLt; omega`. Simplify using `only [hP, e]`. Rewrite using `[e]`. Establish `h0` using `qf_nonneg (hpos _ (hPmem j))`.

Establish `: 1 ≤ M ^ 3` using `one_le_pow₀ hM1`. Use the polynomial consequences of the given equalities and inequalities. Establish `hind : ∀ j, qf (F (P j)) ≤ (M ^ 3) ^ j * qf (F s₀)`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero`. Establish `e : P 0 = s₀` using `by funext k; simp [hP]`. Simplify using `[e]`. Consider the case `succ j ih`. Establish `: 0 ≤ M ^ 3` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation. Establish `hPn : P n = s` using `by funext k; simp [hP, k.isLt]`. Establish `hfin` using `hind n`. Rewrite `hfin` using `[hPn]`. Use `(norm_le_qf (hpos s hs)).trans (hfin.trans (le_of_eq ?_))` and prove the remaining obligations.

Establish `e : M ^ 3 = 64 * (1 + ‖s‖) ^ 6` using `by rw [hMdef]; ring`. Rewrite using `[e, mul_pow, pow_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem upper_half_growth : ∀ (n a : ℕ) (F : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ F (logDom n a) →
    (∀ s ∈ logDom n a, 0 < (F s).im) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a,
    ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) →
    ‖F s‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n a F hF hpos
  set s₀ : Fin n → ℂ := fun k => if (k : ℕ) < a then -1 else 0 with hs₀
  refine ⟨64 ^ n * qf (F s₀), 6 * n, fun s hs hse _ => ?_⟩
  set P : ℕ → Fin n → ℂ := fun j k => if (k : ℕ) < j then s k else s₀ k with hP
  have hs' : ∀ k : Fin n, if (k : ℕ) < a then (s k).re < 0 else ‖s k‖ < 1 := by
    simpa [logDom] using hs
  have hs₀' : ∀ k : Fin n, if (k : ℕ) < a then (s₀ k).re < 0 else ‖s₀ k‖ < 1 := by
    intro k; simp only [hs₀]; split_ifs <;> norm_num
  have hs₀mem : s₀ ∈ logDom n a := by simpa [logDom] using hs₀'
  have hPmem : ∀ j, P j ∈ logDom n a := by
    intro j
    simp only [logDom, Set.mem_setOf_eq]
    intro k
    by_cases hk : (k : ℕ) < j
    · have e : P j k = s k := if_pos hk
      rw [e]; exact hs' k
    · have e : P j k = s₀ k := if_neg hk
      rw [e]; exact hs₀' k
  have hco : ∀ k : Fin n, ‖logExp a s k‖ ≤ 1 / 2 := fun k => (norm_le_pi_norm (logExp a s) k).trans hse
  have hsk : ∀ k : Fin n, ‖s k‖ ≤ ‖s‖ := fun k => norm_le_pi_norm s k
  set M : ℝ := 4 * (1 + ‖s‖) ^ 2 with hMdef
  have hM1 : 1 ≤ M := by
    have : 1 ≤ (1 + ‖s‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg s])
    linarith
  have step : ∀ j, qf (F (P (j + 1))) ≤ M ^ 3 * qf (F (P j)) := by
    intro j
    by_cases hj : j < n
    · set i : Fin n := ⟨j, hj⟩ with hi
      have hPi : P (j + 1) = Function.update (P j) i (s i) := by
        funext k
        by_cases hk : k = i
        · rw [hk, Function.update_self]
          exact if_pos (show (i : ℕ) < j + 1 by simp [hi])
        · rw [Function.update_of_ne hk]
          have hkj : (k : ℕ) ≠ j := fun h => hk (Fin.ext h)
          have e : ((k : ℕ) < j + 1 ↔ (k : ℕ) < j) := by omega
          simp only [hP, e]
      have hPj : Function.update (P j) i (s₀ i) = P j := by
        rw [Function.update_eq_self_iff]
        have hn : ¬ ((i : ℕ) < j) := by simp [hi]
        exact (if_neg hn).symm
      by_cases ha : j < a
      · have hai : (i : ℕ) < a := ha
        have hre : (s i).re ≤ -1 / 2 := by
          apply re_le_of_exp
          have := hco i
          simpa [logExp, hai] using this
        obtain ⟨hζ, hMb⟩ := cay_bound hre
        have hdf : DifferentiableOn ℂ (fun ζ => F (Function.update (P j) i (cay ζ))) (Metric.ball 0 1) :=
          (upd_diff hF (hPmem j) i (D := {z | z.re < 0}) (fun z hz => by simpa [hai] using hz)).comp
            cay_diff (fun ζ hζ => cay_re hζ)
        have hposf : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 < (F (Function.update (P j) i (cay z))).im :=
          fun z hz => hpos _ (upd_mem (hPmem j) i (by simpa [hai] using cay_re hz))
        have key := qf_ball_le hdf hposf hζ (M := M)
          (hMb.trans (by rw [hMdef]; gcongr; exact hsk i))
        have hsi : (s i).re < 0 := by simpa [hai] using hs' i
        have e0 : s₀ i = -1 := by simp [hs₀, hai]
        simp only [cay_inv hsi, cay_zero] at key
        rw [← e0, hPj] at key
        rw [hPi]
        exact key
      · have hai : ¬ (i : ℕ) < a := ha
        have hle : ‖s i‖ ≤ 1 / 2 := by
          have := hco i
          simpa [logExp, hai] using this
        have hζ : ‖s i‖ < 1 := by linarith
        have hdf : DifferentiableOn ℂ (fun ζ => F (Function.update (P j) i ζ)) (Metric.ball 0 1) :=
          upd_diff hF (hPmem j) i (fun z hz => by simpa [hai] using hz)
        have hposf : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 < (F (Function.update (P j) i z)).im :=
          fun z hz => hpos _ (upd_mem (hPmem j) i (by simpa [hai] using hz))
        have hMb : 2 / (1 - ‖s i‖) ≤ M := by
          rw [div_le_iff₀ (by linarith)]
          have : 1 ≤ (1 + ‖s‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg s])
          nlinarith
        have key := qf_ball_le hdf hposf hζ hMb
        have e0 : s₀ i = 0 := by simp [hs₀, hai]
        rw [← e0, hPj, ← hPi] at key
        exact key
    · have e : P (j + 1) = P j := by
        funext k
        have e : ((k : ℕ) < j + 1 ↔ (k : ℕ) < j) := by have := k.isLt; omega
        simp only [hP, e]
      rw [e]
      have h0 := qf_nonneg (hpos _ (hPmem j))
      have : 1 ≤ M ^ 3 := one_le_pow₀ hM1
      nlinarith
  have hind : ∀ j, qf (F (P j)) ≤ (M ^ 3) ^ j * qf (F s₀) := by
    intro j
    induction j with
    | zero =>
      have e : P 0 = s₀ := by funext k; simp [hP]
      simp [e]
    | succ j ih =>
      have : 0 ≤ M ^ 3 := by positivity
      calc qf (F (P (j + 1))) ≤ M ^ 3 * qf (F (P j)) := step j
        _ ≤ M ^ 3 * ((M ^ 3) ^ j * qf (F s₀)) := mul_le_mul_of_nonneg_left ih this
        _ = (M ^ 3) ^ (j + 1) * qf (F s₀) := by ring
  have hPn : P n = s := by funext k; simp [hP, k.isLt]
  have hfin := hind n
  rw [hPn] at hfin
  refine (norm_le_qf (hpos s hs)).trans (hfin.trans (le_of_eq ?_))
  have e : M ^ 3 = 64 * (1 + ‖s‖) ^ 6 := by rw [hMdef]; ring
  rw [e, mul_pow, pow_mul]
  ring

end GlobalTheory
