import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.Growth

open UpperHalfPlane hiding I

def sF (w : ℍ) : ℝ := (1 + ‖(w : ℂ)‖ ^ 2) / w.im

/- English proof (translation)
Rewrite using `[Complex.sq_norm, Complex.normSq_apply, coe_re, coe_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma sq_norm_coe (w : ℍ) : ‖(w : ℂ)‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, coe_re, coe_im]
  ring

/- English proof (translation)
Establish `him` using `w.im_pos`. Rewrite using `[sF, le_div_iff₀ him, one_mul, sq_norm_coe]`. Use polynomial arithmetic with `[sq_nonneg w.re, sq_nonneg (w.im - 1)]`.
-/
lemma one_le_sF (w : ℍ) : 1 ≤ sF w := by
  have him := w.im_pos
  rw [sF, le_div_iff₀ him, one_mul, sq_norm_coe]
  nlinarith [sq_nonneg w.re, sq_nonneg (w.im - 1)]

/- English proof (translation)
The claim follows from `zero_le_one.trans (one_le_sF w)`.
-/
lemma sF_nonneg (w : ℍ) : 0 ≤ sF w := zero_le_one.trans (one_le_sF w)

/- English proof (translation)
Use polynomial arithmetic with `[sq_nonneg (a - b * x), sq_nonneg (c - d * x), sq_nonneg (b * y), sq_nonneg (d * y)]`.
-/
lemma poly_bound (a b c d x y : ℝ) :
    (c * x + d) ^ 2 + (c * y) ^ 2 + ((a * x + b) ^ 2 + (a * y) ^ 2) ≤
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (1 + (x ^ 2 + y ^ 2)) := by
  nlinarith [sq_nonneg (a - b * x), sq_nonneg (c - d * x), sq_nonneg (b * y), sq_nonneg (d * y)]

/- English proof (translation)
Simplify using `[Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma normSq_lin (a b : ℝ) (z : ℍ) :
    Complex.normSq ((a : ℂ) * z + b) = (a * z.re + b) ^ 2 + (a * z.im) ^ 2 := by
  simp [Complex.normSq_apply]; ring

/- English proof (translation)
Establish `hD : 0 < |g.det.val|` using `abs_pos.mpr g.det.ne_zero`. Use `⟨((g 0 0) ^ 2 + (g 0 1) ^ 2 + (g 1 0) ^ 2 + (g 1 1) ^ 2) / |g.det.val|, by positivity, fun z => ?_⟩` and prove the remaining obligations. Establish `hN : 0 < Complex.normSq (denom g z)` using `normSq_denom_pos g z.im_ne_zero`. Establish `him` using `z.im_pos`. Establish `h1 : sF (g • z) = (Complex.normSq (denom g z) + Complex.normSq (num g z)) / (|g.det.val| * z.im)`.

Rewrite using `[sF, im_smul_eq_div_normSq, coe_smul, norm_σ, norm_div, div_pow, Complex.sq_norm, Complex.sq_norm]`. Clear the denominators using the available nonvanishing facts. Establish `h2 : Complex.normSq (denom g z) + Complex.normSq (num g z) ≤ ((g 0 0) ^ 2 + (g 0 1) ^ 2 + (g 1 0) ^ 2 + (g 1 1) ^ 2) * (1 + ‖(z : ℂ)‖ ^ 2)`. Establish `e1 : Complex.normSq (denom g z) = (g 1 0 * z.re + g 1 1) ^ 2 + (g 1 0 * z.im) ^ 2` using `normSq_lin _ _ z`. Establish `e2 : Complex.normSq (num g z) = (g 0 0 * z.re + g 0 1) ^ 2 + (g 0 0 * z.im) ^ 2` using `normSq_lin _ _ z`.

Rewrite using `[e1, e2, sq_norm_coe]`. Conclude with `poly_bound _ _ _ _ _ _`. Rewrite using `[h1, sF, div_mul_div_comm]`. Conclude with `div_le_div_of_nonneg_right h2 (mul_pos hD him).le`.
-/
lemma sF_smul (g : GL (Fin 2) ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℍ, sF (g • z) ≤ K * sF z := by
  have hD : 0 < |g.det.val| := abs_pos.mpr g.det.ne_zero
  refine ⟨((g 0 0) ^ 2 + (g 0 1) ^ 2 + (g 1 0) ^ 2 + (g 1 1) ^ 2) / |g.det.val|, by positivity, fun z => ?_⟩
  have hN : 0 < Complex.normSq (denom g z) := normSq_denom_pos g z.im_ne_zero
  have him := z.im_pos
  have h1 : sF (g • z) =
      (Complex.normSq (denom g z) + Complex.normSq (num g z)) / (|g.det.val| * z.im) := by
    rw [sF, im_smul_eq_div_normSq, coe_smul, norm_σ, norm_div, div_pow, Complex.sq_norm, Complex.sq_norm]
    field_simp
  have h2 : Complex.normSq (denom g z) + Complex.normSq (num g z) ≤
      ((g 0 0) ^ 2 + (g 0 1) ^ 2 + (g 1 0) ^ 2 + (g 1 1) ^ 2) * (1 + ‖(z : ℂ)‖ ^ 2) := by
    have e1 : Complex.normSq (denom g z) = (g 1 0 * z.re + g 1 1) ^ 2 + (g 1 0 * z.im) ^ 2 :=
      normSq_lin _ _ z
    have e2 : Complex.normSq (num g z) = (g 0 0 * z.re + g 0 1) ^ 2 + (g 0 0 * z.im) ^ 2 :=
      normSq_lin _ _ z
    rw [e1, e2, sq_norm_coe]
    exact poly_bound _ _ _ _ _ _
  rw [h1, sF, div_mul_div_comm]
  exact div_le_div_of_nonneg_right h2 (mul_pos hD him).le

/- English proof (translation)
Establish `hq : 0 < (g 1 0) ^ 2 + (g 1 1) ^ 2`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h10 : g 1 0 = 0` using `by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]`. Establish `h11 : g 1 1 = 0` using `by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]`.

Establish `hdet` using `g.det.ne_zero`. Simplify using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h10, h11] at hdet`. Use `⟨1 + 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2), by positivity, fun z => ?_⟩` and prove the remaining obligations. Establish `him` using `z.im_pos`. Establish `hm : 0 < ‖denom g z‖` using `norm_pos_iff.mpr (denom_ne_zero g z)`.

Establish `hN : ‖denom g z‖ ^ 2 = (g 1 0 * z.re + g 1 1) ^ 2 + (g 1 0 * z.im) ^ 2`. Rewrite using `[Complex.sq_norm]`. Conclude with `normSq_lin _ _ z`. Establish `key : ((g 1 0) ^ 2 + (g 1 1) ^ 2) * z.im ^ 2 ≤ ‖denom g z‖ ^ 2 * (1 + ‖(z : ℂ)‖ ^ 2)`. Rewrite using `[hN, sq_norm_coe]`.

Use polynomial arithmetic with `[sq_nonneg (g 1 0 * z.re + g 1 1), sq_nonneg ((g 1 0 * z.re + g 1 1) * z.re + g 1 0 * z.im ^ 2)]`. Establish `hK1 : 1 ≤ 1 + 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2)`. Establish `: 0 ≤ 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hKq : (1 + 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2)) * ((g 1 0) ^ 2 + (g 1 1) ^ 2) = ((g 1 0) ^ 2 + (g 1 1) ^ 2) + 1`.

Clear the denominators using the available nonvanishing facts. Establish `hT1 : 1 ≤ 1 + ‖(z : ℂ)‖ ^ 2` using `by nlinarith [sq_nonneg ‖(z : ℂ)‖]`. Use `set q := (g 1 0) ^ 2 + (g 1 1) ^ 2 with hqdef`. Use `set K := 1 + 1 / q with hKdef`. Use `set T := 1 + ‖(z : ℂ)‖ ^ 2 with hTdef`.

Use `set m := ‖denom g z‖ with hmdef`. Establish `h1 : 1 ≤ K ^ 2 * q * T`. Establish `e : K ^ 2 * q * T = K * (K * q) * T` using `by ring`. Rewrite using `[e, hKq]`. Conclude with `one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK1 (by linarith)) hT1`.

Establish `hsq : z.im ^ 2 ≤ (K * T * m) ^ 2`. Establish `e : (K * T * m) ^ 2 = K ^ 2 * T * (m ^ 2 * T)` using `by ring`. Rewrite using `[e]`. Establish `hKT : 0 ≤ K ^ 2 * T` using `by positivity`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left key hKT, mul_le_mul_of_nonneg_right h1 (sq_nonneg z.im)]`.

Establish `hP : 0 ≤ K * T * m` using `by positivity`. Establish `hy : z.im ≤ K * T * m` using `by nlinarith`. Rewrite using `[inv_eq_one_div, div_le_iff₀ hm, sF, ← hTdef, show K * (T / z.im) * m = (K * T * m) / z.im by ring, le_div_iff₀ him, one_mul]`. Conclude with `hy`.
-/
lemma denom_inv (g : GL (Fin 2) ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℍ, ‖denom g z‖⁻¹ ≤ K * sF z := by
  have hq : 0 < (g 1 0) ^ 2 + (g 1 1) ^ 2 := by
    by_contra hc
    push_neg at hc
    have h10 : g 1 0 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    have h11 : g 1 1 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    have hdet := g.det.ne_zero
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h10, h11] at hdet
  refine ⟨1 + 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2), by positivity, fun z => ?_⟩
  have him := z.im_pos
  have hm : 0 < ‖denom g z‖ := norm_pos_iff.mpr (denom_ne_zero g z)
  have hN : ‖denom g z‖ ^ 2 = (g 1 0 * z.re + g 1 1) ^ 2 + (g 1 0 * z.im) ^ 2 := by
    rw [Complex.sq_norm]
    exact normSq_lin _ _ z
  have key : ((g 1 0) ^ 2 + (g 1 1) ^ 2) * z.im ^ 2 ≤ ‖denom g z‖ ^ 2 * (1 + ‖(z : ℂ)‖ ^ 2) := by
    rw [hN, sq_norm_coe]
    nlinarith [sq_nonneg (g 1 0 * z.re + g 1 1),
      sq_nonneg ((g 1 0 * z.re + g 1 1) * z.re + g 1 0 * z.im ^ 2)]
  have hK1 : 1 ≤ 1 + 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2) := by
    have : 0 ≤ 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2) := by positivity
    linarith
  have hKq : (1 + 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2)) * ((g 1 0) ^ 2 + (g 1 1) ^ 2) =
      ((g 1 0) ^ 2 + (g 1 1) ^ 2) + 1 := by
    field_simp
  have hT1 : 1 ≤ 1 + ‖(z : ℂ)‖ ^ 2 := by nlinarith [sq_nonneg ‖(z : ℂ)‖]
  set q := (g 1 0) ^ 2 + (g 1 1) ^ 2 with hqdef
  set K := 1 + 1 / q with hKdef
  set T := 1 + ‖(z : ℂ)‖ ^ 2 with hTdef
  set m := ‖denom g z‖ with hmdef
  have h1 : 1 ≤ K ^ 2 * q * T := by
    have e : K ^ 2 * q * T = K * (K * q) * T := by ring
    rw [e, hKq]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK1 (by linarith)) hT1
  have hsq : z.im ^ 2 ≤ (K * T * m) ^ 2 := by
    have e : (K * T * m) ^ 2 = K ^ 2 * T * (m ^ 2 * T) := by ring
    rw [e]
    have hKT : 0 ≤ K ^ 2 * T := by positivity
    nlinarith [mul_le_mul_of_nonneg_left key hKT, mul_le_mul_of_nonneg_right h1 (sq_nonneg z.im)]
  have hP : 0 ≤ K * T * m := by positivity
  have hy : z.im ≤ K * T * m := by nlinarith
  rw [inv_eq_one_div, div_le_iff₀ hm, sF, ← hTdef,
    show K * (T / z.im) * m = (K * T * m) / z.im by ring, le_div_iff₀ him, one_mul]
  exact hy

variable {F : Type} [Field F] [NumberField F]

def sP (z : Hn F) : ℝ := ∏ v, sF (z v)

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
lemma one_le_sP (z : Hn F) : 1 ≤ sP z := by
  calc (1 : ℝ) = ∏ v, (1 : ℝ) := by simp
    _ ≤ ∏ v, sF (z v) := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun v _ => one_le_sF _)

/- English proof (translation)
The claim follows from `zero_le_one.trans (one_le_sP z)`.
-/
lemma sP_nonneg (z : Hn F) : 0 ≤ sP z := zero_le_one.trans (one_le_sP z)

/- English proof (translation)
Rewrite using `[Gr.eq_1]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨C, A, hC⟩`. Use `⟨max C 0, A, le_max_right _ _, fun z => (hC z).trans ?_⟩` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (sP_nonneg z) A)`.

Introduce and unpack `⟨C, A, -, hC⟩`. Conclude with `⟨C, A, hC⟩`.
-/
lemma gr_iff (f : Hn F → ℂ) : Gr f ↔ ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ z, ‖f z‖ ≤ C * sP z ^ A := by
  rw [Gr.eq_1]
  constructor
  · rintro ⟨C, A, hC⟩
    refine ⟨max C 0, A, le_max_right _ _, fun z => (hC z).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (sP_nonneg z) A)
  · rintro ⟨C, A, -, hC⟩
    exact ⟨C, A, hC⟩

/- English proof (translation)
Rewrite `hf`, `hg`, the goal using `[gr_iff]`. Take `⟨C1, A1, hC1, h1⟩` from `hf`. Take `⟨C2, A2, hC2, h2⟩` from `hg`. Use `⟨C1 + C2, A1 + A2, add_nonneg hC1 hC2, fun z => ?_⟩` and prove the remaining obligations. Establish `hP` using `one_le_sP z`.

Establish `e1 : sP z ^ A1 ≤ sP z ^ (A1 + A2)` using `pow_le_pow_right₀ hP (by omega)`. Establish `e2 : sP z ^ A2 ≤ sP z ^ (A1 + A2)` using `pow_le_pow_right₀ hP (by omega)`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma gr_add {f g : Hn F → ℂ} (hf : Gr f) (hg : Gr g) : Gr (f + g) := by
  rw [gr_iff] at hf hg ⊢
  obtain ⟨C1, A1, hC1, h1⟩ := hf
  obtain ⟨C2, A2, hC2, h2⟩ := hg
  refine ⟨C1 + C2, A1 + A2, add_nonneg hC1 hC2, fun z => ?_⟩
  have hP := one_le_sP z
  have e1 : sP z ^ A1 ≤ sP z ^ (A1 + A2) := pow_le_pow_right₀ hP (by omega)
  have e2 : sP z ^ A2 ≤ sP z ^ (A1 + A2) := pow_le_pow_right₀ hP (by omega)
  calc ‖(f + g) z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ C1 * sP z ^ A1 + C2 * sP z ^ A2 := add_le_add (h1 z) (h2 z)
    _ ≤ C1 * sP z ^ (A1 + A2) + C2 * sP z ^ (A1 + A2) :=
      add_le_add (mul_le_mul_of_nonneg_left e1 hC1) (mul_le_mul_of_nonneg_left e2 hC2)
    _ = (C1 + C2) * sP z ^ (A1 + A2) := by ring

/- English proof (translation)
Rewrite `hf`, `hg`, the goal using `[gr_iff]`. Take `⟨C1, A1, hC1, h1⟩` from `hf`. Take `⟨C2, A2, hC2, h2⟩` from `hg`. Use `⟨C1 * C2, A1 + A2, mul_nonneg hC1 hC2, fun z => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
lemma gr_mul {f g : Hn F → ℂ} (hf : Gr f) (hg : Gr g) : Gr (f * g) := by
  rw [gr_iff] at hf hg ⊢
  obtain ⟨C1, A1, hC1, h1⟩ := hf
  obtain ⟨C2, A2, hC2, h2⟩ := hg
  refine ⟨C1 * C2, A1 + A2, mul_nonneg hC1 hC2, fun z => ?_⟩
  calc ‖(f * g) z‖ = ‖f z‖ * ‖g z‖ := norm_mul _ _
    _ ≤ (C1 * sP z ^ A1) * (C2 * sP z ^ A2) :=
      mul_le_mul (h1 z) (h2 z) (norm_nonneg _) (mul_nonneg hC1 (pow_nonneg (sP_nonneg z) _))
    _ = C1 * C2 * sP z ^ (A1 + A2) := by ring

/- English proof (translation)
Rewrite using `[gr_iff]`. Conclude with `⟨‖c‖, 0, norm_nonneg _, fun z => by simp⟩`.
-/
lemma gr_const (c : ℂ) : Gr (fun _ : Hn F => c) := by
  rw [gr_iff]
  exact ⟨‖c‖, 0, norm_nonneg _, fun z => by simp⟩

/- English proof (translation)
The claim follows from `gr_mul (gr_const c) hf`.
-/
lemma gr_smul (c : ℂ) {f : Hn F → ℂ} (hf : Gr f) : Gr (c • f) := gr_mul (gr_const c) hf

/- English proof (translation)
Rewrite `hf`, the goal using `[gr_iff]`. Take `⟨C, A, hC, hfz⟩` from `hf`. Use `choose K hK0 hK using fun v : InfinitePlace F => sF_smul (cmp v h)`. Establish `hact : ∀ z : Hn F, sP (act h z) ≤ (∏ v, K v) * sP z`. Introduce `z`.

Unfold `sP`. Rewrite using `[← Finset.prod_mul_distrib]`. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `v _`. Conclude with `sF_nonneg _`.

Introduce `v _`. Rewrite using `[act.eq_1]`. Conclude with `hK v (z v)`. Use `⟨C * (∏ v, K v) ^ A, A, mul_nonneg hC (pow_nonneg (Finset.prod_nonneg fun v _ => hK0 v) A), fun z => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
lemma gr_act (h : GL (Fin 2) (InfinitePlace F → ℝ)) {f : Hn F → ℂ} (hf : Gr f) : Gr (fun z => f (act h z)) := by
  rw [gr_iff] at hf ⊢
  obtain ⟨C, A, hC, hfz⟩ := hf
  choose K hK0 hK using fun v : InfinitePlace F => sF_smul (cmp v h)
  have hact : ∀ z : Hn F, sP (act h z) ≤ (∏ v, K v) * sP z := by
    intro z
    unfold sP
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro v _
      exact sF_nonneg _
    · intro v _
      rw [act.eq_1]
      exact hK v (z v)
  refine ⟨C * (∏ v, K v) ^ A, A,
    mul_nonneg hC (pow_nonneg (Finset.prod_nonneg fun v _ => hK0 v) A), fun z => ?_⟩
  calc ‖f (act h z)‖ ≤ C * sP (act h z) ^ A := hfz _
    _ ≤ C * ((∏ v, K v) * sP z) ^ A :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sP_nonneg _) (hact z) A) hC
    _ = C * (∏ v, K v) ^ A * sP z ^ A := by ring

/- English proof (translation)
Rewrite using `[gr_iff]`. Use `choose K hK0 hK using fun v : InfinitePlace F => denom_inv (cmp v h)`. Use `⟨(∏ v, K v) ^ k, k, pow_nonneg (Finset.prod_nonneg fun v _ => hK0 v) k, fun z => ?_⟩` and prove the remaining obligations. Establish `hb : ‖(∏ v, denom (cmp v h) (z v))⁻¹‖ ≤ (∏ v, K v) * sP z`. Rewrite using `[norm_inv, norm_prod, ← Finset.prod_inv_distrib]`.

Unfold `sP`. Rewrite using `[← Finset.prod_mul_distrib]`. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `v _`. Check the signs of the components of the expression.

Introduce `v _`. Conclude with `hK v (z v)`. Rewrite using `[norm_pow, ← mul_pow]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) hb k`.
-/
lemma gr_denom (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) :
    Gr (fun z : Hn F => (∏ v, denom (GlobalTheory.HilbertThetaSeries.cmp v h) (z v))⁻¹ ^ k) := by
  rw [gr_iff]
  choose K hK0 hK using fun v : InfinitePlace F => denom_inv (cmp v h)
  refine ⟨(∏ v, K v) ^ k, k, pow_nonneg (Finset.prod_nonneg fun v _ => hK0 v) k, fun z => ?_⟩
  have hb : ‖(∏ v, denom (cmp v h) (z v))⁻¹‖ ≤ (∏ v, K v) * sP z := by
    rw [norm_inv, norm_prod, ← Finset.prod_inv_distrib]
    unfold sP
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro v _
      positivity
    · intro v _
      exact hK v (z v)
  rw [norm_pow, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hb k

/- English proof (translation)
The claim follows from `gr_mul (gr_denom k h) (gr_act h hf)`.
-/
lemma hilbertModerateGrowth_unnormalizedSlash (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) {f : Hn F → ℂ} (hf : Gr f) : Gr (sl0 k h f) :=
  gr_mul (gr_denom k h) (gr_act h hf)

/- English proof (translation)
The claim follows from `gr_mul (gr_const _) (hilbertModerateGrowth_unnormalizedSlash k h hf)`.
-/
lemma gr_sl (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) {f : Hn F → ℂ} (hf : Gr f) : Gr (sl k h f) :=
  gr_mul (gr_const _) (hilbertModerateGrowth_unnormalizedSlash k h hf)

/- English proof (translation)
Introduce `_ _ _ k _ _ c hf hg` and use `⟨gr_add hf hg, gr_smul c hf, gr_mul hf hg, gr_const 1, gr_const 0, fun h _ => ⟨hilbertModerateGrowth_unnormalizedSlash k h hf, gr_sl k h hf⟩⟩`.
-/
theorem gr_closed : ∀ (F : Type) [Field F] [NumberField F] (k : ℕ) (f g : Hn F → ℂ) (c : ℂ), Gr f → Gr g → Gr (f + g) ∧ Gr (c • f) ∧ Gr (f * g) ∧ Gr (1 : Hn F → ℂ) ∧ Gr (0 : Hn F → ℂ) ∧ ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), Pos h → Gr (sl0 k h f) ∧ Gr (sl k h f) :=
  fun _ _ _ k _ _ c hf hg =>
    ⟨gr_add hf hg, gr_smul c hf, gr_mul hf hg, gr_const 1, gr_const 0, fun h _ => ⟨hilbertModerateGrowth_unnormalizedSlash k h hf, gr_sl k h hf⟩⟩

end GlobalTheory.HilbertThetaSeries.Growth
