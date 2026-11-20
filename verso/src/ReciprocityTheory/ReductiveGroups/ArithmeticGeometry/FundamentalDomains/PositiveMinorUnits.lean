import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.GramDeterminantReal

namespace ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open scoped ComplexConjugate
noncomputable section

variable {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)

def famN (x : Matrix (Fin r) (Fin r) ℂ) (i : ℕ) (hi : i ≤ r) : Fin i → Fin r → ℂ :=
  fun a => col x (Fin.castLE hi a)

def pN (x : Matrix (Fin r) (Fin r) ℂ) (e : Fin r → ℂ) (i : ℕ) : Fin r → ℂ :=
  if h : i ≤ r then pv τ G (famN x i h) e else 0

def mN (x : Matrix (Fin r) (Fin r) ℂ) (e : Fin r → ℂ) (i : ℕ) : ℝ :=
  (hermC τ G (pN τ G x e i) (pN τ G x e i)).re

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem famN_succ (x : Matrix (Fin r) (Fin r) ℂ) (i : ℕ) (h : i + 1 ≤ r) :
    (fun a : Fin i => famN x (i + 1) h a.castSucc) = famN x i (Nat.le_of_succ_le h) := rfl

/- English proof (translation)
Simplify using `[mN, pN, pv, hermC]`.
-/
theorem mN_zero (x : Matrix (Fin r) (Fin r) ℂ) (e : Fin r → ℂ) : mN τ G x e 0 = 0 := by
  simp [mN, pN, pv, hermC]

section Frame
variable {τ G} (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (p0 : ℕ) (hp0 : p0 ≤ r)
  (x : Matrix (Fin r) (Fin r) ℂ) (hx : x.det ≠ 0)
  (hsg : ∀ i (h : i ≤ r), 0 < psgn p0 i * (gramF τ G (famN x i h)).det.re)
  (e : Fin r → ℂ) (he : hermC τ G e e = 0)
include hsg

/- English proof (translation)
Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`. Establish `h1` using `hsg i h`. Rewrite `h1` using `[h0]`. Simplify using `at h1`.
-/
theorem unit_of (i : ℕ) (h : i ≤ r) : IsUnit (gramF τ G (famN x i h)).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have h1 := hsg i h
  rw [h0] at h1
  simp at h1

include hG

/- English proof (translation)
Establish `hp` using `pv_pyth hG (famN x (i + 1) h) e (unit_of p0 x hsg (i + 1) h) (unit_of p0 x hsg i (Nat.le_of_succ_le h))`. Rewrite `hp` using `[famN_succ]`. Simplify using `only [mN, pN, dif_pos h, dif_pos (Nat.le_of_succ_le h)]`. Rewrite using `[hp, Complex.add_re]`.
-/
theorem mN_succ (i : ℕ) (h : i + 1 ≤ r) : mN τ G x e (i + 1) = mN τ G x e i +
    (hermC τ G (dv τ G (famN x (i + 1) h) e) (dv τ G (famN x (i + 1) h) e)).re := by
  have hp := pv_pyth hG (famN x (i + 1) h) e (unit_of p0 x hsg (i + 1) h)
    (unit_of p0 x hsg i (Nat.le_of_succ_le h))
  rw [famN_succ] at hp
  simp only [mN, pN, dif_pos h, dif_pos (Nat.le_of_succ_le h)]
  rw [hp, Complex.add_re]

/- English proof (translation)
Establish `hA1` using `unit_of p0 x hsg (i + 1) h`. Establish `hA0` using `unit_of p0 x hsg i (Nat.le_of_succ_le h)`. Establish `hs` using `det_step hG (famN x (i + 1) h) e hA1 hA0`. Rewrite `hs` using `[famN_succ]`. Rewrite using `[mN_succ hG p0 x hsg e i h, add_sub_cancel_left]`.

Use `set y := yv τ G (famN x (i + 1) h) e (Fin.last i)`. Use `set hd := hermC τ G (dv τ G (famN x (i + 1) h) e) (dv τ G (famN x (i + 1) h) e)`. Establish `hre` using `congrArg Complex.re hs`. Rewrite `hre` using `[Complex.mul_conj, Complex.mul_re, Complex.mul_re, det_gramF_real hG, hC_self_real hG, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul, sub_zero]`. Establish `hps : psgn p0 (i + 1) = psgn p0 i * sgn p0 i` using `Finset.prod_range_succ _ _`.

Establish `key : (psgn p0 i * (gramF τ G (famN x i (Nat.le_of_succ_le h))).det.re) * (sgn p0 i * hd.re) = Complex.normSq y * (psgn p0 (i + 1) * (gramF τ G (famN x (i + 1) h)).det.re)`. Rewrite using `[hps]`. Take the linear combination `(psgn p0 i * sgn p0 i) * hre`. Establish `h1` using `hsg i (Nat.le_of_succ_le h)`. Establish `h2` using `hsg (i + 1) h`.

Use `le_of_mul_le_mul_left ?_ h1` and prove the remaining obligations. Rewrite using `[mul_zero, key]`. Conclude with `mul_nonneg (Complex.normSq_nonneg _) h2.le`.
-/
theorem mN_step (i : ℕ) (h : i + 1 ≤ r) : 0 ≤ sgn p0 i * (mN τ G x e (i + 1) - mN τ G x e i) := by
  have hA1 := unit_of p0 x hsg (i + 1) h
  have hA0 := unit_of p0 x hsg i (Nat.le_of_succ_le h)
  have hs := det_step hG (famN x (i + 1) h) e hA1 hA0
  rw [famN_succ] at hs
  rw [mN_succ hG p0 x hsg e i h, add_sub_cancel_left]
  set y := yv τ G (famN x (i + 1) h) e (Fin.last i)
  set hd := hermC τ G (dv τ G (famN x (i + 1) h) e) (dv τ G (famN x (i + 1) h) e)
  have hre := congrArg Complex.re hs
  rw [Complex.mul_conj, Complex.mul_re, Complex.mul_re, det_gramF_real hG, hC_self_real hG,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul, sub_zero] at hre
  have hps : psgn p0 (i + 1) = psgn p0 i * sgn p0 i := Finset.prod_range_succ _ _
  have key : (psgn p0 i * (gramF τ G (famN x i (Nat.le_of_succ_le h))).det.re) * (sgn p0 i * hd.re) =
      Complex.normSq y * (psgn p0 (i + 1) * (gramF τ G (famN x (i + 1) h)).det.re) := by
    rw [hps]; linear_combination (psgn p0 i * sgn p0 i) * hre
  have h1 := hsg i (Nat.le_of_succ_le h)
  have h2 := hsg (i + 1) h
  refine le_of_mul_le_mul_left ?_ h1
  rw [mul_zero, key]
  exact mul_nonneg (Complex.normSq_nonneg _) h2.le

include hp0 in
/- English proof (translation)
Establish `step : ∀ k, k < p0 → mN τ G x e k ≤ mN τ G x e (k + 1)`. Introduce `k hk`. Establish `h1` using `mN_step (hG := hG) (p0 := p0) (x := x) (hsg := hsg) (e := e) (i := k) (h := by omega)`. Establish `hs : sgn p0 k = 1` using `by simp [sgn, hk]`. Rewrite `h1` using `[hs]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `revert hj`. Proceed by induction on `j, hi using Nat.le_induction with`. Consider the case `base => intro _`. Conclude with `le_refl _`.

Consider the case `succ j hij ih => intro hj; exact (ih (by omega)).trans (step j (by omega))`.
-/
theorem mN_up (j : ℕ) (hj : j ≤ p0) (i : ℕ) (hi : i ≤ j) : mN τ G x e i ≤ mN τ G x e j := by
  have step : ∀ k, k < p0 → mN τ G x e k ≤ mN τ G x e (k + 1) := by
    intro k hk
    have h1 := mN_step (hG := hG) (p0 := p0) (x := x) (hsg := hsg) (e := e) (i := k) (h := by omega)
    have hs : sgn p0 k = 1 := by simp [sgn, hk]
    rw [hs] at h1
    linarith
  revert hj
  induction j, hi using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ j hij ih => intro hj; exact (ih (by omega)).trans (step j (by omega))

/- English proof (translation)
Establish `step : ∀ k, p0 ≤ k → k + 1 ≤ r → mN τ G x e (k + 1) ≤ mN τ G x e k`. Introduce `k hk hkr`. Establish `h1` using `mN_step (hG := hG) (p0 := p0) (x := x) (hsg := hsg) (e := e) (i := k) (h := hkr)`. Establish `hs : sgn p0 k = -1` using `by simp [sgn, not_lt.mpr hk]`. Rewrite `h1` using `[hs]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `revert hj`. Proceed by induction on `j, hij using Nat.le_induction with`. Consider the case `base => intro _`. Conclude with `le_refl _`.

Consider the case `succ j hij ih => intro hj; exact (step j (by omega) hj).trans (ih (by omega))`.
-/
theorem mN_down (i : ℕ) (hi : p0 ≤ i) (j : ℕ) (hij : i ≤ j) (hj : j ≤ r) :
    mN τ G x e j ≤ mN τ G x e i := by
  have step : ∀ k, p0 ≤ k → k + 1 ≤ r → mN τ G x e (k + 1) ≤ mN τ G x e k := by
    intro k hk hkr
    have h1 := mN_step (hG := hG) (p0 := p0) (x := x) (hsg := hsg) (e := e) (i := k) (h := hkr)
    have hs : sgn p0 k = -1 := by simp [sgn, not_lt.mpr hk]
    rw [hs] at h1
    linarith
  revert hj
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ j hij ih => intro hj; exact (step j (by omega) hj).trans (ih (by omega))

include hx in
/- English proof (translation)
Establish `hA` using `unit_of p0 x hsg r le_rfl`. Rewrite using `[pN, dif_pos le_rfl]`. Establish `he' : e = ∑ d, (x⁻¹ *ᵥ e) d • famN x r le_rfl d`. Establish `h1 : x *ᵥ (x⁻¹ *ᵥ e) = e`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hx), Matrix.one_mulVec]`.

Use `conv_lhs => rw [← h1]`. Use function extensionality and compare the values at `k`. Simplify using `only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, famN, col]`. Conclude with `Finset.sum_congr rfl fun d _ => by rw [mul_comm]; rfl`. Establish `h2 : e - pv τ G (famN x r le_rfl) e = ∑ d, ((x⁻¹ *ᵥ e) d - yv τ G (famN x r le_rfl) e d) • famN x r le_rfl d` using `by conv_lhs => arg 1; rw [he']`.

Rewrite using `[pv, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun d _ => (sub_smul _ _ _).symm`. Establish `h3` using `comb_orth_zero τ G (famN x r le_rfl) hA _ fun d => by`. Rewrite using `[← h2, hC_sub_left, pv_orth τ G _ e hA d]`. Conclude with `sub_self _`.

Rewrite `h3` using `[← h2]`. Conclude with `(sub_eq_zero.mp h3).symm`.
-/
theorem pN_top : pN τ G x e r = e := by
  have hA := unit_of p0 x hsg r le_rfl
  rw [pN, dif_pos le_rfl]
  have he' : e = ∑ d, (x⁻¹ *ᵥ e) d • famN x r le_rfl d := by
    have h1 : x *ᵥ (x⁻¹ *ᵥ e) = e := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hx),
        Matrix.one_mulVec]
    conv_lhs => rw [← h1]
    funext k
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, famN, col]
    exact Finset.sum_congr rfl fun d _ => by rw [mul_comm]; rfl
  have h2 : e - pv τ G (famN x r le_rfl) e = ∑ d, ((x⁻¹ *ᵥ e) d - yv τ G (famN x r le_rfl) e d) •
      famN x r le_rfl d := by
    conv_lhs => arg 1; rw [he']
    rw [pv, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => (sub_smul _ _ _).symm
  have h3 := comb_orth_zero τ G (famN x r le_rfl) hA _ fun d => by
    rw [← h2, hC_sub_left, pv_orth τ G _ e hA d]; exact sub_self _
  rw [← h2] at h3
  exact (sub_eq_zero.mp h3).symm

include hx he in
/- English proof (translation)
Unfold `mN`. Rewrite using `[pN_top (hG := hG) (p0 := p0) (x := x) (hx := hx) (hsg := hsg) (e := e), he]`. Simplify using the standard rewrite rules.
-/
theorem mN_top : mN τ G x e r = 0 := by
  unfold mN
  rw [pN_top (hG := hG) (p0 := p0) (x := x) (hx := hx) (hsg := hsg) (e := e), he]
  simp

include hp0 hx he in
/- English proof (translation)
Break down `le_total i p0 with hi0 | hi0` into its components or cases. Prove the components needed by the constructor for the conclusion. Establish `h1` using `mN_up (hG := hG) (p0 := p0) (hp0 := hp0) (x := x) (hsg := hsg) (e := e) (j := i) (hj := hi0) (i := 0) (hi := Nat.zero_le _)`. Rewrite `h1` using `[mN_zero]`. Conclude with `h1`.

Conclude with `mN_up (hG := hG) (p0 := p0) (hp0 := hp0) (x := x) (hsg := hsg) (e := e) (j := p0) (hj := le_rfl) (i := i) (hi := hi0)`. Prove the components needed by the constructor for the conclusion. Establish `h1` using `mN_down (hG := hG) (p0 := p0) (x := x) (hsg := hsg) (e := e) (i := i) (hi := hi0) (j := r) (hij := hi) (hj := le_rfl)`. Rewrite `h1` using `[mN_top (hG := hG) (p0 := p0) (x := x) (hx := hx) (hsg := hsg) (e := e) (he := he)]`. Conclude with `h1`.

Conclude with `mN_down (hG := hG) (p0 := p0) (x := x) (hsg := hsg) (e := e) (i := p0) (hi := le_rfl) (j := i) (hij := hi0) (hj := hi)`.
-/
theorem mN_bounds (i : ℕ) (hi : i ≤ r) : 0 ≤ mN τ G x e i ∧ mN τ G x e i ≤ mN τ G x e p0 := by
  rcases le_total i p0 with hi0 | hi0
  · constructor
    · have h1 := mN_up (hG := hG) (p0 := p0) (hp0 := hp0) (x := x) (hsg := hsg) (e := e)
        (j := i) (hj := hi0) (i := 0) (hi := Nat.zero_le _)
      rw [mN_zero] at h1
      exact h1
    · exact mN_up (hG := hG) (p0 := p0) (hp0 := hp0) (x := x) (hsg := hsg) (e := e)
        (j := p0) (hj := le_rfl) (i := i) (hi := hi0)
  · constructor
    · have h1 := mN_down (hG := hG) (p0 := p0) (x := x) (hsg := hsg) (e := e)
        (i := i) (hi := hi0) (j := r) (hij := hi) (hj := le_rfl)
      rw [mN_top (hG := hG) (p0 := p0) (x := x) (hx := hx) (hsg := hsg) (e := e) (he := he)] at h1
      exact h1
    · exact mN_down (hG := hG) (p0 := p0) (x := x) (hsg := hsg) (e := e)
        (i := p0) (hi := le_rfl) (j := i) (hij := hi0) (hj := hi)

include hp0 hx he in
/- English proof (translation)
Assume the negation of the conclusion as `hle`. Rewrite `hle` using `[not_lt]`. Establish `hz : ∀ i, i ≤ r → mN τ G x e i = 0` using `fun i hi => by`. Use `mN_bounds hG p0 hp0 x hx hsg e he i hi` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hstep : ∀ i (h : i + 1 ≤ r), pN τ G x e (i + 1) = pN τ G x e i`. Introduce `i h`. Establish `hA1` using `unit_of p0 x hsg (i + 1) h`. Establish `hA0` using `unit_of p0 x hsg i (Nat.le_of_succ_le h)`. Establish `hd0 : (hermC τ G (dv τ G (famN x (i + 1) h) e) (dv τ G (famN x (i + 1) h) e)).re = 0`.

Use `mN_succ hG p0 x hsg e i h` as an intermediate fact. Rewrite using `[hz i (by omega), hz (i + 1) h] at this; linarith`. Establish `hs` using `det_step hG (famN x (i + 1) h) e hA1 hA0`. Establish `hre` using `congrArg Complex.re hs`. Rewrite `hre` using `[Complex.mul_conj, Complex.mul_re, Complex.mul_re, det_gramF_real hG, hC_self_real hG, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul, sub_zero, hd0, mul_zero]`.

Establish `hd1 : (gramF τ G (famN x (i + 1) h)).det.re ≠ 0` using `fun h0 => by`. Use `hsg (i + 1) h` as an intermediate fact. Rewrite `this` using `[h0, mul_zero]`. Conclude with `lt_irrefl _ this`. Establish `hy : yv τ G (famN x (i + 1) h) e (Fin.last i) = 0` using `Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hre.symm).resolve_right hd1)`.

Establish `hdv` using `dv_zero τ G (famN x (i + 1) h) e hA1 hA0 hy`. Rewrite `hdv` using `[dv, famN_succ, sub_eq_zero]`. Simplify using `only [pN, dif_pos h, dif_pos (Nat.le_of_succ_le h)]`. Conclude with `hdv`. Establish `hall : ∀ i, i ≤ r → pN τ G x e i = 0`.

Introduce `i hi`. Proceed by induction on `i with`. Consider the case `zero => rw [pN, dif_pos (Nat.zero_le r), pv]`. Conclude with `Finset.sum_empty`. Consider the case `succ i ih => rw [hstep i hi, ih (by omega)]`.

Conclude with `hne ((pN_top hG p0 x hx hsg e).symm.trans (hall r le_rfl))`.
-/
theorem mN_pos (hne : e ≠ 0) : 0 < mN τ G x e p0 := by
  by_contra hle
  rw [not_lt] at hle
  have hz : ∀ i, i ≤ r → mN τ G x e i = 0 := fun i hi => by
    have := mN_bounds hG p0 hp0 x hx hsg e he i hi; linarith
  have hstep : ∀ i (h : i + 1 ≤ r), pN τ G x e (i + 1) = pN τ G x e i := by
    intro i h
    have hA1 := unit_of p0 x hsg (i + 1) h
    have hA0 := unit_of p0 x hsg i (Nat.le_of_succ_le h)
    have hd0 : (hermC τ G (dv τ G (famN x (i + 1) h) e) (dv τ G (famN x (i + 1) h) e)).re = 0 := by
      have := mN_succ hG p0 x hsg e i h
      rw [hz i (by omega), hz (i + 1) h] at this; linarith
    have hs := det_step hG (famN x (i + 1) h) e hA1 hA0
    have hre := congrArg Complex.re hs
    rw [Complex.mul_conj, Complex.mul_re, Complex.mul_re, det_gramF_real hG, hC_self_real hG,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul, sub_zero, hd0,
      mul_zero] at hre
    have hd1 : (gramF τ G (famN x (i + 1) h)).det.re ≠ 0 := fun h0 => by
      have := hsg (i + 1) h; rw [h0, mul_zero] at this; exact lt_irrefl _ this
    have hy : yv τ G (famN x (i + 1) h) e (Fin.last i) = 0 :=
      Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hre.symm).resolve_right hd1)
    have hdv := dv_zero τ G (famN x (i + 1) h) e hA1 hA0 hy
    rw [dv, famN_succ, sub_eq_zero] at hdv
    simp only [pN, dif_pos h, dif_pos (Nat.le_of_succ_le h)]
    exact hdv
  have hall : ∀ i, i ≤ r → pN τ G x e i = 0 := by
    intro i hi
    induction i with
    | zero => rw [pN, dif_pos (Nat.zero_le r), pv]; exact Finset.sum_empty
    | succ i ih => rw [hstep i hi, ih (by omega)]
  exact hne ((pN_top hG p0 x hx hsg e).symm.trans (hall r le_rfl))

end Frame

end

end ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
