import Mathlib
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsGlIsometryCompEqOfNondegenerate

namespace GlobalTheory.UnitaryOrbitForm

open Matrix Filter Topology

variable {r : ℕ}

/- English proof (translation)
Simplify using `only [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma dotProduct_mulVec_star_add_smul_expand (C : Matrix (Fin r) (Fin r) ℂ) (a b : ℂ) (x y : Fin r → ℂ) :
    (a • x + b • y) ⬝ᵥ C *ᵥ star (a • x + b • y) =
      a * star a * (x ⬝ᵥ C *ᵥ star x) + b * star b * (y ⬝ᵥ C *ᵥ star y) +
        a * star b * (x ⬝ᵥ C *ᵥ star y) + b * star a * (y ⬝ᵥ C *ᵥ star x) := by
  simp only [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/- English proof (translation)
Establish `hS : ∀ x y : Fin r → ℂ, x ⬝ᵥ C *ᵥ star y = 0`. Introduce `x y`. Establish `h1` using `h ((1 : ℂ) • x + (1 : ℂ) • y)`. Establish `h2` using `h ((1 : ℂ) • x + Complex.I • y)`. Rewrite `h1`, `h2` using `[dotProduct_mulVec_star_add_smul_expand, h x, h y]`.

Establish `hsI : star Complex.I = -Complex.I` using `by simp`. Rewrite `h2` using `[hsI, star_one]`. Rewrite `h1` using `[star_one]`. Take the linear combination `(1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 + ((x ⬝ᵥ C *ᵥ star y) - (y ⬝ᵥ C *ᵥ star x)) / 2 * Complex.I_sq`. Use extensionality with `i j`.

Use `hS (Pi.single i 1) (Pi.single j 1)` as an intermediate fact. Simplify using `using this`.
-/
theorem eq_zero_of_forall_dotProduct_star_eq_zero {C : Matrix (Fin r) (Fin r) ℂ}
    (h : ∀ u : Fin r → ℂ, u ⬝ᵥ C *ᵥ star u = 0) : C = 0 := by
  have hS : ∀ x y : Fin r → ℂ, x ⬝ᵥ C *ᵥ star y = 0 := by
    intro x y
    have h1 := h ((1 : ℂ) • x + (1 : ℂ) • y)
    have h2 := h ((1 : ℂ) • x + Complex.I • y)
    rw [dotProduct_mulVec_star_add_smul_expand, h x, h y] at h1 h2
    have hsI : star Complex.I = -Complex.I := by simp
    rw [hsI, star_one] at h2
    rw [star_one] at h1
    linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 +
      ((x ⬝ᵥ C *ᵥ star y) - (y ⬝ᵥ C *ᵥ star x)) / 2 * Complex.I_sq
  ext i j
  have := hS (Pi.single i 1) (Pi.single j 1)
  simpa using this

/- English proof (translation)
Apply `eq_zero_of_forall_dotProduct_star_eq_zero` to reduce the goal to its premises. Introduce `u`. Establish `hv : v ⬝ᵥ C *ᵥ star v = 0` using `h.self_of_nhds`. Establish `hc : ∀ s : ℝ, Continuous fun t : ℝ => (1 : ℂ) • v + ((s * t : ℝ) : ℂ) • u` using `fun s => continuous_const.add ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).smul continuous_const)`. Establish `e : ∀ s : ℝ, ∀ᶠ t : ℝ in 𝓝 0, ((1 : ℂ) • v + ((s * t : ℝ) : ℂ) • u) ⬝ᵥ C *ᵥ star ((1 : ℂ) • v + ((s * t : ℝ) : ℂ) • u) = 0` using `fun s => ((hc s).tendsto' 0 v (by simp)).eventually h`.

Take `⟨t, ⟨h1, h2⟩, ht⟩` from `(((e 1).and (e (-1))).filter_mono nhdsWithin_le_nhds |>.and (self_mem_nhdsWithin : ({0}ᶜ : Set ℝ) ∈ 𝓝[≠] (0 : ℝ))).exists`. Rewrite `h1`, `h2` using `[dotProduct_mulVec_star_add_smul_expand, hv]`. Simplify using `only [star_one, Complex.star_def, Complex.conj_ofReal] at h1 h2`. Establish `ht0 : (t : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr ht`. Establish `key : ((t : ℂ) ^ 2) * (u ⬝ᵥ C *ᵥ star u) = 0`.

Move the coercions through the operations in `at h1 h2`. Take the linear combination `(h1 + h2) / 2`. Conclude with `(mul_eq_zero.mp key).resolve_left (pow_ne_zero 2 ht0)`.
-/
theorem eq_zero_of_eventually_dotProduct_star_eq_zero {C : Matrix (Fin r) (Fin r) ℂ}
    {v : Fin r → ℂ} (h : ∀ᶠ w in 𝓝 v, w ⬝ᵥ C *ᵥ star w = 0) : C = 0 := by
  apply eq_zero_of_forall_dotProduct_star_eq_zero
  intro u
  have hv : v ⬝ᵥ C *ᵥ star v = 0 := h.self_of_nhds
  have hc : ∀ s : ℝ, Continuous fun t : ℝ => (1 : ℂ) • v + ((s * t : ℝ) : ℂ) • u := fun s =>
    continuous_const.add ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).smul
      continuous_const)
  have e : ∀ s : ℝ, ∀ᶠ t : ℝ in 𝓝 0,
      ((1 : ℂ) • v + ((s * t : ℝ) : ℂ) • u) ⬝ᵥ C *ᵥ star ((1 : ℂ) • v + ((s * t : ℝ) : ℂ) • u) = 0 :=
    fun s => ((hc s).tendsto' 0 v (by simp)).eventually h
  obtain ⟨t, ⟨h1, h2⟩, ht⟩ :=
    (((e 1).and (e (-1))).filter_mono nhdsWithin_le_nhds |>.and
      (self_mem_nhdsWithin : ({0}ᶜ : Set ℝ) ∈ 𝓝[≠] (0 : ℝ))).exists
  rw [dotProduct_mulVec_star_add_smul_expand, hv] at h1 h2
  simp only [star_one, Complex.star_def, Complex.conj_ofReal] at h1 h2
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have key : ((t : ℂ) ^ 2) * (u ⬝ᵥ C *ᵥ star u) = 0 := by
    push_cast at h1 h2
    linear_combination (h1 + h2) / 2
  exact (mul_eq_zero.mp key).resolve_left (pow_ne_zero 2 ht0)

/- English proof (translation)
Establish `hc : star (w ⬝ᵥ A *ᵥ star w) = w ⬝ᵥ A *ᵥ star w`. Simplify using `only [dotProduct, mulVec, Finset.mul_sum, star_sum, star_mul', star_star, Pi.star_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← hA.apply i j]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `(Complex.conj_eq_iff_re.mp hc).symm`.
-/
theorem dotProduct_star_eq_re {A : Matrix (Fin r) (Fin r) ℂ} (hA : A.IsHermitian)
    (w : Fin r → ℂ) : w ⬝ᵥ A *ᵥ star w = ((w ⬝ᵥ A *ᵥ star w).re : ℂ) := by
  have hc : star (w ⬝ᵥ A *ᵥ star w) = w ⬝ᵥ A *ᵥ star w := by
    simp only [dotProduct, mulVec, Finset.mul_sum, star_sum, star_mul', star_star, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hA.apply i j]
    ring
  exact (Complex.conj_eq_iff_re.mp hc).symm

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.map_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum, starRingEnd_apply, Pi.star_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma transpose_col_mul_mul_map_conj_apply (B : Matrix (Fin r) (Fin r) ℂ) (x : Fin r → ℂ) (i j : Fin 1) :
    ((Matrix.of fun k (_ : Fin 1) => x k)ᵀ * B *
      (Matrix.of fun k (_ : Fin 1) => x k).map (starRingEnd ℂ)) i j = x ⬝ᵥ B *ᵥ star x := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.map_apply, dotProduct,
    mulVec, Finset.sum_mul, Finset.mul_sum, starRingEnd_apply, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Use extensionality with `i`. Simplify using `[mulVec, dotProduct, mul_comm]`.
-/
private lemma of_col_mulVec_eq_smul (x : Fin r → ℂ) (a : Fin 1 → ℂ) :
    (Matrix.of fun k (_ : Fin 1) => x k) *ᵥ a = a 0 • x := by
  ext i
  simp [mulVec, dotProduct, mul_comm]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, mulVec, dotProduct]`.
-/
private lemma mul_of_col_eq_of_mulVec (g : Matrix (Fin r) (Fin r) ℂ) (x : Fin r → ℂ) :
    g * (Matrix.of fun k (_ : Fin 1) => x k) = Matrix.of fun k (_ : Fin 1) => (g *ᵥ x) k := by
  ext i j
  simp [Matrix.mul_apply, mulVec, dotProduct]

/- English proof (translation)
Establish `hG : ∀ a b, starRingEnd ℂ (B a b) = B b a` using `fun a b => by`. Rewrite using `[starRingEnd_apply]`. Conclude with `hB.apply b a`. Establish `h0 : ∀ a : Fin 1 → ℂ, (Matrix.of fun k (_ : Fin 1) => v k) *ᵥ a = 0 ↔ (Matrix.of fun k (_ : Fin 1) => w k) *ᵥ a = 0`. Introduce `a`.

Rewrite using `[of_col_mulVec_eq_smul, of_col_mulVec_eq_smul, smul_eq_zero, smul_eq_zero]`. Simplify using `[hv, hw]`. Establish `hXY : (Matrix.of fun k (_ : Fin 1) => w k)ᵀ * B * (Matrix.of fun k (_ : Fin 1) => w k).map (starRingEnd ℂ) = (Matrix.of fun k (_ : Fin 1) => v k)ᵀ * B * (Matrix.of fun k (_ : Fin 1) => v k).map (starRingEnd ℂ)`. Use extensionality with `i j`. Rewrite using `[transpose_col_mul_mul_map_conj_apply, transpose_col_mul_mul_map_conj_apply, h]`.

Take `⟨γ, hγ, hγX⟩` from `GlobalTheory.HermWitt.exists_gl_isometry_mul_eq two_ne_zero (fun t => Complex.conj_conj t) hG hdet h0 hXY`. Use `⟨γ, hγ, ?_⟩` and prove the remaining obligations. Rewrite `hγX` using `[mul_of_col_eq_of_mulVec]`. Use function extensionality and compare the values at `i`. Simplify using `using congrFun (congrFun hγX i) 0`.
-/
theorem exists_unitary_mulVec_eq {B : Matrix (Fin r) (Fin r) ℂ} (hB : B.IsHermitian)
    (hdet : B.det ≠ 0) {v w : Fin r → ℂ} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : w ⬝ᵥ B *ᵥ star w = v ⬝ᵥ B *ᵥ star v) :
    ∃ g : Matrix (Fin r) (Fin r) ℂ, gᵀ * B * g.map (starRingEnd ℂ) = B ∧ g *ᵥ v = w := by
  have hG : ∀ a b, starRingEnd ℂ (B a b) = B b a := fun a b => by
    rw [starRingEnd_apply]
    exact hB.apply b a
  have h0 : ∀ a : Fin 1 → ℂ, (Matrix.of fun k (_ : Fin 1) => v k) *ᵥ a = 0 ↔
      (Matrix.of fun k (_ : Fin 1) => w k) *ᵥ a = 0 := by
    intro a
    rw [of_col_mulVec_eq_smul, of_col_mulVec_eq_smul, smul_eq_zero, smul_eq_zero]
    simp [hv, hw]
  have hXY : (Matrix.of fun k (_ : Fin 1) => w k)ᵀ * B *
        (Matrix.of fun k (_ : Fin 1) => w k).map (starRingEnd ℂ) =
      (Matrix.of fun k (_ : Fin 1) => v k)ᵀ * B *
        (Matrix.of fun k (_ : Fin 1) => v k).map (starRingEnd ℂ) := by
    ext i j
    rw [transpose_col_mul_mul_map_conj_apply, transpose_col_mul_mul_map_conj_apply, h]
  obtain ⟨γ, hγ, hγX⟩ := GlobalTheory.HermWitt.exists_gl_isometry_mul_eq two_ne_zero
    (fun t => Complex.conj_conj t) hG hdet h0 hXY
  refine ⟨γ, hγ, ?_⟩
  rw [mul_of_col_eq_of_mulVec] at hγX
  funext i
  simpa using congrFun (congrFun hγX i) 0

/- English proof (translation)
Simplify using `only [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma dotProduct_mulVec_star_real_smul (C : Matrix (Fin r) (Fin r) ℂ) (a : ℝ) (x : Fin r → ℂ) :
    ((a : ℂ) • x) ⬝ᵥ C *ᵥ star ((a : ℂ) • x) = ((a ^ 2 : ℝ) : ℂ) * (x ⬝ᵥ C *ᵥ star x) := by
  simp only [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

/- English proof (translation)
Introduce `r A B v hA hB hdet hh`. Establish `hid : (1 : Matrix (Fin r) (Fin r) ℂ)ᵀ * B * (1 : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = B`. Simplify using the standard rewrite rules. Establish `hv : v ≠ 0`. Introduce and unpack `rfl`.

Use `hh 1 hid` as an intermediate fact. Simplify using `at this`. Establish `hAre` using `dotProduct_star_eq_re hA`. Establish `hBre` using `dotProduct_star_eq_re hB`. Establish `horb : ∀ w : Fin r → ℂ, w ≠ 0 → (w ⬝ᵥ B *ᵥ star w).re = (v ⬝ᵥ B *ᵥ star v).re → |(w ⬝ᵥ A *ᵥ star w).re| = 1`.

Introduce `w hw hwv`. Establish `hQ : w ⬝ᵥ B *ᵥ star w = v ⬝ᵥ B *ᵥ star v`. Rewrite using `[hBre w, hBre v, hwv]`. Take `⟨g, hg, rfl⟩` from `exists_unitary_mulVec_eq hB hdet hv hw hQ`. Use `hh g hg` as an intermediate fact.

Rewrite `this` using `[hAre (g *ᵥ v), Complex.norm_real, Real.norm_eq_abs]`. Then use the resulting hypothesis. Establish `hsr : |(v ⬝ᵥ A *ᵥ star v).re| = 1` using `horb v hv rfl`. Establish `hcr : (v ⬝ᵥ B *ᵥ star v).re ≠ 0`. Introduce `h0`. Establish `e` using `horb (((2 : ℝ) : ℂ) • v) (smul_ne_zero (by norm_num) hv) (by rw [dotProduct_mulVec_star_real_smul, Complex.re_ofReal_mul, h0, mul_zero])`.

Rewrite `e` using `[dotProduct_mulVec_star_real_smul, Complex.re_ofReal_mul, abs_mul, hsr]`. Evaluate the numerical expressions using `at e`. Use `set cr := (v ⬝ᵥ B *ᵥ star v).re with hcr_def`. Use `set sr := (v ⬝ᵥ A *ᵥ star v).re with hsr_def`. Establish `hcont : ∀ M : Matrix (Fin r) (Fin r) ℂ, Continuous fun w : Fin r → ℂ => (w ⬝ᵥ M *ᵥ star w).re` using `fun M => Complex.continuous_re.comp (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_star))`.

Establish `hφ : Filter.Tendsto (fun w : Fin r → ℂ => (w ⬝ᵥ A *ᵥ star w).re * cr / (w ⬝ᵥ B *ᵥ star w).re) (𝓝 v) (𝓝 sr)`. Establish `h : ContinuousAt (fun w : Fin r → ℂ => (w ⬝ᵥ A *ᵥ star w).re * cr / (w ⬝ᵥ B *ᵥ star w).re) v` using `((hcont A).continuousAt.mul (continuousAt_const (y := cr))).div (hcont B).continuousAt hcr`. Establish `h2 : Filter.Tendsto (fun w : Fin r → ℂ => (w ⬝ᵥ A *ᵥ star w).re * cr / (w ⬝ᵥ B *ᵥ star w).re) (𝓝 v) (𝓝 (sr * cr / cr))` using `h.tendsto`. Establish `hval : sr * cr / cr = sr` using `by field_simp`. Rewrite `h2` using `[hval]`. Then use the resulting hypothesis.

Establish `E1 : ∀ᶠ w in 𝓝 v, w ≠ 0` using `eventually_ne_nhds hv`. Establish `E2 : ∀ᶠ w in 𝓝 v, 0 < (w ⬝ᵥ B *ᵥ star w).re * cr` using `continuousAt_const.eventually_lt ((hcont B).continuousAt.mul continuousAt_const) (mul_self_pos.mpr hcr)`. Establish `E3` using `hφ.eventually (Ioo_mem_nhds (show sr - 1 < sr by linarith) (show sr < sr + 1 by linarith))`. Establish `key : ∀ᶠ w in 𝓝 v, w ⬝ᵥ (A - ((sr / cr : ℝ) : ℂ) • B) *ᵥ star w = 0` using `by filter_upwards [E1, E2, E3] with w hw hpos hI`. Take `⟨hI1, hI2⟩` from `hI`.

Establish `hqB : (w ⬝ᵥ B *ᵥ star w).re ≠ 0`. Introduce and unpack `h0`. Rewrite `hpos` using `[h0, zero_mul]`. Conclude with `lt_irrefl _ hpos`. Establish `hq : 0 < cr / (w ⬝ᵥ B *ᵥ star w).re`.

Break down `mul_pos_iff.mp hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩` into its components or cases. Conclude with `div_pos h2 h1`. Conclude with `div_pos_of_neg_of_neg h2 h1`. Establish `ha2 : Real.sqrt (cr / (w ⬝ᵥ B *ᵥ star w).re) ^ 2 = cr / (w ⬝ᵥ B *ᵥ star w).re` using `Real.sq_sqrt hq.le`. Establish `ha : Real.sqrt (cr / (w ⬝ᵥ B *ᵥ star w).re) ≠ 0` using `(Real.sqrt_pos.mpr hq).ne'`.

Establish `e` using `horb ((Real.sqrt (cr / (w ⬝ᵥ B *ᵥ star w).re) : ℂ) • w) (smul_ne_zero (Complex.ofReal_ne_zero.mpr ha) hw) (by rw [dotProduct_mulVec_star_real_smul, Complex.re_ofReal_mul, ha2]; field_simp)`. Rewrite `e` using `[dotProduct_mulVec_star_real_smul, Complex.re_ofReal_mul, ha2]`. Establish `e' : |(w ⬝ᵥ A *ᵥ star w).re * cr / (w ⬝ᵥ B *ᵥ star w).re| = 1`. Rewrite using `[← e]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hφw : (w ⬝ᵥ A *ᵥ star w).re * cr / (w ⬝ᵥ B *ᵥ star w).re = sr`. Apply the tactic sequence `rcases (abs_eq zero_le_one).mp e' with h1 | h1 <;>`. Apply the tactic sequence `rcases (abs_eq zero_le_one).mp hsr with h2 | h2 <;> linarith [hI1, hI2]`. Establish `hreal : (w ⬝ᵥ A *ᵥ star w).re - sr / cr * (w ⬝ᵥ B *ᵥ star w).re = 0`.

Establish `h` using `hφw`. Clear denominators, using `at h ⊢` for the nonvanishing conditions. Take the linear combination `h`. Rewrite using `[sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul, hAre w, hBre w, ← Complex.ofReal_mul, ← Complex.ofReal_sub, hreal, Complex.ofReal_zero]`. Establish `hC` using `eq_zero_of_eventually_dotProduct_star_eq_zero key`.

Use `⟨sr / cr, div_ne_zero ?_ hcr, sub_eq_zero.mp hC⟩` and prove the remaining obligations. Introduce `h0`. Rewrite `hsr` using `[h0, abs_zero]`. Conclude with `zero_ne_one hsr`.
-/
theorem eq_smul_of_norm_eq_one_on_orbit :
    ∀ (r : ℕ) (A B : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ), A.IsHermitian → B.IsHermitian →
      B.det ≠ 0 → (∀ h : Matrix (Fin r) (Fin r) ℂ, hᵀ * B * h.map (starRingEnd ℂ) = B →
        ‖(h *ᵥ v) ⬝ᵥ (A *ᵥ star (h *ᵥ v))‖ = 1) → ∃ t : ℝ, t ≠ 0 ∧ A = (t : ℂ) • B := by
  intro r A B v hA hB hdet hh
  have hid : (1 : Matrix (Fin r) (Fin r) ℂ)ᵀ * B * (1 : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) =
      B := by
    simp
  have hv : v ≠ 0 := by
    rintro rfl
    have := hh 1 hid
    simp at this
  have hAre := dotProduct_star_eq_re hA
  have hBre := dotProduct_star_eq_re hB

  have horb : ∀ w : Fin r → ℂ, w ≠ 0 → (w ⬝ᵥ B *ᵥ star w).re = (v ⬝ᵥ B *ᵥ star v).re →
      |(w ⬝ᵥ A *ᵥ star w).re| = 1 := by
    intro w hw hwv
    have hQ : w ⬝ᵥ B *ᵥ star w = v ⬝ᵥ B *ᵥ star v := by
      rw [hBre w, hBre v, hwv]
    obtain ⟨g, hg, rfl⟩ := exists_unitary_mulVec_eq hB hdet hv hw hQ
    have := hh g hg
    rwa [hAre (g *ᵥ v), Complex.norm_real, Real.norm_eq_abs] at this
  have hsr : |(v ⬝ᵥ A *ᵥ star v).re| = 1 := horb v hv rfl

  have hcr : (v ⬝ᵥ B *ᵥ star v).re ≠ 0 := by
    intro h0
    have e := horb (((2 : ℝ) : ℂ) • v) (smul_ne_zero (by norm_num) hv)
      (by rw [dotProduct_mulVec_star_real_smul, Complex.re_ofReal_mul, h0, mul_zero])
    rw [dotProduct_mulVec_star_real_smul, Complex.re_ofReal_mul, abs_mul, hsr] at e
    norm_num at e
  set cr := (v ⬝ᵥ B *ᵥ star v).re with hcr_def
  set sr := (v ⬝ᵥ A *ᵥ star v).re with hsr_def
  have hcont : ∀ M : Matrix (Fin r) (Fin r) ℂ,
      Continuous fun w : Fin r → ℂ => (w ⬝ᵥ M *ᵥ star w).re := fun M =>
    Complex.continuous_re.comp
      (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_star))

  have hφ : Filter.Tendsto (fun w : Fin r → ℂ =>
      (w ⬝ᵥ A *ᵥ star w).re * cr / (w ⬝ᵥ B *ᵥ star w).re) (𝓝 v) (𝓝 sr) := by
    have h : ContinuousAt (fun w : Fin r → ℂ =>
        (w ⬝ᵥ A *ᵥ star w).re * cr / (w ⬝ᵥ B *ᵥ star w).re) v :=
      ((hcont A).continuousAt.mul (continuousAt_const (y := cr))).div (hcont B).continuousAt hcr
    have h2 : Filter.Tendsto (fun w : Fin r → ℂ =>
        (w ⬝ᵥ A *ᵥ star w).re * cr / (w ⬝ᵥ B *ᵥ star w).re) (𝓝 v) (𝓝 (sr * cr / cr)) := h.tendsto
    have hval : sr * cr / cr = sr := by field_simp
    rwa [hval] at h2
  have E1 : ∀ᶠ w in 𝓝 v, w ≠ 0 := eventually_ne_nhds hv
  have E2 : ∀ᶠ w in 𝓝 v, 0 < (w ⬝ᵥ B *ᵥ star w).re * cr :=
    continuousAt_const.eventually_lt ((hcont B).continuousAt.mul continuousAt_const)
      (mul_self_pos.mpr hcr)
  have E3 := hφ.eventually (Ioo_mem_nhds (show sr - 1 < sr by linarith) (show sr < sr + 1 by linarith))
  have key : ∀ᶠ w in 𝓝 v, w ⬝ᵥ (A - ((sr / cr : ℝ) : ℂ) • B) *ᵥ star w = 0 := by
    filter_upwards [E1, E2, E3] with w hw hpos hI
    obtain ⟨hI1, hI2⟩ := hI
    have hqB : (w ⬝ᵥ B *ᵥ star w).re ≠ 0 := by
      rintro h0
      rw [h0, zero_mul] at hpos
      exact lt_irrefl _ hpos
    have hq : 0 < cr / (w ⬝ᵥ B *ᵥ star w).re := by
      rcases mul_pos_iff.mp hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact div_pos h2 h1
      · exact div_pos_of_neg_of_neg h2 h1
    have ha2 : Real.sqrt (cr / (w ⬝ᵥ B *ᵥ star w).re) ^ 2 = cr / (w ⬝ᵥ B *ᵥ star w).re :=
      Real.sq_sqrt hq.le
    have ha : Real.sqrt (cr / (w ⬝ᵥ B *ᵥ star w).re) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'

    have e := horb ((Real.sqrt (cr / (w ⬝ᵥ B *ᵥ star w).re) : ℂ) • w)
      (smul_ne_zero (Complex.ofReal_ne_zero.mpr ha) hw)
      (by rw [dotProduct_mulVec_star_real_smul, Complex.re_ofReal_mul, ha2]; field_simp)
    rw [dotProduct_mulVec_star_real_smul, Complex.re_ofReal_mul, ha2] at e
    have e' : |(w ⬝ᵥ A *ᵥ star w).re * cr / (w ⬝ᵥ B *ᵥ star w).re| = 1 := by
      rw [← e]
      congr 1
      ring
    have hφw : (w ⬝ᵥ A *ᵥ star w).re * cr / (w ⬝ᵥ B *ᵥ star w).re = sr := by
      rcases (abs_eq zero_le_one).mp e' with h1 | h1 <;>
        rcases (abs_eq zero_le_one).mp hsr with h2 | h2 <;> linarith [hI1, hI2]
    have hreal : (w ⬝ᵥ A *ᵥ star w).re - sr / cr * (w ⬝ᵥ B *ᵥ star w).re = 0 := by
      have h := hφw
      field_simp at h ⊢
      linear_combination h
    rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul, hAre w, hBre w,
      ← Complex.ofReal_mul, ← Complex.ofReal_sub, hreal, Complex.ofReal_zero]
  have hC := eq_zero_of_eventually_dotProduct_star_eq_zero key
  refine ⟨sr / cr, div_ne_zero ?_ hcr, sub_eq_zero.mp hC⟩
  intro h0
  rw [h0, abs_zero] at hsr
  exact zero_ne_one hsr

end GlobalTheory.UnitaryOrbitForm
