import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvSubOneMem
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.GaugeSubLip

open Formalism.REAL GlobalTheory.GaugeSubLoc

variable {n d : ℕ}

def trForm (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun X Y => ((X * Yᴴ).trace).re)
    (fun X X' Y => by rw [Matrix.add_mul, Matrix.trace_add, Complex.add_re])
    (fun c X Y => by rw [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re])
    (fun X Y Y' => by
      rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.trace_add, Complex.add_re])
    (fun c X Y => by
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.trace_smul,
        Complex.smul_re])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem trForm_apply (X Y : Matrix (Fin n) (Fin n) ℂ) : trForm n X Y = ((X * Yᴴ).trace).re := rfl

/- English proof (translation)
Establish `: Y * Xᴴ = (X * Yᴴ)ᴴ` using `by rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]`. Rewrite using `[trForm_apply, trForm_apply, this, Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re]`.
-/
theorem trForm_comm (X Y : Matrix (Fin n) (Fin n) ℂ) : trForm n X Y = trForm n Y X := by
  have : Y * Xᴴ = (X * Yᴴ)ᴴ := by rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [trForm_apply, trForm_apply, this, Matrix.trace_conjTranspose, Complex.star_def,
    Complex.conj_re]

/- English proof (translation)
Simplify using `only [trForm_apply, hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `norm_cast`.
-/
theorem hs_eq (g : Matrix (Fin n) (Fin n) ℂ) : hs g = trForm n g g := by
  simp only [trForm_apply, hs, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

/- English proof (translation)
Unfold `hs`. Check the signs of the components of the expression.
-/
theorem hs_nonneg (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs g := by
  unfold hs; positivity

def coord (E : Fin d → Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun X := WithLp.toLp 2 (fun i => trForm n X (E i))
  map_add' X Y := by ext i; simp
  map_smul' c X := by ext i; simp

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_eq]`. Simplify using `[coord]`.
-/
theorem norm_coord (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖coord E X‖ = Real.sqrt (∑ i, trForm n X (E i) ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [coord]

/- English proof (translation)
Simplify using `[map_sum, LinearMap.sum_apply, hE]`.
-/
theorem trForm_sum (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i k, trForm n (E i) (E k) = if i = k then 1 else 0) (a : Fin d → ℝ) (k : Fin d) :
    trForm n (∑ i, a i • E i) (E k) = a k := by
  simp [map_sum, LinearMap.sum_apply, hE]

/- English proof (translation)
Rewrite using `[hs_eq, map_sum (trForm n (∑ i, a i • E i))]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, trForm_sum E hE, smul_eq_mul, sq]`.
-/
theorem hs_sum (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i k, trForm n (E i) (E k) = if i = k then 1 else 0) (a : Fin d → ℝ) :
    hs (∑ i, a i • E i) = ∑ i, a i ^ 2 := by
  rw [hs_eq, map_sum (trForm n (∑ i, a i • E i))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, trForm_sum E hE, smul_eq_mul, sq]

/- English proof (translation)
Rewrite using `[norm_coord]`. Apply `Real.sqrt_le_sqrt` to reduce the goal to its premises. Use `set S := ∑ i, trForm n X (E i) • E i with hS`. Establish `h1 : trForm n S S = ∑ i, trForm n X (E i) ^ 2` using `by rw [← hs_eq, hS, hs_sum E hE]`. Establish `h2 : trForm n X S = ∑ i, trForm n X (E i) ^ 2`.

Rewrite using `[hS, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, sq]`. Establish `h3` using `hs_nonneg (X - S)`. Rewrite `h3` using `[hs_eq, map_sub, LinearMap.map_sub₂, LinearMap.map_sub₂, trForm_comm S X, h1, h2]`.

Rewrite using `[hs_eq]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bessel (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i k, trForm n (E i) (E k) = if i = k then 1 else 0) (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖coord E X‖ ≤ Real.sqrt (hs X) := by
  rw [norm_coord]
  apply Real.sqrt_le_sqrt
  set S := ∑ i, trForm n X (E i) • E i with hS
  have h1 : trForm n S S = ∑ i, trForm n X (E i) ^ 2 := by rw [← hs_eq, hS, hs_sum E hE]
  have h2 : trForm n X S = ∑ i, trForm n X (E i) ^ 2 := by
    rw [hS, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, sq]
  have h3 := hs_nonneg (X - S)
  rw [hs_eq, map_sub, LinearMap.map_sub₂, LinearMap.map_sub₂, trForm_comm S X, h1, h2] at h3
  rw [hs_eq]
  linarith

/- English proof (translation)
Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℝ).1 hX`. Rewrite using `[norm_coord, hs_sum E hE]`. Simplify using `only [trForm_sum E hE]`.
-/
theorem norm_coord_span (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i k, trForm n (E i) (E k) = if i = k then 1 else 0) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : X ∈ Submodule.span ℝ (Set.range E)) : ‖coord E X‖ = Real.sqrt (hs X) := by
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hX
  rw [norm_coord, hs_sum E hE]
  simp only [trForm_sum E hE]

variable {ε : Fin n → Bool}

/- English proof (translation)
Establish `hu : (uMat g)ᴴ * Jm ε * uMat g = Jm ε` using `g.2`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem uMat_inv (g : UJ ε) : uMat g⁻¹ = Jm ε * (uMat g)ᴴ * Jm ε := by
  have hu : (uMat g)ᴴ * Jm ε * uMat g = Jm ε := g.2
  calc uMat g⁻¹ = Jm ε * Jm ε * uMat g⁻¹ := by rw [Jm_mul_self, Matrix.one_mul]
    _ = Jm ε * ((uMat g)ᴴ * Jm ε * uMat g) * uMat g⁻¹ := by rw [hu]
    _ = Jm ε * (uMat g)ᴴ * Jm ε * (uMat g * uMat g⁻¹) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [uMat_mul_inv, Matrix.mul_one]

/- English proof (translation)
Establish `h1 : uMat g⁻¹ - 1 = Jm ε * (uMat g - 1)ᴴ * Jm ε`. Rewrite using `[uMat_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Jm_mul_self]`. Rewrite using `[h1, hs_eq, hs_eq, trForm_apply, trForm_apply]`. Use `set X := uMat g - 1`. Establish `h2 : Jm ε * Xᴴ * Jm ε * (Jm ε * Xᴴ * Jm ε)ᴴ = Jm ε * (Xᴴ * (Jm ε * Jm ε) * X * Jm ε)`.

Simplify using `only [Matrix.conjTranspose_mul, Jm_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]`. Rewrite using `[h2, Jm_mul_self, Matrix.mul_one, Matrix.trace_mul_comm, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one, Matrix.trace_mul_comm]`.
-/
theorem hs_inv_sub_one (g : UJ ε) : hs (uMat g⁻¹ - 1) = hs (uMat g - 1) := by
  have h1 : uMat g⁻¹ - 1 = Jm ε * (uMat g - 1)ᴴ * Jm ε := by
    rw [uMat_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, Jm_mul_self]
  rw [h1, hs_eq, hs_eq, trForm_apply, trForm_apply]
  set X := uMat g - 1
  have h2 : Jm ε * Xᴴ * Jm ε * (Jm ε * Xᴴ * Jm ε)ᴴ = Jm ε * (Xᴴ * (Jm ε * Jm ε) * X * Jm ε) := by
    simp only [Matrix.conjTranspose_mul, Jm_conjTranspose, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  rw [h2, Jm_mul_self, Matrix.mul_one, Matrix.trace_mul_comm, Matrix.mul_assoc, Jm_mul_self,
    Matrix.mul_one, Matrix.trace_mul_comm]

/- English proof (translation)
Rewrite using `[GlobalTheory.GaugeConst.mem_lieJ, uMat_inv]`. Simplify using `only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Jm_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]`. Rewrite using `[← Matrix.mul_assoc (Jm ε) (Jm ε), Jm_mul_self, Matrix.one_mul]`. Normalize the expressions using the abelian group laws.
-/
theorem sub_inv_mem_lie (g : UJ ε) : uMat g - uMat g⁻¹ ∈ GlobalTheory.GaugeConst.lieJ ε := by
  rw [GlobalTheory.GaugeConst.mem_lieJ, uMat_inv]
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Jm_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc,
    Jm_mul_self, Matrix.mul_one]
  rw [← Matrix.mul_assoc (Jm ε) (Jm ε), Jm_mul_self, Matrix.one_mul]
  abel

open scoped Matrix.Norms.Frobenius in
/- English proof (translation)
Establish `key : ∀ g : UJ ε, uMat g - 1 ∈ A → uMat g - uMat g⁻¹ ∈ Submodule.span ℝ (Set.range E)`. Introduce `g hg`. Use `(hsp _).1 ⟨?_, sub_inv_mem_lie g⟩` and prove the remaining obligations. Use `A.sub_mem hg (inv_sub_one_mem A hA g hg)` as an intermediate fact. Rewrite `this` using `[sub_sub_sub_cancel_right]`. Then use the resulting hypothesis.

Establish `hv` using `Submodule.sub_mem _ (key g hg) (key h hh)`. Rewrite `hg'`, `hh'` using `[← hs_inv_sub_one, GlobalTheory.GaugeConst.sqrt_hs]`. Establish `e1 : uMat g⁻¹ * (uMat g - uMat h) * uMat h⁻¹ = uMat h⁻¹ - uMat g⁻¹`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, uMat_inv_mul, Matrix.one_mul, Matrix.mul_assoc, uMat_mul_inv, Matrix.mul_one]`. Use `set v := uMat g - uMat g⁻¹ - (uMat h - uMat h⁻¹) with hvdef`.

Use `set D := uMat g - uMat h with hD`. Use `set a := uMat g⁻¹ - 1 with ha`. Use `set b := uMat h⁻¹ - 1 with hb`. Establish `e2 : v = (2 : ℝ) • D + (a * D * b + a * D + D * b)`. Establish `: a * D * b + a * D + D * b = uMat g⁻¹ * D * uMat h⁻¹ - D`.

Rewrite using `[ha, hb]`. Use `noncomm_ring`. Rewrite using `[this, e1, hvdef, hD, two_smul]`. Normalize the expressions using the abelian group laws. Use `set R := a * D * b + a * D + D * b with hR`.

Establish `ha0` using `norm_nonneg a`. Establish `hb0` using `norm_nonneg b`. Establish `hD0` using `norm_nonneg D`. Establish `n1 : ‖a * D‖ ≤ δ * ‖D‖` using `(Matrix.frobenius_norm_mul a D).trans (mul_le_mul_of_nonneg_right hg'.le hD0)`. Establish `n2 : ‖D * b‖ ≤ ‖D‖ * δ` using `(Matrix.frobenius_norm_mul D b).trans (mul_le_mul_of_nonneg_left hh'.le hD0)`.

Establish `n3 : ‖a * D * b‖ ≤ δ * ‖D‖` using `(Matrix.frobenius_norm_mul _ b).trans ((mul_le_of_le_one_right (norm_nonneg _) (hh'.le.trans hδ)).trans n1)`. Establish `n4 : ‖R‖ ≤ 3 * δ * ‖D‖`. Use `norm_add₃_le (a := a * D * b) (b := a * D) (c := D * b)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `p1` using `norm_coord_span E hE v hv`.

Establish `p2` using `bessel E hE R`. Rewrite `p1`, `p2`, the goal using `[GlobalTheory.GaugeConst.sqrt_hs]`. Establish `p3 : ‖coord E v‖ ≤ 2 * ‖coord E D‖ + ‖coord E R‖`. Rewrite using `[e2, map_add, map_smul]`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[norm_smul, Real.norm_two]`. Establish `p4 : 2 * ‖D‖ ≤ ‖v‖ + ‖R‖`. Establish `: (2 : ℝ) • D = v - R` using `by rw [e2, add_sub_cancel_right]`. Establish `h5` using `norm_sub_le v R`. Rewrite `h5` using `[← this, norm_smul, Real.norm_two]`. Then use the resulting hypothesis.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lower (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A)
    (hE : ∀ i k, trForm n (E i) (E k) = if i = k then 1 else 0)
    (hsp : ∀ X, (X ∈ A ∧ inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) (δ : ℝ) (hδ : δ ≤ 1)
    (g h : UJ ε) (hg : uMat g - 1 ∈ A) (hh : uMat h - 1 ∈ A)
    (hg' : Real.sqrt (hs (uMat g - 1)) < δ) (hh' : Real.sqrt (hs (uMat h - 1)) < δ) :
    (1 - 3 * δ) * Real.sqrt (hs (uMat g - uMat h)) ≤ ‖coord E (uMat g - uMat h)‖ := by
  have key : ∀ g : UJ ε, uMat g - 1 ∈ A →
      uMat g - uMat g⁻¹ ∈ Submodule.span ℝ (Set.range E) := by
    intro g hg
    refine (hsp _).1 ⟨?_, sub_inv_mem_lie g⟩
    have := A.sub_mem hg (inv_sub_one_mem A hA g hg)
    rwa [sub_sub_sub_cancel_right] at this
  have hv := Submodule.sub_mem _ (key g hg) (key h hh)
  rw [← hs_inv_sub_one, GlobalTheory.GaugeConst.sqrt_hs] at hg' hh'
  have e1 : uMat g⁻¹ * (uMat g - uMat h) * uMat h⁻¹ = uMat h⁻¹ - uMat g⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, uMat_inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      uMat_mul_inv, Matrix.mul_one]
  set v := uMat g - uMat g⁻¹ - (uMat h - uMat h⁻¹) with hvdef
  set D := uMat g - uMat h with hD
  set a := uMat g⁻¹ - 1 with ha
  set b := uMat h⁻¹ - 1 with hb
  have e2 : v = (2 : ℝ) • D + (a * D * b + a * D + D * b) := by
    have : a * D * b + a * D + D * b = uMat g⁻¹ * D * uMat h⁻¹ - D := by
      rw [ha, hb]; noncomm_ring
    rw [this, e1, hvdef, hD, two_smul]; abel
  set R := a * D * b + a * D + D * b with hR
  have ha0 := norm_nonneg a
  have hb0 := norm_nonneg b
  have hD0 := norm_nonneg D
  have n1 : ‖a * D‖ ≤ δ * ‖D‖ :=
    (Matrix.frobenius_norm_mul a D).trans (mul_le_mul_of_nonneg_right hg'.le hD0)
  have n2 : ‖D * b‖ ≤ ‖D‖ * δ :=
    (Matrix.frobenius_norm_mul D b).trans (mul_le_mul_of_nonneg_left hh'.le hD0)
  have n3 : ‖a * D * b‖ ≤ δ * ‖D‖ :=
    (Matrix.frobenius_norm_mul _ b).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (hh'.le.trans hδ)).trans n1)
  have n4 : ‖R‖ ≤ 3 * δ * ‖D‖ := by
    have := norm_add₃_le (a := a * D * b) (b := a * D) (c := D * b)
    linarith
  have p1 := norm_coord_span E hE v hv
  have p2 := bessel E hE R
  rw [GlobalTheory.GaugeConst.sqrt_hs] at p1 p2 ⊢
  have p3 : ‖coord E v‖ ≤ 2 * ‖coord E D‖ + ‖coord E R‖ := by
    rw [e2, map_add, map_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_two]
  have p4 : 2 * ‖D‖ ≤ ‖v‖ + ‖R‖ := by
    have : (2 : ℝ) • D = v - R := by rw [e2, add_sub_cancel_right]
    have h5 := norm_sub_le v R
    rwa [← this, norm_smul, Real.norm_two] at h5
  linarith

/- English proof (translation)
Introduce `n ε A d E hA hE hsp κ hκ`. Establish `hk : κ⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hκ`. Establish `hk0 : 0 < κ⁻¹` using `inv_pos.2 (by linarith)`. Use `⟨(1 - κ⁻¹) / 3, by linarith, fun g h hg hh hg' hh' => ?_⟩` and prove the remaining obligations. Establish `e : (WithLp.toLp 2 (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d)) - (WithLp.toLp 2 (fun i => (((uMat h - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d)) = coord E (uMat g - uMat h)`.

Express the relevant statement in the definitionally equal form `coord E (uMat g - 1) - coord E (uMat h - 1) = _`. Rewrite using `[← map_sub, sub_sub_sub_cancel_right]`. Rewrite using `[e]`. Use `⟨bessel E hE _, ?_⟩` and prove the remaining obligations. Establish `h1` using `lower A E hA hE hsp _ (by linarith) g h hg hh hg' hh'`.

Establish `h2 : 1 - 3 * ((1 - κ⁻¹) / 3) = κ⁻¹` using `by ring`. Rewrite `h1` using `[h2]`. Conclude with `(inv_mul_le_iff₀ (by linarith)).1 h1`.
-/
theorem chart_almost_isometric : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∀ κ : ℝ, 1 < κ → ∃ δ : ℝ, 0 < δ ∧ ∀ g h : Formalism.REAL.UJ ε, uMat g - 1 ∈ A → uMat h - 1 ∈ A → Real.sqrt (Formalism.REAL.hs (uMat g - 1)) < δ → Real.sqrt (Formalism.REAL.hs (uMat h - 1)) < δ → ‖(WithLp.toLp 2 (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d)) - (WithLp.toLp 2 (fun i => (((uMat h - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d))‖ ≤ Real.sqrt (Formalism.REAL.hs (uMat g - uMat h)) ∧ Real.sqrt (Formalism.REAL.hs (uMat g - uMat h)) ≤ κ * ‖(WithLp.toLp 2 (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d)) - (WithLp.toLp 2 (fun i => (((uMat h - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d))‖ := by
  intro n ε A d E hA hE hsp κ hκ
  have hk : κ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hκ
  have hk0 : 0 < κ⁻¹ := inv_pos.2 (by linarith)
  refine ⟨(1 - κ⁻¹) / 3, by linarith, fun g h hg hh hg' hh' => ?_⟩
  have e : (WithLp.toLp 2 (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d)) - (WithLp.toLp 2 (fun i => (((uMat h - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d)) = coord E (uMat g - uMat h) := by
    change coord E (uMat g - 1) - coord E (uMat h - 1) = _
    rw [← map_sub, sub_sub_sub_cancel_right]
  rw [e]
  refine ⟨bessel E hE _, ?_⟩
  have h1 := lower A E hA hE hsp _ (by linarith) g h hg hh hg' hh'
  have h2 : 1 - 3 * ((1 - κ⁻¹) / 3) = κ⁻¹ := by ring
  rw [h2] at h1
  exact (inv_mul_le_iff₀ (by linarith)).1 h1

end GlobalTheory.GaugeSubLip
