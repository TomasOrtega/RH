import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ActLPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeightContinuity.MatrixTupleDistortionBoundOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Detlow

open NumberField Matrix UpperTheory.V.KT Filter Topology
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.KB.HeightDistance

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

def tv (B : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ) (y : Lat L N) : ℝ :=
  ∑ w, nsq (B w *ᵥ toR y w)

def lm (B : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ⨅ y : {y : Lat L N // y ≠ 0}, tv B y.1

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun _ _ => nsq_nonneg _`.
-/
theorem tv_nonneg (B : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ) (y : Lat L N) : 0 ≤ tv B y :=
  Finset.sum_nonneg fun _ _ => nsq_nonneg _

/- English proof (translation)
The claim follows from `ciInf_le ⟨0, by rintro _ ⟨z, rfl⟩; exact tv_nonneg B z.1⟩ y`.
-/
theorem lm_le (B : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ) (y : {y : Lat L N // y ≠ 0}) :
    lm B ≤ tv B y.1 :=
  ciInf_le ⟨0, by rintro _ ⟨z, rfl⟩; exact tv_nonneg B z.1⟩ y

/- English proof (translation)
Use `⟨⟨fun _ => (1 : 𝓞 L), fun h => ?_⟩⟩` and prove the remaining obligations. Use `congrArg (fun f : Fin N → 𝓞 L => f ⟨0, hN⟩) h` as an intermediate fact. Simplify using `at this`.
-/
theorem nonempty_ne (hN : 1 ≤ N) : Nonempty {y : Lat L N // y ≠ 0} := by
  refine ⟨⟨fun _ => (1 : 𝓞 L), fun h => ?_⟩⟩
  have := congrArg (fun f : Fin N → 𝓞 L => f ⟨0, hN⟩) h
  simp at this

/- English proof (translation)
Use `haveI := nonempty_ne (L := L) hN`. Conclude with `le_ciInf fun y => h y.1 y.2`.
-/
theorem le_lm (hN : 1 ≤ N) {B : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ} {t : ℝ}
    (h : ∀ y : Lat L N, y ≠ 0 → t ≤ tv B y) : t ≤ lm B := by
  haveI := nonempty_ne (L := L) hN
  exact le_ciInf fun y => h y.1 y.2

/- English proof (translation)
Rewrite using `[← div_le_iff₀' hc]`. Apply `le_lm hN` to reduce the goal to its premises. Introduce `y hy`. Rewrite using `[div_le_iff₀' hc]`. Conclude with `(lm_le B ⟨y, hy⟩).trans (h y)`.
-/
theorem lm_mono (hN : 1 ≤ N) {B B' : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ} {c : ℝ}
    (hc : 0 < c) (h : ∀ y : Lat L N, tv B y ≤ c * tv B' y) : lm B ≤ c * lm B' := by
  rw [← div_le_iff₀' hc]
  apply le_lm hN
  intro y hy
  rw [div_le_iff₀' hc]
  exact (lm_le B ⟨y, hy⟩).trans (h y)

/- English proof (translation)
The claim follows from `lt_of_lt_of_le one_pos (one_le_dist1 A)`.
-/
theorem matrixTupleDistortion_pos {ι : Type} [Fintype ι] (A : ι → Matrix (Fin N) (Fin N) ℂ) : 0 < dist1 A :=
  lt_of_lt_of_le one_pos (one_le_dist1 A)

/- English proof (translation)
Establish `hE : ∀ u : Fin N → ℂ, nsq u = ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin N))‖ ^ 2` using `fun u => by`. Rewrite using `[EuclideanSpace.norm_sq_eq]`. Both sides reduce to the same expression. Establish `hS0 : 0 ≤ ∑ i, ∑ j, ‖M i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖` using `by positivity`. Establish `hv : ∀ j, ‖v j‖ ≤ ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖` using `fun j => by`.

Establish `h2 : ‖v j‖ ^ 2 ≤ ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ ^ 2`. Rewrite using `[← hE]`. Conclude with `Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ j)`. Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2`. Establish `hD : ∀ i, ‖((M - 1) *ᵥ v) i‖ ≤ (∑ j, ‖M i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖) * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖` using `fun i => by`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.sub_apply]`. Use `_ ≤ ∑ j, ‖(M i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j) * v j‖ := norm_sum_le _ _`. Use `_ ≤ ∑ j, ‖M i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖ * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ := Finset.sum_le_sum fun j _ => by`. Rewrite using `[norm_mul]`.

Conclude with `mul_le_mul_of_nonneg_left (hv j) (norm_nonneg _)`. Use `_ = _ := (Finset.sum_mul _ _ _).symm`. Establish `hDn : ‖(WithLp.toLp 2 ((M - 1) *ᵥ v) : EuclideanSpace ℂ (Fin N))‖ ≤ (∑ i, ∑ j, ‖M i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖) * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖`. Rewrite using `[← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hS0 (norm_nonneg _)), ← hE, mul_pow]`. Combine the equalities or inequalities in the displayed calculation.

Unfold `nsq`. Both sides reduce to the same expression. Use `_ ≤ ∑ i, ((∑ j, ‖M i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖) * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖) ^ 2 := Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hD i) 2`. Use `_ = (∑ i, (∑ j, ‖M i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖) ^ 2) * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ ^ 2 := by`. Rewrite using `[Finset.sum_mul]`.

Simplify using `only [mul_pow]`. Use `_ ≤ _ := mul_le_mul_of_nonneg_right (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => by positivity) (by positivity)`. Establish `hMv : M *ᵥ v = v + (M - 1) *ᵥ v`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws.

Rewrite using `[hE, hE v, hMv, WithLp.toLp_add]`. Establish `h1` using `(norm_add_le (WithLp.toLp 2 v) (WithLp.toLp 2 ((M - 1) *ᵥ v))).trans (add_le_add le_rfl hDn)`. Use `(pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (le_of_eq ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem nsq_mulVec_le_one_add_sum_norm_sub_one_sq_mul (M : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    nsq (M *ᵥ v) ≤ (1 + ∑ i, ∑ j, ‖M i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖) ^ 2 * nsq v := by
  have hE : ∀ u : Fin N → ℂ, nsq u = ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin N))‖ ^ 2 := fun u => by
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  have hS0 : 0 ≤ ∑ i, ∑ j, ‖M i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖ := by positivity
  have hv : ∀ j, ‖v j‖ ≤ ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ := fun j => by
    have h2 : ‖v j‖ ^ 2 ≤ ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ ^ 2 := by
      rw [← hE]
      exact Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ j)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  have hD : ∀ i, ‖((M - 1) *ᵥ v) i‖ ≤
      (∑ j, ‖M i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖) * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ := fun i => by
    calc ‖((M - 1) *ᵥ v) i‖ = ‖∑ j, (M i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j) * v j‖ := by
          simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply]
      _ ≤ ∑ j, ‖(M i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j) * v j‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖M i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖ * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ :=
        Finset.sum_le_sum fun j _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hv j) (norm_nonneg _)
      _ = _ := (Finset.sum_mul _ _ _).symm
  have hDn : ‖(WithLp.toLp 2 ((M - 1) *ᵥ v) : EuclideanSpace ℂ (Fin N))‖ ≤
      (∑ i, ∑ j, ‖M i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖) * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hS0 (norm_nonneg _)), ← hE, mul_pow]
    calc nsq ((M - 1) *ᵥ v) = ∑ i, ‖((M - 1) *ᵥ v) i‖ ^ 2 := by
          unfold nsq
          rfl
      _ ≤ ∑ i, ((∑ j, ‖M i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖) * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖) ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hD i) 2
      _ = (∑ i, (∑ j, ‖M i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖) ^ 2) * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ ^ 2 := by
        rw [Finset.sum_mul]
        simp only [mul_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_right
          (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => by positivity) (by positivity)
  have hMv : M *ᵥ v = v + (M - 1) *ᵥ v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  rw [hE, hE v, hMv, WithLp.toLp_add]
  have h1 := (norm_add_le (WithLp.toLp 2 v) (WithLp.toLp 2 ((M - 1) *ᵥ v))).trans (add_le_add le_rfl hDn)
  refine (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (le_of_eq ?_)
  ring

/- English proof (translation)
Apply `lm_mono hN (matrixTupleDistortion_pos A)` to reduce the goal to its premises. Introduce `y`. Unfold `tv`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun w _ => ?_` and prove the remaining obligations.

Rewrite using `[← Matrix.mulVec_mulVec]`. Use `(nsq_mulVec_le_one_add_sum_norm_sub_one_sq_mul (A w) _).trans (mul_le_mul_of_nonneg_right ?_ (nsq_nonneg _))` and prove the remaining obligations. Unfold `dist1`. Use `gcongr`. Conclude with `Finset.single_le_sum (f := fun w => ∑ i, ∑ j, ‖A w i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖) (fun _ _ => by positivity) (Finset.mem_univ w)`.
-/
theorem lm_mul_le (hN : 1 ≤ N) (A B : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ) :
    lm (fun w => A w * B w) ≤ dist1 A * lm B := by
  apply lm_mono hN (matrixTupleDistortion_pos A)
  intro y
  unfold tv
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [← Matrix.mulVec_mulVec]
  refine (nsq_mulVec_le_one_add_sum_norm_sub_one_sq_mul (A w) _).trans (mul_le_mul_of_nonneg_right ?_ (nsq_nonneg _))
  unfold dist1
  gcongr
  exact Finset.single_le_sum (f := fun w => ∑ i, ∑ j, ‖A w i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖)
    (fun _ _ => by positivity) (Finset.mem_univ w)

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `heq : ∀ w : InfinitePlace L, ‖embO w x‖ = w (x : L)`. Introduce `w`. Simplify using `[embO, NumberField.InfinitePlace.norm_embedding_eq]`.

Establish `hnn : ∀ w : InfinitePlace L, 0 ≤ w (x : L)` using `fun w => heq w ▸ norm_nonneg _`. Establish `hlt : ∀ w : InfinitePlace L, w (x : L) < 1`. Introduce `w`. Establish `h1` using `hne w`. Rewrite `h1` using `[heq]`.

Use polynomial arithmetic with `[hnn w]`. Establish `hnorm : (1 : ℝ) ≤ ((|Algebra.norm ℚ (x : L)| : ℚ) : ℝ)`. Rewrite using `[← Algebra.coe_norm_int]`. Establish `: Algebra.norm ℤ x ≠ 0` using `Algebra.norm_ne_zero_iff.mpr hx`. Conclude with `Int.one_le_abs this` after adjusting the coercions.

Rewrite `hnorm` using `[← NumberField.InfinitePlace.prod_eq_abs_norm]`. Take `⟨w0⟩` from `(inferInstance : Nonempty (InfinitePlace L))`. Rewrite `hnorm` using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ w0)]`. Establish `h1 : w0 (x : L) ^ w0.mult < 1` using `pow_lt_one₀ (hnn w0) (hlt w0) (by have := w0.mult_pos; omega)`. Establish `h2 : ∏ w ∈ Finset.univ.erase w0, w (x : L) ^ w.mult ≤ 1` using `Finset.prod_le_one (fun w _ => pow_nonneg (hnn w) _) (fun w _ => pow_le_one₀ (hnn w) (hlt w).le)`.

Establish `h3 : 0 ≤ w0 (x : L) ^ w0.mult` using `pow_nonneg (hnn w0) _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem one_le_norm_place [IsTotallyComplex L] (x : 𝓞 L) (hx : x ≠ 0) :
    ∃ w : InfinitePlace L, 1 ≤ ‖embO w x‖ ^ 2 := by
  classical
  by_contra hne
  push_neg at hne
  have heq : ∀ w : InfinitePlace L, ‖embO w x‖ = w (x : L) := by
    intro w
    simp [embO, NumberField.InfinitePlace.norm_embedding_eq]
  have hnn : ∀ w : InfinitePlace L, 0 ≤ w (x : L) := fun w => heq w ▸ norm_nonneg _
  have hlt : ∀ w : InfinitePlace L, w (x : L) < 1 := by
    intro w
    have h1 := hne w
    rw [heq] at h1
    nlinarith [hnn w]
  have hnorm : (1 : ℝ) ≤ ((|Algebra.norm ℚ (x : L)| : ℚ) : ℝ) := by
    rw [← Algebra.coe_norm_int]
    have : Algebra.norm ℤ x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
    exact_mod_cast Int.one_le_abs this
  rw [← NumberField.InfinitePlace.prod_eq_abs_norm] at hnorm
  obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace L))
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w0)] at hnorm
  have h1 : w0 (x : L) ^ w0.mult < 1 := pow_lt_one₀ (hnn w0) (hlt w0) (by have := w0.mult_pos; omega)
  have h2 : ∏ w ∈ Finset.univ.erase w0, w (x : L) ^ w.mult ≤ 1 :=
    Finset.prod_le_one (fun w _ => pow_nonneg (hnn w) _) (fun w _ => pow_le_one₀ (hnn w) (hlt w).le)
  have h3 : 0 ≤ w0 (x : L) ^ w0.mult := pow_nonneg (hnn w0) _
  nlinarith

/- English proof (translation)
Apply `le_lm hN` to reduce the goal to its premises. Introduce `y hy`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, y i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hy (funext h)`. Take `⟨w, hw⟩` from `one_le_norm_place (y i) hi`. Unfold `tv nsq`. Simplify using `only [Matrix.one_mulVec]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem one_le_lm_one [IsTotallyComplex L] (hN : 1 ≤ N) :
    1 ≤ lm (fun _ : InfinitePlace L => (1 : Matrix (Fin N) (Fin N) ℂ)) := by
  apply le_lm hN
  intro y hy
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy (funext h)
  obtain ⟨w, hw⟩ := one_le_norm_place (y i) hi
  unfold tv nsq
  simp only [Matrix.one_mulVec]
  calc (1 : ℝ) ≤ ‖toR y w i‖ ^ 2 := hw
    _ ≤ ∑ j, ‖toR y w j‖ ^ 2 :=
        Finset.single_le_sum (f := fun j => ‖toR y w j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ v, ∑ j, ‖toR y v j‖ ^ 2 :=
        Finset.single_le_sum (f := fun v => ∑ j, ‖toR y v j‖ ^ 2)
          (fun v _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ w)

def hB (B : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ) : HS L N :=
  mkHS (fun w => (B w)ᴴ * B w) fun w => isHermitian_conjTranspose_mul_self (B w)

/- English proof (translation)
Unfold `q hB qR tv nsq`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Use `show (star (toR y w) ⬝ᵥ ((B w)ᴴ * B w) *ᵥ toR y w).re = _`. Rewrite using `[← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]`. Simplify using `only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.re_sum]`.

Use `norm_cast`.
-/
theorem q_hB (B : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ) (y : Lat L N) :
    q (hB B) y = tv B y := by
  unfold q hB qR tv nsq
  refine Finset.sum_congr rfl fun w _ => ?_
  show (star (toR y w) ⬝ᵥ ((B w)ᴴ * B w) *ᵥ toR y w).re = _
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.re_sum]
  norm_cast

/- English proof (translation)
Unfold `lam lm`. Simplify using `only [q_hB]`.
-/
theorem lam_hB (B : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ) : lam (hB B) = lm B := by
  unfold lam lm
  simp only [q_hB]

def iv (x : Gp L N) : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ :=
  fun w => (((x w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)

def tp (x : Gp L N) : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ :=
  fun w => ((x w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)ᵀ

/- English proof (translation)
Establish `key : ∀ (f g : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ) hf hg, f = g → mkHS f hf = mkHS g hg`. Introduce and unpack `f g hf hg rfl`. Both sides reduce to the same expression. Apply `key` to reduce the goal to its premises. Use function extensionality and compare the values at `w`.

Use `show (iv x w)ᴴ * 1 * iv x w = (iv x w)ᴴ * iv x w`. Rewrite using `[Matrix.mul_one]`.
-/
theorem actL_one_eq (x : Gp L N) : actL x (one L N).1 = hB (iv x) := by
  have key : ∀ (f g : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ) hf hg, f = g → mkHS f hf = mkHS g hg := by
    rintro f g hf hg rfl
    rfl
  apply key
  funext w
  show (iv x w)ᴴ * 1 * iv x w = (iv x w)ᴴ * iv x w
  rw [Matrix.mul_one]

/- English proof (translation)
Establish `key : ∀ (f g : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ) hf hg, f = g → mkHS f hf = mkHS g hg`. Introduce and unpack `f g hf hg rfl`. Both sides reduce to the same expression. Rewrite using `[actL_one_eq]`. Apply `key` to reduce the goal to its premises.

Use function extensionality and compare the values at `w`. Use `show ((iv x w)ᴴ * iv x w)⁻¹ᵀ = (tp x w)ᴴ * tp x w`. Simplify using `only [iv, tp, Matrix.coe_units_inv]`. Rewrite using `[Matrix.mul_inv_rev, Matrix.inv_inv_of_invertible, Matrix.conjTranspose_nonsing_inv, Matrix.inv_inv_of_invertible, Matrix.transpose_mul]`. Both sides reduce to the same expression.
-/
theorem dual_eq (x : Gp L N) : dualH (actL x (one L N).1) = hB (tp x) := by
  have key : ∀ (f g : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ) hf hg, f = g → mkHS f hf = mkHS g hg := by
    rintro f g hf hg rfl
    rfl
  rw [actL_one_eq]
  apply key
  funext w
  show ((iv x w)ᴴ * iv x w)⁻¹ᵀ = (tp x w)ᴴ * tp x w
  simp only [iv, tp, Matrix.coe_units_inv]
  rw [Matrix.mul_inv_rev, Matrix.inv_inv_of_invertible, Matrix.conjTranspose_nonsing_inv,
    Matrix.inv_inv_of_invertible, Matrix.transpose_mul]
  rfl

/- English proof (translation)
Use `show (lam (actL x (one L N).1) * lam (dualH (actL x (one L N).1)))⁻¹ = _`. Rewrite using `[dual_eq, actL_one_eq, lam_hB, lam_hB]`.
-/
theorem ht_eq (x : Gp L N) : ht x = (lm (iv x) * lm (tp x))⁻¹ := by
  show (lam (actL x (one L N).1) * lam (dualH (actL x (one L N).1)))⁻¹ = _
  rw [dual_eq, actL_one_eq, lam_hB, lam_hB]

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `[iv, _root_.mul_inv_rev]`.
-/
theorem iv_mul (x g : Gp L N) : iv (x * g) = fun w => iv g w * iv x w := by
  funext w
  simp [iv, _root_.mul_inv_rev]

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `[tp, Matrix.transpose_mul]`.
-/
theorem tp_mul (x g : Gp L N) : tp (x * g) = fun w => tp g w * tp x w := by
  funext w
  simp [tp, Matrix.transpose_mul]

/- English proof (translation)
Establish `h` using `iv_mul (x * g) g⁻¹`. Establish `e : iv g⁻¹ = fun w => ((g w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)`. Use function extensionality and compare the values at `w`. Simplify using `[iv]`. Rewrite `h` using `[mul_inv_cancel_right, e]`.

Rewrite using `[h]`. Conclude with `lm_mul_le hN _ _`.
-/
theorem lm_iv_le (hN : 1 ≤ N) (x g : Gp L N) :
    lm (iv x) ≤ dist1 (fun w => ((g w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) * lm (iv (x * g)) := by
  have h := iv_mul (x * g) g⁻¹
  have e : iv g⁻¹ = fun w => ((g w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := by
    funext w
    simp [iv]
  rw [mul_inv_cancel_right, e] at h
  rw [h]
  exact lm_mul_le hN _ _

/- English proof (translation)
Establish `h` using `tp_mul (x * g) g⁻¹`. Rewrite `h` using `[mul_inv_cancel_right]`. Rewrite using `[h]`. Conclude with `lm_mul_le hN _ _`.
-/
theorem lm_tp_le (hN : 1 ≤ N) (x g : Gp L N) : lm (tp x) ≤ dist1 (tp g⁻¹) * lm (tp (x * g)) := by
  have h := tp_mul (x * g) g⁻¹
  rw [mul_inv_cancel_right] at h
  rw [h]
  exact lm_mul_le hN _ _

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `[iv]`.
-/
theorem iv_one : iv (1 : Gp L N) = fun _ => 1 := by
  funext w; simp [iv]

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `[tp]`.
-/
theorem tp_one : tp (1 : Gp L N) = fun _ => 1 := by
  funext w; simp [tp]

/- English proof (translation)
Establish `h1` using `one_le_lm_one (L := L) hN`. Establish `h2` using `lm_iv_le hN 1 x`. Rewrite `h2` using `[one_mul, iv_one]`. Conclude with `pos_of_mul_pos_right (lt_of_lt_of_le one_pos (h1.trans h2)) (matrixTupleDistortion_pos _).le`.
-/
theorem lm_iv_pos [IsTotallyComplex L] (hN : 1 ≤ N) (x : Gp L N) : 0 < lm (iv x) := by
  have h1 := one_le_lm_one (L := L) hN
  have h2 := lm_iv_le hN 1 x
  rw [one_mul, iv_one] at h2
  exact pos_of_mul_pos_right (lt_of_lt_of_le one_pos (h1.trans h2)) (matrixTupleDistortion_pos _).le

/- English proof (translation)
Establish `h1` using `one_le_lm_one (L := L) hN`. Establish `h2` using `lm_tp_le hN 1 x`. Rewrite `h2` using `[one_mul, tp_one]`. Conclude with `pos_of_mul_pos_right (lt_of_lt_of_le one_pos (h1.trans h2)) (matrixTupleDistortion_pos _).le`.
-/
theorem lm_tp_pos [IsTotallyComplex L] (hN : 1 ≤ N) (x : Gp L N) : 0 < lm (tp x) := by
  have h1 := one_le_lm_one (L := L) hN
  have h2 := lm_tp_le hN 1 x
  rw [one_mul, tp_one] at h2
  exact pos_of_mul_pos_right (lt_of_lt_of_le one_pos (h1.trans h2)) (matrixTupleDistortion_pos _).le

end PositivityTheory.KB.HeightDistance
