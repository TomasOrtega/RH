import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.TwoSidedJac

open Kronecker

noncomputable def twoSided {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ) :
    Matrix (Fin a) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin b) ℂ where
  toFun T := A * T * B
  map_add' S T := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c T := by simp [Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem twoSided_apply {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ)
    (T : Matrix (Fin a) (Fin b) ℂ) : twoSided A B T = A * T * B := rfl

/- English proof (translation)
Rewrite using `[← LinearMap.det_toMatrix (Matrix.stdBasis ℂ (Fin a) (Fin b))]`. Establish `h : LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin a) (Fin b)) (Matrix.stdBasis ℂ (Fin a) (Fin b)) (twoSided A B) = A ⊗ₖ Bᵀ`. Use extensionality with `⟨i, j⟩ ⟨k, l⟩`. Rewrite using `[LinearMap.toMatrix_apply, Matrix.stdBasis_eq_single, twoSided_apply]`. Establish `hr : ∀ M : Matrix (Fin a) (Fin b) ℂ, (Matrix.stdBasis ℂ (Fin a) (Fin b)).repr M (i, j) = M i j`.

Introduce `M`. Simplify using `[Matrix.stdBasis]`. Rewrite using `[hr]`. Simplify using `[Matrix.mul_apply, Matrix.single, Finset.sum_mul, ite_and]`. Rewrite using `[h, Matrix.det_kronecker, Matrix.det_transpose]`.

Simplify using the standard rewrite rules.
-/
theorem det_twoSided {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ) :
    LinearMap.det (twoSided A B) = A.det ^ b * B.det ^ a := by
  rw [← LinearMap.det_toMatrix (Matrix.stdBasis ℂ (Fin a) (Fin b))]
  have h : LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin a) (Fin b))
      (Matrix.stdBasis ℂ (Fin a) (Fin b)) (twoSided A B) = A ⊗ₖ Bᵀ := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rw [LinearMap.toMatrix_apply, Matrix.stdBasis_eq_single, twoSided_apply]
    have hr : ∀ M : Matrix (Fin a) (Fin b) ℂ,
        (Matrix.stdBasis ℂ (Fin a) (Fin b)).repr M (i, j) = M i j := by
      intro M
      simp [Matrix.stdBasis]
    rw [hr]
    simp [Matrix.mul_apply, Matrix.single, Finset.sum_mul, ite_and]
  rw [h, Matrix.det_kronecker, Matrix.det_transpose]
  simp

section Skew

variable {a : ℕ} {ι : Type} [Fintype ι]

/- English proof (translation)
The claim follows from `skewAdjoint.mem_iff.mp T.2`.
-/
theorem star_coe (T : skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ)) :
    star (T : Matrix (Fin a) (Fin a) ℂ) = -(T : Matrix (Fin a) (Fin a) ℂ) :=
  skewAdjoint.mem_iff.mp T.2

/- English proof (translation)
Establish `hR : ∀ g : ι → ℝ, ∑ i, (g i : ℂ) • (e i : Matrix (Fin a) (Fin a) ℂ) = 0 → ∀ i, g i = 0`. Introduce `g hg`. Apply `Fintype.linearIndependent_iff.mp e.linearIndependent g` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using hg`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Establish `h2 : ∑ i, (starRingEnd ℂ (g i)) • (e i : Matrix (Fin a) (Fin a) ℂ) = 0`. Use `congrArg star hg` as an intermediate fact. Simplify using `only [star_sum, star_smul, star_coe, smul_neg, Finset.sum_neg_distrib, star_zero, neg_eq_zero] at this`.

Conclude with `this`. Establish `hre : ∀ i, 2 * (g i).re = 0`. Apply `hR` to reduce the goal to its premises. Establish `: ∀ i, ((2 * (g i).re : ℝ) : ℂ) = g i + starRingEnd ℂ (g i)` using `fun i => (Complex.add_conj _).symm`. Simplify using `only [this, add_smul, Finset.sum_add_distrib, hg, h2, add_zero]`.

Establish `him : ∀ i, 2 * (g i).im = 0`. Apply `hR` to reduce the goal to its premises. Establish `: ∀ i, ((2 * (g i).im : ℝ) : ℂ) = (-Complex.I) * (g i - starRingEnd ℂ (g i))`. Introduce `i`. Rewrite using `[Complex.sub_conj]`.

Use `Complex.I_mul_I` as an intermediate fact. Take the linear combination `((2 * (g i).im : ℝ) : ℂ) * this`. Simplify using `only [this, mul_smul, ← Finset.smul_sum, sub_smul, Finset.sum_sub_distrib, hg, h2, sub_zero, smul_zero]`. Introduce `i`. Apply `Complex.ext` to reduce the goal to its premises.

Use `hre i` as an intermediate fact. Simplify using `using this`. Use `him i` as an intermediate fact. Simplify using `using this`.
-/
theorem linearIndependent_skew
    (e : Module.Basis ι ℝ (skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ))) :
    LinearIndependent ℂ (fun i => (e i : Matrix (Fin a) (Fin a) ℂ)) := by
  have hR : ∀ g : ι → ℝ, ∑ i, (g i : ℂ) • (e i : Matrix (Fin a) (Fin a) ℂ) = 0 → ∀ i, g i = 0 := by
    intro g hg
    apply Fintype.linearIndependent_iff.mp e.linearIndependent g
    apply Subtype.ext
    simpa using hg
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h2 : ∑ i, (starRingEnd ℂ (g i)) • (e i : Matrix (Fin a) (Fin a) ℂ) = 0 := by
    have := congrArg star hg
    simp only [star_sum, star_smul, star_coe, smul_neg, Finset.sum_neg_distrib, star_zero,
      neg_eq_zero] at this
    exact this
  have hre : ∀ i, 2 * (g i).re = 0 := by
    apply hR
    have : ∀ i, ((2 * (g i).re : ℝ) : ℂ) = g i + starRingEnd ℂ (g i) := fun i =>
      (Complex.add_conj _).symm
    simp only [this, add_smul, Finset.sum_add_distrib, hg, h2, add_zero]
  have him : ∀ i, 2 * (g i).im = 0 := by
    apply hR
    have : ∀ i, ((2 * (g i).im : ℝ) : ℂ) = (-Complex.I) * (g i - starRingEnd ℂ (g i)) := by
      intro i
      rw [Complex.sub_conj]
      have := Complex.I_mul_I
      linear_combination ((2 * (g i).im : ℝ) : ℂ) * this
    simp only [this, mul_smul, ← Finset.smul_sum, sub_smul, Finset.sum_sub_distrib, hg, h2,
      sub_zero, smul_zero]
  intro i
  apply Complex.ext
  · have := hre i
    simpa using this
  · have := him i
    simpa using this

/- English proof (translation)
Establish `hS : ∀ T : Matrix (Fin a) (Fin a) ℂ, star T = -T → T ∈ Submodule.span ℂ (Set.range fun i => (e i : Matrix (Fin a) (Fin a) ℂ))`. Introduce `T hT`. Establish `h` using `congrArg Subtype.val (e.sum_repr ⟨T, skewAdjoint.mem_iff.mpr hT⟩)`. Simplify using `only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at h`. Rewrite using `[← h]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Conclude with `Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Introduce `T _`. Establish `h1` using `hS (T - star T) (by simp)`. Establish `h2` using `hS (Complex.I • (T + star T)) (by simp [star_smul, add_comm])`.

Establish `: T = (1 / 2 : ℂ) • ((T - star T) + (-Complex.I) • (Complex.I • (T + star T)))`. Rewrite using `[smul_smul]`. Simplify using `only [neg_mul, Complex.I_mul_I, neg_neg, one_smul]`. Use `module`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.add_mem _ h1 (Submodule.smul_mem _ _ h2))`.
-/
theorem span_skew
    (e : Module.Basis ι ℝ (skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ))) :
    ⊤ ≤ Submodule.span ℂ (Set.range fun i => (e i : Matrix (Fin a) (Fin a) ℂ)) := by
  have hS : ∀ T : Matrix (Fin a) (Fin a) ℂ, star T = -T →
      T ∈ Submodule.span ℂ (Set.range fun i => (e i : Matrix (Fin a) (Fin a) ℂ)) := by
    intro T hT
    have h := congrArg Subtype.val (e.sum_repr ⟨T, skewAdjoint.mem_iff.mpr hT⟩)
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at h
    rw [← h]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  intro T _
  have h1 := hS (T - star T) (by simp)
  have h2 := hS (Complex.I • (T + star T)) (by simp [star_smul, add_comm])
  have : T = (1 / 2 : ℂ) • ((T - star T) + (-Complex.I) • (Complex.I • (T + star T))) := by
    rw [smul_smul]
    simp only [neg_mul, Complex.I_mul_I, neg_neg, one_smul]
    module
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ h1 (Submodule.smul_mem _ _ h2))

/- English proof (translation)
Set `e` to `Module.finBasis ℝ (skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ))`. Set `e'` to `Module.Basis.mk (linearIndependent_skew e) (span_skew e)`. Establish `he : ∀ i, e' i = (e i : Matrix (Fin a) (Fin a) ℂ)` using `fun i => Module.Basis.mk_apply _ _ i`. Rewrite using `[← LinearMap.det_toMatrix e, ← LinearMap.det_toMatrix e']`. Establish `hm : LinearMap.toMatrix e' e' F = (LinearMap.toMatrix e e L).map Complex.ofRealHom`.

Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, he, ← h]`. Establish `h1 : (L (e j) : Matrix (Fin a) (Fin a) ℂ) = ∑ k, ((e.repr (L (e j)) k : ℝ) : ℂ) • e' k`. Establish `h` using `congrArg Subtype.val (e.sum_repr (L (e j)))`. Simplify using `only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at h`.

Rewrite using `[← h]`. Simplify using `only [he, Complex.coe_smul]`. Rewrite using `[h1, e'.repr_sum_self]`. Both sides reduce to the same expression. Rewrite using `[hm]`.

Conclude with `RingHom.map_det Complex.ofRealHom _`.
-/
theorem det_skew_eq
    (L : skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ) →ₗ[ℝ]
      skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ))
    (F : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin a) ℂ)
    (h : ∀ T, (L T : Matrix (Fin a) (Fin a) ℂ) = F T) :
    ((LinearMap.det L : ℝ) : ℂ) = LinearMap.det F := by
  classical
  let e := Module.finBasis ℝ (skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ))
  let e' := Module.Basis.mk (linearIndependent_skew e) (span_skew e)
  have he : ∀ i, e' i = (e i : Matrix (Fin a) (Fin a) ℂ) := fun i => Module.Basis.mk_apply _ _ i
  rw [← LinearMap.det_toMatrix e, ← LinearMap.det_toMatrix e']
  have hm : LinearMap.toMatrix e' e' F = (LinearMap.toMatrix e e L).map Complex.ofRealHom := by
    ext i j
    rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, he, ← h]
    have h1 : (L (e j) : Matrix (Fin a) (Fin a) ℂ) =
        ∑ k, ((e.repr (L (e j)) k : ℝ) : ℂ) • e' k := by
      have h := congrArg Subtype.val (e.sum_repr (L (e j)))
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at h
      rw [← h]
      simp only [he, Complex.coe_smul]
    rw [h1, e'.repr_sum_self]
    rfl
  rw [hm]
  exact RingHom.map_det Complex.ofRealHom _

end Skew

/- English proof (translation)
Use `⟨fun a b A B L hL => ?_, fun a A L hL => ?_⟩` and prove the remaining obligations. Establish `: L = (twoSided A B).restrictScalars ℝ` using `LinearMap.ext hL`. Rewrite using `[this, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, det_twoSided, Complex.normSq_eq_norm_sq, norm_mul, norm_pow, norm_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `h` using `det_skew_eq L (twoSided A Aᴴ) hL`.

Rewrite `h` using `[det_twoSided, Matrix.det_conjTranspose, ← mul_pow]`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[h, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_mul]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem real_jacobians :
    (∀ (a b : ℕ) (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ) (L : Matrix (Fin a) (Fin b) ℂ →ₗ[ℝ] Matrix (Fin a) (Fin b) ℂ), (∀ T, L T = A * T * B) → LinearMap.det L = ‖A.det‖ ^ (2 * b) * ‖B.det‖ ^ (2 * a)) ∧ ∀ (a : ℕ) (A : Matrix (Fin a) (Fin a) ℂ) (L : skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ) →ₗ[ℝ] skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ)), (∀ T, ((L T : skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ)) : Matrix (Fin a) (Fin a) ℂ) = A * (T : Matrix (Fin a) (Fin a) ℂ) * Aᴴ) → LinearMap.det L = ‖A.det‖ ^ (2 * a) := by
  refine ⟨fun a b A B L hL => ?_, fun a A L hL => ?_⟩
  · have : L = (twoSided A B).restrictScalars ℝ := LinearMap.ext hL
    rw [this, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, det_twoSided,
      Complex.normSq_eq_norm_sq, norm_mul, norm_pow, norm_pow]
    ring
  · have h := det_skew_eq L (twoSided A Aᴴ) hL
    rw [det_twoSided, Matrix.det_conjTranspose, ← mul_pow] at h
    apply Complex.ofReal_injective
    rw [h, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_mul]
    push_cast
    rfl

end GlobalTheory.TwoSidedJac
