import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BlockForm

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem blockOne_zero_zero {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    blockOne t A 0 0 = t := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem blockOne_zero_succ {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K)
    (j : Fin M) : blockOne t A 0 j.succ = 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem blockOne_succ_zero {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K)
    (i : Fin M) : blockOne t A i.succ 0 = 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem blockOne_succ_succ {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K)
    (i j : Fin M) : blockOne t A i.succ j.succ = A i j := rfl

/- English proof (translation)
Establish `h0 : (blockOne t A).submatrix Fin.succ Fin.succ = A`. Use extensionality with `i j`. Conclude with `blockOne_succ_succ t A i j`. Rewrite using `[Matrix.det_succ_row_zero, Fin.sum_univ_succ]`. Simplify using `[blockOne_zero_zero, blockOne_zero_succ, h0]`.
-/
theorem det_blockOne {K : Type} [CommRing K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    (blockOne t A).det = t * A.det := by
  have h0 : (blockOne t A).submatrix Fin.succ Fin.succ = A := by
    ext i j
    exact blockOne_succ_succ t A i j
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [blockOne_zero_zero, blockOne_zero_succ, h0]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hypJ_zero_zero {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    hypJ A 0 0 = 0 := rfl

/- English proof (translation)
Rewrite using `[← Fin.succ_zero_eq_one]`. Both sides reduce to the same expression.
-/
theorem hypJ_zero_one {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    hypJ A 0 1 = 1 := by
  rw [← Fin.succ_zero_eq_one]; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hypJ_zero_succ_succ {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K)
    (j : Fin M) : hypJ A 0 j.succ.succ = 0 := rfl

/- English proof (translation)
Rewrite using `[← Fin.succ_zero_eq_one]`. Both sides reduce to the same expression.
-/
theorem hypJ_one_zero {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    hypJ A 1 0 = 1 := by
  rw [← Fin.succ_zero_eq_one]; rfl

/- English proof (translation)
Rewrite using `[← Fin.succ_zero_eq_one]`. Both sides reduce to the same expression.
-/
theorem hypJ_one_one {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    hypJ A 1 1 = 0 := by
  rw [← Fin.succ_zero_eq_one]; rfl

/- English proof (translation)
Rewrite using `[← Fin.succ_zero_eq_one]`. Both sides reduce to the same expression.
-/
theorem hypJ_one_succ_succ {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K)
    (j : Fin M) : hypJ A 1 j.succ.succ = 0 := by
  rw [← Fin.succ_zero_eq_one]; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hypJ_succ_succ_zero {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K)
    (i : Fin M) : hypJ A i.succ.succ 0 = 0 := rfl

/- English proof (translation)
Rewrite using `[← Fin.succ_zero_eq_one]`. Both sides reduce to the same expression.
-/
theorem hypJ_succ_succ_one {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K)
    (i : Fin M) : hypJ A i.succ.succ 1 = 0 := by
  rw [← Fin.succ_zero_eq_one]; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hypJ_succ_succ_succ_succ {K : Type} [Zero K] [One K] {M : ℕ}
    (A : Matrix (Fin M) (Fin M) K) (i j : Fin M) : hypJ A i.succ.succ j.succ.succ = A i j := rfl

/- English proof (translation)
Establish `h1 : (hypJ A).submatrix Fin.succ (Fin.succAbove 1) = blockOne 1 A`. Rewrite using `[← Fin.succ_zero_eq_one]`. Use extensionality with `i j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j`. Both sides reduce to the same expression.

Both sides reduce to the same expression. Both sides reduce to the same expression. Both sides reduce to the same expression. Rewrite using `[Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]`. Simplify using `[hypJ_zero_zero, hypJ_zero_one, hypJ_zero_succ_succ, h1, det_blockOne]`.
-/
theorem det_hypJ {K : Type} [CommRing K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    (hypJ A).det = -A.det := by
  have h1 : (hypJ A).submatrix Fin.succ (Fin.succAbove 1) = blockOne 1 A := by
    rw [← Fin.succ_zero_eq_one]
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · rfl
    · rfl
    · rfl
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [hypJ_zero_zero, hypJ_zero_one, hypJ_zero_succ_succ, h1, det_blockOne]

variable {F E : Type} [Field F] [Field E] [Algebra F E]

/- English proof (translation)
Use `⟨fun i j => ?_, ?_⟩` and prove the remaining obligations. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations. Simplify using `[hypJ_zero_zero]`. Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations.

Simplify using `[hypJ_zero_one, hypJ_one_zero]`. Simplify using `[hypJ_zero_succ_succ, hypJ_succ_succ_zero]`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations. Simplify using `[hypJ_zero_one, hypJ_one_zero]`.

Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations. Simplify using `[hypJ_one_one]`. Simplify using `[hypJ_one_succ_succ, hypJ_succ_succ_one]`. Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations. Simplify using `[hypJ_zero_succ_succ, hypJ_succ_succ_zero]`.

Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations. Simplify using `[hypJ_one_succ_succ, hypJ_succ_succ_one]`. Rewrite using `[hypJ_succ_succ_succ_succ, hypJ_succ_succ_succ_succ]`. Conclude with `hJ.1 i j`. Rewrite using `[det_hypJ]`.

Conclude with `neg_ne_zero.mpr hJ.2`.
-/
theorem isHermND_hypJ (σ : E →ₐ[F] E) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) : IsHermND σ (hypJ J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [hypJ_zero_zero]
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [hypJ_zero_one, hypJ_one_zero]
        · simp [hypJ_zero_succ_succ, hypJ_succ_succ_zero]
    · refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [hypJ_zero_one, hypJ_one_zero]
        · refine Fin.cases ?_ (fun j => ?_) j
          · simp [hypJ_one_one]
          · simp [hypJ_one_succ_succ, hypJ_succ_succ_one]
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [hypJ_zero_succ_succ, hypJ_succ_succ_zero]
        · refine Fin.cases ?_ (fun j => ?_) j
          · simp [hypJ_one_succ_succ, hypJ_succ_succ_one]
          · rw [hypJ_succ_succ_succ_succ, hypJ_succ_succ_succ_succ]
            exact hJ.1 i j
  · rw [det_hypJ]
    exact neg_ne_zero.mpr hJ.2

/- English proof (translation)
Use `⟨fun i j => ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j`. Simplify using `[blockOne_zero_zero]`. Simplify using `[blockOne_zero_succ, blockOne_succ_zero]`. Simplify using `[blockOne_zero_succ, blockOne_succ_zero]`.

Rewrite using `[blockOne_succ_succ, blockOne_succ_succ]`. Conclude with `hJ.1 i j`. Rewrite using `[det_blockOne]`. Conclude with `mul_ne_zero ((map_ne_zero (algebraMap F E)).mpr ht) hJ.2`.
-/
theorem isHermND_blockOne (σ : E →ₐ[F] E) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) {t : F} (ht : t ≠ 0) : IsHermND σ (blockOne (algebraMap F E t) J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [blockOne_zero_zero]
    · simp [blockOne_zero_succ, blockOne_succ_zero]
    · simp [blockOne_zero_succ, blockOne_succ_zero]
    · rw [blockOne_succ_succ, blockOne_succ_succ]
      exact hJ.1 i j
  · rw [det_blockOne]
    exact mul_ne_zero ((map_ne_zero (algebraMap F E)).mpr ht) hJ.2

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ σ _ _ _ hJ` and use `⟨isHermND_hypJ σ hJ, fun _ ht => isHermND_blockOne σ hJ ht⟩`.
-/
theorem blockForms_isHermND : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsHermND σ (hypJ J) ∧
      ∀ t : F, t ≠ 0 → IsHermND σ (blockOne (algebraMap F E t) J) :=
  fun _ _ _ _ _ _ _ σ _ _ _ hJ => ⟨isHermND_hypJ σ hJ, fun _ ht => isHermND_blockOne σ hJ ht⟩

end GlobalTheory.CompanionTheory.SW.BlockForm
