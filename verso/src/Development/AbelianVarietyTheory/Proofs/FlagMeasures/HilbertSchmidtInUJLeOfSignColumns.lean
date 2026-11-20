import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.RealPlaceAnalysis.FinalF
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Establish `h1` using `congrFun (congrFun hh j) j`. Rewrite `h1` using `[Matrix.mul_apply]`. Simplify using `only [Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at h1`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Use `push_cast`.

Apply the tactic sequence `have : ((if ε j then (1 : ℝ) else -1 : ℝ) : ℂ) = if ε j then (1 : ℂ) else -1 := by split_ifs <;> simp`. Rewrite using `[this, ← h1]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h2 : ((‖h i j‖ : ℝ) : ℂ) ^ 2 = star (h i j) * h i j`. Rewrite using `[Complex.star_def, Complex.conj_mul']`.

Rewrite using `[h2]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem uJ_col_sum {n : ℕ} (ε : Fin n → Bool) (h : Matrix (Fin n) (Fin n) ℂ) (hh : inUJ ε h)
    (j : Fin n) :
    ∑ i, (if ε i then (1 : ℝ) else -1) * ‖h i j‖ ^ 2 = if ε j then (1 : ℝ) else -1 := by
  have h1 := congrFun (congrFun hh j) j
  rw [Matrix.mul_apply] at h1
  simp only [Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at h1
  apply Complex.ofReal_injective
  push_cast
  have : ((if ε j then (1 : ℝ) else -1 : ℝ) : ℂ) = if ε j then (1 : ℂ) else -1 := by
    split_ifs <;> simp
  rw [this, ← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : ((‖h i j‖ : ℝ) : ℂ) ^ 2 = star (h i j) * h i j := by
    rw [Complex.star_def, Complex.conj_mul']
  rw [h2]
  split_ifs <;> simp

/- English proof (translation)
Establish `h1` using `(uJInv n ε h hh).1`. Establish `hJ : Jm ε * Jm ε = 1`. Simplify using `only [Jm, Matrix.diagonal_mul_diagonal]`. Rewrite using `[← Matrix.diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `split_ifs <;> simp`. Unfold `inUJ`. Rewrite using `[Matrix.conjTranspose_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc, hJ, Matrix.mul_one]`. Use `_ = Jm ε := by rw [h1, Matrix.one_mul]`.
-/
theorem uJ_conjTranspose {n : ℕ} (ε : Fin n → Bool) (h : Matrix (Fin n) (Fin n) ℂ)
    (hh : inUJ ε h) : inUJ ε hᴴ := by
  have h1 := (uJInv n ε h hh).1
  have hJ : Jm ε * Jm ε = 1 := by
    simp only [Jm, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    split_ifs <;> simp
  unfold inUJ
  rw [Matrix.conjTranspose_conjTranspose]
  calc h * Jm ε * hᴴ = h * (Jm ε * hᴴ * Jm ε) * Jm ε := by
        simp only [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = Jm ε := by rw [h1, Matrix.one_mul]

/- English proof (translation)
Use `set e : Fin n → ℝ := fun i => if ε i then (1 : ℝ) else -1 with he`. Use `set σ : ℝ := if s then (1 : ℝ) else -1 with hσ`. Establish `hc : ∀ j, ∑ i, e i * ‖h i j‖ ^ 2 = e j` using `uJ_col_sum ε h hh`. Establish `hr : ∀ i, ∑ j, e j * ‖h i j‖ ^ 2 = e i` using `fun i => by`. Use `uJ_col_sum ε hᴴ (uJ_conjTranspose ε h hh) i` as an intermediate fact.

Simplify `this` using `only [Matrix.conjTranspose_apply, norm_star]`. Establish `hee : ∀ i, e i * e i = 1` using `fun i => by`. Apply the tactic sequence `simp only [he]; split_ifs <;> simp`. Establish `A : ∑ i, ∑ j, e i * (e j * ‖h i j‖ ^ 2) = n`. Simplify using `only [← Finset.mul_sum, hr, hee]`.

Simplify using the standard rewrite rules. Establish `B : ∑ i, ∑ j, e j * ‖h i j‖ ^ 2 = ∑ i, ∑ j, e i * ‖h i j‖ ^ 2`. Rewrite using `[Finset.sum_comm (f := fun i j => e i * ‖h i j‖ ^ 2)]`. Simplify using `only [hr, hc]`. Establish `C : ∑ i, ∑ j, (‖h i j‖ ^ 2 - e i * (e j * ‖h i j‖ ^ 2) + σ * (e j * ‖h i j‖ ^ 2) - σ * (e i * ‖h i j‖ ^ 2)) ≤ ∑ i, ∑ j, 4 * (if ε j = s then ‖h i j‖ ^ 2 else 0)`.

Use `Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_` and prove the remaining obligations. Establish `h0 : 0 ≤ ‖h i j‖ ^ 2` using `by positivity`. Simplify using `only [he, hσ]`. Apply the tactic sequence `cases ε i <;> cases ε j <;> cases s <;> simp <;> linarith`. Establish `D : ∑ i, ∑ j, σ * (e j * ‖h i j‖ ^ 2) = ∑ i, ∑ j, σ * (e i * ‖h i j‖ ^ 2)`.

Use `congrArg (σ * ·) B` as an intermediate fact. Simplify `this` using `only [Finset.mul_sum]`. Simplify using `only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at C`. Rewrite `C` using `[A, D]`. Simplify using `only [Finset.sum_filter, Finset.mul_sum, hs]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hs_le_of_cols (n : ℕ) (ε : Fin n → Bool) (s : Bool) (h : Matrix (Fin n) (Fin n) ℂ)
    (hh : inUJ ε h) :
    hs h ≤ n + 4 * ∑ i, ∑ j ∈ univ.filter (fun j => ε j = s), ‖h i j‖ ^ 2 := by
  set e : Fin n → ℝ := fun i => if ε i then (1 : ℝ) else -1 with he
  set σ : ℝ := if s then (1 : ℝ) else -1 with hσ
  have hc : ∀ j, ∑ i, e i * ‖h i j‖ ^ 2 = e j := uJ_col_sum ε h hh
  have hr : ∀ i, ∑ j, e j * ‖h i j‖ ^ 2 = e i := fun i => by
    have := uJ_col_sum ε hᴴ (uJ_conjTranspose ε h hh) i
    simpa only [Matrix.conjTranspose_apply, norm_star] using this
  have hee : ∀ i, e i * e i = 1 := fun i => by
    simp only [he]; split_ifs <;> simp
  have A : ∑ i, ∑ j, e i * (e j * ‖h i j‖ ^ 2) = n := by
    simp only [← Finset.mul_sum, hr, hee]
    simp
  have B : ∑ i, ∑ j, e j * ‖h i j‖ ^ 2 = ∑ i, ∑ j, e i * ‖h i j‖ ^ 2 := by
    rw [Finset.sum_comm (f := fun i j => e i * ‖h i j‖ ^ 2)]
    simp only [hr, hc]
  have C : ∑ i, ∑ j, (‖h i j‖ ^ 2 - e i * (e j * ‖h i j‖ ^ 2) + σ * (e j * ‖h i j‖ ^ 2)
      - σ * (e i * ‖h i j‖ ^ 2)) ≤ ∑ i, ∑ j, 4 * (if ε j = s then ‖h i j‖ ^ 2 else 0) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have h0 : 0 ≤ ‖h i j‖ ^ 2 := by positivity
    simp only [he, hσ]
    cases ε i <;> cases ε j <;> cases s <;> simp <;> linarith
  have D : ∑ i, ∑ j, σ * (e j * ‖h i j‖ ^ 2) = ∑ i, ∑ j, σ * (e i * ‖h i j‖ ^ 2) := by
    have := congrArg (σ * ·) B
    simpa only [Finset.mul_sum] using this
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at C
  rw [A, D] at C
  simp only [Finset.sum_filter, Finset.mul_sum, hs]
  linarith

end GlobalTheory
