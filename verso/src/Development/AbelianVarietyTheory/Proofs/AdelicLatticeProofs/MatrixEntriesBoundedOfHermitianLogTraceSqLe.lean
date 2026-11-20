import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Establish `h : (Matrix.trace (xᴴ * x)).re = ∑ b, ∑ a, ‖x a b‖ ^ 2`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.conj_mul']`. Use `norm_cast`.

Rewrite using `[h]`. Combine the equalities or inequalities in the displayed calculation.
-/
private lemma energy_entry_sq_le {ι : Type} [Fintype ι] (x : Matrix ι ι ℂ) (i j : ι) :
    ‖x i j‖ ^ 2 ≤ (Matrix.trace (xᴴ * x)).re := by
  have h : (Matrix.trace (xᴴ * x)).re = ∑ b, ∑ a, ‖x a b‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  rw [h]
  calc ‖x i j‖ ^ 2 ≤ ∑ a, ‖x a j‖ ^ 2 :=
        Finset.single_le_sum (f := fun a => ‖x a j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
    _ ≤ _ := Finset.single_le_sum (f := fun b => ∑ a, ‖x a b‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ j)

/- English proof (translation)
Establish `hU' : Uᴴ * U = 1` using `mul_eq_one_comm.mp hU`. Rewrite using `[Matrix.trace_mul_cycle, hU', one_mul, Matrix.trace_diagonal, Complex.re_sum]`. Simplify using the standard rewrite rules.
-/
private lemma energy_trace_conj {ι : Type} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (hU : U * Uᴴ = 1)
    (d : ι → ℝ) : (Matrix.trace (U * diagonal (fun i => (d i : ℂ)) * Uᴴ)).re = ∑ i, d i := by
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  rw [Matrix.trace_mul_cycle, hU', one_mul, Matrix.trace_diagonal, Complex.re_sum]
  simp

/- English proof (translation)
Introduce `ι _ _ E`. Use `⟨max (√E) (√(Fintype.card ι * Real.exp (√E))), ?_⟩` and prove the remaining obligations. Introduce and unpack `x H ⟨U, d, hU, hH, hA⟩ hE i j`. Establish `hU' : Uᴴ * U = 1` using `mul_eq_one_comm.mp hU`. Establish `hherm : Hᴴ = H`.

Rewrite using `[hH]`. Simplify using `[Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, Matrix.mul_assoc, Pi.star_def]`. Establish `hHH : H * H = U * diagonal (fun i => ((d i ^ 2 : ℝ) : ℂ)) * Uᴴ`. Rewrite using `[hH]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by`. Rewrite using `[hU', Matrix.mul_one, Matrix.diagonal_mul_diagonal]`. Use `congr 3`. Use function extensionality and compare the values at `k`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hd : ∀ k, d k ≤ √E`. Introduce `k`. Establish `h1 : ∑ k, d k ^ 2 ≤ E`.

Rewrite `hE` using `[hHH, energy_trace_conj U hU]`. Conclude with `hE`. Establish `h2 : d k ^ 2 ≤ ∑ k, d k ^ 2` using `Finset.single_le_sum (f := fun k => d k ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)`. Conclude with `Real.le_sqrt_of_sq_le (h2.trans h1)`. Prove the components needed by the constructor for the conclusion.

Use `le_trans ?_ (le_max_right _ _)` and prove the remaining obligations. Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises. Use `(energy_entry_sq_le x i j).trans ?_` and prove the remaining obligations. Rewrite using `[hA, energy_trace_conj U hU (fun i => Real.exp (d i))]`. Combine the equalities or inequalities in the displayed calculation.

Use `le_trans ?_ (le_max_left _ _)` and prove the remaining obligations. Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises. Use `(energy_entry_sq_le H i j).trans ?_` and prove the remaining obligations. Rewrite using `[hherm]` and apply the resulting hypothesis.
-/
theorem entries_le_of_energy_le : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (E : ℝ), ∃ C : ℝ, ∀ x H : Matrix ι ι ℂ, IsLog H (xᴴ * x) → (Matrix.trace (H * H)).re ≤ E → ∀ i j, ‖x i j‖ ≤ C ∧ ‖H i j‖ ≤ C := by
  intro ι _ _ E
  refine ⟨max (√E) (√(Fintype.card ι * Real.exp (√E))), ?_⟩
  rintro x H ⟨U, d, hU, hH, hA⟩ hE i j
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  have hherm : Hᴴ = H := by
    rw [hH]
    simp [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, Matrix.mul_assoc, Pi.star_def]
  have hHH : H * H = U * diagonal (fun i => ((d i ^ 2 : ℝ) : ℂ)) * Uᴴ := by
    rw [hH]
    calc U * diagonal (fun i => (d i : ℂ)) * Uᴴ * (U * diagonal (fun i => (d i : ℂ)) * Uᴴ)
        = U * (diagonal (fun i => (d i : ℂ)) * (Uᴴ * U) * diagonal (fun i => (d i : ℂ))) * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hU', Matrix.mul_one, Matrix.diagonal_mul_diagonal]
          congr 3
          funext k
          push_cast
          ring
  have hd : ∀ k, d k ≤ √E := by
    intro k
    have h1 : ∑ k, d k ^ 2 ≤ E := by
      rw [hHH, energy_trace_conj U hU] at hE
      exact hE
    have h2 : d k ^ 2 ≤ ∑ k, d k ^ 2 :=
      Finset.single_le_sum (f := fun k => d k ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)
    exact Real.le_sqrt_of_sq_le (h2.trans h1)
  constructor
  · refine le_trans ?_ (le_max_right _ _)
    apply Real.le_sqrt_of_sq_le
    refine (energy_entry_sq_le x i j).trans ?_
    rw [hA, energy_trace_conj U hU (fun i => Real.exp (d i))]
    calc ∑ k, Real.exp (d k) ≤ ∑ _k : ι, Real.exp (√E) :=
          Finset.sum_le_sum fun k _ => Real.exp_le_exp.mpr (hd k)
      _ = _ := by simp
  · refine le_trans ?_ (le_max_left _ _)
    apply Real.le_sqrt_of_sq_le
    refine (energy_entry_sq_le H i j).trans ?_
    rwa [hherm]

end GlobalTheory.ClassFin
