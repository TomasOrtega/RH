import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinC

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open Matrix

/- English proof (translation)
Introduce `d G hG B`. Take `⟨R, hRu, hGR⟩` from `whiten_holds d G hG`. Use `set A : ℝ := ∑ i, ∑ j, |R⁻¹ i j| with hA`. Use `set M : ℤ := ⌈A * (1 + B)⌉ with hM`. Use `(Set.Finite.pi (t := fun _ : Fin d => Set.Icc (-M) M) fun _ => Set.finite_Icc _ _).subset ?_` and prove the remaining obligations.

Introduce `c hc`. Simplify using `only [Set.mem_setOf_eq] at hc`. Simplify using `only [Set.mem_pi, Set.mem_univ, true_implies]`. Introduce `i`. Use `set cv : Fin d → ℝ := fun i => (c i : ℝ) with hcv`.

Use `set y : Fin d → ℝ := R *ᵥ cv with hy`. Establish `hyy : ∑ j, y j * y j ≤ B`. Establish `e : cv ⬝ᵥ (G *ᵥ cv) = y ⬝ᵥ y`. Rewrite using `[hGR, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]`. Rewrite `hc` using `[e]`.

Simplify `hc` using `[dotProduct]`. Establish `hyj : ∀ j, |y j| ≤ 1 + B`. Introduce `j`. Establish `h1 : y j * y j ≤ ∑ k, y k * y k` using `Finset.single_le_sum (f := fun k => y k * y k) (fun k _ => mul_self_nonneg (y k)) (Finset.mem_univ j)`. Establish `h2 : |y j| ≤ 1 + y j * y j`.

Use polynomial arithmetic with `[abs_nonneg (y j), sq_abs (y j), abs_mul_abs_self (y j)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hB : 0 ≤ 1 + B` using `(abs_nonneg _).trans (hyj i)`. Establish `hcvR : cv = R⁻¹ *ᵥ y`. Rewrite using `[hy, mulVec_mulVec, nonsing_inv_mul R hRu, one_mulVec]`.

Establish `hci : |cv i| ≤ A * (1 + B)`. Establish `e : cv i = ∑ j, R⁻¹ i j * y j`. Rewrite using `[hcvR]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_right ?_ hB` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun i => ∑ j, |R⁻¹ i j|) (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i)`. Establish `hle : ((|c i| : ℤ) : ℝ) ≤ (M : ℝ)`. Rewrite using `[Int.cast_abs]`.

Conclude with `hci.trans (Int.le_ceil _)`. Establish `hle' : |c i| ≤ M` using `by exact_mod_cast hle`. Conclude with `abs_le.1 hle'`.
-/
theorem finiteShort_holds : FiniteShortStatement := by
  intro d G hG B
  obtain ⟨R, hRu, hGR⟩ := whiten_holds d G hG
  set A : ℝ := ∑ i, ∑ j, |R⁻¹ i j| with hA
  set M : ℤ := ⌈A * (1 + B)⌉ with hM
  refine (Set.Finite.pi (t := fun _ : Fin d => Set.Icc (-M) M) fun _ => Set.finite_Icc _ _).subset ?_
  intro c hc
  simp only [Set.mem_setOf_eq] at hc
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  intro i
  set cv : Fin d → ℝ := fun i => (c i : ℝ) with hcv
  set y : Fin d → ℝ := R *ᵥ cv with hy
  have hyy : ∑ j, y j * y j ≤ B := by
    have e : cv ⬝ᵥ (G *ᵥ cv) = y ⬝ᵥ y := by
      rw [hGR, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    rw [e] at hc
    simpa [dotProduct] using hc
  have hyj : ∀ j, |y j| ≤ 1 + B := by
    intro j
    have h1 : y j * y j ≤ ∑ k, y k * y k :=
      Finset.single_le_sum (f := fun k => y k * y k) (fun k _ => mul_self_nonneg (y k)) (Finset.mem_univ j)
    have h2 : |y j| ≤ 1 + y j * y j := by
      nlinarith [abs_nonneg (y j), sq_abs (y j), abs_mul_abs_self (y j)]
    linarith
  have hB : 0 ≤ 1 + B := (abs_nonneg _).trans (hyj i)
  have hcvR : cv = R⁻¹ *ᵥ y := by
    rw [hy, mulVec_mulVec, nonsing_inv_mul R hRu, one_mulVec]
  have hci : |cv i| ≤ A * (1 + B) := by
    have e : cv i = ∑ j, R⁻¹ i j * y j := by
      rw [hcvR]
      rfl
    rw [e]
    calc |∑ j, R⁻¹ i j * y j| ≤ ∑ j, |R⁻¹ i j * y j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |R⁻¹ i j| * |y j| := by simp only [abs_mul]
      _ ≤ ∑ j, |R⁻¹ i j| * (1 + B) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hyj j) (abs_nonneg _)
      _ = (∑ j, |R⁻¹ i j|) * (1 + B) := by rw [Finset.sum_mul]
      _ ≤ A * (1 + B) := by
          refine mul_le_mul_of_nonneg_right ?_ hB
          exact Finset.single_le_sum (f := fun i => ∑ j, |R⁻¹ i j|)
            (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hle : ((|c i| : ℤ) : ℝ) ≤ (M : ℝ) := by
    rw [Int.cast_abs]
    exact hci.trans (Int.le_ceil _)
  have hle' : |c i| ≤ M := by exact_mod_cast hle
  exact abs_le.1 hle'

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
