import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMaxOnePowLeOnSiegelTorusConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCountSumBoundOfRationalDiagonalisingStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TorusStack

/- English proof (translation)
Introduce `D m n r X Y X' Y' c hc L hL`. Establish `hST : Matrix.fromCols X (Matrix.fromCols Y (1 : Matrix (Fin m) (Fin m) D.host.E)) * Matrix.fromRows Y' (Matrix.fromRows X' (1 - X * Y' - Y * X')) = 1`. Rewrite using `[Matrix.fromCols_mul_fromRows, Matrix.fromCols_mul_fromRows, Matrix.one_mul]`. Normalize the expressions using the abelian group laws. Take `⟨N, C, hC, h⟩` from `GlobalTheory.T.latticeCount_sum_bound_of_rational_diagonalising D (Fin r ⊕ Fin r ⊕ Fin m) m n _ _ hST L hL`.

Take `⟨C', hC', h'⟩` from `GlobalTheory.T.prod_max_one_pow_le_on_siegelTorusCone r m (Module.finrank ℚ D.host.F * (2 * n)) c hc`. Use `⟨N, C * C', mul_nonneg hC hC', fun t ht B hB => ?_⟩` and prove the remaining obligations. Establish `htpos : ∀ i, 0 < t i` using `ht.1`. Use `(h (Sum.elim t (Sum.elim (fun i => (t i)⁻¹) (fun _ => (1 : ℝ)))) ?_ B ?_).trans ?_` and prove the remaining obligations. Introduce and unpack `(k | k | k)`.

Conclude with `htpos k`. Conclude with `inv_pos.2 (htpos k)`. Conclude with `one_pos`. Introduce `τ`. Take `⟨h1, h2, h3⟩` from `hB τ`.

Use extensionality with `k j`. Break down `k with k | k | k` into its components or cases. Use `congrFun (congrFun h1 k) j` as an intermediate fact. Rewrite `this`, the goal using `[Matrix.diagonal_mul]`. Simplify `this` using `[Matrix.mul_apply]`.

Use `congrFun (congrFun h2 k) j` as an intermediate fact. Rewrite `this`, the goal using `[Matrix.diagonal_mul]`. Simplify `this` using `[Matrix.mul_apply]`. Use `congrFun (congrFun h3 k) j` as an intermediate fact. Rewrite using `[Matrix.diagonal_mul]`.

Simplify using `only [Matrix.mul_apply, Matrix.map_apply, Matrix.fromRows_apply_inr, Sum.elim_inr, Complex.ofReal_one, inv_one, one_mul] at this ⊢`. Conclude with `this`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Rewrite using `[mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (h' t ht) hC`.
-/
theorem lattice_count_stack : ∀ (D : D7) (m n r : ℕ) (X Y : Matrix (Fin m) (Fin r) D.host.E) (X' Y' : Matrix (Fin r) (Fin m) D.host.E) (c : ℝ), 0 < c → ∀ L : ℕ, 0 < L → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ B : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, (∀ τ, Y'.map (tauE D τ) * B τ = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹) * Y'.map (tauE D τ) ∧ X'.map (tauE D τ) * B τ = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)) * X'.map (tauE D τ) ∧ (1 - X * Y' - Y * X').map (tauE D τ) * B τ = (1 - X * Y' - Y * X').map (tauE D τ)) → ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator (fun ξ => ENNReal.ofReal (((1 + ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖) ^ N)⁻¹)) ξ ≤ ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  intro D m n r X Y X' Y' c hc L hL
  have hST : Matrix.fromCols X (Matrix.fromCols Y (1 : Matrix (Fin m) (Fin m) D.host.E)) *
      Matrix.fromRows Y' (Matrix.fromRows X' (1 - X * Y' - Y * X')) = 1 := by
    rw [Matrix.fromCols_mul_fromRows, Matrix.fromCols_mul_fromRows, Matrix.one_mul]
    abel
  obtain ⟨N, C, hC, h⟩ := GlobalTheory.T.latticeCount_sum_bound_of_rational_diagonalising D (Fin r ⊕ Fin r ⊕ Fin m) m n _ _ hST L hL
  obtain ⟨C', hC', h'⟩ := GlobalTheory.T.prod_max_one_pow_le_on_siegelTorusCone r m (Module.finrank ℚ D.host.F * (2 * n)) c hc
  refine ⟨N, C * C', mul_nonneg hC hC', fun t ht B hB => ?_⟩
  have htpos : ∀ i, 0 < t i := ht.1
  refine (h (Sum.elim t (Sum.elim (fun i => (t i)⁻¹) (fun _ => (1 : ℝ)))) ?_ B ?_).trans ?_
  · rintro (k | k | k)
    · exact htpos k
    · exact inv_pos.2 (htpos k)
    · exact one_pos
  · intro τ
    obtain ⟨h1, h2, h3⟩ := hB τ
    ext k j
    rcases k with k | k | k
    · have := congrFun (congrFun h1 k) j
      rw [Matrix.diagonal_mul] at this ⊢
      simpa [Matrix.mul_apply] using this
    · have := congrFun (congrFun h2 k) j
      rw [Matrix.diagonal_mul] at this ⊢
      simpa [Matrix.mul_apply] using this
    · have := congrFun (congrFun h3 k) j
      rw [Matrix.diagonal_mul]
      simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.fromRows_apply_inr, Sum.elim_inr,
        Complex.ofReal_one, inv_one, one_mul] at this ⊢
      exact this
  · apply ENNReal.ofReal_le_ofReal
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (h' t ht) hC

end GlobalTheory.TorusStack
