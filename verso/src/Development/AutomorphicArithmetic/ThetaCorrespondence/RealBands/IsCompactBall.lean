import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.DecaysZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.RightDerivativeZeroOutsideSupport

open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

/- English proof (translation)
Introduce `n ε`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `R`. Take `⟨hemb, -⟩` from `isClosedEmbeddingMatrix n ε`. Establish `hK` using `(hermitian_small_ball n ε).1 R`.

Establish `hpre` using `hemb.isCompact_preimage hK`. Use `hpre using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `⟨g.2, h⟩`. Introduce `h`. Conclude with `h.2`. Introduce `x y`.

Rewrite using `[← Real.sqrt_mul (frobenius_nonneg x)]`. Conclude with `Real.sqrt_le_sqrt (frobenius_mul_le x y)`. Introduce `g`. Establish `h1 : umat g⁻¹ = Jm ε * (coeMatrixAlt ε g)ᴴ * Jm ε` using `coeMatrix_inv_eq ε g`. Establish `h2 : coeMatrixAlt ε g = umat g` using `rfl`.

Rewrite using `[h1, h2]`. Establish `hd : ∀ i, ‖(if ε i = true then (1 : ℂ) else -1)‖ = 1`. Introduce `i`. Apply the tactic sequence `split <;> simp`. Simplify using `only [hs, Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, norm_mul, hd, one_mul, mul_one, norm_star]`.

Conclude with `Finset.sum_comm`. Conclude with `continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)`.
-/
theorem UpperTheory.Lit.Cusp.isCompact_ball :
    ∀ (n : ℕ) (ε : Fin n → Bool), (∀ R : ℝ, IsCompact {g : UJ ε | hs (umat g) ≤ R}) ∧
      (∀ x y : Matrix (Fin n) (Fin n) ℂ, Real.sqrt (hs (x * y)) ≤ Real.sqrt (hs x) * Real.sqrt (hs y)) ∧
      (∀ g : UJ ε, hs (umat g⁻¹) = hs (umat g)) ∧ Continuous (fun g : UJ ε => hs (umat g)) := by
  intro n ε
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R
    obtain ⟨hemb, -⟩ := isClosedEmbeddingMatrix n ε
    have hK := (hermitian_small_ball n ε).1 R
    have hpre := hemb.isCompact_preimage hK
    convert hpre using 1
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · intro h
      exact ⟨g.2, h⟩
    · intro h
      exact h.2
  · intro x y
    rw [← Real.sqrt_mul (frobenius_nonneg x)]
    exact Real.sqrt_le_sqrt (frobenius_mul_le x y)
  · intro g
    have h1 : umat g⁻¹ = Jm ε * (coeMatrixAlt ε g)ᴴ * Jm ε := coeMatrix_inv_eq ε g
    have h2 : coeMatrixAlt ε g = umat g := rfl
    rw [h1, h2]
    have hd : ∀ i, ‖(if ε i = true then (1 : ℂ) else -1)‖ = 1 := by
      intro i
      split <;> simp
    simp only [hs, Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, norm_mul, hd,
      one_mul, mul_one, norm_star]
    exact Finset.sum_comm
  · exact continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)
