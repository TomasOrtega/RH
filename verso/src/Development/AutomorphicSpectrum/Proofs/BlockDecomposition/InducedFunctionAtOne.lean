import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem one_mem_GLs (n : ℕ) : (1 : Mat n) ∈ GLs n :=
  unit_mem (1 : Matrix.unitaryGroup (Fin n) ℂ)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ini_injective {n : ℕ} (j : Fin n) : Function.Injective (ini j) :=
  Fin.castLE_injective j.isLt

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem lm_one {n : ℕ} (j : Fin n) : lm j (1 : Mat n) = 1 := by
  unfold lm
  rw [Matrix.submatrix_one _ (ini_injective j), Matrix.det_one]

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities.
-/
theorem gm_one {n : ℕ} (j : Fin n) : gm j (1 : Mat n) = 1 := by
  unfold gm
  have h : ((1 : Mat n).submatrix (ini j) id) * ((1 : Mat n).submatrix (ini j) id)ᴴ = 1 := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id, Matrix.one_apply]
    simp [(ini_injective j).eq_iff]
  rw [h, Matrix.det_one]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem fRaw_one (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ) : fRaw lam lev 1 = 1 := by
  unfold fRaw
  rw [Set.indicator_of_mem (one_mem_GLs n)]
  simp [lm_one, gm_one]

end GlobalTheory.CompanionTheory.ModelS
