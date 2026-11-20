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
The claim follows from `unit_mem (1 : Matrix.unitaryGroup (Fin n) ℂ)`.
-/
theorem one_mem_GLs (n : ℕ) : (1 : Mat n) ∈ GLs n :=
  unit_mem (1 : Matrix.unitaryGroup (Fin n) ℂ)

/- English proof (translation)
The claim follows from `Fin.castLE_injective j.isLt`.
-/
theorem ini_injective {n : ℕ} (j : Fin n) : Function.Injective (ini j) :=
  Fin.castLE_injective j.isLt

/- English proof (translation)
Unfold `lm`. Rewrite using `[Matrix.submatrix_one _ (ini_injective j), Matrix.det_one]`.
-/
theorem lm_one {n : ℕ} (j : Fin n) : lm j (1 : Mat n) = 1 := by
  unfold lm
  rw [Matrix.submatrix_one _ (ini_injective j), Matrix.det_one]

/- English proof (translation)
Unfold `gm`. Establish `h : ((1 : Mat n).submatrix (ini j) id) * ((1 : Mat n).submatrix (ini j) id)ᴴ = 1`. Use extensionality with `a b`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id, Matrix.one_apply]`. Simplify using `[(ini_injective j).eq_iff]`.

Rewrite using `[h, Matrix.det_one]`.
-/
theorem gm_one {n : ℕ} (j : Fin n) : gm j (1 : Mat n) = 1 := by
  unfold gm
  have h : ((1 : Mat n).submatrix (ini j) id) * ((1 : Mat n).submatrix (ini j) id)ᴴ = 1 := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id, Matrix.one_apply]
    simp [(ini_injective j).eq_iff]
  rw [h, Matrix.det_one]

/- English proof (translation)
Unfold `fRaw`. Rewrite using `[Set.indicator_of_mem (one_mem_GLs n)]`. Simplify using `[lm_one, gm_one]`.
-/
theorem fRaw_one (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ) : fRaw lam lev 1 = 1 := by
  unfold fRaw
  rw [Set.indicator_of_mem (one_mem_GLs n)]
  simp [lm_one, gm_one]

end GlobalTheory.CompanionTheory.ModelS
