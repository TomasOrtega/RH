import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelTransfer.LzOutRight

open Matrix

noncomputable section

namespace PIQnLT

open Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k i r' : ℕ}

set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Establish `h0 : ιLev k i r' 0 = 1 - Lz k i r' 1`. Rewrite using `[← Lz_one (k := k) (i := i) (r' := r') hL]`. Normalize the expressions using the abelian group laws. Use `letI : NormedRing (Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℂ (Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) := Matrix.linftyOpNormedAlgebra`.

Use `letI : NormedRing (Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℂ (Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ) := Matrix.linftyOpNormedAlgebra`. Establish `h1` using `NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y`. Establish `h3` using `NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (Lz k i r' Y)`. Establish `hc : Continuous (LzL k i r')` using `(LzL k i r').continuous_of_finiteDimensional`.

Establish `h2` using `h1.map (LzL k i r') hc`. Establish `hfun : (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (Lz k i r' Y) ^ n) = (fun n : ℕ => (LzL k i r') (((n.factorial : ℂ)⁻¹) • Y ^ n) + (if n = 0 then (1 - Lz k i r' 1) else 0))`. Use function extensionality and compare the values at `n`. Consider the cases of `n with`. Consider the case `zero => simp [LzL_apply]`.

Consider the case `succ m`. Establish `hm : m + 1 ≠ 0` using `by omega`. Rewrite using `[if_neg hm, add_zero, LinearMap.map_smul, LzL_apply, Lz_pow hL]`. Establish `h5 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (Lz k i r' Y) ^ n) (LzL k i r' (NormedSpace.exp Y) + (1 - Lz k i r' 1))`. Rewrite using `[hfun]`.

Conclude with `h2.add (hasSum_ite_eq 0 (1 - Lz k i r' 1))`. Establish `e` using `h3.unique h5`. Use `e.trans ?_` and prove the remaining obligations. Rewrite using `[ιLev_eq, h0]`. Both sides reduce to the same expression.
-/
theorem exp_Lz (hL : LevHom) (Y : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    NormedSpace.exp (Lz k i r' Y) = ιLev k i r' (NormedSpace.exp Y) := by
  have h0 : ιLev k i r' 0 = 1 - Lz k i r' 1 := by
    rw [← Lz_one (k := k) (i := i) (r' := r') hL]
    abel
  letI : NormedRing (Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :=
    Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ) :=
    Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ) :=
    Matrix.linftyOpNormedAlgebra
  have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y
  have h3 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (Lz k i r' Y)
  have hc : Continuous (LzL k i r') := (LzL k i r').continuous_of_finiteDimensional
  have h2 := h1.map (LzL k i r') hc
  have hfun : (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (Lz k i r' Y) ^ n) =
      (fun n : ℕ => (LzL k i r') (((n.factorial : ℂ)⁻¹) • Y ^ n) +
        (if n = 0 then (1 - Lz k i r' 1) else 0)) := by
    funext n
    cases n with
    | zero => simp [LzL_apply]
    | succ m =>
      have hm : m + 1 ≠ 0 := by omega
      rw [if_neg hm, add_zero, LinearMap.map_smul, LzL_apply, Lz_pow hL]
  have h5 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (Lz k i r' Y) ^ n)
      (LzL k i r' (NormedSpace.exp Y) + (1 - Lz k i r' 1)) := by
    rw [hfun]
    exact h2.add (hasSum_ite_eq 0 (1 - Lz k i r' 1))
  have e := h3.unique h5
  refine e.trans ?_
  rw [ιLev_eq, h0]
  rfl

end PIQnLT
