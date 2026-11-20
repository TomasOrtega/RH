import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CstD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransposeInverseLocal

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal

namespace GlobalTheory.CompanionTheory.UnfoldingAlt.TrBasic

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(g.val.transpose).transpose = g.val`. Rewrite using `[Matrix.transpose_transpose]`.
-/
theorem ti_ti {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (g : GL n R) :
    ti (ti g) = g := by
  apply Units.ext
  change (g.val.transpose).transpose = g.val
  rw [Matrix.transpose_transpose]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [dl3, dg, AdelicGLn.diagonal]`.
-/
theorem rational_sign_diag_adelic : dia dl3 = (dg 1 (-1) 1 : GL (Fin 3) 𝔸[ℚ]) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dl3, dg, AdelicGLn.diagonal]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [w3, ti, dg, uni, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct] <;> ring`.
-/
theorem conj_uni {R : Type*} [CommRing R] (x y z : R) :
    w3 * ti (dg 1 (-1) 1 : GL (Fin 3) R) * ti (uni x y z) =
      uni z (x * z - y) x * (w3 * ti (dg 1 (-1) 1 : GL (Fin 3) R)) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [w3, ti, dg, uni, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct] <;> ring

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [w3, ti, dg, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct] <;> ring`.
-/
theorem conj_cen {R : Type*} [CommRing R] (a : Rˣ) :
    w3 * ti (dg 1 (-1) 1 : GL (Fin 3) R) * ti (dg a a a) =
      dg a⁻¹ a⁻¹ a⁻¹ * (w3 * ti (dg 1 (-1) 1 : GL (Fin 3) R)) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [w3, ti, dg, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct] <;> ring

/- English proof (translation)
Express the relevant statement in the definitionally equal form `W (w3 * ti (dia dl3 * g)) = _`. Rewrite using `[GlobalTheory.CompanionTheory.TransposeInverse.ti_mul, mul_assoc]`.
-/
theorem tr_apply (W : G3 → ℂ) (g : G3) : tr W g = W (w3 * ti (dia dl3) * ti g) := by
  change W (w3 * ti (dia dl3 * g)) = _
  rw [GlobalTheory.CompanionTheory.TransposeInverse.ti_mul, mul_assoc]

/- English proof (translation)
Use `⟨tr_apply, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `W h g`. Rewrite using `[tr_apply, tr_apply, GlobalTheory.CompanionTheory.TransposeInverse.ti_mul]`. Simplify using `only [mul_assoc]`. Introduce `W W' e`.

Use function extensionality and compare the values at `x`. Use `congrFun e (ti ((w3 * ti (dia dl3))⁻¹ * x))` as an intermediate fact. Rewrite `this` using `[tr_apply, tr_apply, ti_ti, mul_inv_cancel_left]`. Then use the resulting hypothesis. Introduce `W hW x y z g`. Rewrite using `[tr_apply, tr_apply, GlobalTheory.CompanionTheory.TransposeInverse.ti_mul, ← mul_assoc, rational_sign_diag_adelic, conj_uni, mul_assoc, hW, add_comm z x]`.

Introduce `W hW a g`. Rewrite using `[tr_apply, tr_apply, GlobalTheory.CompanionTheory.TransposeInverse.ti_mul, ← mul_assoc, rational_sign_diag_adelic, conj_cen]`. Use `hW a⁻¹ (w3 * ti (dg 1 (-1) 1 : GL (Fin 3) 𝔸[ℚ]) * ti g)` as an intermediate fact. Rewrite using `[mul_assoc, this]`.
-/
theorem main :
    (∀ (W : G3 → ℂ) (g : G3), tr W g = W (w3 * ti (dia dl3) * ti g)) ∧
    (∀ (W : G3 → ℂ) (h g : G3), tr W (g * h) = tr (fun x => W (x * ti h)) g) ∧
    Function.Injective tr ∧
    (∀ W : G3 → ℂ, (∀ x y z g, W (uni x y z * g) = (adelicChar ℚ (x + z) : ℂ) * W g) →
      ∀ x y z g, tr W (uni x y z * g) = (adelicChar ℚ (x + z) : ℂ) * tr W g) ∧
    (∀ W : G3 → ℂ, (∀ (a : (𝔸[ℚ])ˣ) g, W (dg a a a * g) = W g) →
      ∀ (a : (𝔸[ℚ])ˣ) g, tr W (dg a a a * g) = tr W g) := by
  refine ⟨tr_apply, ?_, ?_, ?_, ?_⟩
  · intro W h g
    rw [tr_apply, tr_apply, GlobalTheory.CompanionTheory.TransposeInverse.ti_mul]
    simp only [mul_assoc]
  · intro W W' e
    funext x
    have := congrFun e (ti ((w3 * ti (dia dl3))⁻¹ * x))
    rwa [tr_apply, tr_apply, ti_ti, mul_inv_cancel_left] at this
  · intro W hW x y z g
    rw [tr_apply, tr_apply, GlobalTheory.CompanionTheory.TransposeInverse.ti_mul, ← mul_assoc, rational_sign_diag_adelic, conj_uni, mul_assoc,
      hW, add_comm z x]
  · intro W hW a g
    rw [tr_apply, tr_apply, GlobalTheory.CompanionTheory.TransposeInverse.ti_mul, ← mul_assoc, rational_sign_diag_adelic, conj_cen]
    have := hW a⁻¹ (w3 * ti (dg 1 (-1) 1 : GL (Fin 3) 𝔸[ℚ]) * ti g)
    rw [mul_assoc, this]

end GlobalTheory.CompanionTheory.UnfoldingAlt.TrBasic

end
