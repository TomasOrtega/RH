import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

/- English proof (translation)
Simplify using `[vandermondeOf, map_prod, map_sub, aeval_X]`.
-/
theorem aeval_vandermondeOf_X {m : ℕ} (v : Fin m → ℂ) :
    aeval v (vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ))) = vandermondeOf v := by
  simp [vandermondeOf, map_prod, map_sub, aeval_X]

/- English proof (translation)
Introduce `k nu hk`. Establish `hw : ∀ j : Fin k, rootOfUnityPoint k k j = rootOfUnity k ^ (j : ℕ)` using `fun j => by`. Simplify using `[rootOfUnityPoint, j.isLt]`. Establish `key` using `congrArg (aeval (rootOfUnityPoint k k)) (Schur.det_pow_add_staircase_eq nu)`. Rewrite `key` using `[map_mul, h1 k k k nu hk le_rfl, AlgHom.map_det, aeval_vandermondeOf_X]`.

Establish `hv : rootOfUnityPoint k k = fun i : Fin k => rootOfUnity k ^ (i : ℕ)` using `funext hw`. Rewrite `key` using `[hv]`. Rewrite using `[← key]`. Use `congr 1`. Use extensionality with `i j`.

Simplify using `[AlgHom.mapMatrix_apply, Matrix.map_apply, aeval_X, ← pow_mul]`.
-/
theorem SchRootOfUnityBialternant.proof (h1 : SchSchurEvalMatrix.Statement) :
    SchRootOfUnityBialternant.Statement := by
  intro k nu hk
  have hw : ∀ j : Fin k, rootOfUnityPoint k k j = rootOfUnity k ^ (j : ℕ) := fun j => by
    simp [rootOfUnityPoint, j.isLt]
  have key := congrArg (aeval (rootOfUnityPoint k k)) (Schur.det_pow_add_staircase_eq nu)
  rw [map_mul, h1 k k k nu hk le_rfl, AlgHom.map_det, aeval_vandermondeOf_X] at key
  have hv : rootOfUnityPoint k k = fun i : Fin k => rootOfUnity k ^ (i : ℕ) := funext hw
  rw [hv] at key
  rw [← key]
  congr 1
  ext i j
  simp [AlgHom.mapMatrix_apply, Matrix.map_apply, aeval_X, ← pow_mul]

end GroundTheory.Heights₂.Heights.RestTerms
