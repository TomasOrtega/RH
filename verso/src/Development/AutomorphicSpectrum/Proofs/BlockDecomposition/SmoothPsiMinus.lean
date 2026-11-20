import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjInvariantCharacterTransport
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirFun

open Matrix

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Use `show Continuous fun A : Matrix (Fin n) (Fin n) k => glEmbMat k n A i j`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => induction j using Fin.lastCases <;> simpa [glEmbMat] using continuous_const`. Consider the case `cast i`.

Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simpa [glEmbMat] using continuous_const`. Consider the case `cast j`. Simplify using `only [glEmbMat, Fin.lastCases_castSucc]`. Conclude with `(continuous_apply j).comp (continuous_apply i)`.
-/
theorem continuous_glEmbHom (n : ℕ) : Continuous (glEmbHom k n) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun A : Matrix (Fin n) (Fin n) k => glEmbMat k n A i j
  induction i using Fin.lastCases with
  | last => induction j using Fin.lastCases <;> simpa [glEmbMat] using continuous_const
  | cast i =>
    induction j using Fin.lastCases with
    | last => simpa [glEmbMat] using continuous_const
    | cast j =>
      simp only [glEmbMat, Fin.lastCases_castSucc]
      exact (continuous_apply j).comp (continuous_apply i)

/- English proof (translation)
Establish `h : Continuous (glEmb k n)` using `Continuous.units_map _ (continuous_glEmbHom k n)`. Conclude with `h.subtype_mk _`.
-/
theorem continuous_levi (n : ℕ) : Continuous (levi k n) := by
  have h : Continuous (glEmb k n) := Continuous.units_map _ (continuous_glEmbHom k n)
  exact h.subtype_mk _

/- English proof (translation)
Apply the tactic sequence `apply _root_.UpperTheory.Reformulated.B.DYhc8.main <;> assumption`.
-/
theorem smPsiMinus : SmPsiMinus k :=
  by apply _root_.UpperTheory.Reformulated.B.DYhc8.main <;> assumption

end GlobalTheory.CompanionTheory.BZMirFun
