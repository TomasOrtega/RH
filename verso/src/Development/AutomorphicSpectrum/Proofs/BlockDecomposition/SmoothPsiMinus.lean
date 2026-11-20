import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjInvariantCharacterTransport
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirFun

open Matrix

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Proceed by induction. Treat this case separately. Treat this case separately. Proceed by induction.

Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem continuous_levi (n : ℕ) : Continuous (levi k n) := by
  have h : Continuous (glEmb k n) := Continuous.units_map _ (continuous_glEmbHom k n)
  exact h.subtype_mk _

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem smPsiMinus : SmPsiMinus k :=
  by apply _root_.UpperTheory.Reformulated.B.DYhc8.main <;> assumption

end GlobalTheory.CompanionTheory.BZMirFun
