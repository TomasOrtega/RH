import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMir

/- English proof (translation)
Introduce `ψ n`. Establish `h : chrV k ψ n = chrA k ψ (Pi.single (Fin.last n) 1)`. Use extensionality with `v`. Simplify using `[chrV, chrA]`. Rewrite using `[mirChar, thetaA, h]`.
-/
theorem mirChar_eq_thetaA_single (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : GlobalTheory.BZMir.Fun.MirCharEq k := by
  intro ψ n
  have h : chrV k ψ n = chrA k ψ (Pi.single (Fin.last n) 1) := by
    ext v
    simp [chrV, chrA]
  rw [mirChar, thetaA, h]

end GlobalTheory.CompanionTheory.BZMir
