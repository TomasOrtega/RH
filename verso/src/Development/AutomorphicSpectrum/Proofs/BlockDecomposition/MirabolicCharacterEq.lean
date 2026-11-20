import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMir

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem mirChar_eq_thetaA_single (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : GlobalTheory.BZMir.Fun.MirCharEq k := by
  intro ψ n
  have h : chrV k ψ n = chrA k ψ (Pi.single (Fin.last n) 1) := by
    ext v
    simp [chrV, chrA]
  rw [mirChar, thetaA, h]

end GlobalTheory.CompanionTheory.BZMir
