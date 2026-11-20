import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockUnitaryFiniteSubspaceOfLeStable
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HoweR.unitOn_of_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsBlockUnitaryFiniteSubspaceOfLeStable.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.isBlockUnitaryFiniteSubspace_of_le_stable : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ U U' : Submodule ℂ M, UnitOn s F U → U' ≤ U → (∀ a b, s a = s b → ∀ u ∈ U', F a b u ∈ U') → UnitOn s F U' := by
  first | exact @GlobalTheory.HoweR.unitOn_of_le | exact GlobalTheory.HoweR.unitOn_of_le | (intros; apply GlobalTheory.HoweR.unitOn_of_le <;> assumption)
