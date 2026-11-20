import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockUnitaryFiniteSubspaceMapIntertwiner
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HoweR.unitOn_map` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsBlockUnitaryFiniteSubspaceMapIntertwiner.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.isBlockUnitaryFiniteSubspace_map_intertwiner : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (F' : ι → ι → Module.End ℂ M') (f : M →ₗ[ℂ] M') (U : Submodule ℂ M), (∀ a b, s a = s b → ∀ x ∈ U, f (F a b x) = F' a b (f x)) → UnitOn s F U → UnitOn s F' (U.map f) := by
  first | exact @GlobalTheory.HoweR.unitOn_map | exact GlobalTheory.HoweR.unitOn_map | (intros; apply GlobalTheory.HoweR.unitOn_map <;> assumption)
