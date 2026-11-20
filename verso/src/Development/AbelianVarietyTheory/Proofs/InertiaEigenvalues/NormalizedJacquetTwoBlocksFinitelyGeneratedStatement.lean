import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedJacquetTwoBlocksFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JacquetFinGen.jacquet_fg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNormalizedJacquetTwoBlocksFinitelyGenerated.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.normalizedJacquetTwoBlocks_finitelyGenerated : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b n : ℕ) (h : a + b = n) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible → ∃ s : Finset (Jacquet π (unipRad k (two (stdSum h)))), Submodule.span ℂ {w | ∃ g : GL (Fin a) k × GL (Fin b) k, ∃ v ∈ s, w = jac₂ (stdSum h) π g v} = ⊤ := by
  first | exact @GlobalTheory.JacquetFinGen.jacquet_fg | exact GlobalTheory.JacquetFinGen.jacquet_fg | (intros; apply GlobalTheory.JacquetFinGen.jacquet_fg <;> assumption)
