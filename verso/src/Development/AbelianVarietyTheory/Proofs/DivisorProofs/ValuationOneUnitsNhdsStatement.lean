import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationOneUnitsNhds
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.units_valuation_eq_one_mem_nhds_one` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FValuationOneUnitsNhds.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.valuation_one_units_nhds : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    {x : kˣ | ValuativeRel.valuation k (x : k) = 1} ∈ 𝓝 (1 : kˣ) := by
  first | exact @GlobalTheory.units_valuation_eq_one_mem_nhds_one | exact GlobalTheory.units_valuation_eq_one_mem_nhds_one | (intros; apply GlobalTheory.units_valuation_eq_one_mem_nhds_one <;> assumption)
