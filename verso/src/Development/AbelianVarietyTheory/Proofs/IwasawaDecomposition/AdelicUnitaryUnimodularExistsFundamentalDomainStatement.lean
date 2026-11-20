import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FAdelicUnitaryUnimodularExistsFundamentalDomain.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.adelicUnitary_unimodular_exists_fundamentalDomain : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)), μ.IsHaarMeasure → μ.IsMulRightInvariant ∧ ∃ 𝓕, IsFundamentalDomain (GQ V) 𝓕 μ := by
  first | exact @GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain | exact GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain | (intros; apply GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain <;> assumption)
