import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardMeasureUnitaryPQEqVolumeSmulCompactDual
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.VolUFactProdMulLe
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FStandardMeasureUnitaryPQEqVolumeSmulCompactDual.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.standardMeasure_unitaryPQ_eq_volume_smul_compactDual : ∀ (cd : CDHaar) (p q : ℕ) (m : Measure (UpqT p q)), Lev.IsMinf m → m = ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) • cd.cd p q := by
  first | exact @GlobalTheory.LowRow.CompactDualScale.isMinf_eq_volU_smul_cd | exact GlobalTheory.LowRow.CompactDualScale.isMinf_eq_volU_smul_cd | (intros; apply GlobalTheory.LowRow.CompactDualScale.isMinf_eq_volU_smul_cd <;> assumption)
