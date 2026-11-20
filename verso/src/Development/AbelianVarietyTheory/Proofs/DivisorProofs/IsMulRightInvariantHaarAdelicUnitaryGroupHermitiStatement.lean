import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
import Formalism.LocalRingCardinality.DataExtra
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsMulRightInvariantHaarAdelicUnitaryGroupHermiti.lean&line=291#L291)
-/
theorem _root_.GlobalTheory.T.isMulRightInvariant_haar_adelicUnitaryGroup_hermitianSpace : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure | exact GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure | (intros; apply GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure <;> assumption)
