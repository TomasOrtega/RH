import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleBaseChangeMemIdeal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLogHomIsMultipleOfLogAbs
import GroundTheory.GlobalFields.TateThesis.AdeleIdealMeasure
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped nonZeroDivisors TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdeleBaseChangeMemIdeal.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.adele_base_change_mem_ideal : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (h𝔞 : 𝔞 ≠ 0) (z : AE F E),
    (∀ v : Pl F, compFin F E v z ∈ GlobalTheory.LocIdeal.locId v 𝔞) →
    (GroundTheory.Global.AdeleBaseChange.adeleTensorAlgEquivLeft F E z).2 ∈ GroundTheory.Global.idealFiniteAdeles (Units.mk0 𝔞 h𝔞) := by
  first | exact @GlobalTheory.LocIdealAdele.mem_idealFiniteAdeles_of_locId | exact GlobalTheory.LocIdealAdele.mem_idealFiniteAdeles_of_locId | (intros; apply GlobalTheory.LocIdealAdele.mem_idealFiniteAdeles_of_locId <;> assumption)
