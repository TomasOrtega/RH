import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldUnitMemOpenArchimedeanUnits
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitsDense.exists_unit_mem_open` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFieldUnitMemOpenArchimedeanUnits.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.exists_field_unit_mem_open_archimedean_units : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (V : Set (Cinf E)ˣ), IsOpen V → V.Nonempty → ∃ α : Eˣ, Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom α ∈ V := by
  first | exact @GlobalTheory.UnitsDense.exists_unit_mem_open | exact GlobalTheory.UnitsDense.exists_unit_mem_open | (intros; apply GlobalTheory.UnitsDense.exists_unit_mem_open <;> assumption)
