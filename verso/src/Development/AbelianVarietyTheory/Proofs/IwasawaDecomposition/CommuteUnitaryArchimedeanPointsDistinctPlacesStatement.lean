import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteUnitaryArchimedeanPointsDistinctPlaces
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FCommuteUnitaryArchimedeanPointsDistinctPlaces.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.commute_unitaryArchimedeanPoints_distinct_places : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ τ' : E →+* ℂ), InfinitePlace.mk τ ≠ InfinitePlace.mk τ' → ∀ x ∈ embU n τ, ∀ y ∈ embU n τ', Commute x y := by
  first | exact @GlobalTheory.UnitaryBC.embU_commute | exact GlobalTheory.UnitaryBC.embU_commute | (intros; apply GlobalTheory.UnitaryBC.embU_commute <;> assumption)
