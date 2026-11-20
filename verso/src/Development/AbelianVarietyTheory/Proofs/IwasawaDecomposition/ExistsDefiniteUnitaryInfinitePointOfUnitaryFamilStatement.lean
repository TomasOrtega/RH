import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDefiniteUnitaryInfinitePointOfUnitaryFamil
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsDefiniteUnitaryInfinitePointOfUnitaryFamil.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.exists_definiteUnitaryInfinitePoint_of_unitary_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (g : InfinitePlace E → GL (Fin n) ℂ), (∀ v, ((g v : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∃ x ∈ infU E n, cAll x = g := by
  first | exact @GlobalTheory.InfSurj.exists_infU_cAll_eq | exact GlobalTheory.InfSurj.exists_infU_cAll_eq | (intros; apply GlobalTheory.InfSurj.exists_infU_cAll_eq <;> assumption)
