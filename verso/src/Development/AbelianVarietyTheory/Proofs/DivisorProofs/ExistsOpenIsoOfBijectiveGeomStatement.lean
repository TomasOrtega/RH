import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenIsoOfBijectiveGeom
import Mathlib
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isIso_restrict_of_bijective_geomPts` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsOpenIsoOfBijectiveGeom.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.exists_open_iso_of_bijective_geom : ∀ (K : Type) [Field K] [CharZero K] (X T : Scheme.{0}) [IsIntegral X] [IsIntegral T] (f : X ⟶ T) (q : T ⟶ Spec (.of K)), LocallyOfFiniteType f → LocallyQuasiFinite f → IsSeparated f → QuasiCompact f → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T), ∃! x : Spec (.of Ω) ⟶ X, x ≫ f = t) → ∃ U : T.Opens, Nonempty U ∧ IsIso (f ∣_ U) := by
  first | exact @GlobalTheory.isIso_restrict_of_bijective_geomPts | exact GlobalTheory.isIso_restrict_of_bijective_geomPts | (intros; apply GlobalTheory.isIso_restrict_of_bijective_geomPts <;> assumption)
