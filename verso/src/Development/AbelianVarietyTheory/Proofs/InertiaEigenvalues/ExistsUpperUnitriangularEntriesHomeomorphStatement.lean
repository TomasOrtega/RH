import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUpperUnitriangularEntriesHomeomorph
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsUpperUnitriangularEntriesHomeomorph.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.exists_upperUnitriangular_entries_homeomorph : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (n : ℕ),
    ∃ e : (GlobalTheory.SmGL.unipB R (Fin n)) ≃ₜ ({p : Fin n × Fin n // p.1 < p.2} → R),
      ∀ u : GlobalTheory.SmGL.unipB R (Fin n), e u = fun p => ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2 := by
  first | exact @GlobalTheory.UnipCoords.unipCoordsHomeomorph | exact GlobalTheory.UnipCoords.unipCoordsHomeomorph | (intros; apply GlobalTheory.UnipCoords.unipCoordsHomeomorph <;> assumption)
