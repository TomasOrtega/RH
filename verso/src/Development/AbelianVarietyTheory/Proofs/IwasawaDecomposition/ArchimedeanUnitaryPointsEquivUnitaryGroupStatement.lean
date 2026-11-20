import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroup
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FArchimedeanUnitaryPointsEquivUnitaryGroup.lean&line=230#L230)
-/
theorem _root_.GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ : E →+* ℂ), ∃ e : embU n τ ≃ₜ* Matrix.unitaryGroup (Fin n) ℂ, ∀ x : embU n τ, GlobalTheory.Branching.unitaryIncl n (e x) = cEmb τ (x : UA E n) := by
  first | exact @GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup | exact GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup | (intros; apply GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup <;> assumption)
