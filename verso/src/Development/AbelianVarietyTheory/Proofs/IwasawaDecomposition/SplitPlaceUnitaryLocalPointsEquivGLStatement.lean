import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FSplitPlaceUnitaryLocalPointsEquivGL.lean&line=216#L216)
-/
theorem _root_.GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ∃ e : locU n w ≃ₜ* GL (Fin n) (w.adicCompletion E), ∀ x : locU n w, e x = cLoc w (x : UA E n) := by
  first | exact @GlobalTheory.locU_equiv_GL | exact GlobalTheory.locU_equiv_GL | (intros; apply GlobalTheory.locU_equiv_GL <;> assumption)
