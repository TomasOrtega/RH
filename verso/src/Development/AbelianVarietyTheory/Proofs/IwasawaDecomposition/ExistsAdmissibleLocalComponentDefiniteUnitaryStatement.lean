import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdmissibleLocalComponentDefiniteUnitary
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsAdmissibleLocalComponentDefiniteUnitary.lean&line=89#L89)
-/
theorem _root_.GlobalTheory.T.exists_admissible_localComponent_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (w : HeightOneSpectrum (𝓞 E)), ∃ σ : SmIrr (locU n w), IsAdmissible σ.ρ ∧ IsCompAlong π.V (locU n w) (MonoidHom.id _) σ.ρ := by
  first | exact @GlobalTheory.DefU.LocAdm.exists_admissible_comp | exact GlobalTheory.DefU.LocAdm.exists_admissible_comp | (intros; apply GlobalTheory.DefU.LocAdm.exists_admissible_comp <;> assumption)
