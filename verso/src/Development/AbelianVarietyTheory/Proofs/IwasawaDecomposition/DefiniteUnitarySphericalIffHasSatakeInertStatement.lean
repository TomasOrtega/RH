import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitarySphericalIffHasSatakeInert
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FDefiniteUnitarySphericalIffHasSatakeInert.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.definiteUnitary_spherical_iff_hasSatake_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AU E n) (w : HeightOneSpectrum (𝓞 E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → ¬ IsSplitAt w → (π.Sph w ↔ ∃ α, π.IsSat w α) := by
  first | exact @GlobalTheory.InertSatake.sph_iff_isSat | exact GlobalTheory.InertSatake.sph_iff_isSat | (intros; apply GlobalTheory.InertSatake.sph_iff_isSat <;> assumption)
