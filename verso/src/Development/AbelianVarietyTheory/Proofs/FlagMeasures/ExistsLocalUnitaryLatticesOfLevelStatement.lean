import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLocalUnitaryLatticesOfLevel
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.St.G.exists_unitary_of_TLat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsLocalUnitaryLatticesOfLevel.lean&line=328#L328)
-/
theorem _root_.GlobalTheory.T.exists_localUnitary_lattices_of_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → TLat cm.sig J T f M → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∃ h ∈ UPts cm.sig J (v.adicCompletion F), ∀ x, x ∈ loc v L ↔ h.1 *ᵥ x ∈ loc v M := by
  first | exact @GlobalTheory.St.G.exists_unitary_of_TLat | exact GlobalTheory.St.G.exists_unitary_of_TLat | (intros; apply GlobalTheory.St.G.exists_unitary_of_TLat <;> assumption)
