import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticesLevelOneGenus
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FHermitianLatticesLevelOneGenus.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.hermitianLattices_level_one_genus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → TLat cm.sig J T f M → ∃ h : UPts cm.sig J (Ad F), ∀ x, (h⁻¹).1.1 *ᵥ x ∈ hat F L ↔ x ∈ hat F M := by
  first | exact @GlobalTheory.St.G.tlat_one_genus | exact GlobalTheory.St.G.tlat_one_genus | (intros; apply GlobalTheory.St.G.tlat_one_genus <;> assumption)
