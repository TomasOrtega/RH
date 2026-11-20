import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLocalUnitaryOfSelfDualAtPlace
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsLocalUnitaryOfSelfDualAtPlace.lean&line=304#L304)
-/
theorem _root_.GlobalTheory.T.exists_localUnitary_of_selfDual_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (L M : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat M → ∀ (v : HeightOneSpectrum (𝓞 F)), SelfDualAt cm.sig J v L → SelfDualAt cm.sig J v M → ∃ h ∈ UPts cm.sig J (v.adicCompletion F), ∀ x, x ∈ loc v L ↔ h.1 *ᵥ x ∈ loc v M := by
  first | exact @GlobalTheory.St.G.Unimod.exists_unitary_of_selfDualAt | exact GlobalTheory.St.G.Unimod.exists_unitary_of_selfDualAt | (intros; apply GlobalTheory.St.G.Unimod.exists_unitary_of_selfDualAt <;> assumption)
