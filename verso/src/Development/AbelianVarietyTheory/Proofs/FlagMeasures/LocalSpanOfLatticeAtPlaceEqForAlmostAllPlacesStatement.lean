import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalSpanOfLatticeAtPlaceEqForAlmostAllPlaces
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FLocalSpanOfLatticeAtPlaceEqForAlmostAllPlaces.lean&line=105#L105)
-/
theorem _root_.GlobalTheory.T.localSpanOfLatticeAtPlace_eq_for_almost_all_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat M → {v : HeightOneSpectrum (𝓞 F) | loc v L ≠ loc v M}.Finite := by
  first | exact @GlobalTheory.St.G.loc_eq_almost_all | exact GlobalTheory.St.G.loc_eq_almost_all | (intros; apply GlobalTheory.St.G.loc_eq_almost_all <;> assumption)
