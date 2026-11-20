import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceComponentEqOneIffComponentsOverEqOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FPlaceComponentEqOneIffComponentsOverEqOne.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.placeComponent_eq_one_iff_components_over_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (z : AfE F E), Formalism.UG.prV (E := E) v z = 1 ↔ ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → GlobalTheory.Mem.Col2.afIso F E z P = 1 := by
  first | exact @GlobalTheory.AfIsoPrV.prV_eq_one_iff_afIso | exact GlobalTheory.AfIsoPrV.prV_eq_one_iff_afIso | (intros; apply GlobalTheory.AfIsoPrV.prV_eq_one_iff_afIso <;> assumption)
