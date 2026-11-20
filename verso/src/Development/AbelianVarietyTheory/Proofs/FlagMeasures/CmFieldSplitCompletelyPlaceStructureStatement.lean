import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitCompletelyPlaceStructure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.St.G.SplitPrime.split_place` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FCmFieldSplitCompletelyPlaceStructure.lean&line=244#L244)
-/
theorem _root_.GlobalTheory.T.cmField_splitCompletely_place_structure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (p : ℕ), p.Prime → SplitsIn E p → ({v : HeightOneSpectrum (𝓞 F) | (p : 𝓞 F) ∈ v.asIdeal}.ncard = Module.finrank ℚ F) ∧ ∀ (v : HeightOneSpectrum (𝓞 F)), (p : 𝓞 F) ∈ v.asIdeal → Nat.card (kv F v) = p ∧ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {(p : v.adicCompletionIntegers F)} ∧ ∃ sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F, (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) ∧ ∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a) := by
  first | exact @GlobalTheory.St.G.SplitPrime.split_place | exact GlobalTheory.St.G.SplitPrime.split_place | (intros; apply GlobalTheory.St.G.SplitPrime.split_place <;> assumption)
