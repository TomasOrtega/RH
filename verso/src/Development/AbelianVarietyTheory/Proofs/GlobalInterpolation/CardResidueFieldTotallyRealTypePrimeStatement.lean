import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CardResidueFieldTotallyRealTypePrime
import Formalism.LocalToGlobal.HermitianForms.TiedSym
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GSplit
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SplitResidueCard.card_kv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FCardResidueFieldTotallyRealTypePrime.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.card_residue_field_totally_real_type_prime : ∀ (D : D7) (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal → Nat.card (kv D.host.F v) = D.host.g i := by
  first | exact @GlobalTheory.SplitResidueCard.card_kv | exact GlobalTheory.SplitResidueCard.card_kv | (intros; apply GlobalTheory.SplitResidueCard.card_kv <;> assumption)
