import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsCechNerveQuasiIsoOfSmoothSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EtC.chains_cechAug_quasiIso_of_smooth` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FChainsCechNerveQuasiIsoOfSmoothSurjective.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.chains_cechNerve_quasiIso_of_smooth_surjective : ∀ (R : Type) [CommRing R] {Y X : Scheme.{0}} (f : Y ⟶ X) [Smooth f] [Surjective f], QuasiIso ((chains R).map (cechAug f)) := by
  first | exact @GlobalTheory.EtC.chains_cechAug_quasiIso_of_smooth | exact GlobalTheory.EtC.chains_cechAug_quasiIso_of_smooth | (intros; apply GlobalTheory.EtC.chains_cechAug_quasiIso_of_smooth <;> assumption)
