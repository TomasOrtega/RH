import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsIsoOfFreeIso
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FChainsIsoOfFreeIso.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.chains_iso_of_free_iso : ∀ (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E'), (∀ n, IsIso ((free R).map (f.app n))) → IsIso ((chains R).map f) := by
  first | exact @GlobalTheory.EtC.isIso_chains_map_of_isIso_free | exact GlobalTheory.EtC.isIso_chains_map_of_isIso_free | (intros; apply GlobalTheory.EtC.isIso_chains_map_of_isIso_free <;> assumption)
