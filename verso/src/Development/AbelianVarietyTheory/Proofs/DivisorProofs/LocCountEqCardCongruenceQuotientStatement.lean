import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCountEqCardCongruenceQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntLocConjIntLocConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open scoped TensorProduct
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdelicU GlobalTheory.TamOne
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocCountEqCardCongruenceQuotient.lean&line=161#L161)
-/
theorem _root_.GlobalTheory.T.locCount_eq_card_congruence_quotient : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)), Λ.FG → ∀ (v : HeightOneSpectrum (𝓞 F)) (k : ℕ), locCount σ J Λ v k = Nat.card (Quot (congRel σ J Λ v ((v.asIdeal ^ k).map (algebraMap (𝓞 F) (𝓞 E))))) := by
  first | exact @GlobalTheory.TamOne.locCount_eq_card_congRel | exact GlobalTheory.TamOne.locCount_eq_card_congRel | (intros; apply GlobalTheory.TamOne.locCount_eq_card_congRel <;> assumption)
