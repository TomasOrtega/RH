import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingGoodAtUniformizer
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemGenLatSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.SUCong
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalRingGoodAtUniformizer.lean&line=386#L386)
-/
theorem _root_.GlobalTheory.T.local_ring_good_at_uniformizer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (π : 𝓞 (maximalRealSubfield E)), π ∈ v.asIdeal → π ∉ v.asIdeal ^ 2 → GoodRing (intA (E := E) v) (sigR (Fv (maximalRealSubfield E) v) (IsCMField.complexConj E).toAlgHom) ((1 : Fv (maximalRealSubfield E) v) ⊗ₜ[maximalRealSubfield E] algebraMap (maximalRealSubfield E) E (π : maximalRealSubfield E)) (Ideal.absNorm v.asIdeal) := by
  first | exact @GlobalTheory.SUCong.goodRing_intA_of_unr | exact GlobalTheory.SUCong.goodRing_intA_of_unr | (intros; apply GlobalTheory.SUCong.goodRing_intA_of_unr <;> assumption)
