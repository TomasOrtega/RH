import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexLocalCongruenceEqAbsNormPow
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemGenLatSmul
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRelIndexLocalCongruenceEqAbsNormPow.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.relIndex_local_congruence_eq_absNorm_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), 2 ≤ r → Unr E → SelfDualLat G Λ → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (k : ℕ), 1 ≤ k → (GlobalTheory.TamCnt.locCong (IsCMField.complexConj E).toAlgHom Gᵀ Λ v (k + 1)).relIndex (GlobalTheory.TamCnt.locCong (IsCMField.complexConj E).toAlgHom Gᵀ Λ v k) = Ideal.absNorm v.asIdeal ^ (r ^ 2 - 1) := by
  first | exact @GlobalTheory.TamCnt.relIndex_locCong | exact GlobalTheory.TamCnt.relIndex_locCong | (intros; apply GlobalTheory.TamCnt.relIndex_locCong <;> assumption)
