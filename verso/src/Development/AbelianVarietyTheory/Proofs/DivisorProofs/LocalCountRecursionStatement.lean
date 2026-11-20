import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCountRecursion
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalCountRecursion.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.local_count_recursion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), 2 ≤ r → Unr E → SelfDualLat G Λ → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (k : ℕ), 1 ≤ k → locCount (IsCMField.complexConj E).toAlgHom Gᵀ Λ v (k + 1) = locCount (IsCMField.complexConj E).toAlgHom Gᵀ Λ v k * Ideal.absNorm v.asIdeal ^ (r ^ 2 - 1) := by
  first | exact @GlobalTheory.TamCnt.locCount_succ | exact GlobalTheory.TamCnt.locCount_succ | (intros; apply GlobalTheory.TamCnt.locCount_succ <;> assumption)
