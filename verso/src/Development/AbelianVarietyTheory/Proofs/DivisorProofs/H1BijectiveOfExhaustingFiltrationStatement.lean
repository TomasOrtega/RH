import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1BijectiveOfExhaustingFiltration
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CxCoh.restriction_h1_bijective_of_exhaustion` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FH1BijectiveOfExhaustingFiltration.lean&line=247#L247)
-/
theorem _root_.GlobalTheory.T.h1_resMap_bijective_of_exhausting_properties : ∀ (C : Type 1) [Category.{0} C] (D : Type) [Category.{0} D] (K : Cx C) (P : ℕ → ObjectProperty C) (ℓ : D ⥤ C) (N₀ : ℕ), (∀ m n T, m ≤ n → P m T → P n T) → (∀ T, ∃ n, P n T) → (∀ N, N₀ ≤ N → ∃ h : ∀ U, P N (ℓ.obj U), ((K.res (P N).ι).resMap ((P N).lift ℓ h)).Bij) → Function.Bijective (K.resMap ℓ).h1 := by
  first | exact @GlobalTheory.CxCoh.restriction_h1_bijective_of_exhaustion | exact GlobalTheory.CxCoh.restriction_h1_bijective_of_exhaustion | (intros; apply GlobalTheory.CxCoh.restriction_h1_bijective_of_exhaustion <;> assumption)
