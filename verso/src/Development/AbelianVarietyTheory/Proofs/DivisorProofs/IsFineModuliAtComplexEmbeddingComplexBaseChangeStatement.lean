import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFineModuliAtComplexEmbeddingComplexBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsFineModuliAtComplexEmbeddingComplexBaseChange.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.isFineModuliAtComplexEmbedding_complexBaseChange : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (F' : Fam ℂ O Λ g), IsBC F' F σ → FineAt F σ ρ N C → FineAt F' (RingHom.id ℂ) ρ N C := by
  first | exact @GlobalTheory.PELU.fineAt_of_isBC | exact GlobalTheory.PELU.fineAt_of_isBC | (intros; apply GlobalTheory.PELU.fineAt_of_isBC <;> assumption)
