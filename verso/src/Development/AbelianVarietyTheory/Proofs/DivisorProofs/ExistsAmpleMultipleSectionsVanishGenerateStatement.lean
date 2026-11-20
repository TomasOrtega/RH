import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleMultipleSectionsVanishGenerate
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IdGenRat.exists_sections_vanish_generate` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsAmpleMultipleSectionsVanishGenerate.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.exists_ampleMultiple_sections_vanish_generate : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (A : CartierDiv X) (z : X), IsAmpleLB (toLB A) → ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → ∃ (r : ℕ) (κ : Fin r → X.functionField), (∀ i, κ i ∈ (l • A).sections) ∧ (∀ i, (l • A).VanishesAt z (κ i)) ∧ ∀ y, ¬ z ⤳ y → ∃ i, (l • A).GeneratesAt y (κ i) := by
  first | exact @GlobalTheory.IdGenRat.exists_sections_vanish_generate | exact GlobalTheory.IdGenRat.exists_sections_vanish_generate | (intros; apply GlobalTheory.IdGenRat.exists_sections_vanish_generate <;> assumption)
