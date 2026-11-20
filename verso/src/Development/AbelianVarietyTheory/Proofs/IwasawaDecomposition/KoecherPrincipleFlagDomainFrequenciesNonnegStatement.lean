import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KoecherPrincipleFlagDomainFrequenciesNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.freqNonneg_of_thickBdd` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FKoecherPrincipleFlagDomainFrequenciesNonneg.lean&line=128#L128)
-/
theorem _root_.GlobalTheory.T.koecher_principle_flagDomain_frequencies_nonneg : OrbitThickSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), 1 < Module.finrank ℚ E / 2 → X.IsSec la P → ThickBdd X (X.pnorm la P) → FreqNonneg X la P := by
  first | exact @GlobalTheory.freqNonneg_of_thickBdd | exact GlobalTheory.freqNonneg_of_thickBdd | (intros; apply GlobalTheory.freqNonneg_of_thickBdd <;> assumption)
