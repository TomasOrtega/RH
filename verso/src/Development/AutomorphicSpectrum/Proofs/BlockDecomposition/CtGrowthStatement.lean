import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CtGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCtGrowth.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.constant_term_moderate_growth_alt : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (φ : Sm E a), IsAutForm φ → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ g : GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖∫ x in 𝓕, φ.1 (unip x * (g * infGL E a y)) ∂μ‖ ≤ C * height y ^ N := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.Growth.ct_growth | exact GlobalTheory.CompanionTheory.CTFin.Growth.ct_growth | (intros; apply GlobalTheory.CompanionTheory.CTFin.Growth.ct_growth <;> assumption)
