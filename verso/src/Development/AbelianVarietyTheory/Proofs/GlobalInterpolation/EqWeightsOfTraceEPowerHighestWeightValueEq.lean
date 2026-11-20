import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceEPowerHighestWeightValueGeneratingSeriesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ResidueMultisetEqOfShiftedSeriesEqStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOfDominantWeightsLowestAlcoveLinkedStatement

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

/- English proof (translation)
Introduce `p hp k _ _ N ν μ hν hμ hb hval`. Establish `hS : PowerSeries.mk (hcVal k fun i => (μ i : k)) = PowerSeries.mk (hcVal k fun i => (ν i : k))`. Use extensionality with `j`. Simplify using `[hval j]`. Establish `gμ` using `GlobalTheory.T.traceEPowerHighestWeightValue_generating_series k N (fun i => (μ i : k))`.

Establish `gν` using `GlobalTheory.T.traceEPowerHighestWeightValue_generating_series k N (fun i => (ν i : k))`. Rewrite `gμ` using `[hS]`. Establish `cast : ∀ (w : Fin N → ℕ) (i : Fin N), shift k (fun i => (w i : k)) i = ((w i + (N - 1 - i.val) : ℕ) : k)`. Introduce `w i`. Simplify using `[shift]`.

Simplify using `only [cast] at gμ gν`. Use `GlobalTheory.T.eq_of_dominantWeights_lowestAlcove_linked p N hp ν μ hν hμ hb ?_` and prove the remaining obligations. Use `GlobalTheory.T.residue_multiset_eq_of_shifted_series_eq p hp k N (fun i => ν i + (N - 1 - i.val)) (fun i => μ i + (N - 1 - i.val)) ?_` and prove the remaining obligations. Rewrite using `[← gν, ← gμ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eq_of_hcVal_eq : ∀ (p : ℕ), p.Prime → ∀ (k : Type) [Field k] [CharP k p] (N : ℕ) (ν μ : Fin N → ℕ), Antitone ν → Antitone μ → (∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩ ∧ ν ⟨0, h⟩ + (N - 1) ≤ p) → (∀ j, hcVal k (fun i => (μ i : k)) j = hcVal k (fun i => (ν i : k)) j) → μ = ν := by
  intro p hp k _ _ N ν μ hν hμ hb hval
  have hS : PowerSeries.mk (hcVal k fun i => (μ i : k)) = PowerSeries.mk (hcVal k fun i => (ν i : k)) := by
    ext j
    simp [hval j]
  have gμ := GlobalTheory.T.traceEPowerHighestWeightValue_generating_series k N (fun i => (μ i : k))
  have gν := GlobalTheory.T.traceEPowerHighestWeightValue_generating_series k N (fun i => (ν i : k))
  rw [hS] at gμ
  have cast : ∀ (w : Fin N → ℕ) (i : Fin N),
      shift k (fun i => (w i : k)) i = ((w i + (N - 1 - i.val) : ℕ) : k) := by
    intro w i
    simp [shift]
  simp only [cast] at gμ gν
  refine GlobalTheory.T.eq_of_dominantWeights_lowestAlcove_linked p N hp ν μ hν hμ hb ?_
  refine GlobalTheory.T.residue_multiset_eq_of_shifted_series_eq p hp k N (fun i => ν i + (N - 1 - i.val)) (fun i => μ i + (N - 1 - i.val)) ?_
  rw [← gν, ← gμ]
  ring

end GlobalTheory.Alc
