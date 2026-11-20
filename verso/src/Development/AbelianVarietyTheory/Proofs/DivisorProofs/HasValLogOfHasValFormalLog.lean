import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHasPAdicPowerSeriesValueOfDiffCoeffsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueAddSmulMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueMapOfContinuousEvaluatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicEvaluationSubstCompatibleThickeningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueSubMemPdIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNaturaStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

set_option autoImplicit false

namespace GlobalTheory.QLog

/- English proof (translation)
Introduce `α i`. Establish `hα : α = Finsupp.single () (α ())` using `Finsupp.unique_single α`. Establish `hc : coeff α (PowerSeries.log Q : MvPowerSeries Unit Q) = PowerSeries.coeff (α ()) (PowerSeries.log Q)` using `by conv_lhs => rw [hα]`. Both sides reduce to the same expression. Rewrite using `[hc, PowerSeries.coeff_log]`.

Take `rfl : i = ()` from `rfl`. Use `split_ifs with h`. Conclude with `⟨0, trivial, by simp⟩`. Use `⟨(-1) ^ (α () + 1), trivial, ?_⟩` and prove the remaining obligations. Establish `h' : ((α () : ℕ) : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 h`.

Rewrite using `[← map_natCast (algebraMap ℚ Q), ← map_mul, mul_div_cancel₀ _ h']`. Simplify using the standard rewrite rules.
-/
theorem dIn_top_powerSeriesLog (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q] :
    DIn (⊤ : Ideal B) (PowerSeries.log Q : MvPowerSeries Unit Q) := by
  intro α i
  have hα : α = Finsupp.single () (α ()) := Finsupp.unique_single α
  have hc : coeff α (PowerSeries.log Q : MvPowerSeries Unit Q)
      = PowerSeries.coeff (α ()) (PowerSeries.log Q) := by
    conv_lhs => rw [hα]
    rfl
  rw [hc, PowerSeries.coeff_log]
  obtain rfl : i = () := rfl
  split_ifs with h
  · exact ⟨0, trivial, by simp⟩
  · refine ⟨(-1) ^ (α () + 1), trivial, ?_⟩
    have h' : ((α () : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 h
    rw [← map_natCast (algebraMap ℚ Q), ← map_mul, mul_div_cancel₀ _ h']
    simp

/- English proof (translation)
Introduce `p _ B O Q _ _ _ _ _ θ hF σ _ _ z hz E hE g q hg hq`. Use `haveI := hF.complete`. Establish `hu : ∀ j : Unit, constantCoeff ((fun _ : Unit => g - 1) j) = 0` using `fun _ => by simp [hg]`. Establish `hEu : E (g - 1) = E g - 1` using `by rw [map_sub, map_one]`. Establish `hnil : ∃ N : ℕ, (p : B) ∣ (E g - 1) ^ N` using `hEu ▸ ((GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p B B σ z hz).2 E hE).2.1 (g - 1) (hu ())`.

Establish `hD` using `dIn_top_powerSeriesLog B Q`. Take `⟨q', hq', -⟩` from `GlobalTheory.T.existsUnique_hasPAdicPowerSeriesValue_of_diffCoeffs p B O Q θ hF Unit (fun _ => E g - 1) (fun _ => hnil) _ hD`. Establish `h4` using `GlobalTheory.T.pAdicEvaluation_subst_compatible_thickening p B O Q θ hF σ z hz E hE Unit (fun _ => g - 1) _ q' hu hD (by simpa only [hEu] using hq')`. Establish `h5 : subst (up Q (fun _ : Unit => g - 1)) (PowerSeries.log Q : MvPowerSeries Unit Q) = formalLog (map (algebraMap B Q) g)`. Unfold `formalLog PowerSeries.subst up`.

Simplify using `only [map_sub, map_one]`. Rewrite `h4` using `[h5]`. Rewrite using `[HasVal.unique hF hq h4]` and apply the resulting hypothesis.
-/
theorem hasVal_log_of_hasVal_formalLog : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ (g : MvPowerSeries σ B) (q : Q), constantCoeff g = 1 → HasVal p z (formalLog (map (algebraMap B Q) g)) q → HasVal p (fun _ : Unit => E g - 1) (PowerSeries.log Q : MvPowerSeries Unit Q) q := by
  intro p _ B O Q _ _ _ _ _ θ hF σ _ _ z hz E hE g q hg hq
  haveI := hF.complete
  have hu : ∀ j : Unit, constantCoeff ((fun _ : Unit => g - 1) j) = 0 := fun _ => by simp [hg]
  have hEu : E (g - 1) = E g - 1 := by rw [map_sub, map_one]
  have hnil : ∃ N : ℕ, (p : B) ∣ (E g - 1) ^ N :=
    hEu ▸ ((GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p B B σ z hz).2 E hE).2.1 (g - 1) (hu ())
  have hD := dIn_top_powerSeriesLog B Q
  obtain ⟨q', hq', -⟩ := GlobalTheory.T.existsUnique_hasPAdicPowerSeriesValue_of_diffCoeffs p B O Q θ hF Unit (fun _ => E g - 1) (fun _ => hnil) _ hD
  have h4 := GlobalTheory.T.pAdicEvaluation_subst_compatible_thickening p B O Q θ hF σ z hz E hE Unit (fun _ => g - 1) _ q' hu hD
    (by simpa only [hEu] using hq')
  have h5 : subst (up Q (fun _ : Unit => g - 1)) (PowerSeries.log Q : MvPowerSeries Unit Q)
      = formalLog (map (algebraMap B Q) g) := by
    unfold formalLog PowerSeries.subst up
    simp only [map_sub, map_one]
  rw [h5] at h4
  rwa [HasVal.unique hF hq h4]

end GlobalTheory.QLog
