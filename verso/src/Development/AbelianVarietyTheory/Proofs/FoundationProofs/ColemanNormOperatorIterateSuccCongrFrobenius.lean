import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormOpCongrStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormOpFrobStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColemanNormOperatorPowerSeriesCoeffAutMapCommStatement
open GlobalTheory.Col PowerSeries

namespace GlobalTheory

/- English proof (translation)
Unfold `normOp`. Conclude with `hu.map _`.
-/
theorem normOp_isUnit {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime] {h : PowerSeries R} (hu : IsUnit h) :
    IsUnit (normOp p h) := by
  unfold normOp
  exact hu.map _

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simpa using hu`. Consider the case `succ j ih => rw [Function.iterate_succ_apply']`. Conclude with `normOp_isUnit p ih`.
-/
theorem normOp_iterate_isUnit {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime] {h : PowerSeries R} (hu : IsUnit h)
    (j : ℕ) : IsUnit ((normOp p)^[j] h) := by
  induction j with
  | zero => simpa using hu
  | succ j ih => rw [Function.iterate_succ_apply']; exact normOp_isUnit p ih

/- English proof (translation)
Introduce `R _ p hp σ hσ h hu j`. Proceed by induction on `j with`. Consider the case `zero`. Take `⟨r, hr⟩` from `GlobalTheory.T.normOp_eq_smap_add_mul R p σ hσ h`. Conclude with `⟨r, by simpa using hr⟩`.

Consider the case `succ j ih`. Take `⟨r, hr⟩` from `ih`. Establish `hu2 : IsUnit (smap σ ((normOp p)^[j] h))` using `(normOp_iterate_isUnit p hu j).map _`. Take `⟨r', hr'⟩` from `GlobalTheory.T.normOp_congr_mod_pow_succ R p σ hσ _ _ r (j + 1) (by omega) hu2 hr`. Use `⟨r', ?_⟩` and prove the remaining obligations.

Rewrite using `[Function.iterate_succ_apply' (normOp p) (j + 1), hr', GlobalTheory.T.colemanNormOperator_powerSeriesCoeffAutMap_comm R p σ, ← Function.iterate_succ_apply' (normOp p) j]`.
-/
theorem normOp_iterate_congr : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ →
    ∀ (h : PowerSeries R), IsUnit h → ∀ j : ℕ, ∃ r : PowerSeries R,
      (normOp p)^[j + 1] h = smap σ ((normOp p)^[j] h) + (p : PowerSeries R) ^ (j + 1) * r := by
  intro R _ p hp σ hσ h hu j
  induction j with
  | zero =>
    obtain ⟨r, hr⟩ := GlobalTheory.T.normOp_eq_smap_add_mul R p σ hσ h
    exact ⟨r, by simpa using hr⟩
  | succ j ih =>
    obtain ⟨r, hr⟩ := ih
    have hu2 : IsUnit (smap σ ((normOp p)^[j] h)) := (normOp_iterate_isUnit p hu j).map _
    obtain ⟨r', hr'⟩ := GlobalTheory.T.normOp_congr_mod_pow_succ R p σ hσ _ _ r (j + 1) (by omega) hu2 hr
    refine ⟨r', ?_⟩
    rw [Function.iterate_succ_apply' (normOp p) (j + 1), hr', GlobalTheory.T.colemanNormOperator_powerSeriesCoeffAutMap_comm R p σ, ← Function.iterate_succ_apply' (normOp p) j]

end GlobalTheory
