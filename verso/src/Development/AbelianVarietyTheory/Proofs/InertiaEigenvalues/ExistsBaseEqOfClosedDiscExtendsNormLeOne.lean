import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscCoefficientsTopologicallyFreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscBoundedFunctionIsPowerSeriesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopologicalBasisBasicFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionOfPowDvdStatement

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Introduce `l _ K bk A _ s ι TB ρ hρ hρ1 y hy`. Establish `hj : ∀ ρ' : ℝ≥0, 0 < ρ' → ∃ j : bk.DS ρ' →+* Disc l (s X) ρ', IsDiscMap s j` using `fun ρ' h => GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd l bk.S A s X (s X) ρ' ρ' 1 h (by rw [pow_one]) (by rw [pow_one])`. Take `⟨j, hjd⟩` from `hj ρ hρ`. Take `⟨cD, hc1, -, hc3, hc4, -, hc6, -, -⟩` from `GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ hρ hρ1 j hjd`. Establish `hz : ∀ i, ∃ z : bk.S, toDisc l (X : bk.S) ρ z = cD i y`.

Introduce `i`. Apply `GlobalTheory.T.disc_bounded_function_isPowerSeries l K bk ρ hρ hρ1` to reduce the goal to its premises. Introduce `ρ₁ hρ₁`. Take `⟨ρ', R, y', h1, h2, h3, hR, hRy, hy'⟩` from `hy ρ₁ hρ₁`. Establish `hρ' : 0 < ρ'` using `hρ.trans_le h2`.

Take `⟨j', hj'd⟩` from `hj ρ' hρ'`. Take `⟨cD', hc1', -, hc3', -⟩` from `GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ' hρ' h3 j' hj'd`. Take `⟨RS, hRS⟩` from `GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd l bk.S bk.S (RingHom.id _) X X ρ' ρ 1 hρ (by simp) (by simpa using h2)`. Use `⟨ρ', RS, cD' i y', h1, h2, h3, hRS, ?_, (hc3' i y').trans hy'⟩` and prove the remaining obligations. Establish `htor : ∀ z : bk.DS ρ, l • z = 0 → z = 0` using `fun z hz => by`.

Rewrite `hz` using `[nsmul_eq_mul]`. Conclude with `(isUnit_l_disc l (X : bk.S) ρ).mul_right_eq_zero.1 hz`. Establish `hF : Continuous ((RS : bk.DS ρ' →+ bk.DS ρ).comp (cD' i))` using `AddMonoidHomClass.continuous_of_bound _ 1 fun x => by show ‖RS (cD' i x)‖ ≤ 1 * ‖x‖`. Rewrite using `[one_mul]`. Conclude with `(hRS.norm_le _).trans (hc3' i x)`.

Establish `hG : Continuous ((cD i).comp (R : Disc l (s X) ρ' →+ Disc l (s X) ρ))` using `AddMonoidHomClass.continuous_of_bound _ 1 fun x => by show ‖cD i (R x)‖ ≤ 1 * ‖x‖`. Rewrite using `[one_mul]`. Conclude with `(hc3 i _).trans (hR.norm_le x)`. Establish `key` using `(GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ').2.2.1 (bk.DS ρ) htor _ _ hF hG fun a => by show RS (cD' i (toDisc l (s X) ρ' a)) = cD i (R (toDisc l (s X) ρ' a))`. Rewrite using `[hc1', hRS.ext, hR.ext, hc1]`.

Both sides reduce to the same expression. Rewrite using `[← hRy]`. Conclude with `DFunLike.congr_fun key y'`. Use `choose z hz using hz`. Use `haveI : IsAdicComplete bk.J bk.S := bk.complete`.

Establish `hfin : ∀ n : ℕ, {i | z i ∉ bk.J ^ n}.Finite`. Introduce `n`. Take `⟨r, hr, hr'⟩` from `(GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk bk.S (RingHom.id _) Unit (TopBasis.self bk.J) ρ hρ hρ1).2.1 n`. Use `(Filter.mem_cofinite.1 (hc4 y (Metric.closedBall_mem_nhds 0 hr))).subset fun i hi h => hi ?_` and prove the remaining obligations. Establish `h' : ‖toDisc l (X : bk.S) ρ (z i)‖ ≤ r`.

Rewrite using `[hz i]`. Simplify using `using h`. Use `hr' (z i) h'` as an intermediate fact. Rewrite `this` using `[Ideal.map_id]`. Then use the resulting hypothesis. Take `⟨a, ha⟩` from `(GlobalTheory.T.topologicalBasis_basic_facts bk.S A s bk.J ι TB bk.complete.toIsHausdorff).2.2.2.1 z hfin`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `h0 : ‖y - toDisc l (s X) ρ a‖ ≤ 0` using `hc6 _ 0 le_rfl fun i => by`. Rewrite using `[map_sub, hc1, ha, hz, sub_self, norm_zero]`. Conclude with `(sub_eq_zero.1 (norm_le_zero_iff.1 h0)).symm`.
-/
theorem exists_toDisc_eq_of_extends_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type)
    [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ ρ : ℝ≥0, 0 < ρ → ρ < 1 →
    ∀ y : Disc l (s X) ρ, (∀ ρ₁ : ℝ≥0, ρ₁ < 1 → ∃ (ρ' : ℝ≥0) (R : Disc l (s X) ρ' →+* Disc l (s X) ρ)
      (y' : Disc l (s X) ρ'), ρ₁ ≤ ρ' ∧ ρ ≤ ρ' ∧ ρ' < 1 ∧ IsDiscMap (RingHom.id A) R ∧ R y' = y ∧ ‖y'‖ ≤ 1) →
    ∃ a, toDisc l (s X) ρ a = y := by
  intro l _ K bk A _ s ι TB ρ hρ hρ1 y hy
  have hj : ∀ ρ' : ℝ≥0, 0 < ρ' → ∃ j : bk.DS ρ' →+* Disc l (s X) ρ', IsDiscMap s j := fun ρ' h =>
    GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd l bk.S A s X (s X) ρ' ρ' 1 h (by rw [pow_one]) (by rw [pow_one])
  obtain ⟨j, hjd⟩ := hj ρ hρ
  obtain ⟨cD, hc1, -, hc3, hc4, -, hc6, -, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ hρ hρ1 j hjd

  have hz : ∀ i, ∃ z : bk.S, toDisc l (X : bk.S) ρ z = cD i y := by
    intro i
    apply GlobalTheory.T.disc_bounded_function_isPowerSeries l K bk ρ hρ hρ1
    intro ρ₁ hρ₁
    obtain ⟨ρ', R, y', h1, h2, h3, hR, hRy, hy'⟩ := hy ρ₁ hρ₁
    have hρ' : 0 < ρ' := hρ.trans_le h2
    obtain ⟨j', hj'd⟩ := hj ρ' hρ'
    obtain ⟨cD', hc1', -, hc3', -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ' hρ' h3 j' hj'd
    obtain ⟨RS, hRS⟩ := GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd l bk.S bk.S (RingHom.id _) X X ρ' ρ 1 hρ (by simp) (by simpa using h2)
    refine ⟨ρ', RS, cD' i y', h1, h2, h3, hRS, ?_, (hc3' i y').trans hy'⟩

    have htor : ∀ z : bk.DS ρ, l • z = 0 → z = 0 := fun z hz => by
      rw [nsmul_eq_mul] at hz
      exact (isUnit_l_disc l (X : bk.S) ρ).mul_right_eq_zero.1 hz
    have hF : Continuous ((RS : bk.DS ρ' →+ bk.DS ρ).comp (cD' i)) :=
      AddMonoidHomClass.continuous_of_bound _ 1 fun x => by
        show ‖RS (cD' i x)‖ ≤ 1 * ‖x‖
        rw [one_mul]; exact (hRS.norm_le _).trans (hc3' i x)
    have hG : Continuous ((cD i).comp (R : Disc l (s X) ρ' →+ Disc l (s X) ρ)) :=
      AddMonoidHomClass.continuous_of_bound _ 1 fun x => by
        show ‖cD i (R x)‖ ≤ 1 * ‖x‖
        rw [one_mul]; exact (hc3 i _).trans (hR.norm_le x)
    have key := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ').2.2.1 (bk.DS ρ) htor _ _ hF hG fun a => by
      show RS (cD' i (toDisc l (s X) ρ' a)) = cD i (R (toDisc l (s X) ρ' a))
      rw [hc1', hRS.ext, hR.ext, hc1]; rfl
    rw [← hRy]
    exact DFunLike.congr_fun key y'
  choose z hz using hz

  haveI : IsAdicComplete bk.J bk.S := bk.complete
  have hfin : ∀ n : ℕ, {i | z i ∉ bk.J ^ n}.Finite := by
    intro n
    obtain ⟨r, hr, hr'⟩ := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk bk.S (RingHom.id _) Unit (TopBasis.self bk.J) ρ hρ hρ1).2.1 n
    refine (Filter.mem_cofinite.1 (hc4 y (Metric.closedBall_mem_nhds 0 hr))).subset fun i hi h => hi ?_
    have h' : ‖toDisc l (X : bk.S) ρ (z i)‖ ≤ r := by
      rw [hz i]; simpa using h
    have := hr' (z i) h'
    rwa [Ideal.map_id] at this
  obtain ⟨a, ha⟩ := (GlobalTheory.T.topologicalBasis_basic_facts bk.S A s bk.J ι TB bk.complete.toIsHausdorff).2.2.2.1 z hfin
  refine ⟨a, ?_⟩
  have h0 : ‖y - toDisc l (s X) ρ a‖ ≤ 0 := hc6 _ 0 le_rfl fun i => by
    rw [map_sub, hc1, ha, hz, sub_self, norm_zero]
  exact (sub_eq_zero.1 (norm_le_zero_iff.1 h0)).symm

end GlobalTheory.BSP
