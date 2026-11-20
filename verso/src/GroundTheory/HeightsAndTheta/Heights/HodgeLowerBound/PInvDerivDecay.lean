import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsInvDerivDecay
set_option maxSynthPendingDepth 1

noncomputable section

open Nat Set Filter Topology

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

/- English proof (translation)
Rewrite using `[← (contDiffAt_inv ℂ hz (n := k)).restrictScalars_iteratedFDeriv (𝕜 := ℝ), Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_inv]`. Rewrite using `[show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]`. Simplify using the standard rewrite rules.
-/
theorem norm_iteratedFDeriv_real_inv (k : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ‖iteratedFDeriv ℝ k (Inv.inv : ℂ → ℂ) z‖ = k ! * (‖z‖ ^ (k + 1))⁻¹ := by
  rw [← (contDiffAt_inv ℂ hz (n := k)).restrictScalars_iteratedFDeriv (𝕜 := ℝ),
    Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_inv]
  rw [show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  simp

/- English proof (translation)
Introduce `v G ρ R hρ hG hv`. Use `set t : Set ℂ := Metric.ball 0 ρ with ht_def`. Establish `ht : IsOpen t` using `Metric.isOpen_ball`. Establish `hK : Metric.closedBall (0 : ℂ) (ρ / 2) ⊆ t` using `Metric.closedBall_subset_ball (by linarith)`. Establish `hbd : ∀ i : ℕ, i ≤ 2 → ∃ M : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) (ρ / 2), ‖iteratedFDerivWithin ℝ i G t z‖ ≤ M`.

Introduce `i hi`. Conclude with `(isCompact_closedBall (0 : ℂ) (ρ / 2)).exists_bound_of_continuousOn ((hG.continuousOn_iteratedFDerivWithin (by exact_mod_cast hi) ht.uniqueDiffOn).mono hK)`. Take `⟨M₀, hM₀⟩` from `hbd 0 (by norm_num)`. Take `⟨M₁, hM₁⟩` from `hbd 1 (by norm_num)`. Take `⟨M₂, hM₂⟩` from `hbd 2 le_rfl`.

Use `set M : ℝ := max 0 (max M₀ (max M₁ M₂)) with hM_def`. Establish `hM0 : 0 ≤ M` using `le_max_left _ _`. Establish `hMi : ∀ i : ℕ, i ≤ 2 → ∀ z ∈ Metric.closedBall (0 : ℂ) (ρ / 2), ‖iteratedFDerivWithin ℝ i G t z‖ ≤ M`. Introduce `i hi z hz`. Use `interval_cases i`.

Conclude with `(hM₀ z hz).trans (by simp [hM_def])`. Conclude with `(hM₁ z hz).trans (by simp [hM_def])`. Conclude with `(hM₂ z hz).trans (by simp [hM_def])`. Use `set R₀ : ℝ := max R (max 1 (2 / ρ)) with hR₀_def`. Use `⟨4 * M, R₀, fun y hy => ?_⟩` and prove the remaining obligations.

Establish `hRR₀ : R ≤ R₀` using `le_max_left _ _`. Establish `h1R₀ : 1 ≤ R₀` using `(le_max_left _ _).trans (le_max_right _ _)`. Establish `h2R₀ : 2 / ρ ≤ R₀` using `(le_max_right _ _).trans (le_max_right _ _)`. Use `set s : Set ℂ := {z | R₀ < ‖z‖} with hs_def`. Establish `hs : IsOpen s` using `isOpen_lt continuous_const continuous_norm`.

Establish `hys : y ∈ s` using `hy`. Establish `hy1 : 1 < ‖y‖` using `lt_of_le_of_lt h1R₀ hy`. Establish `hypos : 0 < ‖y‖` using `by linarith`. Establish `hy0 : y ≠ 0` using `norm_pos_iff.mp hypos`. Establish `hinvK : ∀ z ∈ s, z⁻¹ ∈ Metric.closedBall (0 : ℂ) (ρ / 2)`.

Introduce `z hz`. Establish `hz' : R₀ < ‖z‖` using `hz`. Establish `hzpos : 0 < ‖z‖` using `by linarith`. Rewrite using `[mem_closedBall_zero_iff, norm_inv, inv_le_comm₀ hzpos (by positivity), inv_div]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hmaps : MapsTo (Inv.inv : ℂ → ℂ) s t` using `fun z hz => hK (hinvK z hz)`. Establish `hinvC : ContDiffOn ℝ 2 (Inv.inv : ℂ → ℂ) s`. Introduce `z hz`. Establish `hz' : R₀ < ‖z‖` using `hz`. Establish `hzpos : 0 < ‖z‖` using `by linarith`.

Conclude with `(contDiffAt_inv ℝ (norm_pos_iff.mp hzpos)).contDiffWithinAt`. Establish `hev : v =ᶠ[𝓝 y] G ∘ Inv.inv` using `by filter_upwards [hs.mem_nhds hys] with z hz`. Conclude with `hv z (lt_of_le_of_lt hRR₀ hz)`. Establish `hinvD : ∀ k : ℕ, ‖iteratedFDerivWithin ℝ k (Inv.inv : ℂ → ℂ) s y‖ = k ! * (‖y‖ ^ (k + 1))⁻¹`. Introduce `k`.

Rewrite using `[iteratedFDerivWithin_of_isOpen k hs hys, norm_iteratedFDeriv_real_inv k hy0]`. Establish `hcomp : ∀ k : ℕ, iteratedFDeriv ℝ k v y = iteratedFDerivWithin ℝ k (G ∘ Inv.inv) s y`. Introduce `k`. Rewrite using `[iteratedFDerivWithin_of_isOpen k hs hys]`. Conclude with `(hev.iteratedFDeriv ℝ k).eq_of_nhds`.

Establish `hC : ∀ i, i ≤ 2 → ‖iteratedFDerivWithin ℝ i G t (y⁻¹)‖ ≤ M` using `fun i hi => hMi i hi _ (hinvK y hys)`. Prove the components needed by the constructor for the conclusion. Establish `hD1 : ∀ i, 1 ≤ i → i ≤ 1 → ‖iteratedFDerivWithin ℝ i (Inv.inv : ℂ → ℂ) s y‖ ≤ ((‖y‖ ^ 2)⁻¹) ^ i`. Introduce `i h1 h2`. Take `rfl : i = 1` from `le_antisymm h2 h1`.

Rewrite using `[hinvD]`. Simplify using the standard rewrite rules. Establish `key` using `norm_iteratedFDerivWithin_comp_le (n := 1) hG hinvC (by norm_num) ht.uniqueDiffOn hs.uniqueDiffOn hmaps hys (fun i hi => hC i (by omega)) hD1`. Rewrite using `[← norm_iteratedFDeriv_one (𝕜 := ℝ), hcomp 1]`. Use `key.trans ?_` and prove the remaining obligations.

Establish `hp : 0 < (‖y‖ ^ 2)⁻¹` using `by positivity`. Rewrite using `[div_eq_mul_inv]`. Simplify using `only [factorial_one, cast_one, one_mul, pow_one]`. Conclude with `mul_le_mul_of_nonneg_right (by linarith) hp.le`. Use `set D : ℝ := Real.sqrt (2 / ‖y‖ ^ 3) with hD_def`.

Establish `hDsq : D ^ 2 = 2 / ‖y‖ ^ 3` using `Real.sq_sqrt (by positivity)`. Establish `hD2 : ∀ i, 1 ≤ i → i ≤ 2 → ‖iteratedFDerivWithin ℝ i (Inv.inv : ℂ → ℂ) s y‖ ≤ D ^ i`. Introduce `i h1 h2`. Rewrite using `[hinvD]`. Use `interval_cases i`.

Rewrite using `[pow_one, hD_def, Real.le_sqrt (by positivity) (by positivity)]`. Simplify using `only [factorial_one, cast_one, one_mul]`. Rewrite using `[inv_pow, ← pow_mul, inv_le_iff_one_le_mul₀ (by positivity)]`. Rewrite using `[show (1 + 1) * 2 = 4 by norm_num, show ‖y‖ ^ 4 = ‖y‖ * ‖y‖ ^ 3 by ring, div_mul_eq_mul_div, ← mul_assoc, mul_div_assoc, div_self (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[hDsq]`. Simplify using `[div_eq_mul_inv]`. Establish `key` using `norm_iteratedFDerivWithin_comp_le (n := 2) hG hinvC le_rfl ht.uniqueDiffOn hs.uniqueDiffOn hmaps hys hC hD2`. Rewrite using `[hcomp 2]`. Use `key.trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[hDsq]`. Simplify using `only [factorial_two, cast_ofNat]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem InvDerivDecay.proof : InvDerivDecay.Statement := by
  intro v G ρ R hρ hG hv
  set t : Set ℂ := Metric.ball 0 ρ with ht_def
  have ht : IsOpen t := Metric.isOpen_ball
  have hK : Metric.closedBall (0 : ℂ) (ρ / 2) ⊆ t :=
    Metric.closedBall_subset_ball (by linarith)
  have hbd : ∀ i : ℕ, i ≤ 2 → ∃ M : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) (ρ / 2),
      ‖iteratedFDerivWithin ℝ i G t z‖ ≤ M := by
    intro i hi
    exact (isCompact_closedBall (0 : ℂ) (ρ / 2)).exists_bound_of_continuousOn
      ((hG.continuousOn_iteratedFDerivWithin (by exact_mod_cast hi) ht.uniqueDiffOn).mono hK)
  obtain ⟨M₀, hM₀⟩ := hbd 0 (by norm_num)
  obtain ⟨M₁, hM₁⟩ := hbd 1 (by norm_num)
  obtain ⟨M₂, hM₂⟩ := hbd 2 le_rfl
  set M : ℝ := max 0 (max M₀ (max M₁ M₂)) with hM_def
  have hM0 : 0 ≤ M := le_max_left _ _
  have hMi : ∀ i : ℕ, i ≤ 2 → ∀ z ∈ Metric.closedBall (0 : ℂ) (ρ / 2),
      ‖iteratedFDerivWithin ℝ i G t z‖ ≤ M := by
    intro i hi z hz
    interval_cases i
    · exact (hM₀ z hz).trans (by simp [hM_def])
    · exact (hM₁ z hz).trans (by simp [hM_def])
    · exact (hM₂ z hz).trans (by simp [hM_def])
  set R₀ : ℝ := max R (max 1 (2 / ρ)) with hR₀_def
  refine ⟨4 * M, R₀, fun y hy => ?_⟩
  have hRR₀ : R ≤ R₀ := le_max_left _ _
  have h1R₀ : 1 ≤ R₀ := (le_max_left _ _).trans (le_max_right _ _)
  have h2R₀ : 2 / ρ ≤ R₀ := (le_max_right _ _).trans (le_max_right _ _)
  set s : Set ℂ := {z | R₀ < ‖z‖} with hs_def
  have hs : IsOpen s := isOpen_lt continuous_const continuous_norm
  have hys : y ∈ s := hy
  have hy1 : 1 < ‖y‖ := lt_of_le_of_lt h1R₀ hy
  have hypos : 0 < ‖y‖ := by linarith
  have hy0 : y ≠ 0 := norm_pos_iff.mp hypos
  have hinvK : ∀ z ∈ s, z⁻¹ ∈ Metric.closedBall (0 : ℂ) (ρ / 2) := by
    intro z hz
    have hz' : R₀ < ‖z‖ := hz
    have hzpos : 0 < ‖z‖ := by linarith
    rw [mem_closedBall_zero_iff, norm_inv,
      inv_le_comm₀ hzpos (by positivity), inv_div]
    linarith
  have hmaps : MapsTo (Inv.inv : ℂ → ℂ) s t := fun z hz => hK (hinvK z hz)
  have hinvC : ContDiffOn ℝ 2 (Inv.inv : ℂ → ℂ) s := by
    intro z hz
    have hz' : R₀ < ‖z‖ := hz
    have hzpos : 0 < ‖z‖ := by linarith
    exact (contDiffAt_inv ℝ (norm_pos_iff.mp hzpos)).contDiffWithinAt
  have hev : v =ᶠ[𝓝 y] G ∘ Inv.inv := by
    filter_upwards [hs.mem_nhds hys] with z hz
    exact hv z (lt_of_le_of_lt hRR₀ hz)
  have hinvD : ∀ k : ℕ, ‖iteratedFDerivWithin ℝ k (Inv.inv : ℂ → ℂ) s y‖ =
      k ! * (‖y‖ ^ (k + 1))⁻¹ := by
    intro k
    rw [iteratedFDerivWithin_of_isOpen k hs hys, norm_iteratedFDeriv_real_inv k hy0]
  have hcomp : ∀ k : ℕ, iteratedFDeriv ℝ k v y = iteratedFDerivWithin ℝ k (G ∘ Inv.inv) s y := by
    intro k
    rw [iteratedFDerivWithin_of_isOpen k hs hys]
    exact (hev.iteratedFDeriv ℝ k).eq_of_nhds
  have hC : ∀ i, i ≤ 2 → ‖iteratedFDerivWithin ℝ i G t (y⁻¹)‖ ≤ M :=
    fun i hi => hMi i hi _ (hinvK y hys)
  constructor
  · have hD1 : ∀ i, 1 ≤ i → i ≤ 1 →
        ‖iteratedFDerivWithin ℝ i (Inv.inv : ℂ → ℂ) s y‖ ≤ ((‖y‖ ^ 2)⁻¹) ^ i := by
      intro i h1 h2
      obtain rfl : i = 1 := le_antisymm h2 h1
      rw [hinvD]
      simp
    have key := norm_iteratedFDerivWithin_comp_le (n := 1) hG hinvC (by norm_num)
      ht.uniqueDiffOn hs.uniqueDiffOn hmaps hys (fun i hi => hC i (by omega)) hD1
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ), hcomp 1]
    refine key.trans ?_
    have hp : 0 < (‖y‖ ^ 2)⁻¹ := by positivity
    rw [div_eq_mul_inv]
    simp only [factorial_one, cast_one, one_mul, pow_one]
    exact mul_le_mul_of_nonneg_right (by linarith) hp.le
  · set D : ℝ := Real.sqrt (2 / ‖y‖ ^ 3) with hD_def
    have hDsq : D ^ 2 = 2 / ‖y‖ ^ 3 := Real.sq_sqrt (by positivity)
    have hD2 : ∀ i, 1 ≤ i → i ≤ 2 →
        ‖iteratedFDerivWithin ℝ i (Inv.inv : ℂ → ℂ) s y‖ ≤ D ^ i := by
      intro i h1 h2
      rw [hinvD]
      interval_cases i
      · rw [pow_one, hD_def, Real.le_sqrt (by positivity) (by positivity)]
        simp only [factorial_one, cast_one, one_mul]
        rw [inv_pow, ← pow_mul, inv_le_iff_one_le_mul₀ (by positivity)]
        rw [show (1 + 1) * 2 = 4 by norm_num, show ‖y‖ ^ 4 = ‖y‖ * ‖y‖ ^ 3 by ring,
          div_mul_eq_mul_div, ← mul_assoc, mul_div_assoc, div_self (by positivity)]
        nlinarith
      · rw [hDsq]
        simp [div_eq_mul_inv]
    have key := norm_iteratedFDerivWithin_comp_le (n := 2) hG hinvC le_rfl
      ht.uniqueDiffOn hs.uniqueDiffOn hmaps hys hC hD2
    rw [hcomp 2]
    refine key.trans (le_of_eq ?_)
    rw [hDsq]
    simp only [factorial_two, cast_ofNat]
    ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
