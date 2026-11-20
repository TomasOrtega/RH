import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.LeviForms.TailCutA
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LoglogQuotNonneg
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHoldsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalDensityInclusionExclusionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSetStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

/- English proof (translation)
Simplify using `[levi]`.
-/
theorem levi_const_zero {D : ℕ} (y w : Fin D → ℂ) : levi (fun _ : Fin D → ℂ => (0 : ℝ)) y w = 0 := by
  simp [levi]

/- English proof (translation)
Introduce `e X _ A Θ L s C₅ C t₁ hΘ hpos hL hC₅ hC ht₁ hte`. Establish `hr : ∀ y, Real.exp 1 ≤ rW L s y` using `fun y => by`. Use `hL y` as an intermediate fact. Unfold `rW`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `he1 : (1 : ℝ) ≤ Real.exp 1` using `by linarith [Real.add_one_le_exp (1 : ℝ)]`. Establish `hlogr : ∀ y, 0 ≤ Real.log (rW L s y)` using `fun y => Real.log_nonneg (he1.trans (hr y))`. Establish `hε : ∀ t, 0 < t → t ≤ t₁ → 0 ≤ epsT C t`. Introduce `t ht htt`. Rewrite using `[epsT_eq_mul]`.

Conclude with `mul_nonneg hC (loglog_quot_nonneg ht (htt.trans hte))`. Establish `hll : ∀ t, 0 < t → t ≤ t₁ → 1 ≤ Real.log (Real.log (1 / t))` using `fun t ht htt => (log_inv_bounds ht (htt.trans hte)).2`. Establish `h0 : A.Smooth (0 : X → ℝ)` using `fun j => contDiffOn_const`. Establish `ht1 : t₁ < 1`. Conclude with `hte.trans_lt (Real.exp_lt_one_iff.2 (neg_lt_zero.2 (Real.exp_pos 1)))`.

Use `⟨⟨isPotential_ofFun A 0 h0, fun j => contDiffOn_const, ?_, fun y _ => ⟨?_, hC₅⟩⟩, ⟨ht₁, ht1, fun t ht htt => ?_⟩, fun j K _ _ => ⟨fun u hu => Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu, fun u hu => Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu, fun u hu = …` and prove the remaining obligations. Introduce `x j y _ w show 0 ≤ levi (fun z => (0 : X → ℝ) ((A.chart j).symm z) + (0 : X → ℝ) ((A.chart j).symm z)) y w`. Simplify using `only [Pi.zero_apply, add_zero]`. Rewrite using `[levi_const_zero]`. Use `mul_nonneg hC₅ (hlogr y) show -C₅ * Real.log (rW L s y) ≤ 0` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hεt` using `hε t ht htt`. Establish `hr3 : 0 ≤ t ^ ((1 : ℝ) / 3)` using `Real.rpow_nonneg ht.le _`. Use `⟨h0, fun _ => hC, fun _ _ => le_refl _, fun _ => ?_, ?_, fun _ _ _ => ?_, fun y _ => ?_, fun t' htt' ht' _ => ?_⟩` and prove the remaining obligations. Use `mul_nonneg hC (le_trans zero_le_one (hll t ht htt)) show -C * Real.log (Real.log (1 / t)) ≤ 0` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `x j y hy w`. Take `⟨hyt, hyU⟩` from `hy`. Establish `hU : (A.chart j).symm y ∈ (Set.univ ∩ Set.univ) ∩ Θ.U x` using `hyU`. Establish `hO2 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x)` using `(A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target (Θ.isOpen_U x)`.

Establish `hΘ2 : ContDiffAt ℝ 2 (Θ.φ x ∘ (A.chart j).symm) y` using `((hΘ.1 x j).contDiffAt (hO2.mem_nhds ⟨hyt, hU.2⟩)).of_le (by norm_cast)`. Establish `hΘl : 0 ≤ levi (Θ.φ x ∘ (A.chart j).symm) y w`. Distinguish the cases in `hw : w = 0`. Rewrite using `[hw, levi_zero]`. Conclude with `(hpos x j y ⟨hyt, hU.2⟩ w hw).le`.

Establish `hfun : (LocPot.ofFun 0 + LocPot.ofFun 0 + Θ.rsmul (epsT C t)).φ x ∘ (A.chart j).symm = fun z => (fun _ : Fin e → ℂ => (0 : ℝ)) z + epsT C t * (Θ.φ x ∘ (A.chart j).symm) z`. Use function extensionality and compare the values at `z`. Use `show (0 : X → ℝ) _ + (0 : X → ℝ) _ + epsT C t * Θ.φ x _ = 0 + epsT C t * Θ.φ x _`. Simplify using the standard rewrite rules. Rewrite using `[hfun, levi_add_smul (epsT C t) contDiffAt_const hΘ2 w, levi_const_zero]`.

Conclude with `add_nonneg le_rfl (mul_nonneg hεt hΘl)`. Use `show (0 : ℝ) ≤ 0 + t ^ ((1 : ℝ) / 3) + epsT C t`. Combine the linear equalities and inequalities to obtain the conclusion. Use `mul_nonneg hεt (le_trans (Real.exp_pos 1).le (hr y)) show (0 : ℝ) ≤ 0 + t ^ ((1 : ℝ) / 3) + epsT C t * rW L s y` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `mul_nonneg hC (hε t' (ht.trans_le htt') ht') show (0 : ℝ) ≤ 0 + C * epsT C t'` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem zeroMember_isRegFamily : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) (C₅ C t₁ : ℝ), IsPotential A Θ → IsPosPot A Θ → (∀ y, logNormSec L s y ≤ 0) → 0 ≤ C₅ → 0 ≤ C → 0 < t₁ → t₁ ≤ Real.exp (-Real.exp 1) → IsSingWeight A L s (LocPot.ofFun 0) 0 C₅ ∧ IsRegFamily A Θ L s (LocPot.ofFun 0) 0 (fun _ => 0) C t₁ ∧ IsRegFamilyC2 A s 0 (fun _ => 0) := by
  intro e X _ A Θ L s C₅ C t₁ hΘ hpos hL hC₅ hC ht₁ hte
  have hr : ∀ y, Real.exp 1 ≤ rW L s y := fun y => by
    have := hL y; unfold rW; linarith
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlogr : ∀ y, 0 ≤ Real.log (rW L s y) := fun y => Real.log_nonneg (he1.trans (hr y))
  have hε : ∀ t, 0 < t → t ≤ t₁ → 0 ≤ epsT C t := by
    intro t ht htt
    rw [epsT_eq_mul]
    exact mul_nonneg hC (loglog_quot_nonneg ht (htt.trans hte))
  have hll : ∀ t, 0 < t → t ≤ t₁ → 1 ≤ Real.log (Real.log (1 / t)) :=
    fun t ht htt => (log_inv_bounds ht (htt.trans hte)).2
  have h0 : A.Smooth (0 : X → ℝ) := fun j => contDiffOn_const
  have ht1 : t₁ < 1 := by
    exact hte.trans_lt (Real.exp_lt_one_iff.2 (neg_lt_zero.2 (Real.exp_pos 1)))
  refine ⟨⟨isPotential_ofFun A 0 h0, fun j => contDiffOn_const, ?_, fun y _ => ⟨?_, hC₅⟩⟩,
    ⟨ht₁, ht1, fun t ht htt => ?_⟩, fun j K _ _ => ⟨fun u hu => Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu,
      fun u hu => Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu,
      fun u hu => Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu⟩⟩
  · intro x j y _ w
    show 0 ≤ levi (fun z => (0 : X → ℝ) ((A.chart j).symm z) + (0 : X → ℝ) ((A.chart j).symm z)) y w
    simp only [Pi.zero_apply, add_zero]
    rw [levi_const_zero]
  · have := mul_nonneg hC₅ (hlogr y)
    show -C₅ * Real.log (rW L s y) ≤ 0
    linarith
  · have hεt := hε t ht htt
    have hr3 : 0 ≤ t ^ ((1 : ℝ) / 3) := Real.rpow_nonneg ht.le _
    refine ⟨h0, fun _ => hC, fun _ _ => le_refl _, fun _ => ?_, ?_, fun _ _ _ => ?_, fun y _ => ?_,
      fun t' htt' ht' _ => ?_⟩
    · have := mul_nonneg hC (le_trans zero_le_one (hll t ht htt))
      show -C * Real.log (Real.log (1 / t)) ≤ 0
      linarith
    · intro x j y hy w
      obtain ⟨hyt, hyU⟩ := hy
      have hU : (A.chart j).symm y ∈ (Set.univ ∩ Set.univ) ∩ Θ.U x := hyU
      have hO2 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x) :=
        (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target (Θ.isOpen_U x)
      have hΘ2 : ContDiffAt ℝ 2 (Θ.φ x ∘ (A.chart j).symm) y :=
        ((hΘ.1 x j).contDiffAt (hO2.mem_nhds ⟨hyt, hU.2⟩)).of_le (by norm_cast)
      have hΘl : 0 ≤ levi (Θ.φ x ∘ (A.chart j).symm) y w := by
        by_cases hw : w = 0
        · rw [hw, levi_zero]
        · exact (hpos x j y ⟨hyt, hU.2⟩ w hw).le
      have hfun : (LocPot.ofFun 0 + LocPot.ofFun 0 + Θ.rsmul (epsT C t)).φ x ∘ (A.chart j).symm =
          fun z => (fun _ : Fin e → ℂ => (0 : ℝ)) z + epsT C t * (Θ.φ x ∘ (A.chart j).symm) z := by
        funext z
        show (0 : X → ℝ) _ + (0 : X → ℝ) _ + epsT C t * Θ.φ x _ = 0 + epsT C t * Θ.φ x _
        simp
      rw [hfun, levi_add_smul (epsT C t) contDiffAt_const hΘ2 w, levi_const_zero]
      exact add_nonneg le_rfl (mul_nonneg hεt hΘl)
    · show (0 : ℝ) ≤ 0 + t ^ ((1 : ℝ) / 3) + epsT C t
      linarith
    · have := mul_nonneg hεt (le_trans (Real.exp_pos 1).le (hr y))
      show (0 : ℝ) ≤ 0 + t ^ ((1 : ℝ) / 3) + epsT C t * rW L s y
      linarith
    · have := mul_nonneg hC (hε t' (ht.trans_le htt') ht')
      show (0 : ℝ) ≤ 0 + C * epsT C t'
      linarith

end GlobalTheory.CompanionTheory.Ar.Giv
