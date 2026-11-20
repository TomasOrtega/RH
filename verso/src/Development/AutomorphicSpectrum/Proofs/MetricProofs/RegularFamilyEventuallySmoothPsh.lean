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

namespace GlobalTheory.CompanionTheory.Ar.Giv.EvPsh

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tendsto_epsT_zero (C : ℝ) :
    Tendsto (fun t => epsT C t) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
  have hℓ : Tendsto (fun t : ℝ => Real.log (1 / t)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) atTop := by
    have h := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
    refine h.congr (fun t => ?_)
    simp [one_div]
  have hq : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have h2 := (hq.comp hℓ).const_mul C
  rw [mul_zero] at h2
  refine h2.congr (fun t => ?_)
  simp only [Function.comp_apply, epsT]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem isPsh_of_isPosPot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (h : IsPosPot A Θ) : IsPsh A Θ := by
  intro x j y hy w
  by_cases hw : w = 0
  · subst hw
    simp [levi]
  · exact (h x j y hy w hw).le

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Split into cases according to the possible forms of the given data. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

A detailed English derivation is pending.
-/
theorem eventually_isPsh_add_pot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ L : LocPot X) (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ)
    (C t₀ : ℝ) (hΘ : IsPotential A Θ) (hΘp : IsPosPot A Θ) (hth : IsPotential A th)
    (hF : IsRegFamily A Θ L s th ph phT C t₀) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      A.Smooth (phT t) ∧ IsPsh A (th + LocPot.ofFun (phT t) + Θ) := by
  obtain ⟨ht₀, -, hF⟩ := hF
  have hε : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), epsT C t < 1 :=
    (tendsto_epsT_zero C).eventually (gt_mem_nhds one_pos)
  have hsmall : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Ioo 0 t₀ :=
    Ioo_mem_nhdsGT ht₀
  filter_upwards [hε, hsmall] with t hεt ht
  obtain ⟨h1, -, -, -, h5, -⟩ := hF t ht.1 ht.2.le
  refine ⟨h1, ?_⟩
  have h := GlobalTheory.CompanionTheory.Ar.Giv.isPsh_rsmul_mono A Θ th (phT t) hΘ (isPsh_of_isPosPot A Θ hΘp) hth h1 hεt.le h5
  have e1 : Θ.rsmul 1 = Θ := by
    cases Θ
    simp [LocPot.rsmul]
  rwa [e1] at h

end GlobalTheory.CompanionTheory.Ar.Giv.EvPsh
