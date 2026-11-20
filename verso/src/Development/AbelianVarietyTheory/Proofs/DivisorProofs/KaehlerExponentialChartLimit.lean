import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry MeasureTheory GlobalTheory.ChernReg GlobalTheory.ShFam GlobalTheory.CxPts Filter Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RegLim

/- English proof (translation)
Introduce `hK k _ Y p σ d _ a E ha hE f c y hy hU`. Take `⟨U, hU, hcont⟩` from `hU`. Establish `hyT : c.e y ∈ c.e.target` using `c.e.map_source hy`. Take `⟨C, t₀, hC, ht₀, H⟩` from `hK k Y p σ d a E ha hE c {c.e y} isCompact_singleton (Set.singleton_subset_iff.2 hyT)`. Establish `hsy : c.e.symm (c.e y) = y` using `c.e.left_inv hy`.

Establish `hca : ContinuousAt (f ∘ c.e.symm) (c.e y)` using `hcont.continuousAt hU`. Take `⟨r₀, hr₀, hr₀U⟩` from `Metric.mem_nhds_iff.1 hU`. Establish `hq` using `continuous_and_smul ha hy`. Establish `hpos` using `ha.2 c y hy`. Establish `hM` using `mass_pos hq.1 hq.2 hpos`.

Establish `hI` using `integrable_cutoff hq.1 hq.2 hpos`. Rewrite using `[Metric.tendsto_nhdsWithin_nhds]`. Introduce `ε hε`. Take `⟨η, hη, hηf⟩` from `Metric.continuousAt_iff.1 hca (ε / 2) (half_pos hε)`. Use `set r := min η r₀ / 2 with hr`.

Establish `hr0 : 0 < r` using `by positivity`. Establish `hrη : r < η` using `by rw [hr]; linarith [min_le_left η r₀, lt_min hη hr₀]`. Establish `hrr₀ : r < r₀` using `by rw [hr]; linarith [min_le_right η r₀, lt_min hη hr₀]`. Use `⟨min t₀ (r / C), lt_min ht₀ (div_pos hr0 hC), fun t ht htd => ?_⟩` and prove the remaining obligations. Establish `ht : 0 < t` using `ht`.

Rewrite `htd` using `[Real.dist_eq, sub_zero, abs_of_pos ht]`. Establish `htt₀ : t ≤ t₀` using `(htd.trans_le (min_le_left _ _)).le`. Establish `hCt : C * t < r`. Use `htd.trans_le (min_le_right _ _)` as an intermediate fact. Rewrite `this` using `[lt_div_iff₀ hC, mul_comm]`. Then use the resulting hypothesis.

Take `⟨-, hball, hint⟩` from `H y hy rfl t ht htt₀`. Establish `hcl : Metric.closedBall (c.e y) r ⊆ U` using `(Metric.closedBall_subset_ball hrr₀).trans hr₀U`. Establish `hIO : IntegrableOn (f ∘ c.e.symm) (Metric.ball (c.e y) (C * t))` using `((hcont.mono hcl).integrableOn_compact (isCompact_closedBall _ _)).mono_set (Metric.ball_subset_ball hCt.le |>.trans Metric.ball_subset_closedBall)`. Establish `hg` using `(hint f hIO).1`. Establish `hpt : ∀ ξ, ‖(f (E c y (t • ξ)) - f y) * ChernReg.cutoff (a c y ξ)‖ ≤ ε / 2 * ChernReg.cutoff (a c y ξ)`.

Introduce `ξ`. Rewrite using `[norm_mul, Real.norm_of_nonneg (ChernReg.cutoff_nonneg _)]`. Distinguish the cases in `h1 : a c y ξ < 1`. Take `⟨hs, hb⟩` from `hball ξ h1`. Establish `hd : dist (c.e (E c y (t • ξ))) (c.e y) < η` using `(Metric.mem_ball.1 hb).trans (hCt.trans hrη)`.

Use `hηf hd` as an intermediate fact. Rewrite `this` using `[Function.comp_apply, Function.comp_apply, c.e.left_inv hs, hsy, Real.dist_eq]`. Conclude with `mul_le_mul_of_nonneg_right (Real.norm_eq_abs _ ▸ this.le) (ChernReg.cutoff_nonneg _)`. Establish `: ChernReg.cutoff (a c y ξ) = 0` using `by unfold ChernReg.cutoff; rw [if_neg h1]`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Establish `hdiff : rho a E f y t - f y = (∫ ξ, (f (E c y (t • ξ)) - f y) * ChernReg.cutoff (a c y ξ)) / ∫ ξ, ChernReg.cutoff (a c y ξ)`. Rewrite using `[rho_eq ha hE f hy t, rhoIn, mean]`. Repeatedly rewrite using `[sub_mul]`. Rewrite using `[integral_sub hg (hI.const_mul (f y)), integral_const_mul, sub_div, mul_div_cancel_right₀ _ hM.ne']`.

Rewrite using `[Real.dist_eq, hdiff, abs_div, abs_of_pos hM, div_lt_iff₀ hM]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rho_tendsto : GlobalTheory.HeightParts.KernelSt → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) (σ : k →+* ℂ) (d : ℕ)
    [SmoothOfRelativeDimension d p] (a : ChartForm p σ d) (E : ChartMap p σ d), IsKaehlerForm (GlobalTheory.AnRead.all p σ d) a →
    IsExph a E → ∀ (f : GlobalTheory.CxPts p σ → ℝ) (c : GlobalTheory.AlgChart p σ d) (y : GlobalTheory.CxPts p σ), y ∈ c.e.source →
    (∃ U ∈ 𝓝 (c.e y), ContinuousOn (f ∘ c.e.symm) U) → Tendsto (fun t => rho a E f y t) (𝓝[>] 0) (𝓝 (f y)) := by
  intro hK k _ Y p σ d _ a E ha hE f c y hy hU
  obtain ⟨U, hU, hcont⟩ := hU
  have hyT : c.e y ∈ c.e.target := c.e.map_source hy
  obtain ⟨C, t₀, hC, ht₀, H⟩ := hK k Y p σ d a E ha hE c {c.e y} isCompact_singleton
    (Set.singleton_subset_iff.2 hyT)
  have hsy : c.e.symm (c.e y) = y := c.e.left_inv hy
  have hca : ContinuousAt (f ∘ c.e.symm) (c.e y) := hcont.continuousAt hU
  obtain ⟨r₀, hr₀, hr₀U⟩ := Metric.mem_nhds_iff.1 hU
  have hq := continuous_and_smul ha hy
  have hpos := ha.2 c y hy
  have hM := mass_pos hq.1 hq.2 hpos
  have hI := integrable_cutoff hq.1 hq.2 hpos
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨η, hη, hηf⟩ := Metric.continuousAt_iff.1 hca (ε / 2) (half_pos hε)
  set r := min η r₀ / 2 with hr
  have hr0 : 0 < r := by positivity
  have hrη : r < η := by rw [hr]; linarith [min_le_left η r₀, lt_min hη hr₀]
  have hrr₀ : r < r₀ := by rw [hr]; linarith [min_le_right η r₀, lt_min hη hr₀]
  refine ⟨min t₀ (r / C), lt_min ht₀ (div_pos hr0 hC), fun t ht htd => ?_⟩
  have ht : 0 < t := ht
  rw [Real.dist_eq, sub_zero, abs_of_pos ht] at htd
  have htt₀ : t ≤ t₀ := (htd.trans_le (min_le_left _ _)).le
  have hCt : C * t < r := by
    have := htd.trans_le (min_le_right _ _)
    rwa [lt_div_iff₀ hC, mul_comm] at this
  obtain ⟨-, hball, hint⟩ := H y hy rfl t ht htt₀

  have hcl : Metric.closedBall (c.e y) r ⊆ U :=
    (Metric.closedBall_subset_ball hrr₀).trans hr₀U
  have hIO : IntegrableOn (f ∘ c.e.symm) (Metric.ball (c.e y) (C * t)) :=
    ((hcont.mono hcl).integrableOn_compact (isCompact_closedBall _ _)).mono_set
      (Metric.ball_subset_ball hCt.le |>.trans Metric.ball_subset_closedBall)
  have hg := (hint f hIO).1

  have hpt : ∀ ξ, ‖(f (E c y (t • ξ)) - f y) * ChernReg.cutoff (a c y ξ)‖ ≤ ε / 2 * ChernReg.cutoff (a c y ξ) := by
    intro ξ
    rw [norm_mul, Real.norm_of_nonneg (ChernReg.cutoff_nonneg _)]
    by_cases h1 : a c y ξ < 1
    · obtain ⟨hs, hb⟩ := hball ξ h1
      have hd : dist (c.e (E c y (t • ξ))) (c.e y) < η :=
        (Metric.mem_ball.1 hb).trans (hCt.trans hrη)
      have := hηf hd
      rw [Function.comp_apply, Function.comp_apply, c.e.left_inv hs, hsy, Real.dist_eq] at this
      exact mul_le_mul_of_nonneg_right (Real.norm_eq_abs _ ▸ this.le) (ChernReg.cutoff_nonneg _)
    · have : ChernReg.cutoff (a c y ξ) = 0 := by unfold ChernReg.cutoff; rw [if_neg h1]
      rw [this]; simp
  have hdiff : rho a E f y t - f y =
      (∫ ξ, (f (E c y (t • ξ)) - f y) * ChernReg.cutoff (a c y ξ)) / ∫ ξ, ChernReg.cutoff (a c y ξ) := by
    rw [rho_eq ha hE f hy t, rhoIn, mean]
    simp_rw [sub_mul]
    rw [integral_sub hg (hI.const_mul (f y)), integral_const_mul, sub_div,
      mul_div_cancel_right₀ _ hM.ne']
  rw [Real.dist_eq, hdiff, abs_div, abs_of_pos hM, div_lt_iff₀ hM]
  calc |∫ ξ, (f (E c y (t • ξ)) - f y) * ChernReg.cutoff (a c y ξ)|
      ≤ ∫ ξ, ε / 2 * ChernReg.cutoff (a c y ξ) :=
        norm_integral_le_of_norm_le (hI.const_mul _) (Filter.Eventually.of_forall hpt)
    _ = ε / 2 * ∫ ξ, ChernReg.cutoff (a c y ξ) := integral_const_mul _ _
    _ < ε * ∫ ξ, ChernReg.cutoff (a c y ξ) := by nlinarith

end GlobalTheory.RegLim
