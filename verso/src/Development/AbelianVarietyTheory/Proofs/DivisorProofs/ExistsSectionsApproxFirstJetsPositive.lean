import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureLowerBoundOnCoverBallsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyAtlasBallPartitionCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RoughHormanderEstimateCompactManifoldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeakSectionsFiniteWeightedAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeakSectionSmallFirstJetNormalFrameStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

/- English proof (translation)
Introduce `n Y _ _ _ _ _ _ ι La _ A H hH T`. Take `⟨C⟩` from `GlobalTheory.T.nonempty_atlasBallPartitionCover n Y ι La A`. Take `⟨q, c, Cq, r0, hc, hr0, hqT, hrest⟩` from `GlobalTheory.T.peak_sections_finite_weighted_atlas n Y ι La A C H hH T`. Use `⟨q, fun P hP => (hqT P hP).1, ?_⟩` and prove the remaining obligations. Introduce `G p hp ε hε`.

Take `⟨K', t0, hK', hk6⟩` from `GlobalTheory.T.rough_hormander_estimate_compact_manifold n Y ι La A C`. Take `⟨k1, hk1⟩` from `GlobalTheory.T.curvature_lower_bound_on_cover_balls n Y ι La A C H G hH t0`. Take `⟨K, hK, hF0⟩` from `hrest G p hp`. Establish `hloc : ∀ P : Y, ∃ k0 : ℕ, P ∈ T → ∀ k ≥ k0, ∀ D : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) D → DifferentiableOn ℂ (D (A.pick P) ∘ (A.chart (A.pick P)).symm) (ball (A.chart (A.pick P) P) r0) → n0 A (G + k • H) D ≤ ENNReal.ofReal ((K' * K) * Real.exp (-c * k)) → ‖D (A.pick P) ((A. …`. Introduce `P`.

Distinguish the cases in `hP : P ∈ T`. Take `⟨k0, hk0⟩` from `GlobalTheory.T.peak_section_small_first_jet_normal_frame n Y ι La A H G (A.pick P) (A.chart (A.pick P) P) r0 c Cq (K' * K) (q P) hr0 hc (hqT P hP).2.1 (hqT P hP).1 (hqT P hP).2.2 ε hε`. Conclude with `⟨k0, fun _ => hk0⟩`. Conclude with `⟨0, fun h => absurd h hP⟩`. Use `choose k0 hk0 using hloc`.

Use `⟨max k1 (T.sup k0), fun k hk => ?_⟩` and prove the remaining obligations. Establish `hk1' : k1 ≤ k` using `le_trans (le_max_left _ _) hk`. Take `⟨F0, hF0s, hF0b, hF0n⟩` from `hF0 k`. Take `⟨F, hFs, hFn⟩` from `hk6 (G + k • H) t0 le_rfl (hk1 k hk1') F0 hF0s`. Use `⟨F, hFs, fun P hP => ?_⟩` and prove the remaining obligations.

Establish `hkP : k0 P ≤ k` using `le_trans (le_trans (Finset.le_sup hP) (le_max_right _ _)) hk`. Establish `hDs : A.IsSSec (A.kap + (G + k • H)) (F0 - F)`. Use `⟨fun j => ?_, fun a b y ha hb => ?_⟩` and prove the remaining obligations. Establish `hd : DifferentiableOn ℂ (F j ∘ (A.chart j).symm) (A.chart j).target` using `(hFs.1 j).mono fun _ hv => ⟨hv, trivial⟩`. Establish `hF' : ContDiffOn ℝ ∞ (F j ∘ (A.chart j).symm) (A.chart j).target` using `fun v hv => (hyq_contDiffAt_of_holo (A.chart j).open_target hd hv).contDiffWithinAt`.

Conclude with `(hF0s.1 j).sub hF'`. Simplify using `only [Pi.sub_apply]`. Rewrite using `[hF0s.2 a b y ha hb, hFs.2 a b y trivial ha hb]`. Expand and normalize the polynomial expressions, which then agree. Establish `hb : ball (A.chart (A.pick P) P) r0 ⊆ (A.chart (A.pick P)).target` using `ball_subset_closedBall.trans (hqT P hP).2.1`.

Establish `hDd : DifferentiableOn ℂ ((F0 - F) (A.pick P) ∘ (A.chart (A.pick P)).symm) (ball (A.chart (A.pick P) P) r0)`. Establish `hg : DifferentiableOn ℂ (fun v => p P v * Complex.exp (k * q P v) - F (A.pick P) ((A.chart (A.pick P)).symm v)) (ball (A.chart (A.pick P) P) r0)`. Use `DifferentiableOn.sub ?_ ?_` and prove the remaining obligations. Conclude with `((hp P).mul (((hqT P hP).1.const_mul _).cexp)).differentiableOn`. Conclude with `(hFs.1 (A.pick P)).mono fun v hv => ⟨hb hv, trivial⟩`.

Use `hg.congr fun v hv => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Pi.sub_apply]`. Rewrite using `[hF0b P hP v hv]`. Establish `hDn : n0 A (G + k • H) (F0 - F) ≤ ENNReal.ofReal ((K' * K) * Real.exp (-c * k))`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨h1, h2⟩` from `hk0 P hP k hkP (F0 - F) hDs hDd hDn`. Establish `key : ∀ v ∈ ball (A.chart (A.pick P) P) r0, F (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v)) - p P v = -((F0 - F) (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v)))`. Introduce `v hv`. Establish `h0` using `hF0b P hP v hv`. Establish `hE : Complex.exp (k * q P v) * Complex.exp (-(k * q P v)) = 1`.

Rewrite using `[← Complex.exp_add]`. Simplify using the standard rewrite rules. Simplify using `only [Pi.sub_apply]`. Rewrite using `[h0]`. Take the linear combination `p P v * hE`.

Establish `hPx : (A.chart (A.pick P)).symm (A.chart (A.pick P) P) = P` using `(A.chart (A.pick P)).left_inv (A.mem_pick P)`. Establish `hx : A.chart (A.pick P) P ∈ ball (A.chart (A.pick P) P) r0` using `mem_ball_self hr0`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h3` using `key _ hx`. Rewrite `h3`, `h1` using `[hPx]`.

Rewrite using `[h3, norm_neg]`. Conclude with `h1`. Establish `hev : (fun v => F (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v)) - p P v) =ᶠ[𝓝 (A.chart (A.pick P) P)] fun v => -((F0 - F) (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v)))` using `by filter_upwards [isOpen_ball.mem_nhds hx] with v hv using key v hv`. Rewrite using `[hev.fderiv_eq, fderiv_fun_neg, norm_neg]`. Conclude with `h2`.
-/
theorem jets_approx_sections_of_positive : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ T : Finset Y, ∃ q : Y → V n → ℂ, (∀ P ∈ T, Differentiable ℂ (q P)) ∧ ∀ (G : La) (p : Y → V n → ℂ), (∀ P, Differentiable ℂ (p P)) → ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k ≥ k0, ∃ F : ι → Y → ℂ, A.IsSec (A.kap + (G + k • H)) F ∧ ∀ P ∈ T, ‖F (A.pick P) P * Complex.exp (-(k * q P (A.chart (A.pick P) P))) - p P (A.chart (A.pick P) P)‖ ≤ ε ∧ ‖fderiv ℂ (fun v => F (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v)) - p P v) (A.chart (A.pick P) P)‖ ≤ ε := by
  intro n Y _ _ _ _ _ _ ι La _ A H hH T
  obtain ⟨C⟩ := GlobalTheory.T.nonempty_atlasBallPartitionCover n Y ι La A
  obtain ⟨q, c, Cq, r0, hc, hr0, hqT, hrest⟩ := GlobalTheory.T.peak_sections_finite_weighted_atlas n Y ι La A C H hH T
  refine ⟨q, fun P hP => (hqT P hP).1, ?_⟩
  intro G p hp ε hε
  obtain ⟨K', t0, hK', hk6⟩ := GlobalTheory.T.rough_hormander_estimate_compact_manifold n Y ι La A C
  obtain ⟨k1, hk1⟩ := GlobalTheory.T.curvature_lower_bound_on_cover_balls n Y ι La A C H G hH t0
  obtain ⟨K, hK, hF0⟩ := hrest G p hp
  have hloc : ∀ P : Y, ∃ k0 : ℕ, P ∈ T → ∀ k ≥ k0, ∀ D : ι → Y → ℂ,
      A.IsSSec (A.kap + (G + k • H)) D →
      DifferentiableOn ℂ (D (A.pick P) ∘ (A.chart (A.pick P)).symm) (ball (A.chart (A.pick P) P) r0) →
      n0 A (G + k • H) D ≤ ENNReal.ofReal ((K' * K) * Real.exp (-c * k)) →
      ‖D (A.pick P) ((A.chart (A.pick P)).symm (A.chart (A.pick P) P)) *
          Complex.exp (-(k * q P (A.chart (A.pick P) P)))‖ ≤ ε ∧
      ‖fderiv ℂ (fun v => D (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v)))
          (A.chart (A.pick P) P)‖ ≤ ε := by
    intro P
    by_cases hP : P ∈ T
    · obtain ⟨k0, hk0⟩ := GlobalTheory.T.peak_section_small_first_jet_normal_frame n Y ι La A H G (A.pick P) (A.chart (A.pick P) P) r0 c Cq
        (K' * K) (q P) hr0 hc (hqT P hP).2.1 (hqT P hP).1 (hqT P hP).2.2 ε hε
      exact ⟨k0, fun _ => hk0⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose k0 hk0 using hloc
  refine ⟨max k1 (T.sup k0), fun k hk => ?_⟩
  have hk1' : k1 ≤ k := le_trans (le_max_left _ _) hk
  obtain ⟨F0, hF0s, hF0b, hF0n⟩ := hF0 k
  obtain ⟨F, hFs, hFn⟩ := hk6 (G + k • H) t0 le_rfl (hk1 k hk1') F0 hF0s
  refine ⟨F, hFs, fun P hP => ?_⟩
  have hkP : k0 P ≤ k := le_trans (le_trans (Finset.le_sup hP) (le_max_right _ _)) hk
  have hDs : A.IsSSec (A.kap + (G + k • H)) (F0 - F) := by
    refine ⟨fun j => ?_, fun a b y ha hb => ?_⟩
    · have hd : DifferentiableOn ℂ (F j ∘ (A.chart j).symm) (A.chart j).target :=
        (hFs.1 j).mono fun _ hv => ⟨hv, trivial⟩
      have hF' : ContDiffOn ℝ ∞ (F j ∘ (A.chart j).symm) (A.chart j).target := fun v hv =>
        (hyq_contDiffAt_of_holo (A.chart j).open_target hd hv).contDiffWithinAt
      exact (hF0s.1 j).sub hF'
    · simp only [Pi.sub_apply]
      rw [hF0s.2 a b y ha hb, hFs.2 a b y trivial ha hb]
      ring
  have hb : ball (A.chart (A.pick P) P) r0 ⊆ (A.chart (A.pick P)).target :=
    ball_subset_closedBall.trans (hqT P hP).2.1
  have hDd : DifferentiableOn ℂ ((F0 - F) (A.pick P) ∘ (A.chart (A.pick P)).symm)
      (ball (A.chart (A.pick P) P) r0) := by
    have hg : DifferentiableOn ℂ (fun v => p P v * Complex.exp (k * q P v) -
        F (A.pick P) ((A.chart (A.pick P)).symm v)) (ball (A.chart (A.pick P) P) r0) := by
      refine DifferentiableOn.sub ?_ ?_
      · exact ((hp P).mul (((hqT P hP).1.const_mul _).cexp)).differentiableOn
      · exact (hFs.1 (A.pick P)).mono fun v hv => ⟨hb hv, trivial⟩
    refine hg.congr fun v hv => ?_
    simp only [Function.comp_apply, Pi.sub_apply]
    rw [hF0b P hP v hv]
  have hDn : n0 A (G + k • H) (F0 - F) ≤ ENNReal.ofReal ((K' * K) * Real.exp (-c * k)) := by
    calc n0 A (G + k • H) (F0 - F) ≤ ENNReal.ofReal K' * n1 C (G + k • H) F0 := hFn
      _ ≤ ENNReal.ofReal K' * ENNReal.ofReal (K * Real.exp (-c * k)) := by gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul hK', mul_assoc]
  obtain ⟨h1, h2⟩ := hk0 P hP k hkP (F0 - F) hDs hDd hDn
  have key : ∀ v ∈ ball (A.chart (A.pick P) P) r0,
      F (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v)) - p P v =
        -((F0 - F) (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v))) := by
    intro v hv
    have h0 := hF0b P hP v hv
    have hE : Complex.exp (k * q P v) * Complex.exp (-(k * q P v)) = 1 := by
      rw [← Complex.exp_add]; simp
    simp only [Pi.sub_apply]
    rw [h0]
    linear_combination p P v * hE
  have hPx : (A.chart (A.pick P)).symm (A.chart (A.pick P) P) = P :=
    (A.chart (A.pick P)).left_inv (A.mem_pick P)
  have hx : A.chart (A.pick P) P ∈ ball (A.chart (A.pick P) P) r0 := mem_ball_self hr0
  refine ⟨?_, ?_⟩
  · have h3 := key _ hx
    rw [hPx] at h3 h1
    rw [h3, norm_neg]
    exact h1
  · have hev : (fun v => F (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v)) - p P v)
        =ᶠ[𝓝 (A.chart (A.pick P) P)]
        fun v => -((F0 - F) (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v))) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with v hv using key v hv
    rw [hev.fderiv_eq, fderiv_fun_neg, norm_neg]
    exact h2

end GlobalTheory
