import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZariskiObjects
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolGermPointIdealSpan
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

/- English proof (translation)
Take `⟨p, r, hp⟩` from `hf`. Establish `hrad : p.shift.radius = p.radius` using `FormalMultilinearSeries.radius_shift p`. Establish `hq : 0 < p.shift.radius` using `by rw [hrad]; exact lt_of_lt_of_le hp.r_pos hp.r_le`. Establish `hG : HasFPowerSeriesOnBall p.shift.sum p.shift 0 p.shift.radius` using `p.shift.hasFPowerSeriesOnBall hq`. Use `⟨fun i z => p.shift.sum (z - w) (Pi.single i 1), fun i => ?_, ?_⟩` and prove the remaining obligations.

Establish `h2 : AnalyticAt ℂ (fun z : σ → ℂ => z - w) w` using `analyticAt_id.sub analyticAt_const`. Establish `h3 : AnalyticAt ℂ p.shift.sum ((fun z : σ → ℂ => z - w) w)`. Simplify using `using hG.analyticAt`. Conclude with `((ContinuousLinearMap.apply ℂ ℂ (Pi.single i (1 : ℂ))).analyticAt _).comp (AnalyticAt.comp (g := p.shift.sum) (f := fun z : σ → ℂ => z - w) h3 h2)`. Use `filter_upwards [Metric.eball_mem_nhds w hp.r_pos] with z hz set y := z - w with hy`.

Establish `hy0 : y ∈ Metric.eball (0 : σ → ℂ) r`. Rewrite `hz`, the goal using `[Metric.mem_eball]`. Rewrite using `[edist_zero_right, hy, ← edist_eq_enorm_sub]` and apply the resulting hypothesis. Establish `hy1 : y ∈ Metric.eball (0 : σ → ℂ) p.shift.radius` using `Metric.eball_subset_eball (hrad ▸ hp.r_le) hy0`. Establish `h1` using `hp.hasSum hy0`.

Establish `h2` using `hG.hasSum hy1`. Rewrite `h2` using `[zero_add]`. Establish `h3` using `(ContinuousLinearMap.apply ℂ ℂ y).hasSum h2`. Establish `h4 : ∀ n, (ContinuousLinearMap.apply ℂ ℂ y) (p.shift n fun _ => y) = p (n + 1) fun _ => y`. Introduce `n`.

Simplify using `only [ContinuousLinearMap.apply_apply, FormalMultilinearSeries.shift, ContinuousMultilinearMap.curryRight_apply]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun k => ?_) j <;> simp`. Simplify using `only [h4, ContinuousLinearMap.apply_apply] at h3`.

Establish `h5` using `(hasSum_nat_add_iff' 1).mpr h1`. Simplify using `only [Finset.range_one, Finset.sum_singleton, hp.coeff_zero] at h5`. Establish `e` using `h5.unique h3`. Establish `hwz : w + y = z` using `by rw [hy]; abel`. Rewrite `e` using `[hwz]`.

Establish `e2 : p.shift.sum y y = ∑ i, (z i - w i) * p.shift.sum y (Pi.single i 1)`. Establish `hyy : p.shift.sum y y = p.shift.sum y (∑ i, Pi.single i (y i))`. Rewrite using `[Finset.univ_sum_single]`. Rewrite using `[hyy, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[show (Pi.single i (y i) : σ → ℂ) = y i • Pi.single i 1 by`. Use extensionality with `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h], map_smul, smul_eq_mul, hy, Pi.sub_apply]`. Rewrite using `[← e2, ← e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hadamard_decomposition {σ : Type} [Fintype σ] {w : σ → ℂ} {f : (σ → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f w) :
    ∃ g : σ → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (g i) w) ∧
      ∀ᶠ z in 𝓝 w, f z = f w + ∑ i, (z i - w i) * g i z := by
  classical
  obtain ⟨p, r, hp⟩ := hf
  have hrad : p.shift.radius = p.radius := FormalMultilinearSeries.radius_shift p
  have hq : 0 < p.shift.radius := by rw [hrad]; exact lt_of_lt_of_le hp.r_pos hp.r_le
  have hG : HasFPowerSeriesOnBall p.shift.sum p.shift 0 p.shift.radius :=
    p.shift.hasFPowerSeriesOnBall hq
  refine ⟨fun i z => p.shift.sum (z - w) (Pi.single i 1), fun i => ?_, ?_⟩
  · have h2 : AnalyticAt ℂ (fun z : σ → ℂ => z - w) w := analyticAt_id.sub analyticAt_const
    have h3 : AnalyticAt ℂ p.shift.sum ((fun z : σ → ℂ => z - w) w) := by
      simpa using hG.analyticAt
    exact ((ContinuousLinearMap.apply ℂ ℂ (Pi.single i (1 : ℂ))).analyticAt _).comp
      (AnalyticAt.comp (g := p.shift.sum) (f := fun z : σ → ℂ => z - w) h3 h2)
  · filter_upwards [Metric.eball_mem_nhds w hp.r_pos] with z hz
    set y := z - w with hy
    have hy0 : y ∈ Metric.eball (0 : σ → ℂ) r := by
      rw [Metric.mem_eball] at hz ⊢
      rwa [edist_zero_right, hy, ← edist_eq_enorm_sub]
    have hy1 : y ∈ Metric.eball (0 : σ → ℂ) p.shift.radius :=
      Metric.eball_subset_eball (hrad ▸ hp.r_le) hy0
    have h1 := hp.hasSum hy0
    have h2 := hG.hasSum hy1
    rw [zero_add] at h2
    have h3 := (ContinuousLinearMap.apply ℂ ℂ y).hasSum h2
    have h4 : ∀ n, (ContinuousLinearMap.apply ℂ ℂ y) (p.shift n fun _ => y) =
        p (n + 1) fun _ => y := by
      intro n
      simp only [ContinuousLinearMap.apply_apply, FormalMultilinearSeries.shift,
        ContinuousMultilinearMap.curryRight_apply]
      congr 1
      funext j
      refine Fin.lastCases ?_ (fun k => ?_) j <;> simp
    simp only [h4, ContinuousLinearMap.apply_apply] at h3
    have h5 := (hasSum_nat_add_iff' 1).mpr h1
    simp only [Finset.range_one, Finset.sum_singleton, hp.coeff_zero] at h5
    have e := h5.unique h3
    have hwz : w + y = z := by rw [hy]; abel
    rw [hwz] at e
    have e2 : p.shift.sum y y = ∑ i, (z i - w i) * p.shift.sum y (Pi.single i 1) := by
      have hyy : p.shift.sum y y = p.shift.sum y (∑ i, Pi.single i (y i)) := by
        rw [Finset.univ_sum_single]
      rw [hyy, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (Pi.single i (y i) : σ → ℂ) = y i • Pi.single i 1 by
        ext j; by_cases h : j = i
        · subst h; simp
        · simp [h], map_smul, smul_eq_mul, hy, Pi.sub_apply]
    rw [← e2, ← e]
    ring

/- English proof (translation)
Introduce `σ _ w`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `⟨_, f, hf, rfl⟩ hφ`. Establish `hfw : f w = 0` using `hφ`. Take `⟨g, hg, hfg⟩` from `hadamard_decomposition hf`.

Establish `key : (⟨(f : Germ (𝓝 w) ℂ), f, hf, rfl⟩ : holGerms w) = ∑ i, polyGerm w (X i - C (w i)) * ⟨(g i : Germ (𝓝 w) ℂ), g i, hg i, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(f : Germ (𝓝 w) ℂ) = (holGerms w).subtype (∑ i, _)`. Rewrite using `[map_sum]`. Simplify using `only [map_mul, Subring.coe_subtype]`.

Establish `hsum : ((fun z => ∑ i, (z i - w i) * g i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = ∑ i, ((fun z : σ → ℂ => z i - w i : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) * (g i : Germ (𝓝 w) ℂ)`. Express the relevant statement in the definitionally equal form `Germ.coeRingHom (𝓝 w) (fun z => ∑ i, (z i - w i) * g i z) = _`. Rewrite using `[show (fun z => ∑ i, (z i - w i) * g i z : (σ → ℂ) → ℂ) = ∑ i, (fun z : σ → ℂ => z i - w i) * g i by`. Use function extensionality and compare the values at `z`. Simplify using `[Finset.sum_apply], map_sum]`.

Both sides reduce to the same expression. Establish `hfe : (f : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, (z i - w i) * g i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)` using `Germ.coe_eq.mpr (hfg.mono fun z hz => by rw [hz, hfw, zero_add])`. Rewrite using `[hfe, hsum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 1`.

Express the relevant statement in the definitionally equal form `_ = ((fun z : σ → ℂ => eval z (X i - C (w i)) : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)`. Simplify using the standard rewrite rules. Rewrite using `[key]`. Conclude with `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)`. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Express the relevant statement in the definitionally equal form `holGermValue w (polyGerm w (X i - C (w i))) = 0`. Rewrite using `[holGermValue_polyGerm]`. Simplify using the standard rewrite rules.
-/
theorem HolGermPointIdealSpan.proof : HolGermPointIdealSpan.Statement := by
  intro σ _ w
  apply le_antisymm
  · rintro ⟨_, f, hf, rfl⟩ hφ
    have hfw : f w = 0 := hφ
    obtain ⟨g, hg, hfg⟩ := hadamard_decomposition hf
    have key : (⟨(f : Germ (𝓝 w) ℂ), f, hf, rfl⟩ : holGerms w) =
        ∑ i, polyGerm w (X i - C (w i)) * ⟨(g i : Germ (𝓝 w) ℂ), g i, hg i, rfl⟩ := by
      apply Subtype.ext
      change (f : Germ (𝓝 w) ℂ) = (holGerms w).subtype (∑ i, _)
      rw [map_sum]
      simp only [map_mul, Subring.coe_subtype]
      have hsum : ((fun z => ∑ i, (z i - w i) * g i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) =
          ∑ i, ((fun z : σ → ℂ => z i - w i : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) * (g i : Germ (𝓝 w) ℂ) := by
        change Germ.coeRingHom (𝓝 w) (fun z => ∑ i, (z i - w i) * g i z) = _
        rw [show (fun z => ∑ i, (z i - w i) * g i z : (σ → ℂ) → ℂ) =
            ∑ i, (fun z : σ → ℂ => z i - w i) * g i by
          funext z; simp [Finset.sum_apply], map_sum]
        rfl
      have hfe : (f : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, (z i - w i) * g i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) :=
        Germ.coe_eq.mpr (hfg.mono fun z hz => by rw [hz, hfw, zero_add])
      rw [hfe, hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      change _ = ((fun z : σ → ℂ => eval z (X i - C (w i)) : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)
      simp
    rw [key]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change holGermValue w (polyGerm w (X i - C (w i))) = 0
    rw [holGermValue_polyGerm]
    simp

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
