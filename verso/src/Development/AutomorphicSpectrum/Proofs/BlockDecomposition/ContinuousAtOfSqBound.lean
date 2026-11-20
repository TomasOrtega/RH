import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose

noncomputable section

open MeasureTheory Topology
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KerVec

/- English proof (translation)
Simplify using `only [ker, mul_assoc]`.
-/
theorem ker_mul_right {G : Type} [Group G] (Γ : Subgroup G) (φ : G → ℂ) (z y w : G) :
    ker Γ (fun g => φ (g * w)) z y = ker Γ φ z (y * w) := by
  simp only [ker, mul_assoc]

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1.comp (continuous_mul_const w), h.2.comp_homeomorph (Homeomorph.mulRight w)⟩`.
-/
theorem tst_mul_right {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {φ : G → ℂ} (h : Tst φ) (w : G) : Tst (fun g => φ (g * w)) :=
  ⟨h.1.comp (continuous_mul_const w), h.2.comp_homeomorph (Homeomorph.mulRight w)⟩

/- English proof (translation)
Rewrite using `[ContinuousAt, ← map_mul_left_nhds_one y₀, Filter.tendsto_map'_iff, Metric.tendsto_nhds]`. Introduce `ε hε`. Establish `hc0 : 0 ≤ c.toReal` using `ENNReal.toReal_nonneg`. Establish `hε' : 0 < ε / (c.toReal + 1)` using `by positivity`. Use `filter_upwards [h _ hε'] with w hw`.

Establish `hb : ‖f (y₀ * w) - f y₀‖ ^ 2 ≤ c.toReal * (ε / (c.toReal + 1)) ^ 2`. Establish `hr : ENNReal.ofReal (‖f (y₀ * w) - f y₀‖ ^ 2) ≤ ENNReal.ofReal (c.toReal * (ε / (c.toReal + 1)) ^ 2)`. Rewrite using `[ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_mul hc0, ENNReal.ofReal_pow hε'.le, ENNReal.ofReal_toReal hc, ofReal_norm]`. Conclude with `hw`. Conclude with `(ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hr`.

Establish `hlt : c.toReal * (ε / (c.toReal + 1)) ^ 2 < ε ^ 2`. Establish `hd : 0 < (c.toReal + 1) ^ 2` using `by positivity`. Rewrite using `[div_pow, ← mul_div_assoc, div_lt_iff₀ hd]`. Establish `: 0 < ε ^ 2` using `by positivity`. Use polynomial arithmetic with `[mul_nonneg hc0 hc0, mul_nonneg hc0 this.le, mul_nonneg (mul_nonneg hc0 hc0) this.le]`.

Use `show dist (f ((fun x => y₀ * x) w)) (f y₀) < ε`. Rewrite using `[dist_eq_norm]`. Conclude with `lt_of_pow_lt_pow_left₀ 2 hε.le (hb.trans_lt hlt)`.
-/
theorem continuousAt_of_sq_bound {G E : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SeminormedAddCommGroup E] (f : G → E) (y₀ : G) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ w in 𝓝 (1 : G),
      ‖f (y₀ * w) - f y₀‖ₑ ^ 2 ≤ c * ENNReal.ofReal ε ^ 2) : ContinuousAt f y₀ := by
  rw [ContinuousAt, ← map_mul_left_nhds_one y₀, Filter.tendsto_map'_iff, Metric.tendsto_nhds]
  intro ε hε
  have hc0 : 0 ≤ c.toReal := ENNReal.toReal_nonneg
  have hε' : 0 < ε / (c.toReal + 1) := by positivity
  filter_upwards [h _ hε'] with w hw
  have hb : ‖f (y₀ * w) - f y₀‖ ^ 2 ≤ c.toReal * (ε / (c.toReal + 1)) ^ 2 := by
    have hr : ENNReal.ofReal (‖f (y₀ * w) - f y₀‖ ^ 2) ≤
        ENNReal.ofReal (c.toReal * (ε / (c.toReal + 1)) ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_mul hc0,
        ENNReal.ofReal_pow hε'.le, ENNReal.ofReal_toReal hc, ofReal_norm]
      exact hw
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hr
  have hlt : c.toReal * (ε / (c.toReal + 1)) ^ 2 < ε ^ 2 := by
    have hd : 0 < (c.toReal + 1) ^ 2 := by positivity
    rw [div_pow, ← mul_div_assoc, div_lt_iff₀ hd]
    have : 0 < ε ^ 2 := by positivity
    nlinarith [mul_nonneg hc0 hc0, mul_nonneg hc0 this.le, mul_nonneg (mul_nonneg hc0 hc0) this.le]
  show dist (f ((fun x => y₀ * x) w)) (f y₀) < ε
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le (hb.trans_lt hlt)

/- English proof (translation)
Introduce `hC hL hT hV X ι _ Φ hΦ`. Set `k : X.G → ι → X.Hs ι` to `fun y j => WithLp.toLp 2 fun l => ((hL X (Φ l j) (hΦ l j)).1 y).toLp _`. Establish `hk : ∀ y j, X.IsVec Φ y j (k y j)` using `fun y j l => ((hL X (Φ l j) (hΦ l j)).1 y).coeFn_toLp`. Use `⟨k, fun j => continuous_iff_continuousAt.2 fun y₀ => ?_, hk⟩` and prove the remaining obligations. Take `⟨N, hNc, hN1⟩` from `exists_compact_mem_nhds (1 : X.G)`.

Establish `h1N : (1 : X.G) ∈ N` using `mem_of_mem_nhds hN1`. Establish `hS : IsCompact (⋃ l, tsupport (Φ l j))` using `isCompact_iUnion fun l => (hΦ l j).2`. Take `⟨Ω, hΩdef⟩ : ∃ Ω : Set X.G, Ω = (⋃ l, tsupport (Φ l j)) * N⁻¹` from `⟨_, rfl⟩`. Establish `hΩ : IsCompact Ω` using `hΩdef ▸ hS.mul hNc.inv`. Establish `hsub : ∀ (l : ι) (w : X.G), w ∈ N → Function.support (fun g => Φ l j (g * w)) ⊆ Ω`.

Introduce `l w hw g hg`. Rewrite using `[hΩdef]`. Establish `h1 : g * w ∈ ⋃ l, tsupport (Φ l j)` using `Set.mem_iUnion.2 ⟨l, subset_tsupport _ hg⟩`. Establish `h2 : w⁻¹ ∈ N⁻¹` using `Set.inv_mem_inv.2 hw`. Simplify using `using Set.mul_mem_mul h1 h2`.

Establish `hc : (Fintype.card ι : ℝ≥0∞) * (X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y₀) ≠ ⊤` using `ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top hΩ.inv.measure_lt_top.ne ((hC X).1 _ (hΩ.inv.mul hΩ) y₀))`. Use `continuousAt_of_sq_bound (fun y => k y j) y₀ _ hc fun ε hε => ?_` and prove the remaining obligations. Use `choose W hW hW' using fun l => hT X (Φ l j) ε (hΦ l j) hε`. Use `filter_upwards [hN1, Filter.eventually_all.2 hW] with w hwN hwW`. Establish `hv : X.IsVec (fun l i g => Φ l i (g * w)) y₀ j (k (y₀ * w) j)` using `fun l => (hk (y₀ * w) j l).trans (Filter.Eventually.of_forall fun z => (ker_mul_right X.Γ (Φ l j) z y₀ w).symm)`.

Establish `key` using `hV X ι (fun l i g => Φ l i (g * w)) Φ Ω ε y₀ j _ _ hΩ (fun l => ⟨tst_mul_right (hΦ l j) w, hΦ l j, hsub l w hwN, by simpa using hsub l 1 h1N, fun z => by`. Simplify using `using hW' l 1 (mem_of_mem_nhds (hW l)) w (hwW l) z⟩) hv (hk y₀ j)`. Use `key.trans (le_of_eq ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vecEx : CntBasic → KernelL2RowsColumns → TwoUnif → VecClose → VecEx := by
  intro hC hL hT hV X ι _ Φ hΦ
  let k : X.G → ι → X.Hs ι := fun y j =>
    WithLp.toLp 2 fun l => ((hL X (Φ l j) (hΦ l j)).1 y).toLp _
  have hk : ∀ y j, X.IsVec Φ y j (k y j) := fun y j l =>
    ((hL X (Φ l j) (hΦ l j)).1 y).coeFn_toLp
  refine ⟨k, fun j => continuous_iff_continuousAt.2 fun y₀ => ?_, hk⟩
  obtain ⟨N, hNc, hN1⟩ := exists_compact_mem_nhds (1 : X.G)
  have h1N : (1 : X.G) ∈ N := mem_of_mem_nhds hN1
  have hS : IsCompact (⋃ l, tsupport (Φ l j)) := isCompact_iUnion fun l => (hΦ l j).2
  obtain ⟨Ω, hΩdef⟩ : ∃ Ω : Set X.G, Ω = (⋃ l, tsupport (Φ l j)) * N⁻¹ := ⟨_, rfl⟩
  have hΩ : IsCompact Ω := hΩdef ▸ hS.mul hNc.inv
  have hsub : ∀ (l : ι) (w : X.G), w ∈ N → Function.support (fun g => Φ l j (g * w)) ⊆ Ω := by
    intro l w hw g hg
    rw [hΩdef]
    have h1 : g * w ∈ ⋃ l, tsupport (Φ l j) :=
      Set.mem_iUnion.2 ⟨l, subset_tsupport _ hg⟩
    have h2 : w⁻¹ ∈ N⁻¹ := Set.inv_mem_inv.2 hw
    simpa using Set.mul_mem_mul h1 h2
  have hc : (Fintype.card ι : ℝ≥0∞) * (X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y₀) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top hΩ.inv.measure_lt_top.ne
      ((hC X).1 _ (hΩ.inv.mul hΩ) y₀))
  refine continuousAt_of_sq_bound (fun y => k y j) y₀ _ hc fun ε hε => ?_
  choose W hW hW' using fun l => hT X (Φ l j) ε (hΦ l j) hε
  filter_upwards [hN1, Filter.eventually_all.2 hW] with w hwN hwW
  have hv : X.IsVec (fun l i g => Φ l i (g * w)) y₀ j (k (y₀ * w) j) := fun l =>
    (hk (y₀ * w) j l).trans (Filter.Eventually.of_forall fun z => (ker_mul_right X.Γ (Φ l j) z y₀ w).symm)
  have key := hV X ι (fun l i g => Φ l i (g * w)) Φ Ω ε y₀ j _ _ hΩ
    (fun l => ⟨tst_mul_right (hΦ l j) w, hΦ l j, hsub l w hwN,
      by simpa using hsub l 1 h1N, fun z => by
        simpa using hW' l 1 (mem_of_mem_nhds (hW l)) w (hwW l) z⟩) hv (hk y₀ j)
  refine key.trans (le_of_eq ?_)
  ring

end GlobalTheory.CompanionTheory.KerVec

end
