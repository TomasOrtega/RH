import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeRowDifferenceSummableBoundStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.LatBd

/- English proof (translation)
Distinguish the cases in `hz : z = 0`. Substitute `hz` using the available equality. Establish `: ∀ s : ℝ, trm j s 0 = 0` using `fun s => by`. Simplify using `[trm, zero_pow (by omega : j ≠ 0)]`. Simplify using `only [this]`.

Conclude with `continuous_const`. Unfold `trm`. Use `continuous_const.mul (Complex.continuous_ofReal.comp ?_)` and prove the remaining obligations. Conclude with `continuous_const.rpow (continuous_const.mul continuous_id) fun _ => Or.inl (norm_ne_zero_iff.2 hz)`.
-/
theorem continuous_eisensteinLatticeTermWeightS_exponent {j : ℕ} (hj : 1 ≤ j) (z : ℂ) : Continuous fun s : ℝ => trm j s z := by
  by_cases hz : z = 0
  · subst hz
    have : ∀ s : ℝ, trm j s 0 = 0 := fun s => by
      simp [trm, zero_pow (by omega : j ≠ 0)]
    simp only [this]; exact continuous_const
  · unfold trm
    refine continuous_const.mul (Complex.continuous_ofReal.comp ?_)
    exact continuous_const.rpow (continuous_const.mul continuous_id) fun _ => Or.inl (norm_ne_zero_iff.2 hz)

/- English proof (translation)
Introduce `h`. Establish `him : (x.1 : ℝ) * τ.im = 0`. Use `congrArg Complex.im h` as an intermediate fact. Simplify using `using this`. Establish `h1 : x.1 = 0`.

Break down `mul_eq_zero.1 him with h' | h'` into its components or cases. Conclude with `h'` after adjusting the coercions. Conclude with `absurd h' τ.im_pos.ne'`. Establish `h2 : x.2 = 0`. Use `congrArg Complex.re h` as an intermediate fact.

Simplify using `[h1] at this`. Conclude with `this` after adjusting the coercions. Conclude with `hx (Prod.ext h1 h2)`.
-/
theorem lin_ne_zero (x : ℤ × ℤ) (hx : x ≠ 0) (τ : ℍ) : (x.1 : ℂ) * (τ : ℂ) + x.2 ≠ 0 := by
  intro h
  have him : (x.1 : ℝ) * τ.im = 0 := by
    have := congrArg Complex.im h
    simpa using this
  have h1 : x.1 = 0 := by
    rcases mul_eq_zero.1 him with h' | h'
    · exact_mod_cast h'
    · exact absurd h' τ.im_pos.ne'
  have h2 : x.2 = 0 := by
    have := congrArg Complex.re h
    simp [h1] at this
    exact_mod_cast this
  exact hx (Prod.ext h1 h2)

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Establish `: ∀ τ : ℍ, trm j s (((0 : ℤ × ℤ).1 : ℂ) * τ + (0 : ℤ × ℤ).2) = 0` using `fun τ => by`. Simplify using `[trm, zero_pow (by omega : j ≠ 0)]`. Simplify using `only [this]`.

Conclude with `continuous_const`. Establish `hc : Continuous fun τ : ℍ => (x.1 : ℂ) * (τ : ℂ) + x.2` using `(continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const`. Unfold `trm`. Use `((hc.pow j).inv₀ fun τ => pow_ne_zero _ (lin_ne_zero x hx τ)).mul (Complex.continuous_ofReal.comp ((continuous_norm.comp hc).rpow_const fun τ => Or.inl ?_))` and prove the remaining obligations. Conclude with `norm_ne_zero_iff.2 (lin_ne_zero x hx τ)`.
-/
theorem trm_cont_tau {j : ℕ} (hj : 1 ≤ j) (s : ℝ) (x : ℤ × ℤ) :
    Continuous fun τ : ℍ => trm j s ((x.1 : ℂ) * τ + x.2) := by
  by_cases hx : x = 0
  · subst hx
    have : ∀ τ : ℍ, trm j s (((0 : ℤ × ℤ).1 : ℂ) * τ + (0 : ℤ × ℤ).2) = 0 := fun τ => by
      simp [trm, zero_pow (by omega : j ≠ 0)]
    simp only [this]; exact continuous_const
  · have hc : Continuous fun τ : ℍ => (x.1 : ℂ) * (τ : ℂ) + x.2 :=
      (continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const
    unfold trm
    refine ((hc.pow j).inv₀ fun τ => pow_ne_zero _ (lin_ne_zero x hx τ)).mul
      (Complex.continuous_ofReal.comp ((continuous_norm.comp hc).rpow_const fun τ => Or.inl ?_))
    exact norm_ne_zero_iff.2 (lin_ne_zero x hx τ)

/- English proof (translation)
Unfold `dif`. Conclude with `(h x).sub (continuous_const.mul (continuous_finset_sum _ fun r _ => h _))`.
-/
theorem dif_cont {α : Type*} [TopologicalSpace α] (L : ℕ) (v : ℤ × ℤ) (F : α → ℤ × ℤ → ℂ)
    (h : ∀ x, Continuous fun a => F a x) (x : ℤ × ℤ) : Continuous fun a => dif L v (F a) x := by
  unfold dif
  exact (h x).sub (continuous_const.mul (continuous_finset_sum _ fun r _ => h _))

/- English proof (translation)
Use `show ‖dif L v F x - (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, dif L v F (x + (r : ℤ) • v)‖ ≤ _`. Use `(norm_sub_le _ _).trans (add_le_add (h x) ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_inv, Complex.norm_natCast]`. Conclude with `mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => h _)) (inv_nonneg.2 (Nat.cast_nonneg L))`.
-/
theorem difdif_le (L : ℕ) (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) (u : ℤ × ℤ → ℝ) (h : ∀ x, ‖dif L v F x‖ ≤ u x)
    (x : ℤ × ℤ) : ‖dif L v (dif L v F) x‖ ≤ u x + (L : ℝ)⁻¹ * ∑ r ∈ Finset.range L, u (x + (r : ℤ) • v) := by
  show ‖dif L v F x - (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, dif L v F (x + (r : ℤ) • v)‖ ≤ _
  refine (norm_sub_le _ _).trans (add_le_add (h x) ?_)
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => h _))
    (inv_nonneg.2 (Nat.cast_nonneg L))

/- English proof (translation)
Establish `h1 : ∀ r : ℕ, HasSum (fun x => u (x + (r : ℤ) • v)) S` using `fun r => (Equiv.addRight ((r : ℤ) • v)).hasSum_iff.2 hu`. Establish `h2` using `hasSum_sum (s := Finset.range L) fun r _ => h1 r`. Establish `h3` using `hu.add (h2.mul_left ((L : ℝ)⁻¹))`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]`.

Establish `: (L : ℝ) ≠ 0` using `by exact_mod_cast hL.ne'`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasSum_dom (L : ℕ) (hL : 0 < L) (v : ℤ × ℤ) (u : ℤ × ℤ → ℝ) {S : ℝ} (hu : HasSum u S) :
    HasSum (fun x => u x + (L : ℝ)⁻¹ * ∑ r ∈ Finset.range L, u (x + (r : ℤ) • v)) (2 * S) := by
  have h1 : ∀ r : ℕ, HasSum (fun x => u (x + (r : ℤ) • v)) S := fun r =>
    (Equiv.addRight ((r : ℤ) • v)).hasSum_iff.2 hu
  have h2 := hasSum_sum (s := Finset.range L) fun r _ => h1 r
  have h3 := hu.add (h2.mul_left ((L : ℝ)⁻¹))
  convert h3 using 1
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  field_simp; ring

/- English proof (translation)
Establish `e : ∀ x, ∑' i, g x i = ∫ i, g x i ∂(Measure.count : Measure I)` using `fun x => by`. Distinguish the cases in `hf : Summable (g x)`. Establish `hi : Integrable (g x) (Measure.count : Measure I)`. Rewrite using `[integrable_count_iff]`. Conclude with `summable_norm_iff.mpr hf`.

Rewrite using `[integral_countable hi]`. Simplify using `[measureReal_def]`. Rewrite using `[tsum_eq_zero_of_not_summable hf, integral_undef]`. Introduce `hi`. Rewrite `hi` using `[integrable_count_iff]`.

Conclude with `hf (summable_norm_iff.mp hi)`. Simplify using `only [e]`. Establish `hm : Measurable fun p : X × I => g p.1 p.2` using `measurable_from_prod_countable_left hg`. Conclude with `(StronglyMeasurable.integral_prod_right' (ν := (Measure.count : Measure I)) hm.stronglyMeasurable).measurable`.
-/
theorem measurable_tsum_any {X I : Type} [MeasurableSpace X] [Countable I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (g : X → I → ℂ) (hg : ∀ i, Measurable fun x => g x i) :
    Measurable fun x => ∑' i, g x i := by
  have e : ∀ x, ∑' i, g x i = ∫ i, g x i ∂(Measure.count : Measure I) := fun x => by
    by_cases hf : Summable (g x)
    · have hi : Integrable (g x) (Measure.count : Measure I) := by
        rw [integrable_count_iff]; exact summable_norm_iff.mpr hf
      rw [integral_countable hi]; simp [measureReal_def]
    · rw [tsum_eq_zero_of_not_summable hf, integral_undef]
      intro hi; rw [integrable_count_iff] at hi; exact hf (summable_norm_iff.mp hi)
  simp only [e]
  have hm : Measurable fun p : X × I => g p.1 p.2 := measurable_from_prod_countable_left hg
  exact (StronglyMeasurable.integral_prod_right' (ν := (Measure.count : Measure I))
    hm.stronglyMeasurable).measurable

end GlobalTheory.EisM.LatBd

namespace GlobalTheory.EisM.LatBd

/- English proof (translation)
Introduce `j L Φ hj hL ⟨B, hB⟩`. Establish `hB0 : 0 ≤ B` using `(norm_nonneg _).trans (hB 0)`. Establish `hj1 : 1 ≤ j` using `by omega`. Take `⟨C, A, hrow⟩` from `GlobalTheory.T.eisensteinLattice_rowDifference_summable_bound j L hj hL`. Establish `dom : ∀ τ : ℍ, ∃ U : ℤ × ℤ → ℝ, ∃ S : ℝ, HasSum U (2 * S) ∧ S ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹) ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ x, ‖Φ x * dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x‖ ≤ B * U x`.

Introduce `τ`. Take `⟨u, hus, hule, hu⟩` from `hrow τ`. Use `⟨_, _, hasSum_dom L hL (0, 1) u hus.hasSum, hule, fun s hs0 hs1 x => ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (hB x) (difdif_le L (0, 1) _ u (fun x => hu s x hs0 hs1) x) (norm_nonneg _) hB0`.

Use `⟨⟨2 * B * C, A, fun s τ hs0 hs1 => ?_⟩, fun s => ?_, fun τ => ?_⟩` and prove the remaining obligations. Take `⟨U, S, hU, hS, hb⟩` from `dom τ`. Establish `h` using `tsum_of_norm_bounded (hU.mul_left B) (hb s hs0 hs1)`. Establish `hpos : 0 ≤ B * 2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.

Unfold `lat`. Use `measurable_tsum_any (fun (τ : ℍ) x => Φ x * dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x) fun x => ?_` and prove the remaining obligations. Conclude with `(continuous_const.mul (dif_cont L (0, 1) _ (dif_cont L (0, 1) _ (fun y => trm_cont_tau hj1 s y)) x)).measurable`. Take `⟨U, S, hU, -, hb⟩` from `dom τ`. Unfold `lat`.

Use `tendsto_tsum_of_dominated_convergence (bound := fun x => B * U x) (hU.mul_left B).summable (fun x => ?_) ?_` and prove the remaining obligations. Establish `hc : Continuous fun s : ℝ => Φ x * dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x` using `continuous_const.mul (dif_cont L (0, 1) _ (dif_cont L (0, 1) _ (fun y => continuous_eisensteinLatticeTermWeightS_exponent hj1 _)) x)`. Conclude with `(hc.tendsto 0).mono_left nhdsWithin_le_nhds`. Use `filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with s hs`. Conclude with `hb s hs.1.le hs.2.le`.
-/
theorem lat_mod_meas_tendsto : ∀ (j L : ℕ) (Φ : ℤ × ℤ → ℂ), 2 ≤ j → 0 < L → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) →
    (∃ (C : ℝ) (A : ℕ), ∀ (s : ℝ) (τ : ℍ), 0 ≤ s → s ≤ 1 → ‖lat j s L (0, 1) Φ τ‖ ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹)) ∧
    (∀ s : ℝ, Measurable (lat j s L (0, 1) Φ)) ∧
    ∀ τ : ℍ, Tendsto (fun s : ℝ => lat j s L (0, 1) Φ τ) (𝓝[>] 0) (𝓝 (lat j 0 L (0, 1) Φ τ)) := by
  intro j L Φ hj hL ⟨B, hB⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hj1 : 1 ≤ j := by omega
  obtain ⟨C, A, hrow⟩ := GlobalTheory.T.eisensteinLattice_rowDifference_summable_bound j L hj hL

  have dom : ∀ τ : ℍ, ∃ U : ℤ × ℤ → ℝ, ∃ S : ℝ, HasSum U (2 * S) ∧ S ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹) ∧
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ x, ‖Φ x * dif L (0, 1) (dif L (0, 1)
        fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x‖ ≤ B * U x := by
    intro τ
    obtain ⟨u, hus, hule, hu⟩ := hrow τ
    refine ⟨_, _, hasSum_dom L hL (0, 1) u hus.hasSum, hule, fun s hs0 hs1 x => ?_⟩
    rw [norm_mul]
    exact mul_le_mul (hB x) (difdif_le L (0, 1) _ u (fun x => hu s x hs0 hs1) x) (norm_nonneg _) hB0
  refine ⟨⟨2 * B * C, A, fun s τ hs0 hs1 => ?_⟩, fun s => ?_, fun τ => ?_⟩
  · obtain ⟨U, S, hU, hS, hb⟩ := dom τ
    have h := tsum_of_norm_bounded (hU.mul_left B) (hb s hs0 hs1)
    have hpos : 0 ≤ B * 2 := by positivity
    calc ‖lat j s L (0, 1) Φ τ‖ ≤ B * (2 * S) := h
      _ = (B * 2) * S := by ring
      _ ≤ (B * 2) * (C * (τ.im ^ A + (τ.im ^ A)⁻¹)) := mul_le_mul_of_nonneg_left hS hpos
      _ = 2 * B * C * (τ.im ^ A + (τ.im ^ A)⁻¹) := by ring
  · unfold lat
    refine measurable_tsum_any (fun (τ : ℍ) x => Φ x * dif L (0, 1) (dif L (0, 1)
      fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x) fun x => ?_
    exact (continuous_const.mul (dif_cont L (0, 1) _
      (dif_cont L (0, 1) _ (fun y => trm_cont_tau hj1 s y)) x)).measurable
  · obtain ⟨U, S, hU, -, hb⟩ := dom τ
    unfold lat
    refine tendsto_tsum_of_dominated_convergence (bound := fun x => B * U x) (hU.mul_left B).summable
      (fun x => ?_) ?_
    · have hc : Continuous fun s : ℝ => Φ x * dif L (0, 1) (dif L (0, 1)
          fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x :=
        continuous_const.mul (dif_cont L (0, 1) _ (dif_cont L (0, 1) _ (fun y => continuous_eisensteinLatticeTermWeightS_exponent hj1 _)) x)
      exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with s hs
      exact hb s hs.1.le hs.2.le

end GlobalTheory.EisM.LatBd
