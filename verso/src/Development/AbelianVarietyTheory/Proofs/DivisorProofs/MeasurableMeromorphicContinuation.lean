import Mathlib
open MeasureTheory Filter Topology

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa [iteratedDeriv_zero] using ⟨hdiff, hmeas⟩`. Consider the case `succ n ih`. Take `⟨ihd, ihm⟩` from `ih`. Use `⟨fun g => ?_, fun s hs => ?_⟩` and prove the remaining obligations.

Rewrite using `[iteratedDeriv_succ]`. Conclude with `(ihd g).deriv hV`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.1 hV s hs set t : ℕ → ℂ := fun m => s + (((ε / 2) * (1 / ((m : ℝ) + 1)) : ℝ) : ℂ) with ht`. Establish `hpos : ∀ m : ℕ, 0 < (ε / 2) * (1 / ((m : ℝ) + 1))` using `fun m => by positivity`. Establish `htV : ∀ m, t m ∈ V` using `fun m => by`.

Apply `hball` to reduce the goal to its premises. Rewrite using `[Metric.mem_ball, ht, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos m)]`. Establish `: 1 / ((m : ℝ) + 1) ≤ 1`. Rewrite using `[div_le_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `htne : ∀ m, t m ≠ s` using `fun m => by`. Introduce `h`. Establish `h2 : (((ε / 2) * (1 / ((m : ℝ) + 1)) : ℝ) : ℂ) = 0`. Use `congrArg (· - s) h` as an intermediate fact. Simplify `this` using `[ht]`.

Conclude with `(hpos m).ne' (by exact_mod_cast h2)`. Establish `hlim : Tendsto t atTop (𝓝[≠] s)`. Use `tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall htne⟩` and prove the remaining obligations. Establish `h0 : Tendsto (fun m : ℕ => (ε / 2) * (1 / ((m : ℝ) + 1))) atTop (𝓝 0)`. Simplify using `using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (ε / 2)`.

Establish `h1` using `(Complex.continuous_ofReal.tendsto 0).comp h0`. Simplify `(tendsto_const_nhds (x := s)).add h1` using `[ht]`. Establish `hq : ∀ m, Measurable (fun g => slope (iteratedDeriv n (F · g)) s (t m))`. Introduce `m`. Simplify using `only [slope_def_field]`.

Conclude with `((ihm _ (htV m)).sub (ihm _ hs)).div_const _`. Use `measurable_of_tendsto_metrizable hq (tendsto_pi_nhds.2 fun g => ?_)` and prove the remaining obligations. Rewrite using `[iteratedDeriv_succ]`. Establish `hd : DifferentiableAt ℂ (iteratedDeriv n (F · g)) s` using `(ihd g).differentiableAt (hV.mem_nhds hs)`. Conclude with `(hasDerivAt_iff_tendsto_slope.1 hd.hasDerivAt).comp hlim`.
-/
theorem measurable_iteratedDeriv_of_differentiableOn {X : Type} [MeasurableSpace X]
    (F : ℂ → X → ℂ) (V : Set ℂ) (hV : IsOpen V)
    (hdiff : ∀ g, DifferentiableOn ℂ (F · g) V) (hmeas : ∀ s ∈ V, Measurable (F s)) (n : ℕ) :
    (∀ g, DifferentiableOn ℂ (iteratedDeriv n (F · g)) V) ∧
      ∀ s ∈ V, Measurable (fun g => iteratedDeriv n (F · g) s) := by
  induction n with
  | zero => simpa [iteratedDeriv_zero] using ⟨hdiff, hmeas⟩
  | succ n ih =>
    obtain ⟨ihd, ihm⟩ := ih
    refine ⟨fun g => ?_, fun s hs => ?_⟩
    · rw [iteratedDeriv_succ]
      exact (ihd g).deriv hV
    · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV s hs
      set t : ℕ → ℂ := fun m => s + (((ε / 2) * (1 / ((m : ℝ) + 1)) : ℝ) : ℂ) with ht
      have hpos : ∀ m : ℕ, 0 < (ε / 2) * (1 / ((m : ℝ) + 1)) := fun m => by positivity
      have htV : ∀ m, t m ∈ V := fun m => by
        apply hball
        rw [Metric.mem_ball, ht, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (hpos m)]
        have : 1 / ((m : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
        nlinarith
      have htne : ∀ m, t m ≠ s := fun m => by
        intro h
        have h2 : (((ε / 2) * (1 / ((m : ℝ) + 1)) : ℝ) : ℂ) = 0 := by
          have := congrArg (· - s) h; simpa [ht] using this
        exact (hpos m).ne' (by exact_mod_cast h2)
      have hlim : Tendsto t atTop (𝓝[≠] s) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall htne⟩
        have h0 : Tendsto (fun m : ℕ => (ε / 2) * (1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
          simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (ε / 2)
        have h1 := (Complex.continuous_ofReal.tendsto 0).comp h0
        simpa [ht] using (tendsto_const_nhds (x := s)).add h1
      have hq : ∀ m, Measurable (fun g => slope (iteratedDeriv n (F · g)) s (t m)) := by
        intro m
        simp only [slope_def_field]
        exact ((ihm _ (htV m)).sub (ihm _ hs)).div_const _
      refine measurable_of_tendsto_metrizable hq (tendsto_pi_nhds.2 fun g => ?_)
      rw [iteratedDeriv_succ]
      have hd : DifferentiableAt ℂ (iteratedDeriv n (F · g)) s :=
        (ihd g).differentiableAt (hV.mem_nhds hs)
      exact (hasDerivAt_iff_tendsto_slope.1 hd.hasDerivAt).comp hlim

end GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `z hz`. Establish `hρ : 0 < ρ` using `Metric.pos_of_mem_ball hz`. Establish `hV` using `measurable_iteratedDeriv_of_differentiableOn F (Metric.ball c (min δ ρ)) Metric.isOpen_ball (fun g => (hdiff g).mono (Metric.ball_subset_ball (min_le_right _ _))) (fun s hs => hmeas s (Metric.ball_subset_ball (min_le_left _ _) hs))`. Establish `hc : c ∈ Metric.ball c (min δ ρ)` using `Metric.mem_ball_self (lt_min hδ hρ)`. Establish `hder : ∀ n, Measurable (fun g => iteratedDeriv n (F · g) c)` using `fun n => (hV n).2 c hc`.

Establish `hsum : ∀ g, HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n (F · g) c) (F z g)` using `fun g => Complex.hasSum_taylorSeries_on_ball (hdiff g) hz`. Use `measurable_of_tendsto_metrizable (f := fun N g => ∑ n ∈ Finset.range N, (n.factorial : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n (F · g) c) (fun N => ?_) (tendsto_pi_nhds.2 fun g => (hsum g).tendsto_sum_nat)` and prove the remaining obligations. Use `Finset.measurable_sum _ fun n _ => ?_` and prove the remaining obligations. Simplify using `only [smul_eq_mul]`. Conclude with `((hder n).const_mul _).const_mul _`.
-/
theorem measurable_on_ball_of_measurable_near_center {X : Type} [MeasurableSpace X]
    (F : ℂ → X → ℂ) (c : ℂ) (ρ δ : ℝ) (hδ : 0 < δ)
    (hdiff : ∀ g, DifferentiableOn ℂ (F · g) (Metric.ball c ρ))
    (hmeas : ∀ s ∈ Metric.ball c δ, Measurable (F s)) :
    ∀ z ∈ Metric.ball c ρ, Measurable (F z) := by
  intro z hz
  have hρ : 0 < ρ := Metric.pos_of_mem_ball hz
  have hV := measurable_iteratedDeriv_of_differentiableOn F (Metric.ball c (min δ ρ))
    Metric.isOpen_ball
    (fun g => (hdiff g).mono (Metric.ball_subset_ball (min_le_right _ _)))
    (fun s hs => hmeas s (Metric.ball_subset_ball (min_le_left _ _) hs))
  have hc : c ∈ Metric.ball c (min δ ρ) := Metric.mem_ball_self (lt_min hδ hρ)
  have hder : ∀ n, Measurable (fun g => iteratedDeriv n (F · g) c) := fun n => (hV n).2 c hc
  have hsum : ∀ g, HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ • (z - c) ^ n •
      iteratedDeriv n (F · g) c) (F z g) := fun g =>
    Complex.hasSum_taylorSeries_on_ball (hdiff g) hz
  refine measurable_of_tendsto_metrizable
    (f := fun N g => ∑ n ∈ Finset.range N, (n.factorial : ℂ)⁻¹ • (z - c) ^ n •
      iteratedDeriv n (F · g) c) (fun N => ?_) (tendsto_pi_nhds.2 fun g => (hsum g).tendsto_sum_nat)
  refine Finset.measurable_sum _ fun n _ => ?_
  simp only [smul_eq_mul]
  exact ((hder n).const_mul _).const_mul _

/- English proof (translation)
Introduce `X _ Eis c hloc hright`. Use `set O : Set ℂ := {s | ∀ᶠ t in 𝓝 s, Measurable (Eis t)} with hO`. Establish `hOopen : IsOpen O` using `isOpen_setOf_eventually_nhds`. Establish `key : ∀ s₀ ∈ closure O, ∃ ε > 0, ∀ s ∈ Metric.ball s₀ ε, s ≠ s₀ → Measurable (Eis s)`. Introduce `s₀ hs₀`.

Take `⟨k, U, Hol, hU, hEq, hHol⟩` from `hloc s₀`. Take `⟨r, hr, hrU⟩` from `Metric.mem_nhds_iff.1 hU`. Take `⟨s₃, hs₃O, hs₃⟩` from `Metric.mem_closure_iff.1 hs₀ (r / 4) (by positivity)`. Take `⟨δ, hδ, hδm⟩` from `Metric.eventually_nhds_iff.1 hs₃O`. Distinguish the cases in `h30 : s₃ = s₀`.

Substitute `h30` using the available equality. Conclude with `⟨δ, hδ, fun s hs _ => hδm hs⟩`. Establish `hd30 : 0 < dist s₃ s₀` using `dist_pos.2 h30`. Establish `hHolm : ∀ s ∈ Metric.ball s₃ (min δ (min (dist s₃ s₀) (r / 4))), Measurable (Hol s)`. Introduce `s hs`.

Rewrite `hs` using `[Metric.mem_ball]`. Establish `h1 : dist s s₃ < δ` using `lt_of_lt_of_le hs (min_le_left _ _)`. Establish `h2 : dist s s₃ < dist s₃ s₀` using `lt_of_lt_of_le hs ((min_le_right _ _).trans (min_le_left _ _))`. Establish `h3 : dist s s₃ < r / 4` using `lt_of_lt_of_le hs ((min_le_right _ _).trans (min_le_right _ _))`. Establish `hsne : s ≠ s₀`.

Introduce and unpack `rfl`. Rewrite `h2` using `[dist_comm]`. Conclude with `lt_irrefl _ h2`. Establish `hsU : s ∈ U` using `hrU (by`. Rewrite using `[Metric.mem_ball]`.

Use `dist_triangle s s₃ s₀` as an intermediate fact. Rewrite `h2` using `[dist_comm s₃ s₀]`. Combine the linear relations using `[dist_comm s₀ s₃])`. Establish `: Hol s = fun g => (s - s₀) ^ k * Eis s g` using `funext (hEq s hsU hsne)`. Rewrite using `[this]`.

Conclude with `(hδm h1).const_mul _`. Establish `hball : Metric.ball s₃ (3 * r / 4) ⊆ U`. Introduce `z hz`. Apply `hrU` to reduce the goal to its premises. Rewrite `hz`, the goal using `[Metric.mem_ball]`.

Use `dist_triangle z s₃ s₀` as an intermediate fact. Establish `: dist s₃ s₀ < r / 4` using `by rw [dist_comm]; exact hs₃`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hall` using `measurable_on_ball_of_measurable_near_center Hol s₃ (3 * r / 4) _ (lt_min hδ (lt_min hd30 (by positivity))) (fun g => (hHol g).mono hball) hHolm`. Use `⟨r / 2, by positivity, fun s hs hne => ?_⟩` and prove the remaining obligations.

Establish `hsb : s ∈ Metric.ball s₃ (3 * r / 4)`. Rewrite `hs`, the goal using `[Metric.mem_ball]`. Use `dist_triangle s s₀ s₃` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsU : s ∈ U` using `hball hsb`.

Establish `hk : (s - s₀) ^ k ≠ 0` using `pow_ne_zero _ (sub_ne_zero.2 hne)`. Establish `: Eis s = fun g => Hol s g / (s - s₀) ^ k` using `funext fun g => by`. Rewrite using `[hEq s hsU hne g]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`.

Conclude with `(hall s hsb).div_const _`. Establish `hCopen : IsOpen (closure O)`. Rewrite using `[Metric.isOpen_iff]`. Introduce `s₀ hs₀`. Take `⟨ε, hε, hm⟩` from `key s₀ hs₀`.

Use `⟨ε, hε, fun s hs => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hss : s = s₀`. Rewrite using `[hss]`. Conclude with `hs₀`. Apply `subset_closure show ∀ᶠ t in 𝓝 s, Measurable (Eis t)` to reduce the goal to its premises.

Establish `h1 : ∀ᶠ t in 𝓝 s, t ∈ Metric.ball s₀ ε` using `Metric.isOpen_ball.mem_nhds hs`. Establish `h2 : ∀ᶠ t in 𝓝 s, t ≠ s₀` using `isOpen_ne.mem_nhds hss`. Use `filter_upwards [h1, h2] with t ht1 ht2 using hm t ht1 ht2`. Establish `hne : (closure O).Nonempty`. Use `⟨((c + 1 : ℝ) : ℂ), subset_closure ?_⟩` and prove the remaining obligations.

Use `show ∀ᶠ t in 𝓝 ((c + 1 : ℝ) : ℂ), Measurable (Eis t)`. Establish `: IsOpen {t : ℂ | c < t.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Use `filter_upwards [this.mem_nhds (by simp)] with t ht using hright t ht`. Establish `huniv : closure O = Set.univ` using `IsClopen.eq_univ ⟨isClosed_closure, hCopen⟩ hne`. Introduce `s₀`.

Take `⟨ε, hε, hm⟩` from `key s₀ (huniv ▸ Set.mem_univ s₀)`. Establish `h1 : ∀ᶠ t in 𝓝[≠] s₀, t ∈ Metric.ball s₀ ε` using `nhdsWithin_le_nhds (Metric.ball_mem_nhds s₀ hε)`. Use `filter_upwards [h1, self_mem_nhdsWithin] with t ht1 ht2 using hm t ht1 ht2`.
-/
theorem measurable_eventually_of_meromorphic_family : ∀ {X : Type} [MeasurableSpace X] (Eis : ℂ → X → ℂ) (c : ℝ),
    (∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (Hol : ℂ → X → ℂ), U ∈ 𝓝 s₀ ∧
      (∀ s ∈ U, s ≠ s₀ → ∀ g, Hol s g = (s - s₀) ^ k * Eis s g) ∧ ∀ g, DifferentiableOn ℂ (Hol · g) U) →
    (∀ s : ℂ, c < s.re → Measurable (Eis s)) → ∀ s₀ : ℂ, ∀ᶠ s in 𝓝[≠] s₀, Measurable (Eis s) := by
  intro X _ Eis c hloc hright

  set O : Set ℂ := {s | ∀ᶠ t in 𝓝 s, Measurable (Eis t)} with hO
  have hOopen : IsOpen O := isOpen_setOf_eventually_nhds

  have key : ∀ s₀ ∈ closure O, ∃ ε > 0, ∀ s ∈ Metric.ball s₀ ε, s ≠ s₀ → Measurable (Eis s) := by
    intro s₀ hs₀
    obtain ⟨k, U, Hol, hU, hEq, hHol⟩ := hloc s₀
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨s₃, hs₃O, hs₃⟩ := Metric.mem_closure_iff.1 hs₀ (r / 4) (by positivity)
    obtain ⟨δ, hδ, hδm⟩ := Metric.eventually_nhds_iff.1 hs₃O
    by_cases h30 : s₃ = s₀
    · subst h30
      exact ⟨δ, hδ, fun s hs _ => hδm hs⟩
    have hd30 : 0 < dist s₃ s₀ := dist_pos.2 h30
    have hHolm : ∀ s ∈ Metric.ball s₃ (min δ (min (dist s₃ s₀) (r / 4))), Measurable (Hol s) := by
      intro s hs
      rw [Metric.mem_ball] at hs
      have h1 : dist s s₃ < δ := lt_of_lt_of_le hs (min_le_left _ _)
      have h2 : dist s s₃ < dist s₃ s₀ := lt_of_lt_of_le hs ((min_le_right _ _).trans (min_le_left _ _))
      have h3 : dist s s₃ < r / 4 := lt_of_lt_of_le hs ((min_le_right _ _).trans (min_le_right _ _))
      have hsne : s ≠ s₀ := by
        rintro rfl; rw [dist_comm] at h2; exact lt_irrefl _ h2
      have hsU : s ∈ U := hrU (by
        rw [Metric.mem_ball]
        have := dist_triangle s s₃ s₀
        rw [dist_comm s₃ s₀] at h2
        linarith [dist_comm s₀ s₃])
      have : Hol s = fun g => (s - s₀) ^ k * Eis s g := funext (hEq s hsU hsne)
      rw [this]
      exact (hδm h1).const_mul _
    have hball : Metric.ball s₃ (3 * r / 4) ⊆ U := by
      intro z hz
      apply hrU
      rw [Metric.mem_ball] at hz ⊢
      have := dist_triangle z s₃ s₀
      have : dist s₃ s₀ < r / 4 := by rw [dist_comm]; exact hs₃
      linarith
    have hall := measurable_on_ball_of_measurable_near_center Hol s₃ (3 * r / 4) _
      (lt_min hδ (lt_min hd30 (by positivity))) (fun g => (hHol g).mono hball) hHolm
    refine ⟨r / 2, by positivity, fun s hs hne => ?_⟩
    have hsb : s ∈ Metric.ball s₃ (3 * r / 4) := by
      rw [Metric.mem_ball] at hs ⊢
      have := dist_triangle s s₀ s₃
      linarith
    have hsU : s ∈ U := hball hsb
    have hk : (s - s₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hne)
    have : Eis s = fun g => Hol s g / (s - s₀) ^ k := funext fun g => by
      rw [hEq s hsU hne g]; field_simp
    rw [this]
    exact (hall s hsb).div_const _

  have hCopen : IsOpen (closure O) := by
    rw [Metric.isOpen_iff]
    intro s₀ hs₀
    obtain ⟨ε, hε, hm⟩ := key s₀ hs₀
    refine ⟨ε, hε, fun s hs => ?_⟩
    by_cases hss : s = s₀
    · rw [hss]; exact hs₀
    · apply subset_closure
      show ∀ᶠ t in 𝓝 s, Measurable (Eis t)
      have h1 : ∀ᶠ t in 𝓝 s, t ∈ Metric.ball s₀ ε := Metric.isOpen_ball.mem_nhds hs
      have h2 : ∀ᶠ t in 𝓝 s, t ≠ s₀ := isOpen_ne.mem_nhds hss
      filter_upwards [h1, h2] with t ht1 ht2 using hm t ht1 ht2
  have hne : (closure O).Nonempty := by
    refine ⟨((c + 1 : ℝ) : ℂ), subset_closure ?_⟩
    show ∀ᶠ t in 𝓝 ((c + 1 : ℝ) : ℂ), Measurable (Eis t)
    have : IsOpen {t : ℂ | c < t.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [this.mem_nhds (by simp)] with t ht using hright t ht
  have huniv : closure O = Set.univ := IsClopen.eq_univ ⟨isClosed_closure, hCopen⟩ hne
  intro s₀
  obtain ⟨ε, hε, hm⟩ := key s₀ (huniv ▸ Set.mem_univ s₀)
  have h1 : ∀ᶠ t in 𝓝[≠] s₀, t ∈ Metric.ball s₀ ε :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds s₀ hε)
  filter_upwards [h1, self_mem_nhdsWithin] with t ht1 ht2 using hm t ht1 ht2

end GlobalTheory
