import Mathlib

namespace ReciprocityTheory.Cheb

open Filter Topology Set Complex

/- English proof (translation)
Rewrite using `[isDiscrete_iff_forall_mem_exists_isOpen]`. Introduce `y hy`. Use `⟨Metric.ball y 1, Metric.isOpen_ball, ?_⟩` and prove the remaining obligations. Use extensionality with `w`. Simplify using `only [mem_inter_iff, Metric.mem_ball, mem_ofPred_eq, mem_singleton_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hw, hwc⟩`. Establish `hexp : Complex.exp w = Complex.exp y` using `hwc.trans hy.symm`. Take `⟨n, hn⟩` from `Complex.exp_eq_exp_iff_exists_int.mp hexp`. Assume the negation of the conclusion as `hne`.

Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`. Apply `hne` to reduce the goal to its premises. Simplify using `using hn`. Establish `hd : dist w y = |(n : ℝ)| * (2 * Real.pi)`.

Rewrite using `[dist_eq_norm, hn, add_sub_cancel_left, norm_mul, Complex.norm_intCast]`. Simplify using `[Complex.norm_I, abs_of_pos Real.pi_pos]`. Establish `h1 : (1 : ℝ) ≤ |(n : ℝ)|` using `by exact_mod_cast Int.one_le_abs hn0`. Use `Real.pi_gt_three` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Introduce and unpack `rfl`. Conclude with `⟨Metric.mem_ball_self one_pos, hy⟩`.
-/
theorem isDiscrete_exp_fiber (c : ℂ) : IsDiscrete {w : ℂ | Complex.exp w = c} := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro y hy
  refine ⟨Metric.ball y 1, Metric.isOpen_ball, ?_⟩
  ext w
  simp only [mem_inter_iff, Metric.mem_ball, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨hw, hwc⟩
    have hexp : Complex.exp w = Complex.exp y := hwc.trans hy.symm
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    by_contra hne
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hne
      simpa using hn
    have hd : dist w y = |(n : ℝ)| * (2 * Real.pi) := by
      rw [dist_eq_norm, hn, add_sub_cancel_left, norm_mul, Complex.norm_intCast]
      simp [Complex.norm_I, abs_of_pos Real.pi_pos]
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
    have := Real.pi_gt_three
    nlinarith
  · rintro rfl
    exact ⟨Metric.mem_ball_self one_pos, hy⟩

/- English proof (translation)
Establish `hslitB : ∀ z ∈ Metric.closedBall (1 : ℂ) (1 / 2), z ∈ slitPlane`. Introduce `z hz`. Rewrite `hz` using `[Metric.mem_closedBall, dist_eq_norm]`. Use `Complex.abs_re_le_norm (z - 1)` as an intermediate fact. Rewrite `this` using `[Complex.sub_re, Complex.one_re]`.

Conclude with `mem_slitPlane_iff.mpr (Or.inl (by linarith [(abs_le.mp (this.trans hz)).1]))`. Take `⟨B, hB⟩` from `(isCompact_closedBall (1 : ℂ) (1 / 2)).exists_bound_of_continuousOn (f := Complex.log) (fun z hz => (continuousAt_clog (hslitB z hz)).continuousWithinAt)`. Establish `hlim' : Tendsto (fun s => Complex.exp (abelian₂ s) / L1) (𝓝[>] 1) (𝓝 1)`. Simplify `hlim.div_const L1` using `[div_self hL1]`. Establish `hev` using `hlim'.eventually (Metric.closedBall_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))`.

Take `⟨u, hu1, hu⟩` from `mem_nhdsGT_iff_exists_Ioo_subset.mp hev`. Establish `hu1 : (1 : ℝ) < u` using `hu1`. Use `set t : ℝ := min ((1 + u) / 2) 2 with ht`. Establish `ht1 : 1 < t` using `lt_min (by linarith) (by norm_num)`. Establish `htu : t < u` using `lt_of_le_of_lt (min_le_left _ _) (by linarith)`.

Establish `ht2 : t ≤ 2` using `min_le_right _ _`. Establish `hSsub : Ioc 1 t ⊆ Ioc (1 : ℝ) 2` using `Ioc_subset_Ioc_right ht2`. Establish `hball : ∀ s ∈ Ioc 1 t, Complex.exp (abelian₂ s) / L1 ∈ Metric.closedBall (1 : ℂ) (1 / 2)` using `fun s hs => hu ⟨hs.1, lt_of_le_of_lt hs.2 htu⟩`. Use `set g : ℝ → ℂ := fun s => abelian₂ s - Complex.log (Complex.exp (abelian₂ s) / L1) with hg`. Establish `hgc : ContinuousOn g (Ioc 1 t)`.

Introduce `s hs`. Establish `h1 : ContinuousWithinAt abelian₂ (Ioc 1 t) s` using `(hcont s (hSsub hs)).mono hSsub`. Establish `h2 : ContinuousWithinAt (fun s => Complex.exp (abelian₂ s) / L1) (Ioc 1 t) s` using `(Complex.continuous_exp.continuousAt.comp_continuousWithinAt h1).div_const L1`. Establish `h3 : ContinuousWithinAt (fun s => Complex.log (Complex.exp (abelian₂ s) / L1)) (Ioc 1 t) s` using `(continuousAt_clog (hslitB _ (hball s hs))).comp_continuousWithinAt (f := fun s => Complex.exp (abelian₂ s) / L1) h2`. Conclude with `h1.sub h3`.

Establish `hmaps : MapsTo g (Ioc 1 t) {w : ℂ | Complex.exp w = L1}`. Introduce `s _`. Establish `hne : Complex.exp (abelian₂ s) / L1 ≠ 0` using `div_ne_zero (Complex.exp_ne_zero _) hL1`. Simplify using `only [mem_ofPred_eq, hg, Complex.exp_sub, Complex.exp_log hne]`. Clear denominators, using `[Complex.exp_ne_zero]` for the nonvanishing conditions.

Take `⟨c, -, hc⟩` from `isPreconnected_Ioc.eqOn_const_of_mapsTo (isDiscrete_exp_fiber L1) hgc hmaps ⟨Complex.log L1, Complex.exp_log hL1⟩`. Take `⟨C2, hC2⟩` from `(isCompact_Icc : IsCompact (Icc t 2)).exists_bound_of_continuousOn (hcont.mono (Icc_subset_Ioc_iff ht2 |>.mpr ⟨ht1, le_rfl⟩))`. Use `⟨max (‖c‖ + B) C2, fun s hs => ?_⟩` and prove the remaining obligations. Break down `le_or_gt s t with hst | hst` into its components or cases. Establish `hs' : s ∈ Ioc 1 t` using `⟨hs.1, hst⟩`.

Establish `hgs : g s = c` using `hc hs'`. Establish `hL : abelian₂ s = c + Complex.log (Complex.exp (abelian₂ s) / L1)`. Rewrite using `[← hgs, hg]`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation.

Conclude with `(hC2 s ⟨hst.le, hs.2⟩).trans (le_max_right _ _)`.
-/
theorem bounded_of_tendsto_exp {abelian₂ : ℝ → ℂ} {L1 : ℂ} (hcont : ContinuousOn abelian₂ (Ioc 1 2))
    (hL1 : L1 ≠ 0) (hlim : Tendsto (fun s => Complex.exp (abelian₂ s)) (𝓝[>] 1) (𝓝 L1)) :
    ∃ C, ∀ s ∈ Ioc (1 : ℝ) 2, ‖abelian₂ s‖ ≤ C := by

  have hslitB : ∀ z ∈ Metric.closedBall (1 : ℂ) (1 / 2), z ∈ slitPlane := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have := Complex.abs_re_le_norm (z - 1)
    rw [Complex.sub_re, Complex.one_re] at this
    exact mem_slitPlane_iff.mpr (Or.inl (by linarith [(abs_le.mp (this.trans hz)).1]))
  obtain ⟨B, hB⟩ := (isCompact_closedBall (1 : ℂ) (1 / 2)).exists_bound_of_continuousOn
    (f := Complex.log) (fun z hz => (continuousAt_clog (hslitB z hz)).continuousWithinAt)

  have hlim' : Tendsto (fun s => Complex.exp (abelian₂ s) / L1) (𝓝[>] 1) (𝓝 1) := by
    simpa [div_self hL1] using hlim.div_const L1
  have hev := hlim'.eventually (Metric.closedBall_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨u, hu1, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hu1 : (1 : ℝ) < u := hu1
  set t : ℝ := min ((1 + u) / 2) 2 with ht
  have ht1 : 1 < t := lt_min (by linarith) (by norm_num)
  have htu : t < u := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht2 : t ≤ 2 := min_le_right _ _
  have hSsub : Ioc 1 t ⊆ Ioc (1 : ℝ) 2 := Ioc_subset_Ioc_right ht2
  have hball : ∀ s ∈ Ioc 1 t, Complex.exp (abelian₂ s) / L1 ∈ Metric.closedBall (1 : ℂ) (1 / 2) :=
    fun s hs => hu ⟨hs.1, lt_of_le_of_lt hs.2 htu⟩

  set g : ℝ → ℂ := fun s => abelian₂ s - Complex.log (Complex.exp (abelian₂ s) / L1) with hg
  have hgc : ContinuousOn g (Ioc 1 t) := by
    intro s hs
    have h1 : ContinuousWithinAt abelian₂ (Ioc 1 t) s := (hcont s (hSsub hs)).mono hSsub
    have h2 : ContinuousWithinAt (fun s => Complex.exp (abelian₂ s) / L1) (Ioc 1 t) s :=
      (Complex.continuous_exp.continuousAt.comp_continuousWithinAt h1).div_const L1
    have h3 : ContinuousWithinAt (fun s => Complex.log (Complex.exp (abelian₂ s) / L1)) (Ioc 1 t) s :=
      (continuousAt_clog (hslitB _ (hball s hs))).comp_continuousWithinAt
        (f := fun s => Complex.exp (abelian₂ s) / L1) h2
    exact h1.sub h3
  have hmaps : MapsTo g (Ioc 1 t) {w : ℂ | Complex.exp w = L1} := by
    intro s _
    have hne : Complex.exp (abelian₂ s) / L1 ≠ 0 := div_ne_zero (Complex.exp_ne_zero _) hL1
    simp only [mem_ofPred_eq, hg, Complex.exp_sub, Complex.exp_log hne]
    field_simp [Complex.exp_ne_zero]
  obtain ⟨c, -, hc⟩ := isPreconnected_Ioc.eqOn_const_of_mapsTo (isDiscrete_exp_fiber L1) hgc hmaps
    ⟨Complex.log L1, Complex.exp_log hL1⟩

  obtain ⟨C2, hC2⟩ := (isCompact_Icc : IsCompact (Icc t 2)).exists_bound_of_continuousOn
    (hcont.mono (Icc_subset_Ioc_iff ht2 |>.mpr ⟨ht1, le_rfl⟩))
  refine ⟨max (‖c‖ + B) C2, fun s hs => ?_⟩
  rcases le_or_gt s t with hst | hst
  · have hs' : s ∈ Ioc 1 t := ⟨hs.1, hst⟩
    have hgs : g s = c := hc hs'
    have hL : abelian₂ s = c + Complex.log (Complex.exp (abelian₂ s) / L1) := by
      rw [← hgs, hg]; ring
    calc ‖abelian₂ s‖ = ‖c + Complex.log (Complex.exp (abelian₂ s) / L1)‖ := by rw [← hL]
      _ ≤ ‖c‖ + ‖Complex.log (Complex.exp (abelian₂ s) / L1)‖ := norm_add_le _ _
      _ ≤ ‖c‖ + B := by gcongr; exact hB _ (hball s hs')
      _ ≤ _ := le_max_left _ _
  · exact (hC2 s ⟨hst.le, hs.2⟩).trans (le_max_right _ _)

/- English proof (translation)
Take `⟨C, hC⟩` from `bounded_of_tendsto_exp (hf.mono Set.Ioc_subset_Ioi_self) hL h`. Conclude with `⟨C, Filter.mem_of_superset (Ioc_mem_nhdsGT one_lt_two) hC⟩`.
-/
theorem bdd_of_exp_tendsto (f : ℝ → ℂ) (hf : ContinuousOn f (Set.Ioi 1)) (L1 : ℂ) (hL : L1 ≠ 0)
    (h : Tendsto (fun s => Complex.exp (f s)) (𝓝[>] 1) (𝓝 L1)) :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), ‖f s‖ ≤ C := by
  obtain ⟨C, hC⟩ := bounded_of_tendsto_exp (hf.mono Set.Ioc_subset_Ioi_self) hL h
  exact ⟨C, Filter.mem_of_superset (Ioc_mem_nhdsGT one_lt_two) hC⟩

end ReciprocityTheory.Cheb
