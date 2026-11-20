import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrkAesmTsum

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

/- English proof (translation)
Break down `le_total a b with h | h` into its components or cases. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rrkb_mul_le (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

/- English proof (translation)
Break down `le_total a 1 with h | h` into its components or cases. Conclude with `le_trans h le_self_add`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rrkb_le_one_add_sq (a : ℝ≥0∞) : a ≤ 1 + a ^ 2 := by
  rcases le_total a 1 with h | h
  · exact le_trans h le_self_add
  · calc a = a * 1 := (mul_one a).symm
      _ ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ 1 + a ^ 2 := le_add_self

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup G} [Countable Γ] {D : Set G}

omit [Group G] [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μ] in
/- English proof (translation)
Establish `h` using `lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) two_ne_zero ENNReal.ofNat_ne_top (Lp.eLpNorm_lt_top f)`. Simplify using `only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h`. Conclude with `h.ne`.
-/
theorem rrkb_sq_fin (f : Lp ℂ 2 (μ.restrict D)) : ∫⁻ y in D, ‖(f : G → ℂ) y‖ₑ ^ 2 ∂μ ≠ ∞ := by
  have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) two_ne_zero ENNReal.ofNat_ne_top
    (Lp.eLpNorm_lt_top f)
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
  exact h.ne

/- English proof (translation)
Take `⟨h1, h2⟩` from `rr_map h g`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_restrict_of_ae (s := D) (rr_rep_ae_eq h hr g)] with x hx`. Rewrite using `[hx]`.

Use `_ = ∫⁻ y, F y ∂(Measure.map (fun x => rr_rep (Γ : Set G) D (x * g)) (μ.restrict D)) := (lintegral_map' hF.aemeasurable h1).symm`. Use `_ = ∫⁻ x in D, F x ∂μ := by rw [h2]`.
-/
theorem rrkb_lint (h : rr_FD μ Γ D) {r : G → G} (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D) (g : G)
    {F : G → ℝ≥0∞} (hF : Measurable F) : ∫⁻ x in D, F (r (x * g)) ∂μ = ∫⁻ x in D, F x ∂μ := by
  obtain ⟨h1, h2⟩ := rr_map h g
  calc ∫⁻ x in D, F (r (x * g)) ∂μ = ∫⁻ x in D, F (rr_rep (Γ : Set G) D (x * g)) ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_of_ae (s := D) (rr_rep_ae_eq h hr g)] with x hx
        rw [hx]
    _ = ∫⁻ y, F y ∂(Measure.map (fun x => rr_rep (Γ : Set G) D (x * g)) (μ.restrict D)) :=
        (lintegral_map' hF.aemeasurable h1).symm
    _ = ∫⁻ x in D, F x ∂μ := by rw [h2]

/- English proof (translation)
Establish `hnull : ∀ δ : Γ, (δ : G) ≠ 1 → μ ((fun y => (δ : G) * y) ⁻¹' ((fun y => (δ : G) * y) '' D ∩ D)) = 0`. Introduce `δ hδ`. Rewrite using `[measure_preimage_mul]`. Conclude with `h.3 δ δ.2 hδ`. Establish `hB : μ (⋃ δ : Γ, ⋃ (_ : (δ : G) ≠ 1), (fun y => (δ : G) * y) ⁻¹' ((fun y => (δ : G) * y) '' D ∩ D)) = 0` using `measure_iUnion_null (fun δ => measure_iUnion_null (fun hδ => hnull δ hδ))`.

Rewrite using `[ae_restrict_iff' h.1, ae_iff]`. Use `measure_mono_null ?_ hB` and prove the remaining obligations. Introduce `y hy`. Simplify using `only [Set.mem_setOf_eq] at hy`. Use `push_neg at hy`.

Take `⟨hyD, γ, hγ⟩` from `hy`. Take `⟨γ', hγ'Γ, hr1, hmem⟩` from `hr ((γ : G) * y)`. Establish `hδ : ((⟨γ' * γ, Γ.mul_mem hγ'Γ γ.2⟩ : Γ) : G) ≠ 1`. Introduce `h1`. Apply `hγ` to reduce the goal to its premises.

Rewrite using `[hr1, ← mul_assoc]`. Conclude with `(congrArg (· * y) h1).trans (one_mul y)`. Simplify using `only [Set.mem_iUnion]`. Use `⟨⟨γ' * γ, Γ.mul_mem hγ'Γ γ.2⟩, hδ, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_image]`.

Use `⟨⟨y, hyD, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show γ' * γ * y ∈ D`. Rewrite using `[mul_assoc]`. Conclude with `hmem`.
-/
theorem rrkb_r_fix (h : rr_FD μ Γ D) {r : G → G} (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D) :
    ∀ᵐ y ∂μ.restrict D, ∀ γ : Γ, r ((γ : G) * y) = y := by
  classical
  have hnull : ∀ δ : Γ, (δ : G) ≠ 1 →
      μ ((fun y => (δ : G) * y) ⁻¹' ((fun y => (δ : G) * y) '' D ∩ D)) = 0 := by
    intro δ hδ
    rw [measure_preimage_mul]
    exact h.3 δ δ.2 hδ
  have hB : μ (⋃ δ : Γ, ⋃ (_ : (δ : G) ≠ 1),
      (fun y => (δ : G) * y) ⁻¹' ((fun y => (δ : G) * y) '' D ∩ D)) = 0 :=
    measure_iUnion_null (fun δ => measure_iUnion_null (fun hδ => hnull δ hδ))
  rw [ae_restrict_iff' h.1, ae_iff]
  refine measure_mono_null ?_ hB
  intro y hy
  simp only [Set.mem_setOf_eq] at hy
  push_neg at hy
  obtain ⟨hyD, γ, hγ⟩ := hy
  obtain ⟨γ', hγ'Γ, hr1, hmem⟩ := hr ((γ : G) * y)
  have hδ : ((⟨γ' * γ, Γ.mul_mem hγ'Γ γ.2⟩ : Γ) : G) ≠ 1 := by
    intro h1
    apply hγ
    rw [hr1, ← mul_assoc]
    exact (congrArg (· * y) h1).trans (one_mul y)
  simp only [Set.mem_iUnion]
  refine ⟨⟨γ' * γ, Γ.mul_mem hγ'Γ γ.2⟩, hδ, ?_⟩
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_image]
  refine ⟨⟨y, hyD, rfl⟩, ?_⟩
  show γ' * γ * y ∈ D
  rw [mul_assoc]
  exact hmem

/- English proof (translation)
Use `set f0 : G → ℂ := (f : G → ℂ) with hf0`. Establish `hf0m : StronglyMeasurable f0` using `Lp.stronglyMeasurable f`. Use `set ψ : G → ℂ := fun y => φ (x⁻¹ * y) * f0 (r y) with hψ`. Establish `hψm : StronglyMeasurable ψ` using `((hφm.comp (measurable_const_mul _)).stronglyMeasurable).mul (hf0m.comp_measurable hrm)`. Establish `e1 : ∫ g, φ g * f0 (r (x * g)) ∂μ = ∫ y, ψ y ∂μ`.

Rewrite using `[← integral_mul_left_eq_self ψ x]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Simplify using `[hψ]`. Establish `hfd` using `rr_isFD h`. Establish `hfix` using `rrkb_r_fix h hr`.

Establish `hγm : ∀ γ : Γ, StronglyMeasurable fun y => ψ (γ • y)` using `fun γ => hψm.comp_measurable (measurable_const_smul γ)`. Establish `hsum : ∑' γ : Γ, ∫⁻ y in D, ‖ψ (γ • y)‖ₑ ∂μ ≠ ∞`. Rewrite using `[← lintegral_tsum (fun γ => (hγm γ).enorm.aemeasurable)]`. Establish `e2 : ∫⁻ y in D, ∑' γ : Γ, ‖ψ (γ • y)‖ₑ ∂μ = ∫⁻ y in D, rrk_Kab Γ φ x y * ‖f0 y‖ₑ ∂μ`. Use `lintegral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [hfix] with y hy`. Rewrite using `[rrk_Kab, ← ENNReal.tsum_mul_right]`. Use `tsum_congr fun γ => ?_` and prove the remaining obligations. Simplify using `only [hψ, Subgroup.smul_def, smul_eq_mul, enorm_mul, hy γ, mul_assoc]`. Rewrite using `[e2]`.

Use `ne_top_of_le_ne_top ?_ (lintegral_mono fun y => rrkb_mul_le _ _)` and prove the remaining obligations. Rewrite using `[lintegral_add_right _ (hf0m.enorm.pow_const 2)]`. Conclude with `ENNReal.add_ne_top.2 ⟨hx, rrkb_sq_fin f⟩`. Establish `hψi : Integrable ψ μ` using `⟨hψm.aestronglyMeasurable, by`. Rewrite using `[hasFiniteIntegral_iff_enorm, hfd.lintegral_eq_tsum'']`.

Conclude with `lt_top_iff_ne_top.2 hsum⟩`. Rewrite using `[e1, hfd.integral_eq_tsum'' ψ hψi, ← integral_tsum (fun γ => (hγm γ).aestronglyMeasurable) hsum]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hfix] with y hy`. Rewrite using `[rrk_K, ← tsum_mul_right]`.

Use `tsum_congr fun γ => ?_` and prove the remaining obligations. Simplify using `only [hψ, Subgroup.smul_def, smul_eq_mul, hy γ, mul_assoc]`.
-/
theorem rrkb_step2 (h : rr_FD μ Γ D) {φ : G → ℂ} (hφm : Measurable φ) {r : G → G} (hrm : Measurable r)
    (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D) (f : Lp ℂ 2 (μ.restrict D)) (x : G)
    (hx : ∫⁻ y in D, (rrk_Kab Γ φ x y) ^ 2 ∂μ ≠ ∞) :
    ∫ g, φ g * (f : G → ℂ) (r (x * g)) ∂μ = ∫ y in D, rrk_K Γ φ x y * (f : G → ℂ) y ∂μ := by
  set f0 : G → ℂ := (f : G → ℂ) with hf0
  have hf0m : StronglyMeasurable f0 := Lp.stronglyMeasurable f
  set ψ : G → ℂ := fun y => φ (x⁻¹ * y) * f0 (r y) with hψ
  have hψm : StronglyMeasurable ψ :=
    ((hφm.comp (measurable_const_mul _)).stronglyMeasurable).mul (hf0m.comp_measurable hrm)
  have e1 : ∫ g, φ g * f0 (r (x * g)) ∂μ = ∫ y, ψ y ∂μ := by
    rw [← integral_mul_left_eq_self ψ x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp [hψ]
  have hfd := rr_isFD h
  have hfix := rrkb_r_fix h hr
  have hγm : ∀ γ : Γ, StronglyMeasurable fun y => ψ (γ • y) := fun γ =>
    hψm.comp_measurable (measurable_const_smul γ)
  have hsum : ∑' γ : Γ, ∫⁻ y in D, ‖ψ (γ • y)‖ₑ ∂μ ≠ ∞ := by
    rw [← lintegral_tsum (fun γ => (hγm γ).enorm.aemeasurable)]
    have e2 : ∫⁻ y in D, ∑' γ : Γ, ‖ψ (γ • y)‖ₑ ∂μ = ∫⁻ y in D, rrk_Kab Γ φ x y * ‖f0 y‖ₑ ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hfix] with y hy
      rw [rrk_Kab, ← ENNReal.tsum_mul_right]
      refine tsum_congr fun γ => ?_
      simp only [hψ, Subgroup.smul_def, smul_eq_mul, enorm_mul, hy γ, mul_assoc]
    rw [e2]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun y => rrkb_mul_le _ _)
    rw [lintegral_add_right _ (hf0m.enorm.pow_const 2)]
    exact ENNReal.add_ne_top.2 ⟨hx, rrkb_sq_fin f⟩
  have hψi : Integrable ψ μ := ⟨hψm.aestronglyMeasurable, by
    rw [hasFiniteIntegral_iff_enorm, hfd.lintegral_eq_tsum'']
    exact lt_top_iff_ne_top.2 hsum⟩
  rw [e1, hfd.integral_eq_tsum'' ψ hψi, ← integral_tsum (fun γ => (hγm γ).aestronglyMeasurable) hsum]
  refine integral_congr_ae ?_
  filter_upwards [hfix] with y hy
  rw [rrk_K, ← tsum_mul_right]
  refine tsum_congr fun γ => ?_
  simp only [hψ, Subgroup.smul_def, smul_eq_mul, hy γ, mul_assoc]

/- English proof (translation)
Use `set f0 : G → ℂ := (f : G → ℂ) with hf0`. Establish `hf0m : StronglyMeasurable f0` using `Lp.stronglyMeasurable f`. Use `set Φ : G × G → ℂ := fun p => φ p.1 * f0 (r (p.2 * p.1)) with hΦ`. Establish `hΦm : StronglyMeasurable Φ` using `((hφm.comp measurable_fst).stronglyMeasurable).mul (hf0m.comp_measurable (hrm.comp (measurable_snd.mul measurable_fst)))`. Establish `hInt : ∀ s, MeasurableSet s → (μ.restrict D) s < ∞ → Integrable Φ (μ.prod ((μ.restrict D).restrict s))`.

Introduce `s hs hfin`. Use `⟨hΦm.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Rewrite using `[hasFiniteIntegral_iff_enorm, lintegral_prod _ hΦm.enorm.aemeasurable]`. Use `set C : ℝ≥0∞ := (μ.restrict D) s + ∫⁻ y in D, ‖f0 y‖ₑ ^ 2 ∂μ with hC`. Establish `hCfin : C ≠ ∞` using `ENNReal.add_ne_top.2 ⟨hfin.ne, rrkb_sq_fin f⟩`.

Establish `hb : ∀ g, ∫⁻ x, ‖Φ (g, x)‖ₑ ∂((μ.restrict D).restrict s) ≤ ‖φ g‖ₑ * C`. Introduce `g`. Establish `hm1 : Measurable fun x => ‖f0 (r (x * g))‖ₑ` using `(hf0m.comp_measurable (hrm.comp (measurable_mul_const g))).enorm`. Simplify using `only [hΦ, enorm_mul]`. Rewrite using `[lintegral_const_mul _ hm1]`.

Use `mul_le_mul' le_rfl ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_add_left measurable_const, lintegral_one, Measure.restrict_apply_univ]`. Use `_ ≤ (μ.restrict D) s + ∫⁻ x in D, ‖f0 (r (x * g))‖ₑ ^ 2 ∂μ := add_le_add le_rfl (lintegral_mono' Measure.restrict_le_self le_rfl)`. Use `_ = C := by rw [rrkb_lint h hr g (F := fun y => ‖f0 y‖ₑ ^ 2) (hf0m.enorm.pow_const 2)]`.

Combine the equalities or inequalities in the displayed calculation. Use `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_ ?_` and prove the remaining obligations. Introduce `s hs hfin`. Conclude with `integrableOn_Lp_of_measure_ne_top _ (by norm_num) hfin.ne`. Introduce `s hs hfin`.

Conclude with `(hInt s hs hfin).integral_prod_right`. Introduce `s hs hfin`. Rewrite using `[← L2.inner_indicatorConstLp_one (𝕜 := ℂ) hs hfin.ne (T f), hT]`. Establish `e : ∀ g, ⟪indicatorConstLp 2 hs hfin.ne (1 : ℂ), R g f⟫_ℂ = ∫ x in s, f0 (r (x * g)) ∂(μ.restrict D)`. Introduce `g`.

Rewrite using `[L2.inner_indicatorConstLp_one]`. Use `integral_congr_ae (ae_restrict_of_ae ?_)` and prove the remaining obligations. Use `filter_upwards [hR g f, ae_restrict_of_ae (s := D) (rr_rep_ae_eq h hr g)] with x a1 a2`. Rewrite using `[a1, a2]`. Simplify using `only [e]`.

Establish `hsw` using `integral_integral_swap (f := fun g x => φ g * f0 (r (x * g))) (μ := μ) (ν := (μ.restrict D).restrict s) (hInt s hs hfin)`. Rewrite using `[← hsw]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Conclude with `(integral_const_mul _ _).symm`.
-/
theorem rrkb_step1 (h : rr_FD μ Γ D) {φ : G → ℂ} (hφm : Measurable φ) {r : G → G} (hrm : Measurable r)
    (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D)
    {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))} (hR : rr_IsReg μ Γ D R)
    (T : Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D)) (hφ : Integrable φ μ)
    (hT : ∀ u v : Lp ℂ 2 (μ.restrict D), ⟪u, T v⟫_ℂ = ∫ g, φ g * ⟪u, R g v⟫_ℂ ∂μ) (f : Lp ℂ 2 (μ.restrict D)) :
    ((T f : Lp ℂ 2 (μ.restrict D)) : G → ℂ) =ᵐ[μ.restrict D] fun x => ∫ g, φ g * (f : G → ℂ) (r (x * g)) ∂μ := by
  set f0 : G → ℂ := (f : G → ℂ) with hf0
  have hf0m : StronglyMeasurable f0 := Lp.stronglyMeasurable f
  set Φ : G × G → ℂ := fun p => φ p.1 * f0 (r (p.2 * p.1)) with hΦ
  have hΦm : StronglyMeasurable Φ :=
    ((hφm.comp measurable_fst).stronglyMeasurable).mul
      (hf0m.comp_measurable (hrm.comp (measurable_snd.mul measurable_fst)))
  have hInt : ∀ s, MeasurableSet s → (μ.restrict D) s < ∞ →
      Integrable Φ (μ.prod ((μ.restrict D).restrict s)) := by
    intro s hs hfin
    refine ⟨hΦm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hΦm.enorm.aemeasurable]
    set C : ℝ≥0∞ := (μ.restrict D) s + ∫⁻ y in D, ‖f0 y‖ₑ ^ 2 ∂μ with hC
    have hCfin : C ≠ ∞ := ENNReal.add_ne_top.2 ⟨hfin.ne, rrkb_sq_fin f⟩
    have hb : ∀ g, ∫⁻ x, ‖Φ (g, x)‖ₑ ∂((μ.restrict D).restrict s) ≤ ‖φ g‖ₑ * C := by
      intro g
      have hm1 : Measurable fun x => ‖f0 (r (x * g))‖ₑ :=
        (hf0m.comp_measurable (hrm.comp (measurable_mul_const g))).enorm
      simp only [hΦ, enorm_mul]
      rw [lintegral_const_mul _ hm1]
      refine mul_le_mul' le_rfl ?_
      calc ∫⁻ x, ‖f0 (r (x * g))‖ₑ ∂((μ.restrict D).restrict s)
          ≤ ∫⁻ x, (1 + ‖f0 (r (x * g))‖ₑ ^ 2) ∂((μ.restrict D).restrict s) :=
            lintegral_mono fun x => rrkb_le_one_add_sq _
        _ = (μ.restrict D) s + ∫⁻ x, ‖f0 (r (x * g))‖ₑ ^ 2 ∂((μ.restrict D).restrict s) := by
            rw [lintegral_add_left measurable_const, lintegral_one, Measure.restrict_apply_univ]
        _ ≤ (μ.restrict D) s + ∫⁻ x in D, ‖f0 (r (x * g))‖ₑ ^ 2 ∂μ :=
            add_le_add le_rfl (lintegral_mono' Measure.restrict_le_self le_rfl)
        _ = C := by rw [rrkb_lint h hr g (F := fun y => ‖f0 y‖ₑ ^ 2) (hf0m.enorm.pow_const 2)]
    calc ∫⁻ g, ∫⁻ x, ‖Φ (g, x)‖ₑ ∂((μ.restrict D).restrict s) ∂μ ≤ ∫⁻ g, ‖φ g‖ₑ * C ∂μ := lintegral_mono hb
      _ = (∫⁻ g, ‖φ g‖ₑ ∂μ) * C := lintegral_mul_const _ hφm.enorm
      _ < ∞ := ENNReal.mul_lt_top hφ.2 (lt_top_iff_ne_top.2 hCfin)
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_ ?_
  · intro s hs hfin
    exact integrableOn_Lp_of_measure_ne_top _ (by norm_num) hfin.ne
  · intro s hs hfin
    exact (hInt s hs hfin).integral_prod_right
  · intro s hs hfin
    rw [← L2.inner_indicatorConstLp_one (𝕜 := ℂ) hs hfin.ne (T f), hT]
    have e : ∀ g, ⟪indicatorConstLp 2 hs hfin.ne (1 : ℂ), R g f⟫_ℂ =
        ∫ x in s, f0 (r (x * g)) ∂(μ.restrict D) := by
      intro g
      rw [L2.inner_indicatorConstLp_one]
      refine integral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [hR g f, ae_restrict_of_ae (s := D) (rr_rep_ae_eq h hr g)] with x a1 a2
      rw [a1, a2]
    simp only [e]
    have hsw := integral_integral_swap (f := fun g x => φ g * f0 (r (x * g))) (μ := μ)
      (ν := (μ.restrict D).restrict s) (hInt s hs hfin)
    rw [← hsw]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact (integral_const_mul _ _).symm

/- English proof (translation)
Take `⟨r, hrm, hr⟩` from `rr_exists_meas_rep h`. Use `filter_upwards [rrkb_step1 h hφm hrm hr hR T hφ hT f, hK] with x a1 a2`. Rewrite using `[a1]`. Conclude with `rrkb_step2 h hφm hrm hr f x a2`.
-/
theorem rrk_unfold (h : rr_FD μ Γ D) {φ : G → ℂ} (hφm : Measurable φ)
    {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))} (hR : rr_IsReg μ Γ D R)
    (T : Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D)) (hφ : Integrable φ μ)
    (hT : ∀ u v : Lp ℂ 2 (μ.restrict D), ⟪u, T v⟫_ℂ = ∫ g, φ g * ⟪u, R g v⟫_ℂ ∂μ)
    (hK : ∀ᵐ x ∂μ.restrict D, ∫⁻ y in D, (rrk_Kab Γ φ x y) ^ 2 ∂μ ≠ ∞) (f : Lp ℂ 2 (μ.restrict D)) :
    ∀ᵐ x ∂μ.restrict D, ((T f : Lp ℂ 2 (μ.restrict D)) : G → ℂ) x =
      ∫ y in D, rrk_K Γ φ x y * (f : G → ℂ) y ∂μ := by
  obtain ⟨r, hrm, hr⟩ := rr_exists_meas_rep h
  filter_upwards [rrkb_step1 h hφm hrm hr hR T hφ hT f, hK] with x a1 a2
  rw [a1]
  exact rrkb_step2 h hφm hrm hr f x a2

end Formalism.MainNotions.LeviCoordinates

end
