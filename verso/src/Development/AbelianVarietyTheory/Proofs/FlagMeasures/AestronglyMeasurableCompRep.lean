import Mathlib

open MeasureTheory Filter Set
open scoped ENNReal symmDiff Topology Pointwise

namespace GlobalTheory.RightRegFund

variable {G : Type} [Group G]

def Good (Γ : Subgroup G) (D : Set G) (y : G) : Prop :=
  ∀ γ γ' : Γ, (γ : G) * y ∈ D → (γ' : G) * y ∈ D → γ = γ'

/- English proof (translation)
Introduce `γ γ' h1 h2`. Use `h (γ * δ) (γ' * δ) (by simpa [mul_assoc] using h1) (by simpa [mul_assoc] using h2)` as an intermediate fact. Conclude with `mul_right_cancel this`.
-/
theorem Good.mul {Γ : Subgroup G} {D : Set G} {y : G} (h : Good Γ D y) (δ : Γ) :
    Good Γ D ((δ : G) * y) := by
  intro γ γ' h1 h2
  have := h (γ * δ) (γ' * δ) (by simpa [mul_assoc] using h1) (by simpa [mul_assoc] using h2)
  exact mul_right_cancel this

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => by simpa using h.mul δ⁻¹, fun h => h.mul δ⟩`.
-/
theorem good_mul_iff {Γ : Subgroup G} {D : Set G} {y : G} (δ : Γ) :
    Good Γ D ((δ : G) * y) ↔ Good Γ D y :=
  ⟨fun h => by simpa using h.mul δ⁻¹, fun h => h.mul δ⟩

variable {Γ : Subgroup G} {D : Set G} {r : G → G}

/- English proof (translation)
Take `⟨δ, h1, h2⟩` from `hr y`. Rewrite using `[h1, h δ γ (h1 ▸ h2) hγ]`.
-/
theorem rep_eq (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) {y : G} (h : Good Γ D y)
    {γ : Γ} (hγ : (γ : G) * y ∈ D) : r y = γ * y := by
  obtain ⟨δ, h1, h2⟩ := hr y
  rw [h1, h δ γ (h1 ▸ h2) hγ]

/- English proof (translation)
Take `⟨γ, h1, h2⟩` from `hr ((δ : G) * y)`. Establish `: r y = ((γ * δ : Γ) : G) * y` using `rep_eq hr h (by simpa [mul_assoc, ← h1] using h2)`. Rewrite using `[this, h1]`. Simplify using `[mul_assoc]`.
-/
theorem rep_mul (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) {y : G} (h : Good Γ D y)
    (δ : Γ) : r ((δ : G) * y) = r y := by
  obtain ⟨γ, h1, h2⟩ := hr ((δ : G) * y)
  have : r y = ((γ * δ : Γ) : G) * y :=
    rep_eq hr h (by simpa [mul_assoc, ← h1] using h2)
  rw [this, h1]; simp [mul_assoc]

variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsMulLeftInvariant] [Countable Γ]

/- English proof (translation)
Unfold `Good`. Use `ae_all_iff.2 fun γ => ae_all_iff.2 fun γ' => ?_` and prove the remaining obligations. Distinguish the cases in `h : γ = γ'`. Conclude with `Eventually.of_forall fun _ _ _ => h`. Establish `h' : γ⁻¹ ≠ γ'⁻¹` using `fun e => h (inv_injective e)`.

Use `hD.aedisjoint h'` as an intermediate fact. Use `(measure_eq_zero_iff_ae_notMem.1 this).mono fun y hy h1 h2 => absurd ?_ hy` and prove the remaining obligations. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `mem_inv_smul_set_iff.2 h1`. Conclude with `mem_inv_smul_set_iff.2 h2`.
-/
theorem ae_good (hD : IsFundamentalDomain Γ D μ) : ∀ᵐ y ∂μ, Good Γ D y := by
  unfold Good
  refine ae_all_iff.2 fun γ => ae_all_iff.2 fun γ' => ?_
  by_cases h : γ = γ'
  · exact Eventually.of_forall fun _ _ _ => h
  · have h' : γ⁻¹ ≠ γ'⁻¹ := fun e => h (inv_injective e)
    have := hD.aedisjoint h'
    refine (measure_eq_zero_iff_ae_notMem.1 this).mono fun y hy h1 h2 => absurd ?_ hy
    refine ⟨?_, ?_⟩
    · exact mem_inv_smul_set_iff.2 h1
    · exact mem_inv_smul_set_iff.2 h2

/- English proof (translation)
Rewrite `hp` using `[ae_restrict_iff' hDm]`. Establish `: ∀ᵐ y ∂μ, ∀ γ : Γ, (γ : G) * y ∈ D → p (γ * y)` using `ae_all_iff.2 fun γ => (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving.ae hp`. Use `this.mono fun y hy => ?_` and prove the remaining obligations. Take `⟨γ, h1, h2⟩` from `hr y`. Rewrite `h2`, the goal using `[h1]`.

Conclude with `hy γ h2`.
-/
theorem ae_rep (hDm : MeasurableSet D) (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    {p : G → Prop} (hp : ∀ᵐ x ∂(μ.restrict D), p x) : ∀ᵐ y ∂μ, p (r y) := by
  rw [ae_restrict_iff' hDm] at hp
  have : ∀ᵐ y ∂μ, ∀ γ : Γ, (γ : G) * y ∈ D → p (γ * y) :=
    ae_all_iff.2 fun γ => (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving.ae hp
  refine this.mono fun y hy => ?_
  obtain ⟨γ, h1, h2⟩ := hr y
  rw [h1] at h2 ⊢
  exact hy γ h2

/- English proof (translation)
Establish `hU : (⋃ γ : Γ, (fun y => (γ : G) * y) ⁻¹' D) = univ`. Use `eq_univ_of_forall fun y => ?_` and prove the remaining obligations. Take `⟨γ, h1, h2⟩` from `hr y`. Conclude with `mem_iUnion.2 ⟨γ, by simpa [← h1] using h2⟩`. Rewrite using `[← Measure.restrict_univ (μ := μ), ← hU, aestronglyMeasurable_iUnion_iff]`.

Introduce `γ`. Establish `hm : Measurable fun y => (γ : G) * y` using `measurable_const_mul _`. Use `((hf.comp_measurable hm).aestronglyMeasurable).congr ?_` and prove the remaining obligations. Use `(ae_restrict_iff' (hm hDm)).2 ((ae_good hD).mono fun y hy h => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp]`.

Rewrite using `[rep_eq hr hy h]`.
-/
theorem aestronglyMeasurable_comp_rep (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) {f : G → ℂ} (hf : StronglyMeasurable f) :
    AEStronglyMeasurable (fun y => f (r y)) μ := by
  have hU : (⋃ γ : Γ, (fun y => (γ : G) * y) ⁻¹' D) = univ := by
    refine eq_univ_of_forall fun y => ?_
    obtain ⟨γ, h1, h2⟩ := hr y
    exact mem_iUnion.2 ⟨γ, by simpa [← h1] using h2⟩
  rw [← Measure.restrict_univ (μ := μ), ← hU, aestronglyMeasurable_iUnion_iff]
  intro γ
  have hm : Measurable fun y => (γ : G) * y := measurable_const_mul _
  refine ((hf.comp_measurable hm).aestronglyMeasurable).congr ?_
  refine (ae_restrict_iff' (hm hDm)).2 ((ae_good hD).mono fun y hy h => ?_)
  simp only [Function.comp]
  rw [rep_eq hr hy h]

/- English proof (translation)
Use `(ae_restrict_iff' hDm).2 ((ae_good hD).mono fun y hy h => ?_)` and prove the remaining obligations. Simplify `h)` using `using rep_eq hr hy (γ := 1) (by simpa`.
-/
theorem ae_rep_eq_self (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) : ∀ᵐ x ∂(μ.restrict D), r x = x := by
  refine (ae_restrict_iff' hDm).2 ((ae_good hD).mono fun y hy h => ?_)
  simpa using rep_eq hr hy (γ := 1) (by simpa using h)

variable [μ.IsMulRightInvariant]

/- English proof (translation)
The claim follows from `(measurePreserving_mul_right μ g).quasiMeasurePreserving.ae (ae_good hD)`.
-/
theorem ae_good_mul (hD : IsFundamentalDomain Γ D μ) (g : G) : ∀ᵐ y ∂μ, Good Γ D (y * g) :=
  (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae (ae_good hD)

/- English proof (translation)
Set `ψ : G → ℝ≥0∞` to `fun y => if Good Γ D y then φ (r y) else 0`. Establish `hψ : ∀ (γ : Γ) (y : G), ψ (γ • y) = ψ y`. Introduce `γ y`. Express the relevant statement in the definitionally equal form `ψ ((γ : G) * y) = ψ y`. Distinguish the cases in `h : Good Γ D y`.

Simplify using `only [ψ, if_pos h, if_pos (h.mul γ), rep_mul hr h]`. Simplify using `only [ψ, if_neg h, if_neg (mt (good_mul_iff γ).1 h)]`. Establish `hD' : IsFundamentalDomain Γ ((fun x => x * g⁻¹) ⁻¹' D) μ` using `hD.preimage_of_equiv (measurePreserving_mul_right μ g⁻¹).quasiMeasurePreserving (e := id) Function.bijective_id fun γ x => by`. Express the relevant statement in the definitionally equal form `((γ : G) * x) * g⁻¹ = (γ : G) * (x * g⁻¹)`. Rewrite using `[mul_assoc]`.

Establish `h1` using `(measurePreserving_mul_right μ g⁻¹).setLIntegral_comp_preimage_emb (measurableEmbedding_mulRight g⁻¹) (fun x => ψ (x * g)) D`. Simplify using `only [inv_mul_cancel_right] at h1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [ψ, if_pos hy]))`. Use `_ = ∫⁻ x in D, ψ x ∂μ := by rw [← h1]; exact hD'.setLIntegral_eq hD ψ hψ`.

Use `_ = ∫⁻ x in D, φ x ∂μ := by`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_restrict_of_ae (ae_good hD), ae_rep_eq_self hD hDm hr] with y hy h2`. Simplify using `only [ψ, if_pos hy, h2]`.
-/
theorem lintegral_comp_rep_mul (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) (φ : G → ℝ≥0∞) (g : G) :
    ∫⁻ x in D, φ (r (x * g)) ∂μ = ∫⁻ x in D, φ x ∂μ := by
  classical
  let ψ : G → ℝ≥0∞ := fun y => if Good Γ D y then φ (r y) else 0
  have hψ : ∀ (γ : Γ) (y : G), ψ (γ • y) = ψ y := by
    intro γ y
    change ψ ((γ : G) * y) = ψ y
    by_cases h : Good Γ D y
    · simp only [ψ, if_pos h, if_pos (h.mul γ), rep_mul hr h]
    · simp only [ψ, if_neg h, if_neg (mt (good_mul_iff γ).1 h)]
  have hD' : IsFundamentalDomain Γ ((fun x => x * g⁻¹) ⁻¹' D) μ :=
    hD.preimage_of_equiv (measurePreserving_mul_right μ g⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id fun γ x => by
        change ((γ : G) * x) * g⁻¹ = (γ : G) * (x * g⁻¹)
        rw [mul_assoc]
  have h1 := (measurePreserving_mul_right μ g⁻¹).setLIntegral_comp_preimage_emb
    (measurableEmbedding_mulRight g⁻¹) (fun x => ψ (x * g)) D
  simp only [inv_mul_cancel_right] at h1
  calc ∫⁻ x in D, φ (r (x * g)) ∂μ = ∫⁻ x in D, ψ (x * g) ∂μ :=
        lintegral_congr_ae (ae_restrict_of_ae ((ae_good_mul hD g).mono fun y hy => by
          simp only [ψ, if_pos hy]))
    _ = ∫⁻ x in D, ψ x ∂μ := by rw [← h1]; exact hD'.setLIntegral_eq hD ψ hψ
    _ = ∫⁻ x in D, φ x ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_of_ae (ae_good hD), ae_rep_eq_self hD hDm hr] with y hy h2
        simp only [ψ, if_pos hy, h2]

variable {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))}

/- English proof (translation)
Use `ContinuousLinearMap.ext fun F => Lp.ext ?_` and prove the remaining obligations. Use `filter_upwards [hR 1 F, ae_rep_eq_self hD hDm hr] with x h1 h2`. Rewrite using `[h1, mul_one, h2]`. Both sides reduce to the same expression.
-/
theorem map_one (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hR : ∀ g F, (R g F : G → ℂ) =ᵐ[μ.restrict D] fun x => F (r (x * g))) : R 1 = 1 := by
  refine ContinuousLinearMap.ext fun F => Lp.ext ?_
  filter_upwards [hR 1 F, ae_rep_eq_self hD hDm hr] with x h1 h2
  rw [h1, mul_one, h2]; rfl

/- English proof (translation)
Use `ContinuousLinearMap.ext fun F => Lp.ext ?_` and prove the remaining obligations. Establish `h1 : ∀ᵐ y ∂μ, (R h F : G → ℂ) (r y) = F (r (y * h))` using `by filter_upwards [ae_rep hDm hr (hR h F), ae_good_mul hD h] with y e1 e2`. Take `⟨γ, e3, -⟩` from `hr y`. Rewrite using `[e1, e3, mul_assoc, rep_mul hr e2]`. Establish `h2` using `(measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h1`.

Use `filter_upwards [hR (g * h) F, hR g (R h F), ae_restrict_of_ae h2] with x e1 e2 e3`. Rewrite using `[e1, ContinuousLinearMap.mul_apply, e2, e3, mul_assoc]`.
-/
theorem map_mul (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hR : ∀ g F, (R g F : G → ℂ) =ᵐ[μ.restrict D] fun x => F (r (x * g))) (g h : G) :
    R (g * h) = R g * R h := by
  refine ContinuousLinearMap.ext fun F => Lp.ext ?_
  have h1 : ∀ᵐ y ∂μ, (R h F : G → ℂ) (r y) = F (r (y * h)) := by
    filter_upwards [ae_rep hDm hr (hR h F), ae_good_mul hD h] with y e1 e2
    obtain ⟨γ, e3, -⟩ := hr y
    rw [e1, e3, mul_assoc, rep_mul hr e2]
  have h2 := (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h1
  filter_upwards [hR (g * h) F, hR g (R h F), ae_restrict_of_ae h2] with x e1 e2 e3
  rw [e1, ContinuousLinearMap.mul_apply, e2, e3, mul_assoc]

/- English proof (translation)
Rewrite using `[Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (hR g F), eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, lintegral_comp_rep_mul hD hDm hr (fun x => ‖F x‖ₑ ^ (2 : ℝ≥0∞).toReal) g]`.
-/
theorem norm_map (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hR : ∀ g F, (R g F : G → ℂ) =ᵐ[μ.restrict D] fun x => F (r (x * g))) (g : G)
    (F : Lp ℂ 2 (μ.restrict D)) : ‖R g F‖ = ‖F‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (hR g F),
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    lintegral_comp_rep_mul hD hDm hr (fun x => ‖F x‖ₑ ^ (2 : ℝ≥0∞).toReal) g]

/- English proof (translation)
Use `set F := indicatorConstLp 2 hs hμs c with hF`. Use `set S := ((fun x => x * g) ⁻¹' (s ∩ D)) ∆ ((fun x => x * g₀) ⁻¹' (s ∩ D)) with hS`. Establish `h1 : ∀ᵐ y ∂μ, (F : G → ℂ) (r y) = s.indicator (fun _ => c) (r y)` using `ae_rep hDm hr (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := c))`. Establish `key : ∀ a b x : G, Good Γ D (x * b) → r (x * a) ∈ s → r (x * b) ∉ s → ∃ γ : Γ, (γ : G) * x * a ∈ s ∩ D ∧ (γ : G) * x * b ∉ s ∩ D`. Introduce `a b x hb h2 h3`.

Take `⟨γ, e1, e2⟩` from `hr (x * a)`. Use `⟨γ, by rw [mul_assoc, ← e1]; exact ⟨h2, e2⟩, fun h => h3 ?_⟩` and prove the remaining obligations. Rewrite `h` using `[mul_assoc]`. Rewrite using `[rep_eq hr hb h.2]`. Conclude with `h.1`.

Establish `hU : μ.restrict D (⋃ γ : Γ, γ • S) ≤ μ S`. Rewrite using `[hD.measure_eq_tsum S]`. Use `(measure_iUnion_le _).trans (le_of_eq (tsum_congr fun γ => ?_))` and prove the remaining obligations. Rewrite using `[Measure.restrict_apply' hDm]`. Rewrite using `[Lp.edist_def]`.

Combine the equalities or inequalities in the displayed calculation. Use `eLpNorm_mono_enorm_ae ?_` and prove the remaining obligations. Use `filter_upwards [hR g F, hR g₀ F, ae_restrict_of_ae ((measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h1), ae_restrict_of_ae ((measurePreserving_mul_right μ g₀).quasiMeasurePreserving.ae h1), ae_restrict_of_ae (ae_good_mul hD g), ae_restrict_of_ae (ae_good_mul hD g₀)] w …`. Rewrite using `[Pi.sub_apply, e1, e2, e3, e4]`. Apply the tactic sequence `by_cases a : r (x * g) ∈ s <;> by_cases b : r (x * g₀) ∈ s`.

Simplify using `[a, b]`. Take `⟨γ, k1, k2⟩` from `key g g₀ x e6 a b`. Establish `: x ∈ ⋃ γ : Γ, γ • S` using `mem_iUnion.2 ⟨γ⁻¹, mem_inv_smul_set_iff.2 (Or.inl ⟨k1, k2⟩)⟩`. Rewrite using `[indicator_of_mem this]`. Simplify using `[a, b]`.

Take `⟨γ, k1, k2⟩` from `key g₀ g x e5 b a`. Establish `: x ∈ ⋃ γ : Γ, γ • S` using `mem_iUnion.2 ⟨γ⁻¹, mem_inv_smul_set_iff.2 (Or.inr ⟨k1, k2⟩)⟩`. Rewrite using `[indicator_of_mem this]`. Simplify using `[a, b]`. Simplify using `[a, b]`.

Use `_ ≤ _ := eLpNorm_indicator_const_le c 2`. Use `_ ≤ _ := by gcongr`.
-/
theorem edist_indicator_le (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hR : ∀ g F, (R g F : G → ℂ) =ᵐ[μ.restrict D] fun x => F (r (x * g)))
    (c : ℂ) {s : Set G} (hs : MeasurableSet s) (hμs : μ.restrict D s ≠ ∞) (g g₀ : G) :
    edist (R g (indicatorConstLp 2 hs hμs c)) (R g₀ (indicatorConstLp 2 hs hμs c)) ≤
      ‖c‖ₑ * μ (((fun x => x * g) ⁻¹' (s ∩ D)) ∆ ((fun x => x * g₀) ⁻¹' (s ∩ D))) ^
        (1 / (2 : ℝ≥0∞).toReal) := by
  set F := indicatorConstLp 2 hs hμs c with hF
  set S := ((fun x => x * g) ⁻¹' (s ∩ D)) ∆ ((fun x => x * g₀) ⁻¹' (s ∩ D)) with hS
  have h1 : ∀ᵐ y ∂μ, (F : G → ℂ) (r y) = s.indicator (fun _ => c) (r y) :=
    ae_rep hDm hr (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := c))
  have key : ∀ a b x : G, Good Γ D (x * b) → r (x * a) ∈ s → r (x * b) ∉ s →
      ∃ γ : Γ, (γ : G) * x * a ∈ s ∩ D ∧ (γ : G) * x * b ∉ s ∩ D := by
    intro a b x hb h2 h3
    obtain ⟨γ, e1, e2⟩ := hr (x * a)
    refine ⟨γ, by rw [mul_assoc, ← e1]; exact ⟨h2, e2⟩, fun h => h3 ?_⟩
    rw [mul_assoc] at h
    rw [rep_eq hr hb h.2]; exact h.1
  have hU : μ.restrict D (⋃ γ : Γ, γ • S) ≤ μ S := by
    rw [hD.measure_eq_tsum S]
    refine (measure_iUnion_le _).trans (le_of_eq (tsum_congr fun γ => ?_))
    rw [Measure.restrict_apply' hDm]
  rw [Lp.edist_def]
  calc eLpNorm (⇑(R g F) - ⇑(R g₀ F)) 2 (μ.restrict D)
      ≤ eLpNorm ((⋃ γ : Γ, γ • S).indicator fun _ => c) 2 (μ.restrict D) := by
        refine eLpNorm_mono_enorm_ae ?_
        filter_upwards [hR g F, hR g₀ F,
          ae_restrict_of_ae ((measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h1),
          ae_restrict_of_ae ((measurePreserving_mul_right μ g₀).quasiMeasurePreserving.ae h1),
          ae_restrict_of_ae (ae_good_mul hD g), ae_restrict_of_ae (ae_good_mul hD g₀)]
          with x e1 e2 e3 e4 e5 e6
        rw [Pi.sub_apply, e1, e2, e3, e4]
        by_cases a : r (x * g) ∈ s <;> by_cases b : r (x * g₀) ∈ s
        · simp [a, b]
        · obtain ⟨γ, k1, k2⟩ := key g g₀ x e6 a b
          have : x ∈ ⋃ γ : Γ, γ • S :=
            mem_iUnion.2 ⟨γ⁻¹, mem_inv_smul_set_iff.2 (Or.inl ⟨k1, k2⟩)⟩
          rw [indicator_of_mem this]; simp [a, b]
        · obtain ⟨γ, k1, k2⟩ := key g₀ g x e5 b a
          have : x ∈ ⋃ γ : Γ, γ • S :=
            mem_iUnion.2 ⟨γ⁻¹, mem_inv_smul_set_iff.2 (Or.inr ⟨k1, k2⟩)⟩
          rw [indicator_of_mem this]; simp [a, b]
        · simp [a, b]
    _ ≤ _ := eLpNorm_indicator_const_le c 2
    _ ≤ _ := by gcongr

/- English proof (translation)
Use `Lp.induction (p := 2) ENNReal.ofNat_ne_top (fun F => Continuous fun g => R g F) ?_ ?_ ?_ F` and prove the remaining obligations. Introduce `c s hs hμs`. Rewrite using `[Lp.simpleFunc.coe_indicatorConst]`. Use `continuous_iff_continuousAt.2 fun g₀ => tendsto_iff_edist_tendsto_0.2 ?_` and prove the remaining obligations. Set `m : C(G, C(G, G))` to `ContinuousMap.curry ⟨fun p : G × G => p.2 * p.1, by fun_prop⟩`.

Establish `ht : Tendsto (fun g => μ (((fun x => x * g) ⁻¹' (s ∩ D)) ∆ ((fun x => x * g₀) ⁻¹' (s ∩ D)))) (𝓝 g₀) (𝓝 0)` using `tendsto_measure_symmDiff_preimage_nhds_zero (μ := μ) (ν := μ) (f := m) (g := m g₀) (m.continuous.tendsto g₀) (Eventually.of_forall fun g => measurePreserving_mul_right μ g) (measurePreserving_mul_right μ g₀) (hs.inter hDm).nullMeasurableSet (by rw [← Measure.restrict_apply hs]; e …`. Establish `ht2` using `((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ≥0∞).toReal)).tendsto 0).comp ht`. Rewrite `ht2` using `[ENNReal.zero_rpow_of_pos (by norm_num)]`. Establish `ht3` using `ENNReal.Tendsto.const_mul (a := ‖c‖ₑ) ht2 (Or.inr enorm_ne_top)`. Rewrite `ht3` using `[mul_zero]`.

Conclude with `tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht3 (fun _ => zero_le) fun g => edist_indicator_le hD hDm hr hR c hs hμs.ne g g₀`. Introduce `f g hf hg _ h1 h2`. Simplify using `only [map_add]`. Conclude with `h1.add h2`. Use `isClosed_of_closure_subset fun F hF => ?_` and prove the remaining obligations.

Use `TendstoUniformly.continuous (F := fun F' g => R g F') (p := 𝓝 F) ?_ (mem_closure_iff_frequently.1 hF)` and prove the remaining obligations. Use `Metric.tendstoUniformly_iff.2 fun ε hε => ?_` and prove the remaining obligations. Use `filter_upwards [Metric.ball_mem_nhds F hε] with F' h g`. Rewrite using `[dist_eq_norm, ← map_sub, norm_map hD hDm hr hR, ← dist_eq_norm, dist_comm]`. Conclude with `h`.
-/
theorem continuous_map [LocallyCompactSpace G] [SecondCountableTopology G]
    [IsFiniteMeasureOnCompacts μ]
    (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hR : ∀ g F, (R g F : G → ℂ) =ᵐ[μ.restrict D] fun x => F (r (x * g)))
    (F : Lp ℂ 2 (μ.restrict D)) : Continuous fun g => R g F := by
  refine Lp.induction (p := 2) ENNReal.ofNat_ne_top (fun F => Continuous fun g => R g F)
    ?_ ?_ ?_ F
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    refine continuous_iff_continuousAt.2 fun g₀ => tendsto_iff_edist_tendsto_0.2 ?_
    let m : C(G, C(G, G)) := ContinuousMap.curry ⟨fun p : G × G => p.2 * p.1, by fun_prop⟩
    have ht : Tendsto (fun g => μ (((fun x => x * g) ⁻¹' (s ∩ D)) ∆
        ((fun x => x * g₀) ⁻¹' (s ∩ D)))) (𝓝 g₀) (𝓝 0) :=
      tendsto_measure_symmDiff_preimage_nhds_zero (μ := μ) (ν := μ) (f := m) (g := m g₀)
        (m.continuous.tendsto g₀) (Eventually.of_forall fun g => measurePreserving_mul_right μ g)
        (measurePreserving_mul_right μ g₀) (hs.inter hDm).nullMeasurableSet
        (by rw [← Measure.restrict_apply hs]; exact hμs.ne)
    have ht2 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ≥0∞).toReal)).tendsto 0).comp ht
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at ht2
    have ht3 := ENNReal.Tendsto.const_mul (a := ‖c‖ₑ) ht2 (Or.inr enorm_ne_top)
    rw [mul_zero] at ht3
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht3 (fun _ => zero_le)
      fun g => edist_indicator_le hD hDm hr hR c hs hμs.ne g g₀
  · intro f g hf hg _ h1 h2
    simp only [map_add]
    exact h1.add h2
  · refine isClosed_of_closure_subset fun F hF => ?_
    refine TendstoUniformly.continuous (F := fun F' g => R g F') (p := 𝓝 F) ?_
      (mem_closure_iff_frequently.1 hF)
    refine Metric.tendstoUniformly_iff.2 fun ε hε => ?_
    filter_upwards [Metric.ball_mem_nhds F hε] with F' h g
    rw [dist_eq_norm, ← map_sub, norm_map hD hDm hr hR, ← dist_eq_norm, dist_comm]
    exact h

end GlobalTheory.RightRegFund
