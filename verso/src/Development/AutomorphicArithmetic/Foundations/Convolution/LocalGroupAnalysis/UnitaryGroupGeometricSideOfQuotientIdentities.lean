import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
open PositivityTheory.Rg.Tf.Geo

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.RightCosetSpace
open scoped ENNReal

/- English proof (translation)
Substitute `hΛ` using the available equality. Use `set D := fundamentalDomain Λ with hDdef`. Use `set E := fundamentalDomain (Λ.map i) with hEdef`. Establish `hD : IsFundamentalDomain Λ D ν` using `isFundamentalDomain_fundamentalDomain Λ ν`. Establish `hE : IsFundamentalDomain (Λ.map i) E μ` using `isFundamentalDomain_fundamentalDomain _ μ`.

Establish `hc : Continuous fun p : X × T => i p.2⁻¹ * p.1` using `(hi.comp continuous_snd.inv).mul continuous_fst`. Establish `hm : Measurable fun p : X × T => ρ (i p.2⁻¹ * p.1)` using `hρ.comp hc.measurable`. Use `set ρ' : X → ℝ≥0∞ := fun x => ∫⁻ d in D, ρ (i d⁻¹ * x) ∂ν with hρ'`. Establish `hρ'm : Measurable ρ'` using `hm.lintegral_prod_right'`. Establish `hinv : ∀ x, ∫⁻ d, ρ (i d⁻¹ * x) ∂ν = 1` using `fun x => by`.

Rewrite using `[← hρ1 x]`. Conclude with `lintegral_inv_eq_self (fun t => ρ (i t * x))`. Establish `hsum : ∀ x, ∑' l : Λ, ρ' (i l * x) = 1` using `fun x => by`. Rewrite using `[← hinv x, hD.lintegral_eq_tsum']`. Use `tsum_congr fun l => ?_` and prove the remaining obligations.

Simplify using `only [hρ']`. Use `lintegral_congr fun d => ?_` and prove the remaining obligations. Simplify using `[Subgroup.smul_def, mul_assoc]`. Establish `hunf : ∫⁻ x, F x * ρ' x ∂μ = ∫⁻ x in E, F x ∂μ`. Rewrite using `[hE.lintegral_eq_tsum'', ← lintegral_tsum]`.

Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[← (Subgroup.equivMapOfInjective Λ i hinj).toEquiv.tsum_eq]`. Establish `: ∀ l : Λ, F ((Subgroup.equivMapOfInjective Λ i hinj).toEquiv l • x) * ρ' ((Subgroup.equivMapOfInjective Λ i hinj).toEquiv l • x) = F x * ρ' (i l * x)` using `fun l => by`. Establish `h : (Subgroup.equivMapOfInjective Λ i hinj).toEquiv l • x = i l * x` using `rfl`. Rewrite using `[h, hFi]`.

Simplify using `only [this]`. Rewrite using `[ENNReal.tsum_mul_left, hsum, mul_one]`. Introduce `g`. Conclude with `((hF.mul hρ'm).comp (measurable_const_smul g)).aemeasurable`. Establish `hfub : ∫⁻ x, F x * ρ' x ∂μ = ν D * ∫⁻ x, F x * ρ x ∂μ`.

Establish `h1 : ∀ x, F x * ρ' x = ∫⁻ d in D, F x * ρ (i d⁻¹ * x) ∂ν` using `fun x => by`. Establish `hd : Measurable fun d : T => ρ (i d⁻¹ * x)` using `hρ.comp ((hi.comp continuous_inv).mul continuous_const).measurable`. Rewrite using `[lintegral_const_mul _ hd]`. Simplify using `only [h1]`. Rewrite using `[lintegral_lintegral_swap]`.

Establish `h2 : ∀ d : T, ∫⁻ x, F x * ρ (i d⁻¹ * x) ∂μ = ∫⁻ x, F x * ρ x ∂μ` using `fun d => by`. Rewrite using `[← lintegral_mul_left_eq_self (fun y => F y * ρ y) (i d⁻¹)]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[hFi]`. Simplify using `only [h2]`.

Rewrite using `[lintegral_const, Measure.restrict_apply_univ, mul_comm]`. Conclude with `((hF.comp measurable_fst).mul hm).aemeasurable`. Rewrite using `[← hunf, hfub]`.
-/
private theorem UpperTheory.ConvolutionTheory.G.stage_key
    {X T : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X] [T2Space X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Group T] [TopologicalSpace T]
    [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (μ : Measure X) [μ.IsHaarMeasure]
    (ν : Measure T) [ν.IsHaarMeasure] [ν.IsInvInvariant] (i : T →* X) (hi : Continuous i)
    (hinj : Function.Injective i) (Λ : Subgroup T) [DiscreteTopology Λ] (Γ₀ : Subgroup X)
    [DiscreteTopology Γ₀] (hΛ : Λ.map i = Γ₀)
    (ρ : X → ℝ≥0∞) (hρ : Measurable ρ) (hρ1 : ∀ x, ∫⁻ t, ρ (i t * x) ∂ν = 1)
    (F : X → ℝ≥0∞) (hF : Measurable F) (hFi : ∀ t x, F (i t * x) = F x) :
    ∫⁻ x in fundamentalDomain Γ₀, F x ∂μ = ν (fundamentalDomain Λ) * ∫⁻ x, F x * ρ x ∂μ := by
  subst hΛ
  set D := fundamentalDomain Λ with hDdef
  set E := fundamentalDomain (Λ.map i) with hEdef
  have hD : IsFundamentalDomain Λ D ν := isFundamentalDomain_fundamentalDomain Λ ν
  have hE : IsFundamentalDomain (Λ.map i) E μ := isFundamentalDomain_fundamentalDomain _ μ
  have hc : Continuous fun p : X × T => i p.2⁻¹ * p.1 :=
    (hi.comp continuous_snd.inv).mul continuous_fst
  have hm : Measurable fun p : X × T => ρ (i p.2⁻¹ * p.1) := hρ.comp hc.measurable
  set ρ' : X → ℝ≥0∞ := fun x => ∫⁻ d in D, ρ (i d⁻¹ * x) ∂ν with hρ'
  have hρ'm : Measurable ρ' := hm.lintegral_prod_right'
  have hinv : ∀ x, ∫⁻ d, ρ (i d⁻¹ * x) ∂ν = 1 := fun x => by
    rw [← hρ1 x]
    exact lintegral_inv_eq_self (fun t => ρ (i t * x))
  have hsum : ∀ x, ∑' l : Λ, ρ' (i l * x) = 1 := fun x => by
    rw [← hinv x, hD.lintegral_eq_tsum']
    refine tsum_congr fun l => ?_
    simp only [hρ']
    refine lintegral_congr fun d => ?_
    simp [Subgroup.smul_def, mul_assoc]
  have hunf : ∫⁻ x, F x * ρ' x ∂μ = ∫⁻ x in E, F x ∂μ := by
    rw [hE.lintegral_eq_tsum'', ← lintegral_tsum]
    · refine lintegral_congr fun x => ?_
      rw [← (Subgroup.equivMapOfInjective Λ i hinj).toEquiv.tsum_eq]
      have : ∀ l : Λ, F ((Subgroup.equivMapOfInjective Λ i hinj).toEquiv l • x) *
          ρ' ((Subgroup.equivMapOfInjective Λ i hinj).toEquiv l • x) = F x * ρ' (i l * x) := fun l => by
        have h : (Subgroup.equivMapOfInjective Λ i hinj).toEquiv l • x = i l * x := rfl
        rw [h, hFi]
      simp only [this]
      rw [ENNReal.tsum_mul_left, hsum, mul_one]
    · intro g
      exact ((hF.mul hρ'm).comp (measurable_const_smul g)).aemeasurable
  have hfub : ∫⁻ x, F x * ρ' x ∂μ = ν D * ∫⁻ x, F x * ρ x ∂μ := by
    have h1 : ∀ x, F x * ρ' x = ∫⁻ d in D, F x * ρ (i d⁻¹ * x) ∂ν := fun x => by
      have hd : Measurable fun d : T => ρ (i d⁻¹ * x) :=
        hρ.comp ((hi.comp continuous_inv).mul continuous_const).measurable
      rw [lintegral_const_mul _ hd]
    simp only [h1]
    rw [lintegral_lintegral_swap]
    · have h2 : ∀ d : T, ∫⁻ x, F x * ρ (i d⁻¹ * x) ∂μ = ∫⁻ x, F x * ρ x ∂μ := fun d => by
        rw [← lintegral_mul_left_eq_self (fun y => F y * ρ y) (i d⁻¹)]
        refine lintegral_congr fun x => ?_
        rw [hFi]
      simp only [h2]
      rw [lintegral_const, Measure.restrict_apply_univ, mul_comm]
    · exact ((hF.comp measurable_fst).mul hm).aemeasurable
  rw [← hunf, hfub]

/- English proof (translation)
Introduce `hQ1 hQ2 X T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ _ i hi Λ _ Γ₀ _ hΛ hvol Φ hΦc hΦi hint`. Establish `hD : IsFundamentalDomain Λ (fundamentalDomain Λ) ν` using `isFundamentalDomain_fundamentalDomain Λ ν`. Establish `hvolD : quotientMeasure Λ ν Set.univ = ν (fundamentalDomain Λ)` using `quotientMeasure_univ ν hD`. Establish `hD0 : ν (fundamentalDomain Λ) ≠ 0` using `hD.measure_ne_zero (NeZero.ne ν)`. Establish `hΦm : Measurable Φ` using `hΦc.measurable`.

Establish `hic : Continuous i` using `hi.continuous`. Establish `hout : ∀ g, Φ (Quotient.out (RightCosetSpace.mk Γ₀ g)) = Φ g` using `fun g => by`. Take `⟨γ, hγ⟩` from `mk_eq_mk_iff.1 (Quotient.out_eq (RightCosetSpace.mk Γ₀ g))`. Establish `hγm : (γ : X) ∈ Λ.map i` using `hΛ ▸ γ.2`. Take `⟨t, -, ht⟩` from `Subgroup.mem_map.1 hγm`.

Rewrite using `[← hγ, Subgroup.smul_def, smul_eq_mul, ← ht, hΦi]`. Establish `key` using `fun ρ hρ hρ1 F hF hFi => UpperTheory.ConvolutionTheory.G.stage_key μ ν i hic hi.injective Λ Γ₀ hΛ ρ hρ hρ1 F hF hFi`. Establish `hEfin : ∫⁻ x in fundamentalDomain Γ₀, ‖Φ x‖ₑ ∂μ < ⊤`. Establish `h` using `hint.2`. Rewrite `h` using `[HasFiniteIntegral, lintegral_quotientMeasure]`.

Simplify `h` using `only [hout]`. Establish `hfin : ∀ ρ, IsNormAlong id i ν ρ → ∫⁻ x, ‖Φ x‖ₑ * ρ x ∂μ < ⊤` using `fun ρ hρ => by`. Establish `h` using `key ρ hρ.1 hρ.2 (fun x => ‖Φ x‖ₑ) hΦm.enorm (fun t x => by simp only [hΦi])`. Rewrite `hEfin` using `[h]`. Assume the negation of the conclusion as `hc`.

Rewrite `hc` using `[not_lt, top_le_iff]`. Rewrite `hEfin` using `[hc, ENNReal.mul_top hD0]`. Conclude with `lt_irrefl _ hEfin`. Use `⟨?_, hfin⟩` and prove the remaining obligations. Take `⟨ρ₀, hρc, hρn, -⟩` from `hQ2 X T ν i hi`.

Establish `e1` using `hQ1 X X T μ ν (MonoidHom.id X) i measurable_id hic Φ (fun x => (ρ₀ x : ℝ≥0∞)) hΦm hΦi hρn (hfin _ hρn)`. Establish `hmeas : (μ.restrict (fundamentalDomain Γ₀)).map Φ = (ν (fundamentalDomain Λ) • μ.withDensity (fun x => (ρ₀ x : ℝ≥0∞))).map Φ`. Rewrite using `[Measure.ext_iff_lintegral]`. Introduce `f hf`. Establish `hw : ∫⁻ a, f (Φ a) ∂μ.withDensity (fun x => (ρ₀ x : ℝ≥0∞)) = ∫⁻ a, f (Φ a) * (ρ₀ a : ℝ≥0∞) ∂μ`.

Rewrite using `[show (fun a => f (Φ a)) = f ∘ Φ from rfl, lintegral_withDensity_eq_lintegral_mul μ hρn.1 (hf.comp hΦm)]`. Conclude with `lintegral_congr fun a => mul_comm _ _`. Rewrite using `[lintegral_map hf hΦm, lintegral_map hf hΦm, lintegral_smul_measure, hw, smul_eq_mul]`. Conclude with `key _ hρn.1 hρn.2 (fun x => f (Φ x)) (hf.comp hΦm) (fun t x => by simp only [hΦi])`. Establish `hq : ∫ y, Φ (Quotient.out y) ∂quotientMeasure Γ₀ μ = ∫ g in fundamentalDomain Γ₀, Φ g ∂μ`.

Rewrite using `[integral_quotientMeasure]`. Simplify using `only [hout]`. Establish `hz : ∫ g in fundamentalDomain Γ₀, Φ g ∂μ = ∫ x, Φ x ∂(ν (fundamentalDomain Λ) • μ.withDensity (fun x => (ρ₀ x : ℝ≥0∞)))`. Establish `h1 : ∀ m : Measure X, ∫ z, z ∂(m.map Φ) = ∫ x, Φ x ∂m` using `fun m => integral_map hΦm.aemeasurable aestronglyMeasurable_id`. Rewrite using `[← h1, ← h1, hmeas]`.

Rewrite using `[hq, hz, integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hρn.1 (Filter.Eventually.of_forall fun x => ENNReal.coe_lt_top), hvolD, Complex.real_smul]`. Use `congr 1`. Establish `e2 : quotInt μ id i ν Φ = ∫ x, Φ x * (((ρ₀ x : ℝ≥0∞)).toReal : ℂ) ∂μ` using `e1`. Rewrite using `[e2]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations.

Simplify using `[Complex.real_smul, mul_comm]`.
-/
theorem UpperTheory.ConvolutionTheory.G.unitaryGroupGeometricSide_of_quotient_identities :
    Q1 → Q2 → U2 := by
  intro hQ1 hQ2 X T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ _ i hi Λ _ Γ₀ _ hΛ hvol Φ hΦc hΦi hint
  have hD : IsFundamentalDomain Λ (fundamentalDomain Λ) ν := isFundamentalDomain_fundamentalDomain Λ ν
  have hvolD : quotientMeasure Λ ν Set.univ = ν (fundamentalDomain Λ) := quotientMeasure_univ ν hD
  have hD0 : ν (fundamentalDomain Λ) ≠ 0 := hD.measure_ne_zero (NeZero.ne ν)
  have hΦm : Measurable Φ := hΦc.measurable
  have hic : Continuous i := hi.continuous
  have hout : ∀ g, Φ (Quotient.out (RightCosetSpace.mk Γ₀ g)) = Φ g := fun g => by
    obtain ⟨γ, hγ⟩ := mk_eq_mk_iff.1 (Quotient.out_eq (RightCosetSpace.mk Γ₀ g))
    have hγm : (γ : X) ∈ Λ.map i := hΛ ▸ γ.2
    obtain ⟨t, -, ht⟩ := Subgroup.mem_map.1 hγm
    rw [← hγ, Subgroup.smul_def, smul_eq_mul, ← ht, hΦi]
  have key := fun ρ hρ hρ1 F hF hFi =>
    UpperTheory.ConvolutionTheory.G.stage_key μ ν i hic hi.injective Λ Γ₀ hΛ ρ hρ hρ1 F hF hFi
  have hEfin : ∫⁻ x in fundamentalDomain Γ₀, ‖Φ x‖ₑ ∂μ < ⊤ := by
    have h := hint.2
    rw [HasFiniteIntegral, lintegral_quotientMeasure] at h
    simpa only [hout] using h
  have hfin : ∀ ρ, IsNormAlong id i ν ρ → ∫⁻ x, ‖Φ x‖ₑ * ρ x ∂μ < ⊤ := fun ρ hρ => by
    have h := key ρ hρ.1 hρ.2 (fun x => ‖Φ x‖ₑ) hΦm.enorm (fun t x => by simp only [hΦi])
    rw [h] at hEfin
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc, ENNReal.mul_top hD0] at hEfin
    exact lt_irrefl _ hEfin
  refine ⟨?_, hfin⟩
  obtain ⟨ρ₀, hρc, hρn, -⟩ := hQ2 X T ν i hi
  have e1 := hQ1 X X T μ ν (MonoidHom.id X) i measurable_id hic Φ (fun x => (ρ₀ x : ℝ≥0∞)) hΦm hΦi hρn (hfin _ hρn)
  have hmeas : (μ.restrict (fundamentalDomain Γ₀)).map Φ =
      (ν (fundamentalDomain Λ) • μ.withDensity (fun x => (ρ₀ x : ℝ≥0∞))).map Φ := by
    rw [Measure.ext_iff_lintegral]
    intro f hf
    have hw : ∫⁻ a, f (Φ a) ∂μ.withDensity (fun x => (ρ₀ x : ℝ≥0∞)) =
        ∫⁻ a, f (Φ a) * (ρ₀ a : ℝ≥0∞) ∂μ := by
      rw [show (fun a => f (Φ a)) = f ∘ Φ from rfl,
        lintegral_withDensity_eq_lintegral_mul μ hρn.1 (hf.comp hΦm)]
      exact lintegral_congr fun a => mul_comm _ _
    rw [lintegral_map hf hΦm, lintegral_map hf hΦm, lintegral_smul_measure, hw, smul_eq_mul]
    exact key _ hρn.1 hρn.2 (fun x => f (Φ x)) (hf.comp hΦm) (fun t x => by simp only [hΦi])
  have hq : ∫ y, Φ (Quotient.out y) ∂quotientMeasure Γ₀ μ = ∫ g in fundamentalDomain Γ₀, Φ g ∂μ := by
    rw [integral_quotientMeasure]
    simp only [hout]
  have hz : ∫ g in fundamentalDomain Γ₀, Φ g ∂μ =
      ∫ x, Φ x ∂(ν (fundamentalDomain Λ) • μ.withDensity (fun x => (ρ₀ x : ℝ≥0∞))) := by
    have h1 : ∀ m : Measure X, ∫ z, z ∂(m.map Φ) = ∫ x, Φ x ∂m := fun m =>
      integral_map hΦm.aemeasurable aestronglyMeasurable_id
    rw [← h1, ← h1, hmeas]
  rw [hq, hz, integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hρn.1
    (Filter.Eventually.of_forall fun x => ENNReal.coe_lt_top), hvolD, Complex.real_smul]
  congr 1
  have e2 : quotInt μ id i ν Φ = ∫ x, Φ x * (((ρ₀ x : ℝ≥0∞)).toReal : ℂ) ∂μ := e1
  rw [e2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [Complex.real_smul, mul_comm]
