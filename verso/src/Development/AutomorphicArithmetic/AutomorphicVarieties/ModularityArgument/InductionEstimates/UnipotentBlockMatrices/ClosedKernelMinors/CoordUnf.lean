import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.AdMeas
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

/- English proof (translation)
Rewrite using `[lintegral_prod _ hf.aemeasurable, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf.lintegral_prod_right']`. Use `lintegral_congr fun t => ?_` and prove the remaining obligations. Rewrite using `[Pi.mul_apply, mul_comm, lintegral_prod (fun y => f (t, y)) (hf.comp measurable_prodMk_left).aemeasurable]`.
-/
private theorem iter3 {B C : Type} [MeasurableSpace B] [MeasurableSpace C] (κ : Measure B) (l : Measure C)
    [SFinite κ] [SFinite l] (f : ℝ × B × C → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ q, f q ∂((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-4 * t))).prod (κ.prod l) =
      ∫⁻ t : ℝ, (∫⁻ k, ∫⁻ X, f (t, k, X) ∂l ∂κ) * ENNReal.ofReal (Real.exp (-4 * t)) := by
  rw [lintegral_prod _ hf.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf.lintegral_prod_right']
  refine lintegral_congr fun t => ?_
  rw [Pi.mul_apply, mul_comm, lintegral_prod (fun y => f (t, y)) (hf.comp measurable_prodMk_left).aemeasurable]

/- English proof (translation)
The claim follows from `inferInstance`.
-/
private theorem oms5 (A B C : Type) [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] [OpensMeasurableSpace A] [OpensMeasurableSpace B] [OpensMeasurableSpace C]
    [SecondCountableTopology A] [SecondCountableTopology C] : OpensMeasurableSpace (A × A × ℝ × B × C) := inferInstance

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
The claim follows from `Subtype.ext (unipGL_add X Y)`.
-/
private theorem nn_add (X Y : UPos (2 + 2) 2 → 𝔸[K]) : nn (X + Y) = nn X * nn Y :=
  Subtype.ext (unipGL_add X Y)

/- English proof (translation)
The claim follows from `Subtype.ext unipGL_zero`.
-/
private theorem nn_zero : nn (0 : UPos (2 + 2) 2 → 𝔸[K]) = 1 :=
  Subtype.ext unipGL_zero

/- English proof (translation)
The claim follows from `continuous_unipGL.subtype_mk _`.
-/
private theorem nn_cont : Continuous (nn : (UPos (2 + 2) 2 → 𝔸[K]) → G1 K (2 + 2)) :=
  continuous_unipGL.subtype_mk _

/- English proof (translation)
Establish `h` using `(blkLaws (K := K)).2.2.2.1`. Unfold `pt`. Use `Continuous.mul (Continuous.mul (nn_cont.comp (by fun_prop)) ?_) (by fun_prop)` and prove the remaining obligations. Conclude with `h.comp (f := fun p : Par K => (p.1, p.2.1, p.2.2.1)) (by fun_prop)`.
-/
private theorem pt_cont : Continuous (pt : Par K → G1 K (2 + 2)) := by
  have h := (blkLaws (K := K)).2.2.2.1
  unfold pt
  refine Continuous.mul (Continuous.mul (nn_cont.comp (by fun_prop)) ?_) (by fun_prop)
  exact h.comp (f := fun p : Par K => (p.1, p.2.1, p.2.2.1)) (by fun_prop)

/- English proof (translation)
Use `haveI i1 : OpensMeasurableSpace (UPos (2 + 2) 2 → 𝔸[K]) := inferInstance`. Use `haveI i2 : OpensMeasurableSpace (G1 K 2) := inferInstance`. Use `haveI i3 : OpensMeasurableSpace (KG K (2 + 2)) := inferInstance`. Use `haveI i4 : SecondCountableTopology (G1 K 2) := inferInstance`. Use `haveI i5 : SecondCountableTopology (UPos (2 + 2) 2 → 𝔸[K]) := inferInstance`.

Use `haveI i9 : OpensMeasurableSpace (Par K) := oms5 _ _ _`. Conclude with `pt_cont.measurable`.
-/
private theorem pt_meas : Measurable (pt : Par K → G1 K (2 + 2)) := by
  haveI i1 : OpensMeasurableSpace (UPos (2 + 2) 2 → 𝔸[K]) := inferInstance
  haveI i2 : OpensMeasurableSpace (G1 K 2) := inferInstance
  haveI i3 : OpensMeasurableSpace (KG K (2 + 2)) := inferInstance
  haveI i4 : SecondCountableTopology (G1 K 2) := inferInstance
  haveI i5 : SecondCountableTopology (UPos (2 + 2) 2 → 𝔸[K]) := inferInstance
  haveI i9 : OpensMeasurableSpace (Par K) := oms5 _ _ _
  exact pt_cont.measurable

/- English proof (translation)
Take `⟨-, hm, h1, -⟩` from `blkLaws (K := K)`. Use `inv_eq_of_mul_eq_one_right ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, ← mul_assoc (lv a b 0), hm, mul_inv_cancel, mul_inv_cancel, add_zero, h1, one_mul, ← nn_add, add_neg_cancel, nn_zero]`.
-/
private theorem inv_eq (ξ : UPos (2 + 2) 2 → 𝔸[K]) (a b : G1 K 2) :
    (nn ξ * lv a b 0)⁻¹ = lv a⁻¹ b⁻¹ 0 * nn (-ξ) := by
  obtain ⟨-, hm, h1, -⟩ := blkLaws (K := K)
  refine inv_eq_of_mul_eq_one_right ?_
  rw [mul_assoc, ← mul_assoc (lv a b 0), hm, mul_inv_cancel, mul_inv_cancel, add_zero, h1, one_mul, ← nn_add,
    add_neg_cancel, nn_zero]

/- English proof (translation)
Take `⟨e, he, hme⟩` from `adMeas a⁻¹ b⁻¹ 0`. Take `⟨-, hm, -⟩` from `blkLaws (K := K)`. Rewrite `hme` using `[mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_smul]`. Establish `hmeas : ∀ c : G1 K (2 + 2), Measurable fun X : UPos (2 + 2) 2 → 𝔸[K] => Φ (c * (nn X * lv m₁ m₂ t * k))` using `fun c => hΦ.comp (continuous_const.mul ((nn_cont.mul continuous_const).mul continuous_const)).measurable`. Establish `h1 : ∀ X, Φ (nn X * lv (a⁻¹ * m₁) (b⁻¹ * m₂) t * k) = Φ (lv a⁻¹ b⁻¹ 0 * (nn (e X) * lv m₁ m₂ t * k))`.

Introduce `X`. Establish `: lv (a⁻¹ * m₁) (b⁻¹ * m₂) t = lv a⁻¹ b⁻¹ 0 * lv m₁ m₂ t` using `by rw [hm, zero_add]`. Rewrite using `[this, ← mul_assoc (nn X), he]`. Simplify using `only [mul_assoc]`. Simplify using `only [h1]`.

Establish `hec : Measurable (e : (UPos (2 + 2) 2 → 𝔸[K]) → (UPos (2 + 2) 2 → 𝔸[K]))` using `e.continuous.measurable`. Rewrite using `[← lintegral_map (hmeas _) hec, hme, isAddFundamentalDomain_unipFundamentalDomain.lintegral_eq_tsum', lintegral_tsum fun ξ => (hmeas _).aemeasurable]`. Use `tsum_congr fun ξ => lintegral_congr fun X => ?_` and prove the remaining obligations. Establish `: (-ξ) +ᵥ X = -ξ.1 + X` using `rfl`. Rewrite using `[this, inv_eq, nn_add]`.

Simplify using `only [mul_assoc]`.
-/
private theorem unfX (Φ : G1 K (2 + 2) → ℝ≥0∞) (hΦ : Measurable Φ) (a b m₁ m₂ : G1 K 2) (t : ℝ) (k : G1 K (2 + 2)) :
    ∫⁻ X, Φ (nn X * lv (a⁻¹ * m₁) (b⁻¹ * m₂) t * k) ∂unipMeasure K (2 + 2) 2 =
      ∫⁻ X, ∑' ξ : unipLattice K (2 + 2) 2, Φ ((nn ξ.1 * lv a b 0)⁻¹ * (nn X * lv m₁ m₂ t * k))
        ∂(unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2) := by
  obtain ⟨e, he, hme⟩ := adMeas a⁻¹ b⁻¹ 0
  obtain ⟨-, hm, -⟩ := blkLaws (K := K)
  rw [mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_smul] at hme
  have hmeas : ∀ c : G1 K (2 + 2), Measurable fun X : UPos (2 + 2) 2 → 𝔸[K] => Φ (c * (nn X * lv m₁ m₂ t * k)) :=
    fun c => hΦ.comp (continuous_const.mul ((nn_cont.mul continuous_const).mul continuous_const)).measurable
  have h1 : ∀ X, Φ (nn X * lv (a⁻¹ * m₁) (b⁻¹ * m₂) t * k) = Φ (lv a⁻¹ b⁻¹ 0 * (nn (e X) * lv m₁ m₂ t * k)) := by
    intro X
    have : lv (a⁻¹ * m₁) (b⁻¹ * m₂) t = lv a⁻¹ b⁻¹ 0 * lv m₁ m₂ t := by rw [hm, zero_add]
    rw [this, ← mul_assoc (nn X), he]
    simp only [mul_assoc]
  simp only [h1]
  have hec : Measurable (e : (UPos (2 + 2) 2 → 𝔸[K]) → (UPos (2 + 2) 2 → 𝔸[K])) := e.continuous.measurable
  rw [← lintegral_map (hmeas _) hec, hme,
    isAddFundamentalDomain_unipFundamentalDomain.lintegral_eq_tsum',
    lintegral_tsum fun ξ => (hmeas _).aemeasurable]
  refine tsum_congr fun ξ => lintegral_congr fun X => ?_
  have : (-ξ) +ᵥ X = -ξ.1 + X := rfl
  rw [this, inv_eq, nn_add]
  simp only [mul_assoc]

/- English proof (translation)
Take `⟨-, hP, hinj, -⟩` from `pkLaws (K := K)`. Take `⟨δ, hδ, hu⟩` from `hE y`. Take `⟨ξ₀, a₀, b₀, h0⟩` from `(hP _).1 ((PK K).inv_mem δ.2)`. Establish `key : ∀ (a b : Gam K 2) (ξ : unipLattice K (2 + 2) 2), ¬ (a = a₀ ∧ b = b₀ ∧ ξ = ξ₀) → E.indicator Ψ ((nn ξ.1 * lv a b 0)⁻¹ * y) = 0`. Introduce `a b ξ hne`.

Use `indicator_of_notMem (fun hm => hne ?_) _` and prove the remaining obligations. Use `hu ⟨_, (PK K).inv_mem ((hP _).2 ⟨ξ, a, b, rfl⟩)⟩ hm` as an intermediate fact. Rewrite `h0` using `[← this]`. Take `⟨h1, h2, h3, -⟩` from `hinj _ _ _ _ _ _ _ _ ((inv_inv _).symm.trans h0)`. Conclude with `⟨Subtype.ext h2, Subtype.ext h3, Subtype.ext h1⟩`.

Rewrite using `[tsum_eq_single a₀ fun a ha => by simp only [key a _ _ fun h => ha h.1, tsum_zero], tsum_eq_single b₀ fun b hb => by simp only [key a₀ b _ fun h => hb h.2.1, tsum_zero], tsum_eq_single ξ₀ fun ξ hξ => key _ _ _ fun h => hξ h.2.2, ← h0, inv_inv]`. Conclude with `(indicator_of_mem hδ _).trans (hΨ _ δ.2 _)`.
-/
private theorem sum_one (E : Set (G1 K (2 + 2))) (hE : ∀ x : G1 K (2 + 2), ∃! γ : PK K, γ • x ∈ E)
    (Ψ : G1 K (2 + 2) → ℝ≥0∞) (hΨ : ∀ γ ∈ PK K, ∀ g, Ψ (γ * g) = Ψ g) (y : G1 K (2 + 2)) :
    ∑' a : Gam K 2, ∑' b : Gam K 2, ∑' ξ : unipLattice K (2 + 2) 2,
      E.indicator Ψ ((nn ξ.1 * lv a b 0)⁻¹ * y) = Ψ y := by
  obtain ⟨-, hP, hinj, -⟩ := pkLaws (K := K)
  obtain ⟨δ, hδ, hu⟩ := hE y
  obtain ⟨ξ₀, a₀, b₀, h0⟩ := (hP _).1 ((PK K).inv_mem δ.2)
  have key : ∀ (a b : Gam K 2) (ξ : unipLattice K (2 + 2) 2), ¬ (a = a₀ ∧ b = b₀ ∧ ξ = ξ₀) →
      E.indicator Ψ ((nn ξ.1 * lv a b 0)⁻¹ * y) = 0 := by
    intro a b ξ hne
    refine indicator_of_notMem (fun hm => hne ?_) _
    have := hu ⟨_, (PK K).inv_mem ((hP _).2 ⟨ξ, a, b, rfl⟩)⟩ hm
    rw [← this] at h0
    obtain ⟨h1, h2, h3, -⟩ := hinj _ _ _ _ _ _ _ _ ((inv_inv _).symm.trans h0)
    exact ⟨Subtype.ext h2, Subtype.ext h3, Subtype.ext h1⟩
  rw [tsum_eq_single a₀ fun a ha => by simp only [key a _ _ fun h => ha h.1, tsum_zero],
    tsum_eq_single b₀ fun b hb => by simp only [key a₀ b _ fun h => hb h.2.1, tsum_zero],
    tsum_eq_single ξ₀ fun ξ hξ => key _ _ _ fun h => hξ h.2.2, ← h0, inv_inv]
  exact (indicator_of_mem hδ _).trans (hΨ _ δ.2 _)

/- English proof (translation)
Introduce `K _ _ μ₂ _ κ _ E hEm hE Ψ hΨm hΨ`. Use `haveI : CompactSpace (KG K (2 + 2)) := isCompact_iff_compactSpace.1 ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 (2 + 2)).1`. Use `haveI : SFinite κ := inferInstance`. Use `haveI : SFinite (fd μ₂) := inferInstance`. Use `haveI : SFinite ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2)) := inferInstance`.

Use `haveI : SFinite (κ.prod ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2))) := inferInstance`. Use `haveI : SFinite (((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-4 * t))).prod (κ.prod ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2)))) := inferInstance`. Establish `hΦ : Measurable (E.indicator Ψ)` using `hΨm.indicator hEm`. Use `set S : Gam K 2 → Gam K 2 → Par K → ℝ≥0∞ := fun a b p => ∑' ξ : unipLattice K (2 + 2) 2, E.indicator Ψ ((nn ξ.1 * lv a b 0)⁻¹ * pt p) with hS`. Establish `hSm : ∀ a b, Measurable (S a b)` using `fun a b => Measurable.ennreal_tsum fun ξ => hΦ.comp (pt_meas.const_mul _)`.

Establish `hTm : ∀ a, Measurable fun p => ∑' b, S a b p` using `fun a => Measurable.ennreal_tsum (hSm a)`. Establish `hR : ∀ p, Ψ (pt p) = ∑' a, ∑' b, S a b p` using `fun p => (sum_one E hE Ψ hΨ _).symm`. Simplify using `only [hR]`. Rewrite using `[lintegral_tsum fun a => (hTm a).aemeasurable, (isFundamentalDomain_fundamentalDomain (Gam K 2) μ₂).lintegral_eq_tsum']`. Use `tsum_congr fun a => ?_` and prove the remaining obligations.

Rewrite using `[parM, lintegral_prod _ (hTm a).aemeasurable]`. Use `lintegral_congr fun m₁ => ?_` and prove the remaining obligations. Establish `h2 : ∀ b, Measurable fun q => S a b (m₁, q)` using `fun b => (hSm a b).comp measurable_prodMk_left`. Rewrite using `[lintegral_tsum fun b => (h2 b).aemeasurable, (isFundamentalDomain_fundamentalDomain (Gam K 2) μ₂).lintegral_eq_tsum']`. Use `tsum_congr fun b => ?_` and prove the remaining obligations.

Rewrite using `[lintegral_prod _ (h2 b).aemeasurable]`. Use `lintegral_congr fun m₂ => ?_` and prove the remaining obligations. Rewrite using `[iter3 _ _ (fun y => S a b (m₁, m₂, y)) ((h2 b).comp measurable_prodMk_left)]`. Use `lintegral_congr fun t => ?_` and prove the remaining obligations. Rewrite using `[← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]`.

Use `lintegral_congr fun k => ?_` and prove the remaining obligations. Rewrite using `[lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]`. Conclude with `congrArg (· * _) (unfX _ hΦ a b m₁ m₂ t k)`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.coordUnf :
    ∀ {K : Type} [Field K] [NumberField K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (κ : Measure (KG K (2 + 2))) [κ.IsHaarMeasure] (E : Set (G1 K (2 + 2))), MeasurableSet E → (∀ x : G1 K (2 + 2), ∃! γ : PK K, γ • x ∈ E) →
      ∀ Ψ : G1 K (2 + 2) → ℝ≥0∞, Measurable Ψ → (∀ γ ∈ PK K, ∀ g, Ψ (γ * g) = Ψ g) →
        ∫⁻ m₁, ∫⁻ m₂, ∫⁻ t : ℝ, ∫⁻ k : KG K (2 + 2), ∫⁻ X, E.indicator Ψ (nn X * lv m₁ m₂ t * k) * ENNReal.ofReal (Real.exp (-4 * t))
          ∂unipMeasure K (2 + 2) 2 ∂κ ∂volume ∂μ₂ ∂μ₂ = ∫⁻ p, Ψ (pt p) ∂parM μ₂ κ := by
  intro K _ _ μ₂ _ κ _ E hEm hE Ψ hΨm hΨ
  haveI : CompactSpace (KG K (2 + 2)) :=
    isCompact_iff_compactSpace.1 ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 (2 + 2)).1
  haveI : SFinite κ := inferInstance
  haveI : SFinite (fd μ₂) := inferInstance
  haveI : SFinite ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2)) := inferInstance
  haveI : SFinite (κ.prod ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2))) := inferInstance
  haveI : SFinite (((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-4 * t))).prod
    (κ.prod ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2)))) := inferInstance
  have hΦ : Measurable (E.indicator Ψ) := hΨm.indicator hEm
  set S : Gam K 2 → Gam K 2 → Par K → ℝ≥0∞ := fun a b p => ∑' ξ : unipLattice K (2 + 2) 2,
    E.indicator Ψ ((nn ξ.1 * lv a b 0)⁻¹ * pt p) with hS
  have hSm : ∀ a b, Measurable (S a b) := fun a b =>
    Measurable.ennreal_tsum fun ξ => hΦ.comp (pt_meas.const_mul _)
  have hTm : ∀ a, Measurable fun p => ∑' b, S a b p := fun a => Measurable.ennreal_tsum (hSm a)
  have hR : ∀ p, Ψ (pt p) = ∑' a, ∑' b, S a b p := fun p => (sum_one E hE Ψ hΨ _).symm
  simp only [hR]
  rw [lintegral_tsum fun a => (hTm a).aemeasurable,
    (isFundamentalDomain_fundamentalDomain (Gam K 2) μ₂).lintegral_eq_tsum']
  refine tsum_congr fun a => ?_
  rw [parM, lintegral_prod _ (hTm a).aemeasurable]
  refine lintegral_congr fun m₁ => ?_
  have h2 : ∀ b, Measurable fun q => S a b (m₁, q) := fun b => (hSm a b).comp measurable_prodMk_left
  rw [lintegral_tsum fun b => (h2 b).aemeasurable,
    (isFundamentalDomain_fundamentalDomain (Gam K 2) μ₂).lintegral_eq_tsum']
  refine tsum_congr fun b => ?_
  rw [lintegral_prod _ (h2 b).aemeasurable]
  refine lintegral_congr fun m₂ => ?_
  rw [iter3 _ _ (fun y => S a b (m₁, m₂, y)) ((h2 b).comp measurable_prodMk_left)]
  refine lintegral_congr fun t => ?_
  rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun k => ?_
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  exact congrArg (· * _) (unfX _ hΦ a b m₁ m₂ t k)
