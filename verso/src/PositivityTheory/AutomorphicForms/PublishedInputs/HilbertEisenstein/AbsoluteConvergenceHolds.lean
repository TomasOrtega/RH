import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.P5meas
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.GaussianWeightRealNonneg
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.KernelMeasureBoundAndMeasurability

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published
open NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L5

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

set_option linter.unusedSectionVars false

/- English proof (translation)
The claim follows from `(summable_norm_smul_algebraMap b hG).comp_injective Units.val_injective`.
-/
theorem summable_theta {G : Ad F → ℂ} (hG : G ∈ schwartzBruhat F) (b : IdeleGroup F) :
    Summable fun ξ : Fˣ => ‖G (b • algebraMap F (Ad F) (ξ : F))‖ :=
  (summable_norm_smul_algebraMap b hG).comp_injective Units.val_injective

/- English proof (translation)
The claim follows from `tsum_nonneg fun _ => norm_nonneg _`.
-/
theorem theta_nonneg (G : Ad F → ℂ) (b : IdeleGroup F) : 0 ≤ theta G b :=
  tsum_nonneg fun _ => norm_nonneg _

/- English proof (translation)
Take `⟨u, hu, hb⟩` from `exists_decay_bound (w0 F) hG hC r`. Use `⟨∑' ξ : Fˣ, u ξ, fun a ha t ht => ?_⟩` and prove the remaining obligations. Establish `hu' : Summable fun ξ : Fˣ => u ξ` using `hu.comp_injective Units.val_injective`. Rewrite using `[theta, ← tsum_mul_right]`. Conclude with `Summable.tsum_le_tsum (fun ξ => (hb a ha t ht ξ ξ.ne_zero).trans_eq (mul_comm _ _)) (summable_theta hG _) (hu'.mul_right _)`.
-/
theorem theta_decay {G : Ad F → ℂ} (hG : G ∈ schwartzBruhat F) {C : Set (IdeleGroup F)} (hC : IsCompact C) (r : ℕ) :
    ∃ M : ℝ, ∀ a ∈ C, ∀ t : {x : ℝ // 0 < x}, 1 ≤ (t : ℝ) →
      theta G (moduleSection (w0 F) t * a) ≤ M * ((t : ℝ) ^ r)⁻¹ := by
  obtain ⟨u, hu, hb⟩ := exists_decay_bound (w0 F) hG hC r
  refine ⟨∑' ξ : Fˣ, u ξ, fun a ha t ht => ?_⟩
  have hu' : Summable fun ξ : Fˣ => u ξ := hu.comp_injective Units.val_injective
  rw [theta, ← tsum_mul_right]
  exact Summable.tsum_le_tsum (fun ξ => (hb a ha t ht ξ ξ.ne_zero).trans_eq (mul_comm _ _)) (summable_theta hG _)
    (hu'.mul_right _)

/- English proof (translation)
Rewrite using `[mul_inv, map_inv]`.
-/
theorem moduleSection_mul_inv (t : {x : ℝ // 0 < x}) (a : IdeleGroup F) :
    (moduleSection (w0 F) t * a)⁻¹ = moduleSection (w0 F) t⁻¹ * a⁻¹ := by
  rw [mul_inv, map_inv]

/- English proof (translation)
Take `⟨u, hu, hb⟩` from `exists_decay_bound (w0 F) (adelicFourier_mem_schwartzBruhat hG) hC.inv 0`. Establish `hcont : Continuous fun a : IdeleGroup F => ((ideleModule F a : ℝ))⁻¹` using `(continuous_subtype_val.comp (continuous_ideleModule (K := F))).inv₀ fun a => (ideleModule F a).2.ne'`. Take `⟨B, hB⟩` from `hC.exists_bound_of_continuousOn hcont.continuousOn`. Use `⟨B * (‖adelicFourier F G 0‖ + ∑' ξ : F, |u ξ|), fun a ha t ht => ?_⟩` and prove the remaining obligations. Use `set b := moduleSection (w0 F) t * a with hbdef`.

Establish `hs : Summable fun ξ : F => ‖G (b • algebraMap F (Ad F) ξ)‖` using `summable_norm_smul_algebraMap b hG`. Establish `h1 : theta G b ≤ ∑' ξ : F, ‖G (b • algebraMap F (Ad F) ξ)‖` using `tsum_comp_le_tsum_of_inj hs (fun _ => norm_nonneg _) Units.val_injective`. Establish `h2 : ∑' ξ : F, ‖G (b • algebraMap F (Ad F) ξ)‖ = ‖∑' ξ : F, G (b • algebraMap F (Ad F) ξ)‖`. Establish `: (∑' ξ : F, G (b • algebraMap F (Ad F) ξ)) = ((∑' ξ : F, ‖G (b • algebraMap F (Ad F) ξ)‖ : ℝ) : ℂ)`. Rewrite using `[Complex.ofReal_tsum]`.

Conclude with `tsum_congr fun ξ => hpos _`. Rewrite using `[this, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]`. Rewrite `h2` using `[tsum_smul_algebraMap_eq b hG]`. Establish `hsF : Summable fun ξ : F => ‖adelicFourier F G (b⁻¹ • algebraMap F (Ad F) ξ)‖` using `summable_norm_adelicFourier_smul_algebraMap b hG`. Establish `ht1 : 1 ≤ ((t⁻¹ : {x : ℝ // 0 < x}) : ℝ)`.

Rewrite using `[Positive.coe_inv]`. Conclude with `one_le_inv₀ t.2 |>.2 ht`. Establish `hterm : ∀ ξ : F, ξ ≠ 0 → ‖adelicFourier F G (b⁻¹ • algebraMap F (Ad F) ξ)‖ ≤ |u ξ|`. Introduce `ξ hξ`. Use `hb a⁻¹ (Set.inv_mem_inv.mpr ha) t⁻¹ ht1 ξ hξ` as an intermediate fact.

Rewrite using `[hbdef, moduleSection_mul_inv]`. Simplify using `using this.trans (le_abs_self _)`. Establish `h3 : ‖∑' ξ : F, adelicFourier F G (b⁻¹ • algebraMap F (Ad F) ξ)‖ ≤ ‖adelicFourier F G 0‖ + ∑' ξ : F, |u ξ|`. Use `(norm_tsum_le_tsum_norm hsF).trans ?_` and prove the remaining obligations. Rewrite using `[hsF.tsum_eq_add_tsum_ite 0, smul_algebraMap_zero]`.

Establish `hle : ∀ ξ : F, (if ξ = 0 then 0 else ‖adelicFourier F G (b⁻¹ • algebraMap F (Ad F) ξ)‖) ≤ |u ξ|`. Introduce `ξ`. Use `split_ifs with h`. Conclude with `abs_nonneg _`. Conclude with `hterm ξ h`.

Establish `hnn : ∀ ξ : F, 0 ≤ (if ξ = 0 then 0 else ‖adelicFourier F G (b⁻¹ • algebraMap F (Ad F) ξ)‖)`. Introduce `ξ`. Apply the tactic sequence `split_ifs <;> simp`. Conclude with `add_le_add le_rfl (Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le hnn hle hu.abs) hu.abs)`. Establish `hmod : ((ideleModule F b : ℝ))⁻¹ ≤ (t : ℝ)⁻¹ * B`.

Establish `hB'` using `hB a ha`. Rewrite `hB'` using `[Real.norm_of_nonneg (inv_nonneg.2 (ideleModule F a).2.le)]`. Rewrite using `[hbdef, map_mul, ideleModule_moduleSection, Positive.val_mul, mul_inv]`. Conclude with `mul_le_mul_of_nonneg_left hB' (inv_nonneg.2 t.2.le)`. Establish `hnn : 0 ≤ ‖adelicFourier F G 0‖ + ∑' ξ : F, |u ξ|` using `add_nonneg (norm_nonneg _) (tsum_nonneg fun _ => abs_nonneg _)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (ideleModule F b).2.le)]`. Use `_ ≤ ((t : ℝ)⁻¹ * B) * (‖adelicFourier F G 0‖ + ∑' ξ : F, |u ξ|) := mul_le_mul hmod h3 (norm_nonneg _) ((inv_nonneg.2 (ideleModule F b).2.le).trans hmod)`. Use `_ = B * (‖adelicFourier F G 0‖ + ∑' ξ : F, |u ξ|) * (t : ℝ)⁻¹ := by ring`.
-/
theorem theta_growth {G : Ad F → ℂ} (hG : G ∈ schwartzBruhat F) (hpos : ∀ x, G x = ((‖G x‖ : ℝ) : ℂ))
    {C : Set (IdeleGroup F)} (hC : IsCompact C) :
    ∃ M : ℝ, ∀ a ∈ C, ∀ t : {x : ℝ // 0 < x}, (t : ℝ) ≤ 1 →
      theta G (moduleSection (w0 F) t * a) ≤ M * (t : ℝ)⁻¹ := by
  obtain ⟨u, hu, hb⟩ := exists_decay_bound (w0 F) (adelicFourier_mem_schwartzBruhat hG) hC.inv 0
  have hcont : Continuous fun a : IdeleGroup F => ((ideleModule F a : ℝ))⁻¹ :=
    (continuous_subtype_val.comp (continuous_ideleModule (K := F))).inv₀ fun a => (ideleModule F a).2.ne'
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨B * (‖adelicFourier F G 0‖ + ∑' ξ : F, |u ξ|), fun a ha t ht => ?_⟩
  set b := moduleSection (w0 F) t * a with hbdef
  have hs : Summable fun ξ : F => ‖G (b • algebraMap F (Ad F) ξ)‖ := summable_norm_smul_algebraMap b hG
  have h1 : theta G b ≤ ∑' ξ : F, ‖G (b • algebraMap F (Ad F) ξ)‖ :=
    tsum_comp_le_tsum_of_inj hs (fun _ => norm_nonneg _) Units.val_injective
  have h2 : ∑' ξ : F, ‖G (b • algebraMap F (Ad F) ξ)‖ = ‖∑' ξ : F, G (b • algebraMap F (Ad F) ξ)‖ := by
    have : (∑' ξ : F, G (b • algebraMap F (Ad F) ξ)) = ((∑' ξ : F, ‖G (b • algebraMap F (Ad F) ξ)‖ : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]
      exact tsum_congr fun ξ => hpos _
    rw [this, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]
  rw [tsum_smul_algebraMap_eq b hG] at h2
  have hsF : Summable fun ξ : F => ‖adelicFourier F G (b⁻¹ • algebraMap F (Ad F) ξ)‖ :=
    summable_norm_adelicFourier_smul_algebraMap b hG
  have ht1 : 1 ≤ ((t⁻¹ : {x : ℝ // 0 < x}) : ℝ) := by
    rw [Positive.coe_inv]
    exact one_le_inv₀ t.2 |>.2 ht
  have hterm : ∀ ξ : F, ξ ≠ 0 → ‖adelicFourier F G (b⁻¹ • algebraMap F (Ad F) ξ)‖ ≤ |u ξ| := by
    intro ξ hξ
    have := hb a⁻¹ (Set.inv_mem_inv.mpr ha) t⁻¹ ht1 ξ hξ
    rw [hbdef, moduleSection_mul_inv]
    simpa using this.trans (le_abs_self _)
  have h3 : ‖∑' ξ : F, adelicFourier F G (b⁻¹ • algebraMap F (Ad F) ξ)‖ ≤
      ‖adelicFourier F G 0‖ + ∑' ξ : F, |u ξ| := by
    refine (norm_tsum_le_tsum_norm hsF).trans ?_
    rw [hsF.tsum_eq_add_tsum_ite 0, smul_algebraMap_zero]
    have hle : ∀ ξ : F, (if ξ = 0 then 0 else ‖adelicFourier F G (b⁻¹ • algebraMap F (Ad F) ξ)‖) ≤ |u ξ| := by
      intro ξ
      split_ifs with h
      · exact abs_nonneg _
      · exact hterm ξ h
    have hnn : ∀ ξ : F, 0 ≤ (if ξ = 0 then 0 else ‖adelicFourier F G (b⁻¹ • algebraMap F (Ad F) ξ)‖) := by
      intro ξ
      split_ifs <;> simp
    exact add_le_add le_rfl (Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le hnn hle hu.abs) hu.abs)
  have hmod : ((ideleModule F b : ℝ))⁻¹ ≤ (t : ℝ)⁻¹ * B := by
    have hB' := hB a ha
    rw [Real.norm_of_nonneg (inv_nonneg.2 (ideleModule F a).2.le)] at hB'
    rw [hbdef, map_mul, ideleModule_moduleSection, Positive.val_mul, mul_inv]
    exact mul_le_mul_of_nonneg_left hB' (inv_nonneg.2 t.2.le)
  have hnn : 0 ≤ ‖adelicFourier F G 0‖ + ∑' ξ : F, |u ξ| :=
    add_nonneg (norm_nonneg _) (tsum_nonneg fun _ => abs_nonneg _)
  calc theta G b ≤ _ := h1
    _ = _ := h2
    _ = ((ideleModule F b : ℝ))⁻¹ * ‖∑' ξ : F, adelicFourier F G (b⁻¹ • algebraMap F (Ad F) ξ)‖ := by
        rw [norm_mul, ← Complex.ofReal_inv, Complex.norm_real,
          Real.norm_of_nonneg (inv_nonneg.2 (ideleModule F b).2.le)]
    _ ≤ ((t : ℝ)⁻¹ * B) * (‖adelicFourier F G 0‖ + ∑' ξ : F, |u ξ|) :=
        mul_le_mul hmod h3 (norm_nonneg _) ((inv_nonneg.2 (ideleModule F b).2.le).trans hmod)
    _ = B * (‖adelicFourier F G 0‖ + ∑' ξ : F, |u ξ|) * (t : ℝ)⁻¹ := by ring

/- English proof (translation)
Establish `hu : ideleModule F (u : IdeleGroup F) = 1` using `u.2`. Simplify using `only [tau, map_mul, ideleModule_moduleSection, hu, mul_one]`.
-/
theorem ideleModule_tau (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) : (ideleModule F (tau t u) : ℝ) = t := by
  have hu : ideleModule F (u : IdeleGroup F) = 1 := u.2
  simp only [tau, map_mul, ideleModule_moduleSection, hu, mul_one]

/- English proof (translation)
The claim follows from `Measurable.ite (measurableSet_le measurable_const measurable_subtype_coe) measurable_subtype_coe.inv measurable_subtype_coe`.
-/
theorem measurable_gB : Measurable gB :=
  Measurable.ite (measurableSet_le measurable_const measurable_subtype_coe) measurable_subtype_coe.inv
    measurable_subtype_coe

/- English proof (translation)
Establish `h1 : IntegrableOn (fun x : ℝ => Real.exp (-|x|)) (Set.Iic 0)` using `(integrableOn_exp_Iic 0).congr_fun (fun x hx => by`. Simplify using `only [Set.mem_Iic] at hx`. Simplify using `[abs_of_nonpos hx]) measurableSet_Iic`. Establish `h2 : IntegrableOn (fun x : ℝ => Real.exp (-|x|)) (Set.Ioi 0)` using `(integrableOn_exp_neg_Ioi 0).congr_fun (fun x hx => by`. Simplify using `only [Set.mem_Ioi] at hx`.

Simplify using `[abs_of_pos hx]) measurableSet_Ioi`. Use `h1.union h2` as an intermediate fact. Rewrite `this` using `[Set.Iic_union_Ioi, integrableOn_univ]`. Then use the resulting hypothesis.
-/
theorem integrable_exp_neg_abs : Integrable fun x : ℝ => Real.exp (-|x|) := by
  have h1 : IntegrableOn (fun x : ℝ => Real.exp (-|x|)) (Set.Iic 0) :=
    (integrableOn_exp_Iic 0).congr_fun (fun x hx => by
      simp only [Set.mem_Iic] at hx
      simp [abs_of_nonpos hx]) measurableSet_Iic
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (-|x|)) (Set.Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).congr_fun (fun x hx => by
      simp only [Set.mem_Ioi] at hx
      simp [abs_of_pos hx]) measurableSet_Ioi
  have := h1.union h2
  rwa [Set.Iic_union_Ioi, integrableOn_univ] at this

/- English proof (translation)
Rewrite using `[posRealMeasure_eq_map_expPos, integrable_map_measure measurable_gB.aestronglyMeasurable measurable_expPos.aemeasurable]`. Use `integrable_exp_neg_abs.congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Establish `he : ((expPos x : {r : ℝ // 0 < r}) : ℝ) = Real.exp x` using `rfl`. Simplify using `only [Function.comp_apply, gB, he]`. Distinguish the cases in `h : 0 ≤ x`.

Rewrite using `[if_pos (Real.one_le_exp h), abs_of_nonneg h, Real.exp_neg]`. Rewrite using `[if_neg (by rw [Real.one_le_exp_iff]; exact h), abs_of_neg (not_le.1 h), neg_neg]`.
-/
theorem integrable_gB_pos : Integrable gB posRealMeasure := by
  rw [posRealMeasure_eq_map_expPos, integrable_map_measure measurable_gB.aestronglyMeasurable
    measurable_expPos.aemeasurable]
  refine integrable_exp_neg_abs.congr (Filter.Eventually.of_forall fun x => ?_)
  have he : ((expPos x : {r : ℝ // 0 < r}) : ℝ) = Real.exp x := rfl
  simp only [Function.comp_apply, gB, he]
  by_cases h : 0 ≤ x
  · rw [if_pos (Real.one_le_exp h), abs_of_nonneg h, Real.exp_neg]
  · rw [if_neg (by rw [Real.one_le_exp_iff]; exact h), abs_of_neg (not_le.1 h), neg_neg]

/- English proof (translation)
Establish `: IsFiniteMeasure ((normOneMeasure F).restrict (normOneFundamentalDomain F))` using `isFiniteMeasure_restrict.2 (normOneMeasure_normOneFundamentalDomain_lt_top F).ne`. Establish `h` using `integrable_gB_pos.mul_prod (integrable_const (1 : ℝ) (μ := (normOneMeasure F).restrict (normOneFundamentalDomain F)))`. Simplify using `using h`.
-/
theorem integrable_gB : Integrable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => gB p.1) (muE F) := by
  have : IsFiniteMeasure ((normOneMeasure F).restrict (normOneFundamentalDomain F)) :=
    isFiniteMeasure_restrict.2 (normOneMeasure_normOneFundamentalDomain_lt_top F).ne
  have h := integrable_gB_pos.mul_prod (integrable_const (1 : ℝ)
    (μ := (normOneMeasure F).restrict (normOneFundamentalDomain F)))
  simpa using h

/- English proof (translation)
Rewrite using `[ae_iff]`. Establish `hs : {p : {r : ℝ // 0 < r} × normOneSubgroup F | ¬ p.2 ∈ normOneFundamentalDomain F} = Set.univ ×ˢ (normOneFundamentalDomain F)ᶜ`. Use extensionality with `p`. Simplify using the standard rewrite rules. Rewrite using `[hs, Measure.prod_prod, Measure.restrict_apply (measurableSet_normOneFundamentalDomain F).compl, Set.compl_inter_self, measure_empty, mul_zero]`.
-/
theorem ae_mem_E : ∀ᵐ p ∂(muE F), p.2 ∈ normOneFundamentalDomain F := by
  rw [ae_iff]
  have hs : {p : {r : ℝ // 0 < r} × normOneSubgroup F | ¬ p.2 ∈ normOneFundamentalDomain F} =
      Set.univ ×ˢ (normOneFundamentalDomain F)ᶜ := by
    ext p; simp
  rw [hs, Measure.prod_prod, Measure.restrict_apply (measurableSet_normOneFundamentalDomain F).compl,
    Set.compl_inter_self, measure_empty, mul_zero]

/- English proof (translation)
Use `set C1 : Set (IdeleGroup F) := (fun u : normOneSubgroup F => (u : IdeleGroup F) * Yid) '' closure (normOneFundamentalDomain F)`. Use `set C2 : Set (IdeleGroup F) := (fun u : normOneSubgroup F => μ * (u : IdeleGroup F)⁻¹) '' closure (normOneFundamentalDomain F)`. Establish `hC1 : IsCompact C1` using `(isCompact_closure_normOneFundamentalDomain F).image (continuous_subtype_val.mul continuous_const)`. Establish `hC2 : IsCompact C2` using `(isCompact_closure_normOneFundamentalDomain F).image (continuous_const.mul continuous_subtype_val.inv)`. Take `⟨A1, hA1⟩` from `theta_decay hH hC1 2`.

Take `⟨B1, hB1⟩` from `theta_growth hH hpos hC1`. Take `⟨A2, hA2⟩` from `theta_decay hH hC2 2`. Take `⟨B2, hB2⟩` from `theta_growth hH hpos hC2`. Use `⟨|A1 * B2| + |B1 * A2|, fun u hu t => ?_⟩` and prove the remaining obligations. Establish `hu1 : (u : IdeleGroup F) * Yid ∈ C1` using `⟨u, subset_closure hu, rfl⟩`.

Establish `hu2 : μ * (u : IdeleGroup F)⁻¹ ∈ C2` using `⟨u, subset_closure hu, rfl⟩`. Establish `e1 : tau t u * Yid = moduleSection (w0 F) t * ((u : IdeleGroup F) * Yid)`. Rewrite using `[tau, mul_assoc]`. Establish `e2 : μ * (tau t u)⁻¹ = moduleSection (w0 F) t⁻¹ * (μ * (u : IdeleGroup F)⁻¹)`. Rewrite using `[tau, mul_inv, map_inv, mul_left_comm]`.

Rewrite using `[e1, e2]`. Use `set θ1 := theta (H1 F) (moduleSection (w0 F) t * ((u : IdeleGroup F) * Yid))`. Use `set θ2 := theta (H1 F) (moduleSection (w0 F) t⁻¹ * (μ * (u : IdeleGroup F)⁻¹))`. Establish `ht : (0 : ℝ) < t` using `t.2`. Establish `n1 : 0 ≤ θ1` using `theta_nonneg _ _`.

Establish `n2 : 0 ≤ θ2` using `theta_nonneg _ _`. Establish `hinv : ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) = (t : ℝ)⁻¹` using `Positive.coe_inv t`. Establish `hM1 : A1 * B2 ≤ |A1 * B2| + |B1 * A2|` using `(le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))`. Establish `hM2 : B1 * A2 ≤ |A1 * B2| + |B1 * A2|` using `(le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))`. Distinguish the cases in `h1 : 1 ≤ (t : ℝ)`.

Establish `d1` using `hA1 _ hu1 t h1`. Establish `g2` using `hB2 _ hu2 t⁻¹ (by rw [hinv]; exact inv_le_one_of_one_le₀ h1)`. Rewrite `g2` using `[hinv, inv_inv]`. Establish `hg : gB t = (t : ℝ)⁻¹` using `if_pos h1`. Rewrite using `[hg]`.

Combine the equalities or inequalities in the displayed calculation. Use `push Not at h1`. Establish `g1` using `hB1 _ hu1 t h1.le`. Establish `d2` using `hA2 _ hu2 t⁻¹ (by rw [hinv]; exact (one_le_inv₀ ht).2 h1.le)`. Rewrite `d2` using `[hinv]`.

Establish `hg : gB t = (t : ℝ)` using `if_neg (not_le.2 h1)`. Rewrite using `[hg]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem theta_prod_le (hH : H1 F ∈ schwartzBruhat F) (hpos : ∀ x, H1 F x = ((‖H1 F x‖ : ℝ) : ℂ))
    (Yid μ : IdeleGroup F) : ∃ M : ℝ, ∀ u ∈ normOneFundamentalDomain F, ∀ t : {r : ℝ // 0 < r},
      theta (H1 F) (tau t u * Yid) * theta (H1 F) (μ * (tau t u)⁻¹) ≤ M * gB t := by
  set C1 : Set (IdeleGroup F) :=
    (fun u : normOneSubgroup F => (u : IdeleGroup F) * Yid) '' closure (normOneFundamentalDomain F)
  set C2 : Set (IdeleGroup F) :=
    (fun u : normOneSubgroup F => μ * (u : IdeleGroup F)⁻¹) '' closure (normOneFundamentalDomain F)
  have hC1 : IsCompact C1 :=
    (isCompact_closure_normOneFundamentalDomain F).image (continuous_subtype_val.mul continuous_const)
  have hC2 : IsCompact C2 :=
    (isCompact_closure_normOneFundamentalDomain F).image (continuous_const.mul continuous_subtype_val.inv)
  obtain ⟨A1, hA1⟩ := theta_decay hH hC1 2
  obtain ⟨B1, hB1⟩ := theta_growth hH hpos hC1
  obtain ⟨A2, hA2⟩ := theta_decay hH hC2 2
  obtain ⟨B2, hB2⟩ := theta_growth hH hpos hC2
  refine ⟨|A1 * B2| + |B1 * A2|, fun u hu t => ?_⟩
  have hu1 : (u : IdeleGroup F) * Yid ∈ C1 := ⟨u, subset_closure hu, rfl⟩
  have hu2 : μ * (u : IdeleGroup F)⁻¹ ∈ C2 := ⟨u, subset_closure hu, rfl⟩
  have e1 : tau t u * Yid = moduleSection (w0 F) t * ((u : IdeleGroup F) * Yid) := by
    rw [tau, mul_assoc]
  have e2 : μ * (tau t u)⁻¹ = moduleSection (w0 F) t⁻¹ * (μ * (u : IdeleGroup F)⁻¹) := by
    rw [tau, mul_inv, map_inv, mul_left_comm]
  rw [e1, e2]
  set θ1 := theta (H1 F) (moduleSection (w0 F) t * ((u : IdeleGroup F) * Yid))
  set θ2 := theta (H1 F) (moduleSection (w0 F) t⁻¹ * (μ * (u : IdeleGroup F)⁻¹))
  have ht : (0 : ℝ) < t := t.2
  have n1 : 0 ≤ θ1 := theta_nonneg _ _
  have n2 : 0 ≤ θ2 := theta_nonneg _ _
  have hinv : ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) = (t : ℝ)⁻¹ := Positive.coe_inv t
  have hM1 : A1 * B2 ≤ |A1 * B2| + |B1 * A2| := (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
  have hM2 : B1 * A2 ≤ |A1 * B2| + |B1 * A2| := (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
  by_cases h1 : 1 ≤ (t : ℝ)
  · have d1 := hA1 _ hu1 t h1
    have g2 := hB2 _ hu2 t⁻¹ (by rw [hinv]; exact inv_le_one_of_one_le₀ h1)
    rw [hinv, inv_inv] at g2
    have hg : gB t = (t : ℝ)⁻¹ := if_pos h1
    rw [hg]
    calc θ1 * θ2 ≤ (A1 * ((t : ℝ) ^ 2)⁻¹) * (B2 * t) := mul_le_mul d1 g2 n2 (n1.trans d1)
      _ = (A1 * B2) * (t : ℝ)⁻¹ := by field_simp
      _ ≤ (|A1 * B2| + |B1 * A2|) * (t : ℝ)⁻¹ := mul_le_mul_of_nonneg_right hM1 (inv_nonneg.2 ht.le)
  · push Not at h1
    have g1 := hB1 _ hu1 t h1.le
    have d2 := hA2 _ hu2 t⁻¹ (by rw [hinv]; exact (one_le_inv₀ ht).2 h1.le)
    rw [hinv] at d2
    have hg : gB t = (t : ℝ) := if_neg (not_le.2 h1)
    rw [hg]
    calc θ1 * θ2 ≤ (B1 * (t : ℝ)⁻¹) * (A2 * (((t : ℝ)⁻¹) ^ 2)⁻¹) := mul_le_mul g1 d2 n2 (n1.trans g1)
      _ = (B1 * A2) * (t : ℝ) := by field_simp
      _ ≤ (|A1 * B2| + |B1 * A2|) * (t : ℝ) := mul_le_mul_of_nonneg_right hM2 ht.le

/- English proof (translation)
Establish `hA : ((τ * diagonal F a : IdeleGroup F) : Ad F) * (Yid : Ad F) = (τ * Yid) • algebraMap F (Ad F) (a : F)`. Rewrite using `[Units.smul_def, smul_eq_mul, Units.val_mul, Units.val_mul, coe_diagonal]`. Expand and normalize the polynomial expressions, which then agree. Establish `hZ : (τ * diagonal F a)⁻¹ • algebraMap F (Ad F) ξ = τ⁻¹ • algebraMap F (Ad F) (((a⁻¹ : Fˣ) : F) * ξ)`. Rewrite using `[mul_inv, ← map_inv (diagonal F) a, Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, Units.val_mul, coe_diagonal, map_mul, mul_assoc]`.

Establish `hmod : ideleModule F (τ * diagonal F a) = ideleModule F τ`. Rewrite using `[map_mul, ideleModule_diagonal, mul_one]`. Establish `h` using `hdom ((τ * Yid) • algebraMap F (Ad F) (a : F)) (τ⁻¹ • algebraMap F (Ad F) (((a⁻¹ : Fˣ) : F) * ξ)) (μ • (τ⁻¹ • algebraMap F (Ad F) (((a⁻¹ : Fˣ) : F) * ξ))) (hμ1 _) (hμ2 _)`. Rewrite `h` using `[smul_smul]`. Unfold `kern`.

Rewrite using `[hkern, hA, hZ, hmod, norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (ideleModule F τ).2.le]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `inv_nonneg.2 (ideleModule F τ).2.le`. Use `_ = _ := by ring`.
-/
theorem kern_le (c : HeightOneSpectrum (𝓞 F) → ℕ) {κ : ℂ}
    (hkern : ∀ A Z : Ad F, adelicFourier F (slice c A) Z = κ * kernF c A Z)
    (hdom : ∀ A Z Z' : Ad F, Z'.1 = Z.1 →
      (condZ c Z → Z'.2 ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)) →
      ‖kernF c A Z‖ ≤ ‖H1 F A‖ * ‖H1 F Z'‖) {μ : IdeleGroup F}
    (hμ1 : ∀ Z : Ad F, (μ • Z).1 = Z.1)
    (hμ2 : ∀ Z : Ad F, condZ c Z → (μ • Z).2 ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ))
    (Yid τ : IdeleGroup F) (a : Fˣ) (ξ : F) :
    ‖kern c (Yid : Ad F) (τ * diagonal F a) ξ‖ ≤ ‖κ‖ * (ideleModule F τ : ℝ)⁻¹ *
      (‖H1 F ((τ * Yid) • algebraMap F (Ad F) (a : F))‖ *
        ‖H1 F ((μ * τ⁻¹) • algebraMap F (Ad F) (((a⁻¹ : Fˣ) : F) * ξ))‖) := by
  have hA : ((τ * diagonal F a : IdeleGroup F) : Ad F) * (Yid : Ad F) =
      (τ * Yid) • algebraMap F (Ad F) (a : F) := by
    rw [Units.smul_def, smul_eq_mul, Units.val_mul, Units.val_mul, coe_diagonal]
    ring
  have hZ : (τ * diagonal F a)⁻¹ • algebraMap F (Ad F) ξ =
      τ⁻¹ • algebraMap F (Ad F) (((a⁻¹ : Fˣ) : F) * ξ) := by
    rw [mul_inv, ← map_inv (diagonal F) a, Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul,
      Units.val_mul, coe_diagonal, map_mul, mul_assoc]
  have hmod : ideleModule F (τ * diagonal F a) = ideleModule F τ := by
    rw [map_mul, ideleModule_diagonal, mul_one]
  have h := hdom ((τ * Yid) • algebraMap F (Ad F) (a : F)) (τ⁻¹ • algebraMap F (Ad F) (((a⁻¹ : Fˣ) : F) * ξ))
    (μ • (τ⁻¹ • algebraMap F (Ad F) (((a⁻¹ : Fˣ) : F) * ξ))) (hμ1 _) (hμ2 _)
  rw [smul_smul] at h
  unfold kern
  rw [hkern, hA, hZ, hmod, norm_mul, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (ideleModule F τ).2.le]
  calc ((ideleModule F τ : ℝ))⁻¹ * (‖κ‖ * ‖kernF c ((τ * Yid) • algebraMap F (Ad F) (a : F))
        (τ⁻¹ • algebraMap F (Ad F) (((a⁻¹ : Fˣ) : F) * ξ))‖)
      ≤ ((ideleModule F τ : ℝ))⁻¹ * (‖κ‖ * (‖H1 F ((τ * Yid) • algebraMap F (Ad F) (a : F))‖ *
        ‖H1 F ((μ * τ⁻¹) • algebraMap F (Ad F) (((a⁻¹ : Fˣ) : F) * ξ))‖)) := by
        gcongr
        exact inv_nonneg.2 (ideleModule F τ).2.le
    _ = _ := by ring

/- English proof (translation)
Use `set K := ‖κ‖ * (ideleModule F τ : ℝ)⁻¹ with hKdef`. Use `set f1 : Fˣ → ℝ := fun a => ‖H1 F ((τ * Yid) • algebraMap F (Ad F) (a : F))‖ with hf1def`. Use `set f2 : Fˣ → ℝ := fun η => ‖H1 F ((μ * τ⁻¹) • algebraMap F (Ad F) (η : F))‖ with hf2def`. Establish `hf1 : Summable f1` using `summable_theta hH _`. Establish `hf2 : Summable f2` using `summable_theta hH _`.

Establish `hprod : Summable fun q : Fˣ × Fˣ => f1 q.1 * f2 q.2` using `hf1.mul_of_nonneg hf2 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)`. Set `e : Fˣ × Fˣ ≃ Fˣ × Fˣ` to `{ toFun := fun q => (q.1, q.1⁻¹ * q.2) invFun := fun q => (q.1, q.1 * q.2) left_inv := fun q => by simp right_inv := fun q => by simp }`. Establish `hprod' : Summable fun q : Fˣ × Fˣ => f1 q.1 * f2 (q.1⁻¹ * q.2)` using `e.summable_iff.2 hprod`. Use `set g : Fˣ × Fˣ → ℝ := fun q => ‖kern c (Yid : Ad F) (τ * diagonal F q.1) (q.2 : F)‖ with hgdef`. Establish `hg_le : ∀ q, g q ≤ K * (f1 q.1 * f2 (q.1⁻¹ * q.2))` using `fun q => by`.

Use `kern_le c hkern hdom hμ1 hμ2 Yid τ q.1 q.2` as an intermediate fact. Simplify `this` using `[g, f1, f2, K, Units.val_mul]`. Establish `hg : Summable g` using `Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hg_le (hprod'.mul_left K)`. Establish `hg' : Summable fun q : Fˣ × Fˣ => g q.swap` using `(Equiv.prodComm Fˣ Fˣ).summable_iff.2 hg`. Establish `hrow : ∀ ξ : Fˣ, Summable fun a : Fˣ => g (a, ξ)` using `fun ξ => hg'.prod_factor ξ`.

Establish `hcol : Summable fun ξ : Fˣ => ∑' a : Fˣ, g (a, ξ)` using `hg'.prod`. Establish `hle : ∀ ξ : Fˣ, ‖coefK c (Yid : Ad F) τ ξ‖ ≤ ∑' a : Fˣ, g (a, ξ)` using `fun ξ => norm_tsum_le_tsum_norm (hrow ξ)`. Use `⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hcol, ?_⟩` and prove the remaining obligations. Establish `hnorm1 : Summable fun a => ‖f1 a‖` using `by simpa only [f1, norm_norm] using hf1`. Establish `hnorm2 : Summable fun a => ‖f2 a‖` using `by simpa only [f2, norm_norm] using hf2`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[tsum_mul_left]`. Use `congr 1`. Conclude with `e.tsum_eq (fun q : Fˣ × Fˣ => f1 q.1 * f2 q.2)`. Use `_ = K * (theta (H1 F) (τ * Yid) * theta (H1 F) (μ * τ⁻¹)) := by`.

Rewrite using `[← tsum_mul_tsum_of_summable_norm hnorm1 hnorm2]`. Both sides reduce to the same expression.
-/
theorem coef_bound (c : HeightOneSpectrum (𝓞 F) → ℕ) {κ : ℂ}
    (hkern : ∀ A Z : Ad F, adelicFourier F (slice c A) Z = κ * kernF c A Z)
    (hH : H1 F ∈ schwartzBruhat F)
    (hdom : ∀ A Z Z' : Ad F, Z'.1 = Z.1 →
      (condZ c Z → Z'.2 ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)) →
      ‖kernF c A Z‖ ≤ ‖H1 F A‖ * ‖H1 F Z'‖) {μ : IdeleGroup F}
    (hμ1 : ∀ Z : Ad F, (μ • Z).1 = Z.1)
    (hμ2 : ∀ Z : Ad F, condZ c Z → (μ • Z).2 ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ))
    (Yid τ : IdeleGroup F) :
    (Summable fun ξ : Fˣ => ‖coefK c (Yid : Ad F) τ ξ‖) ∧
      ∑' ξ : Fˣ, ‖coefK c (Yid : Ad F) τ ξ‖ ≤
        ‖κ‖ * (ideleModule F τ : ℝ)⁻¹ * (theta (H1 F) (τ * Yid) * theta (H1 F) (μ * τ⁻¹)) := by
  set K := ‖κ‖ * (ideleModule F τ : ℝ)⁻¹ with hKdef
  set f1 : Fˣ → ℝ := fun a => ‖H1 F ((τ * Yid) • algebraMap F (Ad F) (a : F))‖ with hf1def
  set f2 : Fˣ → ℝ := fun η => ‖H1 F ((μ * τ⁻¹) • algebraMap F (Ad F) (η : F))‖ with hf2def
  have hf1 : Summable f1 := summable_theta hH _
  have hf2 : Summable f2 := summable_theta hH _
  have hprod : Summable fun q : Fˣ × Fˣ => f1 q.1 * f2 q.2 :=
    hf1.mul_of_nonneg hf2 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  let e : Fˣ × Fˣ ≃ Fˣ × Fˣ :=
    { toFun := fun q => (q.1, q.1⁻¹ * q.2)
      invFun := fun q => (q.1, q.1 * q.2)
      left_inv := fun q => by simp
      right_inv := fun q => by simp }
  have hprod' : Summable fun q : Fˣ × Fˣ => f1 q.1 * f2 (q.1⁻¹ * q.2) :=
    e.summable_iff.2 hprod
  set g : Fˣ × Fˣ → ℝ := fun q => ‖kern c (Yid : Ad F) (τ * diagonal F q.1) (q.2 : F)‖ with hgdef
  have hg_le : ∀ q, g q ≤ K * (f1 q.1 * f2 (q.1⁻¹ * q.2)) := fun q => by
    have := kern_le c hkern hdom hμ1 hμ2 Yid τ q.1 q.2
    simpa [g, f1, f2, K, Units.val_mul] using this
  have hg : Summable g := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hg_le (hprod'.mul_left K)
  have hg' : Summable fun q : Fˣ × Fˣ => g q.swap := (Equiv.prodComm Fˣ Fˣ).summable_iff.2 hg
  have hrow : ∀ ξ : Fˣ, Summable fun a : Fˣ => g (a, ξ) := fun ξ => hg'.prod_factor ξ
  have hcol : Summable fun ξ : Fˣ => ∑' a : Fˣ, g (a, ξ) := hg'.prod
  have hle : ∀ ξ : Fˣ, ‖coefK c (Yid : Ad F) τ ξ‖ ≤ ∑' a : Fˣ, g (a, ξ) := fun ξ =>
    norm_tsum_le_tsum_norm (hrow ξ)
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hcol, ?_⟩
  have hnorm1 : Summable fun a => ‖f1 a‖ := by simpa only [f1, norm_norm] using hf1
  have hnorm2 : Summable fun a => ‖f2 a‖ := by simpa only [f2, norm_norm] using hf2
  calc ∑' ξ : Fˣ, ‖coefK c (Yid : Ad F) τ ξ‖ ≤ ∑' ξ : Fˣ, ∑' a : Fˣ, g (a, ξ) :=
        Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hcol) hcol
    _ = ∑' q : Fˣ × Fˣ, g q.swap := (hg'.tsum_prod' hrow).symm
    _ = ∑' q : Fˣ × Fˣ, g q := (Equiv.prodComm Fˣ Fˣ).tsum_eq g
    _ ≤ ∑' q : Fˣ × Fˣ, K * (f1 q.1 * f2 (q.1⁻¹ * q.2)) :=
        Summable.tsum_le_tsum hg_le hg (hprod'.mul_left K)
    _ = K * ∑' q : Fˣ × Fˣ, f1 q.1 * f2 q.2 := by
        rw [tsum_mul_left]
        congr 1
        exact e.tsum_eq (fun q : Fˣ × Fˣ => f1 q.1 * f2 q.2)
    _ = K * (theta (H1 F) (τ * Yid) * theta (H1 F) (μ * τ⁻¹)) := by
        rw [← tsum_mul_tsum_of_summable_norm hnorm1 hnorm2]
        rfl

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L5

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open L5

/- English proof (translation)
Introduce `hfin hK F _ _ _ ω c H y hy yf`. Take `⟨κ, -, hkern⟩` from `hK F c (hfin F ω c H)`. Take `⟨hH, hpos, hd⟩` from `hdom F`. Take `⟨μ, hμ1, hμ2⟩` from `hmu F c (hfin F ω c H)`. Use `set Yid : IdeleGroup F := UpperTheory.V.TR.infId F y * finId F yf with hYid`.

Establish `hY : yAd y yf = (Yid : Ad F)` using `rfl`. Rewrite using `[hY]`. Take `⟨M, hM⟩` from `theta_prod_le hH hpos Yid μ`. Establish `hmc` using `hmeas F c κ hkern (Yid : Ad F)`. Use `⟨fun ξ => (hmc ξ).aestronglyMeasurable, fun p => (coef_bound c hkern hH (hd c) hμ1 hμ2 Yid (tau p.1 p.2)).1, ?_⟩` and prove the remaining obligations.

Establish `hmeasS : Measurable fun p : {r : ℝ // 0 < r} × normOneSubgroup F => (∑' ξ : Fˣ, ‖coefK c (Yid : Ad F) (tau p.1 p.2) ξ‖) * (p.1 : ℝ)`. Establish `h1 : Measurable fun p : {r : ℝ // 0 < r} × normOneSubgroup F => ∑' ξ : Fˣ, ‖coefK c (Yid : Ad F) (tau p.1 p.2) ξ‖` using `Measurable.tsum fun ξ : Fˣ => (hmc (ξ : F)).norm`. Establish `h2 : Measurable fun p : {r : ℝ // 0 < r} × normOneSubgroup F => (p.1 : ℝ)` using `measurable_subtype_coe.comp measurable_fst`. Conclude with `h1.mul h2`. Use `Integrable.mono' ((integrable_gB (F := F)).const_mul (‖κ‖ * M)) hmeasS.aestronglyMeasurable ?_` and prove the remaining obligations.

Use `filter_upwards [ae_mem_E (F := F)] with p hp`. Take `⟨t, u⟩` from `p`. Establish `hb` using `coef_bound c hkern hH (hd c) hμ1 hμ2 Yid (tau t u)`. Establish `ht : (0 : ℝ) < t` using `t.2`. Rewrite `hb` using `[ideleModule_tau]`.

Establish `h0 : 0 ≤ ∑' ξ : Fˣ, ‖coefK c (Yid : Ad F) (tau t u) ξ‖` using `tsum_nonneg fun _ => norm_nonneg _`. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 ht.le)]`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts. Use `_ ≤ ‖κ‖ * (M * gB t) := mul_le_mul_of_nonneg_left (hM u hp t) (norm_nonneg _)`.

Use `_ = ‖κ‖ * M * gB t := by ring`.
-/
theorem sAbs_of (hdom : P5dom) (hmu : P5mu) (hmeas : P5meas) : SFin → SKern → SAbs := by
  intro hfin hK F _ _ _ ω c H y hy yf
  obtain ⟨κ, -, hkern⟩ := hK F c (hfin F ω c H)
  obtain ⟨hH, hpos, hd⟩ := hdom F
  obtain ⟨μ, hμ1, hμ2⟩ := hmu F c (hfin F ω c H)
  set Yid : IdeleGroup F := UpperTheory.V.TR.infId F y * finId F yf with hYid
  have hY : yAd y yf = (Yid : Ad F) := rfl
  rw [hY]
  obtain ⟨M, hM⟩ := theta_prod_le hH hpos Yid μ
  have hmc := hmeas F c κ hkern (Yid : Ad F)
  refine ⟨fun ξ => (hmc ξ).aestronglyMeasurable,
    fun p => (coef_bound c hkern hH (hd c) hμ1 hμ2 Yid (tau p.1 p.2)).1, ?_⟩
  have hmeasS : Measurable fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
      (∑' ξ : Fˣ, ‖coefK c (Yid : Ad F) (tau p.1 p.2) ξ‖) * (p.1 : ℝ) := by
    have h1 : Measurable fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
        ∑' ξ : Fˣ, ‖coefK c (Yid : Ad F) (tau p.1 p.2) ξ‖ :=
      Measurable.tsum fun ξ : Fˣ => (hmc (ξ : F)).norm
    have h2 : Measurable fun p : {r : ℝ // 0 < r} × normOneSubgroup F => (p.1 : ℝ) :=
      measurable_subtype_coe.comp measurable_fst
    exact h1.mul h2
  refine Integrable.mono' ((integrable_gB (F := F)).const_mul (‖κ‖ * M)) hmeasS.aestronglyMeasurable ?_
  filter_upwards [ae_mem_E (F := F)] with p hp
  obtain ⟨t, u⟩ := p
  have hb := coef_bound c hkern hH (hd c) hμ1 hμ2 Yid (tau t u)
  have ht : (0 : ℝ) < t := t.2
  rw [ideleModule_tau] at hb
  have h0 : 0 ≤ ∑' ξ : Fˣ, ‖coefK c (Yid : Ad F) (tau t u) ξ‖ := tsum_nonneg fun _ => norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 ht.le)]
  calc (∑' ξ : Fˣ, ‖coefK c (Yid : Ad F) (tau t u) ξ‖) * (t : ℝ)
      ≤ ‖κ‖ * (t : ℝ)⁻¹ * (theta (H1 F) (tau t u * Yid) * theta (H1 F) (μ * (tau t u)⁻¹)) * (t : ℝ) :=
        mul_le_mul_of_nonneg_right hb.2 ht.le
    _ = ‖κ‖ * (theta (H1 F) (tau t u * Yid) * theta (H1 F) (μ * (tau t u)⁻¹)) := by
        field_simp
    _ ≤ ‖κ‖ * (M * gB t) := mul_le_mul_of_nonneg_left (hM u hp t) (norm_nonneg _)
    _ = ‖κ‖ * M * gB t := by ring

/- English proof (translation)
The claim follows from `sAbs_of dominating_function_holds measure_bound_holds measurability_holds`.
-/
theorem absolute_convergence_holds : SFin → SKern → SAbs :=
  sAbs_of dominating_function_holds measure_bound_holds measurability_holds

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
