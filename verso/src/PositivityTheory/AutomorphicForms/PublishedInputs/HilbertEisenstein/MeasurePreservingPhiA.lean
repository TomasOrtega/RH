import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SExpDefs

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix ENNReal
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published Filter

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

namespace L6

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/- English proof (translation)
The claim follows from `ω.2.2 a`.
-/
theorem omega_diagonal (ω : HChar F) (a : Fˣ) : ω.1 (diagonal F a) = 1 := ω.2.2 a

/- English proof (translation)
Establish `hu : ideleModule F (u : IdeleGroup F) = 1` using `u.2`. Rewrite using `[tau, map_mul, map_mul, ideleModule_diagonal, ideleModule_moduleSection, hu, mul_one, mul_one]`.
-/
theorem module_tau_diag (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) (a : Fˣ) :
    (ideleModule F (tau t u * diagonal F a) : ℝ) = t := by
  have hu : ideleModule F (u : IdeleGroup F) = 1 := u.2
  rw [tau, map_mul, map_mul, ideleModule_diagonal, ideleModule_moduleSection, hu, mul_one, mul_one]

/- English proof (translation)
Establish `he : diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F) = tau t u * diagonal F a`. Rewrite using `[tau, mul_assoc, mul_comm]`. Rewrite using `[he, module_tau_diag, map_mul, omega_diagonal, mul_one, wt, mul_assoc]`.
-/
theorem G_unfold (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (Y : Ad F) (ξ : F) (t : {r : ℝ // 0 < r})
    (u : normOneSubgroup F) (a : Fˣ) :
    kern c Y (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) ξ *
      ((ω.1 (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) : ℂˣ) : ℂ)⁻¹ *
      ((ideleModule F (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) : ℝ) : ℂ) =
    kern c Y (tau t u * diagonal F a) ξ * wt ω t u := by
  have he : diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F) = tau t u * diagonal F a := by
    rw [tau, mul_assoc, mul_comm]
  rw [he, module_tau_diag, map_mul, omega_diagonal, mul_one, wt, mul_assoc]

/- English proof (translation)
Repeatedly rewrite using `[G_unfold]`. Rewrite using `[coefK, tsum_mul_right]`.
-/
theorem tsum_G (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (Y : Ad F) (ξ : F) (t : {r : ℝ // 0 < r})
    (u : normOneSubgroup F) :
    ∑' a : Fˣ, kern c Y (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) ξ *
      ((ω.1 (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) : ℂˣ) : ℂ)⁻¹ *
      ((ideleModule F (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) : ℝ) : ℂ) =
    coefK c Y (tau t u) ξ * wt ω t u := by
  simp_rw [G_unfold]
  rw [coefK, tsum_mul_right]

def phiA (a : Fˣ) (p : {r : ℝ // 0 < r} × normOneSubgroup F) : IdeleGroup F :=
  diagonal F a * moduleSection (w0 F) p.1 * (p.2 : IdeleGroup F)

/- English proof (translation)
The claim follows from `(continuous_const.mul ((continuous_moduleSection (w0 F)).comp continuous_fst)).mul (continuous_subtype_val.comp continuous_snd)`.
-/
theorem continuous_phiA (a : Fˣ) : Continuous (phiA (F := F) a) :=
  (continuous_const.mul ((continuous_moduleSection (w0 F)).comp continuous_fst)).mul
    (continuous_subtype_val.comp continuous_snd)

/- English proof (translation)
Establish `h0 : MeasurePreserving (normOneSplitting (w0 F)).toHomeomorph.toMeasurableEquiv (ideleMeasure F) ((normOneMeasure F).prod posRealMeasure)` using `measurePreserving_normOneSplitting (w0 F)`. Establish `h1` using `(MeasurePreserving.symm _ h0).comp (Measure.measurePreserving_swap (μ := posRealMeasure) (ν := normOneMeasure F))`. Establish `h3` using `(measurePreserving_mul_left (ideleMeasure F) (diagonal F a)).comp h1`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`.

Express the relevant statement in the definitionally equal form `diagonal F a * moduleSection (w0 F) p.1 * (p.2 : IdeleGroup F) = diagonal F a * ((p.2 : IdeleGroup F) * moduleSection (w0 F) p.1)`. Rewrite using `[mul_assoc, mul_comm (moduleSection (w0 F) p.1)]`.
-/
theorem measurePreserving_phiA (a : Fˣ) :
    MeasurePreserving (phiA (F := F) a) (posRealMeasure.prod (normOneMeasure F)) (ideleMeasure F) := by
  have h0 : MeasurePreserving (normOneSplitting (w0 F)).toHomeomorph.toMeasurableEquiv (ideleMeasure F)
      ((normOneMeasure F).prod posRealMeasure) := measurePreserving_normOneSplitting (w0 F)
  have h1 := (MeasurePreserving.symm _ h0).comp (Measure.measurePreserving_swap
    (μ := posRealMeasure) (ν := normOneMeasure F))
  have h3 := (measurePreserving_mul_left (ideleMeasure F) (diagonal F a)).comp h1
  convert h3 using 1
  funext p
  change diagonal F a * moduleSection (w0 F) p.1 * (p.2 : IdeleGroup F) =
    diagonal F a * ((p.2 : IdeleGroup F) * moduleSection (w0 F) p.1)
  rw [mul_assoc, mul_comm (moduleSection (w0 F) p.1)]

/- English proof (translation)
Establish `h : muE F = (posRealMeasure.prod (normOneMeasure F)).restrict (Set.univ ×ˢ normOneFundamentalDomain F)`. Rewrite using `[← Measure.prod_restrict, Measure.restrict_univ]`. Rewrite using `[h]`. Conclude with `Measure.absolutelyContinuous_of_le Measure.restrict_le_self`.
-/
theorem muE_ac : muE F ≪ posRealMeasure.prod (normOneMeasure F) := by
  have h : muE F = (posRealMeasure.prod (normOneMeasure F)).restrict (Set.univ ×ˢ normOneFundamentalDomain F) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [h]
  exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self

/- English proof (translation)
Establish `hm : ∀ a : Fˣ, Measurable fun p => g (phiA a p)` using `fun a => hg.comp (continuous_phiA a).measurable`. Establish `hin : ∀ t : {r : ℝ // 0 < r}, ∫⁻ u in normOneFundamentalDomain F, ∑' a : Fˣ, g (phiA a (t, u)) ∂normOneMeasure F = ∫⁻ u, g (phiA 1 (t, u)) ∂normOneMeasure F`. Introduce `t`. Establish `h𝓕` using `isFundamentalDomain_normOneFundamentalDomain F (normOneMeasure F)`. Set `e : Fˣ ≃ (diagonalNormOne F).op` to `(diagonalNormOneEquiv F).trans (diagonalNormOne F).equivOp`.

Rewrite using `[lintegral_tsum (f := fun a u => g (phiA a (t, u))) (fun a => ((hm a).comp measurable_prodMk_left).aemeasurable), h𝓕.lintegral_eq_tsum'', ← e.tsum_eq]`. Use `tsum_congr fun a => lintegral_congr fun u => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `g (phiA a (t, u)) = g (phiA 1 (t, u * diagonalToNormOne F a))`. Simplify using `only [phiA, map_one, one_mul, Subgroup.coe_mul, coe_diagonalToNormOne]`. Use `congr 1`.

The two sides agree by associativity and commutativity. Rewrite using `[lintegral_prod _ (Measurable.tsum hm).aemeasurable]`. Repeatedly rewrite using `[hin]`. Rewrite using `[← (measurePreserving_phiA 1).lintegral_comp hg, lintegral_prod _ (hm 1).aemeasurable]`.
-/
theorem lintegral_unfold {g : IdeleGroup F → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, ∑' a : Fˣ, g (phiA a p) ∂(muE F) = ∫⁻ x, g x ∂ideleMeasure F := by
  have hm : ∀ a : Fˣ, Measurable fun p => g (phiA a p) := fun a => hg.comp (continuous_phiA a).measurable
  have hin : ∀ t : {r : ℝ // 0 < r}, ∫⁻ u in normOneFundamentalDomain F, ∑' a : Fˣ, g (phiA a (t, u)) ∂normOneMeasure F
      = ∫⁻ u, g (phiA 1 (t, u)) ∂normOneMeasure F := by
    intro t
    have h𝓕 := isFundamentalDomain_normOneFundamentalDomain F (normOneMeasure F)
    let e : Fˣ ≃ (diagonalNormOne F).op := (diagonalNormOneEquiv F).trans (diagonalNormOne F).equivOp
    rw [lintegral_tsum (f := fun a u => g (phiA a (t, u))) (fun a => ((hm a).comp measurable_prodMk_left).aemeasurable),
      h𝓕.lintegral_eq_tsum'',
      ← e.tsum_eq]
    refine tsum_congr fun a => lintegral_congr fun u => ?_
    change g (phiA a (t, u)) = g (phiA 1 (t, u * diagonalToNormOne F a))
    simp only [phiA, map_one, one_mul, Subgroup.coe_mul, coe_diagonalToNormOne]
    congr 1
    ac_rfl
  rw [lintegral_prod _ (Measurable.tsum hm).aemeasurable]
  simp_rw [hin]
  rw [← (measurePreserving_phiA 1).lintegral_comp hg, lintegral_prod _ (hm 1).aemeasurable]

/- English proof (translation)
Use `set G' := hG.1.mk G`. Establish `hG'm : StronglyMeasurable G'` using `hG.1.stronglyMeasurable_mk`. Establish `hGG' : G =ᵐ[ideleMeasure F] G'` using `hG.1.ae_eq_mk`. Establish `hae : ∀ᵐ p ∂(muE F), ∀ a : Fˣ, G (phiA a p) = G' (phiA a p)`. Use `ae_all_iff.2 fun a => muE_ac.ae_le ?_` and prove the remaining obligations.

Conclude with `(measurePreserving_phiA a).quasiMeasurePreserving.ae_eq_comp hGG'`. Establish `hP' : Integrable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => ∑' a : Fˣ, G' (phiA a p)) (muE F)`. Use `⟨(Measurable.tsum fun a => hG'm.measurable.comp (continuous_phiA a).measurable).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Unfold `HasFiniteIntegral`. Combine the equalities or inequalities in the displayed calculation.

Use `hP'.congr ?_` and prove the remaining obligations. Use `filter_upwards [hae] with p hp`. Conclude with `tsum_congr fun a => (hp a).symm`.
-/
theorem integrable_unfold {G : IdeleGroup F → ℂ} (hG : Integrable G (ideleMeasure F)) :
    Integrable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => ∑' a : Fˣ, G (phiA a p)) (muE F) := by
  set G' := hG.1.mk G
  have hG'm : StronglyMeasurable G' := hG.1.stronglyMeasurable_mk
  have hGG' : G =ᵐ[ideleMeasure F] G' := hG.1.ae_eq_mk
  have hae : ∀ᵐ p ∂(muE F), ∀ a : Fˣ, G (phiA a p) = G' (phiA a p) := by
    refine ae_all_iff.2 fun a => muE_ac.ae_le ?_
    exact (measurePreserving_phiA a).quasiMeasurePreserving.ae_eq_comp hGG'
  have hP' : Integrable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => ∑' a : Fˣ, G' (phiA a p)) (muE F) := by
    refine ⟨(Measurable.tsum fun a => hG'm.measurable.comp (continuous_phiA a).measurable).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ p, ‖∑' a : Fˣ, G' (phiA a p)‖ₑ ∂(muE F)
        ≤ ∫⁻ p, ∑' a : Fˣ, ‖G' (phiA a p)‖ₑ ∂(muE F) := lintegral_mono fun p => enorm_tsum_le_tsum_enorm
      _ = ∫⁻ x, ‖G' x‖ₑ ∂ideleMeasure F := lintegral_unfold hG'm.measurable.enorm
      _ = ∫⁻ x, ‖G x‖ₑ ∂ideleMeasure F := lintegral_congr_ae (hGG'.fun_comp _).symm
      _ < ∞ := hG.2
  refine hP'.congr ?_
  filter_upwards [hae] with p hp
  exact tsum_congr fun a => (hp a).symm

end L6

open L6 in
/- English proof (translation)
Introduce `F _ _ _ ω c H Y ξ hG`. Use `set G : IdeleGroup F → ℂ := fun τ => kern c Y τ ξ * ((ω.1 τ : ℂˣ) : ℂ)⁻¹ * ((ideleModule F τ : ℝ) : ℂ)`. Establish `hP : ∀ p : {r : ℝ // 0 < r} × normOneSubgroup F, coefK c Y (tau p.1 p.2) ξ * wt ω p.1 p.2 = ∑' a : Fˣ, G (phiA a p)` using `fun p => (tsum_G ω c Y ξ p.1 p.2).symm`. Repeatedly rewrite using `[hP]`. Rewrite using `[integral_prod _ (integrable_unfold hG), integral_ideleMeasure_eq_integral_fundamentalDomain (w0 F) hG]`.

Both sides reduce to the same expression.
-/
theorem sUnfold_statement : SUnfold := by
  intro F _ _ _ ω c H Y ξ hG
  set G : IdeleGroup F → ℂ := fun τ => kern c Y τ ξ * ((ω.1 τ : ℂˣ) : ℂ)⁻¹ * ((ideleModule F τ : ℝ) : ℂ)
  have hP : ∀ p : {r : ℝ // 0 < r} × normOneSubgroup F,
      coefK c Y (tau p.1 p.2) ξ * wt ω p.1 p.2 = ∑' a : Fˣ, G (phiA a p) := fun p => (tsum_G ω c Y ξ p.1 p.2).symm
  simp_rw [hP]
  rw [integral_prod _ (integrable_unfold hG), integral_ideleMeasure_eq_integral_fundamentalDomain (w0 F) hG]
  rfl

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
