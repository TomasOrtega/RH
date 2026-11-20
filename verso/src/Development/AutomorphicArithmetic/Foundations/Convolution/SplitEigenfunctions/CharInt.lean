import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SzLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ContinuousPrN
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Iwa
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.NormWfLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.UnitaryMatrixFamily

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x : A ℚ, adelicChar ℚ x ≠ 1 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `adelicChar_ne_one (K := ℚ) (DFunLike.ext _ _ fun x => by simpa using h x)`. Establish `hx' : ψ x ≠ 1` using `fun h => hx (Circle.ext (by simpa [ψ] using h))`.

Establish `hper : ∀ (k : ℚ) (y : A ℚ), ψ ((rt k + y) * rt r) = ψ (y * rt r)`. Introduce `k y`. Rewrite using `[add_mul, Pp.ψ_add, ← map_mul, Pp.ψ_rt, one_mul]`. Establish `h` using `Pp.int_add (F := ℚ) (h := fun b => ψ (b * rt r)) hper (rt r⁻¹ * x)`. Establish `hrr : rt r⁻¹ * rt r = (1 : A ℚ)` using `by rw [← map_mul, inv_mul_cancel₀ hr, map_one]`.

Establish `e : ∀ b : A ℚ, ψ ((b + rt r⁻¹ * x) * rt r) = ψ (b * rt r) * ψ x`. Introduce `b`. Rewrite using `[add_mul, Pp.ψ_add, mul_right_comm, hrr, one_mul]`. Simplify using `only [e] at h`. Rewrite `h` using `[integral_mul_const]`.

Establish `h1 : (∫ b in fundamentalSet ℚ, ψ (b * rt r) ∂(adeleMeasure ℚ)) * (ψ x - 1) = 0`. Rewrite using `[mul_sub, h, mul_one, sub_self]`. Conclude with `(mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 hx')`.
-/
private theorem char_int (r : ℚ) (hr : r ≠ 0) :
    ∫ b in fundamentalSet ℚ, ψ (b * rt r) ∂(adeleMeasure ℚ) = 0 := by
  obtain ⟨x, hx⟩ : ∃ x : A ℚ, adelicChar ℚ x ≠ 1 := by
    by_contra h
    push_neg at h
    exact adelicChar_ne_one (K := ℚ) (DFunLike.ext _ _ fun x => by simpa using h x)
  have hx' : ψ x ≠ 1 := fun h => hx (Circle.ext (by simpa [ψ] using h))
  have hper : ∀ (k : ℚ) (y : A ℚ), ψ ((rt k + y) * rt r) = ψ (y * rt r) := by
    intro k y
    rw [add_mul, Pp.ψ_add, ← map_mul, Pp.ψ_rt, one_mul]
  have h := Pp.int_add (F := ℚ) (h := fun b => ψ (b * rt r)) hper (rt r⁻¹ * x)
  have hrr : rt r⁻¹ * rt r = (1 : A ℚ) := by rw [← map_mul, inv_mul_cancel₀ hr, map_one]
  have e : ∀ b : A ℚ, ψ ((b + rt r⁻¹ * x) * rt r) = ψ (b * rt r) * ψ x := by
    intro b
    rw [add_mul, Pp.ψ_add, mul_right_comm, hrr, one_mul]
  simp only [e] at h
  rw [integral_mul_const] at h
  have h1 : (∫ b in fundamentalSet ℚ, ψ (b * rt r) ∂(adeleMeasure ℚ)) * (ψ x - 1) = 0 := by
    rw [mul_sub, h, mul_one, sub_self]
  exact (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 hx')

/- English proof (translation)
Rewrite using `[measureReal_def, adeleMeasure_fundamentalSet, ENNReal.toReal_one]`.
-/
private theorem vol_one : (adeleMeasure ℚ).real (fundamentalSet ℚ) = 1 := by
  rw [measureReal_def, adeleMeasure_fundamentalSet, ENNReal.toReal_one]

/- English proof (translation)
Establish `hvol : ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) Set.univ = 1`. Rewrite using `[Measure.restrict_apply_univ, adeleMeasure_fundamentalSet]`. Use `haveI : IsProbabilityMeasure ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) := ⟨hvol⟩`. Use `set G : S → A ℚ → ℂ := fun ξ b => ψ (b * rt (q ξ - t)) * c ξ with hG`. Establish `hGc : ∀ ξ, Continuous (G ξ)` using `fun ξ => (Pp.cont_ψ.comp (continuous_id.mul continuous_const)).mul continuous_const`.

Establish `hGn : ∀ ξ b, ‖G ξ b‖ = ‖c ξ‖` using `fun ξ b => by simp [hG, Pp.norm_ψ]`. Establish `e : ∀ b : A ℚ, (∑' ξ : S, ψ (b * rt (q ξ)) * c ξ) * ψ (-(b * rt t)) = ∑' ξ, G ξ b`. Introduce `b`. Rewrite using `[← tsum_mul_right]`. Use `tsum_congr fun ξ => ?_` and prove the remaining obligations.

Establish `h0 : rt (q ξ - t) = rt (q ξ) - rt t` using `map_sub (algebraMap ℚ (A ℚ)) _ _`. Establish `: b * rt (q ξ - t) = b * rt (q ξ) + -(b * rt t)`. Rewrite using `[h0, mul_sub, sub_eq_add_neg]`. Simplify using `only [hG, this, Pp.ψ_add]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [e]`. Establish `hS` using `hasSum_integral_of_summable_integral_norm (μ := (adeleMeasure ℚ).restrict (fundamentalSet ℚ)) (F := G) (fun ξ => Pp.intOn (hGc ξ)) (by`. Simplify using `only [hGn, integral_const, probReal_univ, one_smul]`. Conclude with `hc)`. Rewrite using `[← hS.tsum_eq]`.

Establish `term : ∀ ξ : S, ∫ b in fundamentalSet ℚ, G ξ b ∂(adeleMeasure ℚ) = T.indicator c ξ`. Introduce `ξ`. Simplify using `only [hG]`. Rewrite using `[integral_mul_const]`. Distinguish the cases in `h : q ξ = t`.

Establish `hm : (ξ : Fin 4 → ℚ) ∈ T` using `(hT _).2 ⟨ξ.2, h⟩`. Simplify using `[h, hm, Set.indicator_of_mem, measureReal_def, hvol]`. Establish `hm : (ξ : Fin 4 → ℚ) ∉ T` using `fun hm => h ((hT _).1 hm).2`. Rewrite using `[char_int _ (sub_ne_zero.2 h), zero_mul, Set.indicator_of_notMem hm]`. Simplify using `only [term]`.

Rewrite using `[tsum_subtype S (T.indicator c), tsum_subtype T c]`. Use `tsum_congr fun ξ => ?_` and prove the remaining obligations. Distinguish the cases in `h : ξ ∈ T`. Simplify using `[h, ((hT _).1 h).1]`. Apply the tactic sequence `by_cases h' : ξ ∈ S <;> simp [h, h']`.
-/
private theorem fourier (S T : Set (Fin 4 → ℚ)) (q : (Fin 4 → ℚ) → ℚ) (t : ℚ) (c : (Fin 4 → ℚ) → ℂ)
    (hT : ∀ ξ, ξ ∈ T ↔ ξ ∈ S ∧ q ξ = t) (hc : Summable fun ξ : S => ‖c ξ‖) :
    ∫ b in fundamentalSet ℚ, (∑' ξ : S, ψ (b * rt (q ξ)) * c ξ) * ψ (-(b * rt t)) ∂(adeleMeasure ℚ) =
      ∑' ξ : T, c ξ := by
  have hvol : ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) Set.univ = 1 := by
    rw [Measure.restrict_apply_univ, adeleMeasure_fundamentalSet]
  haveI : IsProbabilityMeasure ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) := ⟨hvol⟩
  set G : S → A ℚ → ℂ := fun ξ b => ψ (b * rt (q ξ - t)) * c ξ with hG
  have hGc : ∀ ξ, Continuous (G ξ) := fun ξ =>
    (Pp.cont_ψ.comp (continuous_id.mul continuous_const)).mul continuous_const
  have hGn : ∀ ξ b, ‖G ξ b‖ = ‖c ξ‖ := fun ξ b => by simp [hG, Pp.norm_ψ]
  have e : ∀ b : A ℚ, (∑' ξ : S, ψ (b * rt (q ξ)) * c ξ) * ψ (-(b * rt t)) = ∑' ξ, G ξ b := by
    intro b
    rw [← tsum_mul_right]
    refine tsum_congr fun ξ => ?_
    have h0 : rt (q ξ - t) = rt (q ξ) - rt t := map_sub (algebraMap ℚ (A ℚ)) _ _
    have : b * rt (q ξ - t) = b * rt (q ξ) + -(b * rt t) := by
      rw [h0, mul_sub, sub_eq_add_neg]
    simp only [hG, this, Pp.ψ_add]
    ring
  simp only [e]
  have hS := hasSum_integral_of_summable_integral_norm (μ := (adeleMeasure ℚ).restrict (fundamentalSet ℚ))
    (F := G) (fun ξ => Pp.intOn (hGc ξ)) (by
      simp only [hGn, integral_const, probReal_univ, one_smul]
      exact hc)
  rw [← hS.tsum_eq]
  have term : ∀ ξ : S, ∫ b in fundamentalSet ℚ, G ξ b ∂(adeleMeasure ℚ) = T.indicator c ξ := by
    intro ξ
    simp only [hG]
    rw [integral_mul_const]
    by_cases h : q ξ = t
    · have hm : (ξ : Fin 4 → ℚ) ∈ T := (hT _).2 ⟨ξ.2, h⟩
      simp [h, hm, Set.indicator_of_mem, measureReal_def, hvol]
    · have hm : (ξ : Fin 4 → ℚ) ∉ T := fun hm => h ((hT _).1 hm).2
      rw [char_int _ (sub_ne_zero.2 h), zero_mul, Set.indicator_of_notMem hm]
  simp only [term]
  rw [tsum_subtype S (T.indicator c), tsum_subtype T c]
  refine tsum_congr fun ξ => ?_
  by_cases h : ξ ∈ T
  · simp [h, ((hT _).1 h).1]
  · by_cases h' : ξ ∈ S <;> simp [h, h']

/- English proof (translation)
Establish `hae : ∀ᵐ p ∂(m.prod (μ₁.prod μ₂)), ‖f p.1 p.2.1 p.2.2‖ ≤ C`. Establish `h1 : ∀ᵐ p ∂(μ₁.prod μ₂), ∀ b h, ‖f b p.1 h‖ ≤ C` using `Measure.quasiMeasurePreserving_fst.ae hb`. Establish `h2 : ∀ᵐ p ∂(m.prod (μ₁.prod μ₂)), ∀ b h, ‖f b p.2.1 h‖ ≤ C` using `Measure.quasiMeasurePreserving_snd.ae h1`. Conclude with `h2.mono fun p hp => hp _ _`. Establish `hF : Integrable (fun p : B × Z × H => f p.1 p.2.1 p.2.2) (m.prod (μ₁.prod μ₂))` using `Integrable.of_bound hf C hae`.

Establish `s1 : ∫ b, ∫ z, ∫ h, f b z h ∂μ₂ ∂μ₁ ∂m = ∫ b, ∫ p : Z × H, f b p.1 p.2 ∂(μ₁.prod μ₂) ∂m`. Use `integral_congr_ae (hF.prod_right_ae.mono fun b hb' => ?_)` and prove the remaining obligations. Conclude with `(integral_prod _ hb').symm`. Establish `s2 : ∫ b, ∫ p : Z × H, f b p.1 p.2 ∂(μ₁.prod μ₂) ∂m = ∫ p : Z × H, ∫ b, f b p.1 p.2 ∂m ∂(μ₁.prod μ₂)` using `integral_integral_swap (f := fun b (p : Z × H) => f b p.1 p.2) hF`. Rewrite using `[s1, s2]`.

Conclude with `integral_prod (fun p : Z × H => ∫ b, f b p.1 p.2 ∂m) hF.integral_prod_right`.
-/
private theorem swap3 {B Z H : Type} [MeasurableSpace B] [MeasurableSpace Z] [MeasurableSpace H]
    (m : Measure B) (μ₁ : Measure Z) (μ₂ : Measure H) [IsFiniteMeasure m] [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (f : B → Z → H → ℂ) (hf : AEStronglyMeasurable (fun p : B × Z × H => f p.1 p.2.1 p.2.2) (m.prod (μ₁.prod μ₂)))
    (C : ℝ) (hb : ∀ᵐ z ∂μ₁, ∀ b h, ‖f b z h‖ ≤ C) :
    ∫ b, ∫ z, ∫ h, f b z h ∂μ₂ ∂μ₁ ∂m = ∫ z, ∫ h, ∫ b, f b z h ∂m ∂μ₂ ∂μ₁ := by
  have hae : ∀ᵐ p ∂(m.prod (μ₁.prod μ₂)), ‖f p.1 p.2.1 p.2.2‖ ≤ C := by
    have h1 : ∀ᵐ p ∂(μ₁.prod μ₂), ∀ b h, ‖f b p.1 h‖ ≤ C := Measure.quasiMeasurePreserving_fst.ae hb
    have h2 : ∀ᵐ p ∂(m.prod (μ₁.prod μ₂)), ∀ b h, ‖f b p.2.1 h‖ ≤ C := Measure.quasiMeasurePreserving_snd.ae h1
    exact h2.mono fun p hp => hp _ _
  have hF : Integrable (fun p : B × Z × H => f p.1 p.2.1 p.2.2) (m.prod (μ₁.prod μ₂)) :=
    Integrable.of_bound hf C hae
  have s1 : ∫ b, ∫ z, ∫ h, f b z h ∂μ₂ ∂μ₁ ∂m = ∫ b, ∫ p : Z × H, f b p.1 p.2 ∂(μ₁.prod μ₂) ∂m := by
    refine integral_congr_ae (hF.prod_right_ae.mono fun b hb' => ?_)
    exact (integral_prod _ hb').symm
  have s2 : ∫ b, ∫ p : Z × H, f b p.1 p.2 ∂(μ₁.prod μ₂) ∂m = ∫ p : Z × H, ∫ b, f b p.1 p.2 ∂m ∂(μ₁.prod μ₂) :=
    integral_integral_swap (f := fun b (p : Z × H) => f b p.1 p.2) hF
  rw [s1, s2]
  exact integral_prod (fun p : Z × H => ∫ b, f b p.1 p.2 ∂m) hF.integral_prod_right

end UpperTheory.ConvolutionTheory.RankTwoDescent.UnitaryMatrixFamily

open UpperTheory.ConvolutionTheory.RankTwoDescent.UnitaryMatrixFamily in
/- English proof (translation)
Introduce `hMaj hTh E _ _ _ D W M N P ph hph φ hφ t g`. Take `⟨hs1, hsc, hnz, hng, -, -, -, -, -, -, hq⟩` from `szLaws E D`. Take `⟨b₀, a₀, k₀, hk₀, rfl⟩` from `UpperTheory.ConvolutionTheory.R2.M.iwa ℚ g`. Establish `hφc : Continuous φ.1`. Take `⟨ψ', hψ'⟩` from `UpperTheory.V.Cm.mem_range_ofCusp.2 (P.cusp φ hφ)`.

Rewrite using `[← hψ']`. Conclude with `ψ'.2.1.continuous`. Establish `hzc : Continuous fun u : IdeleGroup.normOneSubgroup E => sZ D (u : IdeleGroup E)` using `hsc.comp continuous_subtype_val`. Establish `hCc` using `(isCompact_closure_normOneFundamentalDomain E).image hzc`. Establish `hCn : ∀ k ∈ (fun u : IdeleGroup.normOneSubgroup E => sZ D (u : IdeleGroup E)) '' closure (normOneFundamentalDomain E), nu ℚ k = 1`.

Introduce and unpack `_ ⟨u, -, rfl⟩`. Conclude with `hnz _`. Establish `hapos : 0 < ab a₀` using `(IdeleGroup.ideleModule ℚ a₀).2`. Take `⟨B, hB⟩` from `hMaj E D W M N P ph hph φ hφ _ hCc hCn (ab a₀) hapos 0`. Use `set S : Set (Fin 4 → ℚ) := {ξ | qr D.δ ξ ≠ 0} with hS`.

Use `set T : Set (Fin 4 → ℚ) := {ξ | qr D.δ ξ ≠ 0 ∧ qr D.δ ξ = t} with hTd`. Use `set g₀ : G1 ℚ := nU b₀ * mD a₀ * k₀ with hg₀`. Set `x : IdeleGroup.normOneSubgroup E → G1 E → GL (Fin 2) (A E)` to `fun z h => gl h * sZ D (z : IdeleGroup E)`. Establish `hxc : Continuous fun p : IdeleGroup.normOneSubgroup E × G1 E => x p.1 p.2`. Establish `h1 : Continuous (gl : G1 E → GL (Fin 2) (A E))` using `by fun_prop`.

Conclude with `(h1.comp continuous_snd).mul (hzc.comp continuous_fst)`. Establish `hnux : ∀ z h, nu ℚ (x z h) = 1` using `fun z h => by`. Establish `: nu ℚ (x z h) = nu ℚ (gl h) * nu ℚ (sZ D (z : IdeleGroup E))` using `by simp [x, nu, map_mul]`. Rewrite using `[this, hng, hnz, one_mul]`. Set `c : IdeleGroup.normOneSubgroup E → G1 E → (Fin 4 → ℚ) → ℂ` to `fun z h ξ => (W.Om g₀ (W.L (x z h) ph)).1 (rp ξ)`.

Establish `hterm : ∀ b z h ξ, (W.Om (nU b * g₀) (W.L (x z h) ph)).1 (rp ξ) = ψ (b * rt (qr D.δ ξ)) * c z h ξ`. Introduce `b z h ξ`. Rewrite using `[map_mul, Module.End.mul_apply, W.Om_n, hq]`. Establish `hmaj` using `fun (b : A ℚ) (z : IdeleGroup.normOneSubgroup E) (hz : z ∈ normOneFundamentalDomain E) (h : G1 E) => hB b a₀ k₀ hk₀ le_rfl h (sZ D (z : IdeleGroup E)) ⟨z, subset_closure hz, rfl⟩`. Establish `hsum : ∀ z ∈ normOneFundamentalDomain E, ∀ h, Summable fun ξ : S => ‖c z h ξ‖` using `fun z hz h => (hmaj b₀ z hz h).1.subtype S`.

Establish `hnU : ∀ b, nU (b + b₀) * mD a₀ * k₀ = nU b * g₀`. Introduce `b`. Rewrite using `[UpperTheory.ConvolutionTheory.R2.M.nU_add]`. Simplify using `only [hg₀, mul_assoc]`. Set `T' : A ℚ → IdeleGroup.normOneSubgroup E → G1 E → ℂ` to `fun b z h => ThOn S (W.Om (nU b * g₀) (W.L (x z h) ph)).1 * φ.1 (x z h)`.

Set `f : A ℚ → IdeleGroup.normOneSubgroup E → G1 E → ℂ` to `fun b z h => T' b z h * ψ (-(b * rt t))`. Establish `hbd : ∀ z ∈ normOneFundamentalDomain E, ∀ b h, ‖f b z h‖ ≤ B`. Introduce `z hz b h`. Establish `h1` using `(hmaj (b + b₀) z hz h).1`. Establish `h3` using `(hmaj (b + b₀) z hz h).2.2`.

Simplify using `only [hnU, pow_zero, mul_one] at h1 h3`. Establish `h2 : ‖ThOn S (W.Om (nU b * g₀) (W.L (x z h) ph)).1‖ ≤ ∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0}, ‖(W.Om (nU b * g₀) (W.L (gl h * sZ D (z : IdeleGroup E)) ph)).1 (rp ξ.1)‖` using `norm_tsum_le_tsum_norm (h1.subtype S)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [f, T', norm_mul, Pp.norm_ψ, mul_one]`. Use `_ ≤ _ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)`.

Use `_ ≤ B := h3`. Establish `hNc : Continuous fun b : A ℚ => nU b`. Use `Continuous.subtype_mk (continuous_matrix fun i j => ?_) _` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [nU] <;> fun_prop`. Establish `hcont : Continuous fun p : A ℚ × IdeleGroup.normOneSubgroup E × G1 E => f p.1 p.2.1 p.2.2`.

Establish `hp : Continuous fun p : A ℚ × IdeleGroup.normOneSubgroup E × G1 E => (nU p.1 * g₀, x p.2.1 p.2.2)` using `((hNc.comp continuous_fst).mul continuous_const).prodMk (hxc.comp continuous_snd)`. Establish `h1` using `(hTh E D W M N P ph hph S).comp_continuous hp (fun p => hnux _ _)`. Conclude with `(h1.mul (hφc.comp (hxc.comp continuous_snd))).mul (Pp.cont_ψ.comp ((continuous_fst.mul continuous_const).neg))`. Use `haveI : IsFiniteMeasure ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) := ⟨by rw [Measure.restrict_apply_univ, adeleMeasure_fundamentalSet]; exact ENNReal.one_lt_top⟩`. Use `haveI : IsFiniteMeasure ((normOneMeasure E).restrict (normOneFundamentalDomain E)) := ⟨by rw [Measure.restrict_apply_univ]; exact normOneMeasure_normOneFundamentalDomain_lt_top E⟩`.

Use `haveI : IsFiniteMeasure (N.μ.restrict N.D) := ⟨by rw [Measure.restrict_apply_univ]; exact hV E N⟩`. Establish `step : ∀ b, fOn W N S ph φ.1 (nU b * g₀) * ψ (-(b * rt t)) = ∫ z in normOneFundamentalDomain E, ∫ h in N.D, f b z h ∂N.μ ∂normOneMeasure E`. Introduce `b`. Express the relevant statement in the definitionally equal form `(∫ z in normOneFundamentalDomain E, ∫ h in N.D, T' b z h ∂N.μ ∂normOneMeasure E) * _ = _`. Rewrite using `[← integral_mul_const]`.

Use `integral_congr_ae (ae_of_all _ fun z => ?_)` and prove the remaining obligations. Conclude with `(integral_mul_const _ _).symm`. Simplify using `only [step]`. Rewrite using `[swap3 _ _ _ f hcont.aestronglyMeasurable B (ae_restrict_of_forall_mem (measurableSet_normOneFundamentalDomain E) hbd), vol_one, Complex.ofReal_one, one_mul]`. Express the relevant statement in the definitionally equal form `_ = ∫ z in normOneFundamentalDomain E, ∫ h in N.D, ThOn T (W.Om g₀ (W.L (x z h) ph)).1 * φ.1 (x z h) ∂N.μ ∂normOneMeasure E`.

Use `setIntegral_congr_fun (measurableSet_normOneFundamentalDomain E) fun z hz => ?_` and prove the remaining obligations. Use `integral_congr_ae (ae_of_all _ fun h => ?_)` and prove the remaining obligations. Establish `e : ∀ b, f b z h = ((∑' ξ : S, ψ (b * rt (qr D.δ ξ)) * c z h ξ) * ψ (-(b * rt t))) * φ.1 (x z h)`. Introduce `b`. Simplify using `only [f, T', ThOn, hterm]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e]`. Rewrite using `[integral_mul_const, fourier S T (qr D.δ) t (c z h) (fun ξ => Iff.rfl) (hsum z hz h)]`. Both sides reduce to the same expression.
-/
private theorem coefOf (hV : VolE) :
    Maj → ThCont → Coef := by
  intro hMaj hTh E _ _ _ D W M N P ph hph φ hφ t g
  obtain ⟨hs1, hsc, hnz, hng, -, -, -, -, -, -, hq⟩ := szLaws E D
  obtain ⟨b₀, a₀, k₀, hk₀, rfl⟩ := UpperTheory.ConvolutionTheory.R2.M.iwa ℚ g
  have hφc : Continuous φ.1 := by
    obtain ⟨ψ', hψ'⟩ := UpperTheory.V.Cm.mem_range_ofCusp.2 (P.cusp φ hφ)
    rw [← hψ']
    exact ψ'.2.1.continuous
  have hzc : Continuous fun u : IdeleGroup.normOneSubgroup E => sZ D (u : IdeleGroup E) :=
    hsc.comp continuous_subtype_val
  have hCc := (isCompact_closure_normOneFundamentalDomain E).image hzc
  have hCn : ∀ k ∈ (fun u : IdeleGroup.normOneSubgroup E => sZ D (u : IdeleGroup E)) '' closure (normOneFundamentalDomain E),
      nu ℚ k = 1 := by
    rintro _ ⟨u, -, rfl⟩
    exact hnz _
  have hapos : 0 < ab a₀ := (IdeleGroup.ideleModule ℚ a₀).2
  obtain ⟨B, hB⟩ := hMaj E D W M N P ph hph φ hφ _ hCc hCn (ab a₀) hapos 0
  set S : Set (Fin 4 → ℚ) := {ξ | qr D.δ ξ ≠ 0} with hS
  set T : Set (Fin 4 → ℚ) := {ξ | qr D.δ ξ ≠ 0 ∧ qr D.δ ξ = t} with hTd
  set g₀ : G1 ℚ := nU b₀ * mD a₀ * k₀ with hg₀
  let x : IdeleGroup.normOneSubgroup E → G1 E → GL (Fin 2) (A E) := fun z h => gl h * sZ D (z : IdeleGroup E)
  have hxc : Continuous fun p : IdeleGroup.normOneSubgroup E × G1 E => x p.1 p.2 := by
    have h1 : Continuous (gl : G1 E → GL (Fin 2) (A E)) := by fun_prop
    exact (h1.comp continuous_snd).mul (hzc.comp continuous_fst)
  have hnux : ∀ z h, nu ℚ (x z h) = 1 := fun z h => by
    have : nu ℚ (x z h) = nu ℚ (gl h) * nu ℚ (sZ D (z : IdeleGroup E)) := by simp [x, nu, map_mul]
    rw [this, hng, hnz, one_mul]
  let c : IdeleGroup.normOneSubgroup E → G1 E → (Fin 4 → ℚ) → ℂ := fun z h ξ => (W.Om g₀ (W.L (x z h) ph)).1 (rp ξ)
  have hterm : ∀ b z h ξ, (W.Om (nU b * g₀) (W.L (x z h) ph)).1 (rp ξ) = ψ (b * rt (qr D.δ ξ)) * c z h ξ := by
    intro b z h ξ
    rw [map_mul, Module.End.mul_apply, W.Om_n, hq]
  have hmaj := fun (b : A ℚ) (z : IdeleGroup.normOneSubgroup E) (hz : z ∈ normOneFundamentalDomain E) (h : G1 E) =>
    hB b a₀ k₀ hk₀ le_rfl h (sZ D (z : IdeleGroup E)) ⟨z, subset_closure hz, rfl⟩
  have hsum : ∀ z ∈ normOneFundamentalDomain E, ∀ h, Summable fun ξ : S => ‖c z h ξ‖ := fun z hz h =>
    (hmaj b₀ z hz h).1.subtype S
  have hnU : ∀ b, nU (b + b₀) * mD a₀ * k₀ = nU b * g₀ := by
    intro b
    rw [UpperTheory.ConvolutionTheory.R2.M.nU_add]
    simp only [hg₀, mul_assoc]
  let T' : A ℚ → IdeleGroup.normOneSubgroup E → G1 E → ℂ := fun b z h =>
    ThOn S (W.Om (nU b * g₀) (W.L (x z h) ph)).1 * φ.1 (x z h)
  let f : A ℚ → IdeleGroup.normOneSubgroup E → G1 E → ℂ := fun b z h => T' b z h * ψ (-(b * rt t))
  have hbd : ∀ z ∈ normOneFundamentalDomain E, ∀ b h, ‖f b z h‖ ≤ B := by
    intro z hz b h
    have h1 := (hmaj (b + b₀) z hz h).1
    have h3 := (hmaj (b + b₀) z hz h).2.2
    simp only [hnU, pow_zero, mul_one] at h1 h3
    have h2 : ‖ThOn S (W.Om (nU b * g₀) (W.L (x z h) ph)).1‖ ≤
        ∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0}, ‖(W.Om (nU b * g₀) (W.L (gl h * sZ D (z : IdeleGroup E)) ph)).1 (rp ξ.1)‖ :=
      norm_tsum_le_tsum_norm (h1.subtype S)
    calc ‖f b z h‖ = ‖ThOn S (W.Om (nU b * g₀) (W.L (x z h) ph)).1‖ * ‖φ.1 (x z h)‖ := by
          simp only [f, T', norm_mul, Pp.norm_ψ, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ ≤ B := h3
  have hNc : Continuous fun b : A ℚ => nU b := by
    refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
    fin_cases i <;> fin_cases j <;> simp [nU] <;> fun_prop
  have hcont : Continuous fun p : A ℚ × IdeleGroup.normOneSubgroup E × G1 E => f p.1 p.2.1 p.2.2 := by
    have hp : Continuous fun p : A ℚ × IdeleGroup.normOneSubgroup E × G1 E => (nU p.1 * g₀, x p.2.1 p.2.2) :=
      ((hNc.comp continuous_fst).mul continuous_const).prodMk (hxc.comp continuous_snd)
    have h1 := (hTh E D W M N P ph hph S).comp_continuous hp (fun p => hnux _ _)
    exact (h1.mul (hφc.comp (hxc.comp continuous_snd))).mul
      (Pp.cont_ψ.comp ((continuous_fst.mul continuous_const).neg))
  haveI : IsFiniteMeasure ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) :=
    ⟨by rw [Measure.restrict_apply_univ, adeleMeasure_fundamentalSet]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure ((normOneMeasure E).restrict (normOneFundamentalDomain E)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact normOneMeasure_normOneFundamentalDomain_lt_top E⟩
  haveI : IsFiniteMeasure (N.μ.restrict N.D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hV E N⟩
  have step : ∀ b, fOn W N S ph φ.1 (nU b * g₀) * ψ (-(b * rt t)) =
      ∫ z in normOneFundamentalDomain E, ∫ h in N.D, f b z h ∂N.μ ∂normOneMeasure E := by
    intro b
    change (∫ z in normOneFundamentalDomain E, ∫ h in N.D, T' b z h ∂N.μ ∂normOneMeasure E) * _ = _
    rw [← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    exact (integral_mul_const _ _).symm
  simp only [step]
  rw [swap3 _ _ _ f hcont.aestronglyMeasurable B
    (ae_restrict_of_forall_mem (measurableSet_normOneFundamentalDomain E) hbd), vol_one, Complex.ofReal_one, one_mul]
  change _ = ∫ z in normOneFundamentalDomain E, ∫ h in N.D, ThOn T (W.Om g₀ (W.L (x z h) ph)).1 * φ.1 (x z h) ∂N.μ ∂normOneMeasure E
  refine setIntegral_congr_fun (measurableSet_normOneFundamentalDomain E) fun z hz => ?_
  refine integral_congr_ae (ae_of_all _ fun h => ?_)
  have e : ∀ b, f b z h = ((∑' ξ : S, ψ (b * rt (qr D.δ ξ)) * c z h ξ) * ψ (-(b * rt t))) * φ.1 (x z h) := by
    intro b
    simp only [f, T', ThOn, hterm]
    ring
  simp only [e]
  rw [integral_mul_const, fourier S T (qr D.δ) t (c z h) (fun ξ => Iff.rfl) (hsum z hz h)]
  rfl

/- English proof (translation)
The claim follows from `coefOf volE`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.coef :
    Maj → ThCont → Coef :=
  coefOf volE
