import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubS

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Measure NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Pointwise

namespace Formalism.L2.S.Pv.HaarSubS

section Abs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Use `conv_rhs => rw [← hμ]`. Rewrite using `[lintegral_map hg hφ]`.
-/
private theorem lintegral_comp_of_map_eq {μ : Measure G} {φ : G → G} {g : G → ℝ≥0∞} (hφ : Measurable φ) (hμ : μ.map φ = μ)
    (hg : Measurable g) : ∫⁻ x, g (φ x) ∂μ = ∫⁻ x, g x ∂μ := by
  conv_rhs => rw [← hμ]
  rw [lintegral_map hg hφ]

/- English proof (translation)
Establish `hae_ν : ∀ᵐ y ∂ν, y ∈ H` using `(ae_iff (p := fun a => a ∈ H)).mpr hνc`. Establish `hae_μ : ∀ᵐ x ∂μ, x ∈ H` using `(ae_iff (p := fun a => a ∈ H)).mpr hμc`. Apply `Measure.ext_of_lintegral` to reduce the goal to its premises. Introduce `f hf`. Establish `hF : Measurable (Function.uncurry fun y x => f (y⁻¹ * x))` using `hf.comp (measurable_fst.inv.mul measurable_snd)`.

Rewrite using `[lintegral_smul_measure, lintegral_map hf (measurable_inv : Measurable fun x : G => x⁻¹)]`. Combine the equalities or inequalities in the displayed calculation. Apply `lintegral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hae_ν] with y hy`. Conclude with `(lintegral_comp_of_map_eq (φ := fun x => y⁻¹ * x) (g := f) (measurable_const_mul _) (hμl _ (hinvH y hy)) hf).symm`.

Use `_ = ∫⁻ x, ∫⁻ y, f (y⁻¹ * x) ∂ν ∂μ := lintegral_lintegral_swap hF.aemeasurable`. Use `_ = ∫⁻ x, ∫⁻ y, f y⁻¹ ∂ν ∂μ := by`. Apply `lintegral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hae_μ] with x hx`. Combine the equalities or inequalities in the displayed calculation.

Use `_ = μ Set.univ * ∫⁻ y, f y⁻¹ ∂ν := by rw [lintegral_const, mul_comm]`.
-/
theorem eq_smul_inv {H : Set G} (hHm : MeasurableSet H) (hinvH : ∀ h ∈ H, h⁻¹ ∈ H) {μ ν : Measure G}
    [SFinite μ] [IsProbabilityMeasure ν] (hμc : μ Hᶜ = 0) (hμl : ∀ h ∈ H, μ.map (fun x => h * x) = μ)
    (hνc : ν Hᶜ = 0) (hνl : ∀ h ∈ H, ν.map (fun x => h * x) = ν) :
    μ = μ Set.univ • ν.map (fun x => x⁻¹) := by
  have hae_ν : ∀ᵐ y ∂ν, y ∈ H := (ae_iff (p := fun a => a ∈ H)).mpr hνc
  have hae_μ : ∀ᵐ x ∂μ, x ∈ H := (ae_iff (p := fun a => a ∈ H)).mpr hμc
  apply Measure.ext_of_lintegral
  intro f hf
  have hF : Measurable (Function.uncurry fun y x => f (y⁻¹ * x)) :=
    hf.comp (measurable_fst.inv.mul measurable_snd)
  rw [lintegral_smul_measure, lintegral_map hf (measurable_inv : Measurable fun x : G => x⁻¹)]
  calc ∫⁻ x, f x ∂μ = ∫⁻ y, ∫⁻ x, f x ∂μ ∂ν := by rw [lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ y, ∫⁻ x, f (y⁻¹ * x) ∂μ ∂ν := by
        apply lintegral_congr_ae
        filter_upwards [hae_ν] with y hy
        exact (lintegral_comp_of_map_eq (φ := fun x => y⁻¹ * x) (g := f) (measurable_const_mul _)
          (hμl _ (hinvH y hy)) hf).symm
    _ = ∫⁻ x, ∫⁻ y, f (y⁻¹ * x) ∂ν ∂μ := lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ x, ∫⁻ y, f y⁻¹ ∂ν ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hae_μ] with x hx
        calc ∫⁻ y, f (y⁻¹ * x) ∂ν = ∫⁻ z, f ((x * z)⁻¹ * x) ∂ν :=
              (lintegral_comp_of_map_eq (φ := fun z => x * z) (g := fun y => f (y⁻¹ * x)) (measurable_const_mul x)
                (hνl x hx) (hf.comp (measurable_inv.mul_const x))).symm
          _ = ∫⁻ z, f z⁻¹ ∂ν := lintegral_congr fun z => by rw [show (x * z)⁻¹ * x = z⁻¹ by group]
    _ = μ Set.univ * ∫⁻ y, f y⁻¹ ∂ν := by rw [lintegral_const, mul_comm]

/- English proof (translation)
Establish `hμeq` using `eq_smul_inv hHm hinvH hμc hμl hνc hνl`. Establish `hνeq` using `eq_smul_inv hHm hinvH hνc hνl hνc hνl`. Rewrite `hνeq` using `[measure_univ, one_smul]`. Establish `hS : ∀ S, μ S = μ Set.univ * (ν.map (fun x => x⁻¹)) S`. Introduce `S`.

Use `conv_lhs => rw [hμeq]`. Rewrite using `[Measure.smul_apply, smul_eq_mul]`. Establish `hfin : μ Set.univ < ⊤`. Assume the negation of the conclusion as `hinf`. Rewrite `hinf` using `[not_lt, top_le_iff]`.

Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, μ (spanningSets μ i) ≠ 0 := by`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Establish `h0 : μ Set.univ = 0`. Rewrite using `[← iUnion_spanningSets μ]`.

Conclude with `measure_iUnion_null hall`. Rewrite `hinf` using `[h0]`. Conclude with `ENNReal.zero_ne_top hinf`. Establish `hlt` using `measure_spanningSets_lt_top μ i`. Rewrite `hlt`, `hi` using `[hS, hinf]`.

Establish `h0 : (ν.map (fun x => x⁻¹)) (spanningSets μ i) = 0`. Assume the negation of the conclusion as `h`. Rewrite `hlt` using `[ENNReal.top_mul h]`. Conclude with `lt_irrefl _ hlt`. Rewrite `hi` using `[h0, mul_zero]`.

Conclude with `hi rfl`. Establish `hint : ∀ g : G → ℝ≥0∞, Measurable g → ∫⁻ x, g x ∂μ = μ Set.univ * ∫⁻ y, g y⁻¹ ∂ν`. Introduce `g hg`. Use `conv_lhs => rw [hμeq]`. Simplify using `only [lintegral_smul_measure, smul_eq_mul]`.

Rewrite using `[lintegral_map hg (measurable_inv : Measurable fun x : G => x⁻¹)]`. Use `⟨⟨hfin⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `h hh`. Apply `Measure.ext_of_lintegral` to reduce the goal to its premises. Introduce `f hf`.

Establish `hstep : ∫⁻ y, f (y⁻¹ * h) ∂ν = ∫⁻ y, f y⁻¹ ∂ν`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(lintegral_map hf (measurable_mul_const h)).trans ((hint (fun x => f (x * h)) (hf.comp (measurable_mul_const h))).trans ((congrArg (fun c => μ Set.univ * c) hstep).trans (hint f hf).symm))`. Apply `Measure.ext_of_lintegral` to reduce the goal to its premises. Introduce `f hf`.

Establish `hstep2 : ∫⁻ y, f y⁻¹⁻¹ ∂ν = ∫⁻ y, f y⁻¹ ∂ν`. Simplify using `only [inv_inv]`. Use `conv_lhs => rw [hνeq]`. Rewrite using `[lintegral_map hf (measurable_inv : Measurable fun x : G => x⁻¹)]`. Conclude with `(lintegral_map hf measurable_inv).trans ((hint (fun x => f x⁻¹) (hf.comp measurable_inv)).trans ((congrArg (fun c => μ Set.univ * c) hstep2).trans (hint f hf).symm))`.
-/
theorem finite_bi {H : Set G} (hHm : MeasurableSet H) (hinvH : ∀ h ∈ H, h⁻¹ ∈ H) {μ ν : Measure G}
    [SigmaFinite μ] [IsProbabilityMeasure ν] (hμc : μ Hᶜ = 0) (hμl : ∀ h ∈ H, μ.map (fun x => h * x) = μ)
    (hνc : ν Hᶜ = 0) (hνl : ∀ h ∈ H, ν.map (fun x => h * x) = ν) :
    IsFiniteMeasure μ ∧ (∀ h ∈ H, μ.map (fun x => x * h) = μ) ∧ μ.map (fun x => x⁻¹) = μ := by
  have hμeq := eq_smul_inv hHm hinvH hμc hμl hνc hνl
  have hνeq := eq_smul_inv hHm hinvH hνc hνl hνc hνl
  rw [measure_univ, one_smul] at hνeq
  have hS : ∀ S, μ S = μ Set.univ * (ν.map (fun x => x⁻¹)) S := by
    intro S
    conv_lhs => rw [hμeq]
    rw [Measure.smul_apply, smul_eq_mul]
  have hfin : μ Set.univ < ⊤ := by
    by_contra hinf
    rw [not_lt, top_le_iff] at hinf
    obtain ⟨i, hi⟩ : ∃ i, μ (spanningSets μ i) ≠ 0 := by
      by_contra hall
      push_neg at hall
      have h0 : μ Set.univ = 0 := by
        rw [← iUnion_spanningSets μ]
        exact measure_iUnion_null hall
      rw [h0] at hinf
      exact ENNReal.zero_ne_top hinf
    have hlt := measure_spanningSets_lt_top μ i
    rw [hS, hinf] at hlt hi
    have h0 : (ν.map (fun x => x⁻¹)) (spanningSets μ i) = 0 := by
      by_contra h
      rw [ENNReal.top_mul h] at hlt
      exact lt_irrefl _ hlt
    rw [h0, mul_zero] at hi
    exact hi rfl
  have hint : ∀ g : G → ℝ≥0∞, Measurable g → ∫⁻ x, g x ∂μ = μ Set.univ * ∫⁻ y, g y⁻¹ ∂ν := by
    intro g hg
    conv_lhs => rw [hμeq]
    simp only [lintegral_smul_measure, smul_eq_mul]
    rw [lintegral_map hg (measurable_inv : Measurable fun x : G => x⁻¹)]
  refine ⟨⟨hfin⟩, ?_, ?_⟩
  · intro h hh
    apply Measure.ext_of_lintegral
    intro f hf
    have hstep : ∫⁻ y, f (y⁻¹ * h) ∂ν = ∫⁻ y, f y⁻¹ ∂ν := by
      calc ∫⁻ y, f (y⁻¹ * h) ∂ν = ∫⁻ z, f ((h * z)⁻¹ * h) ∂ν :=
            (lintegral_comp_of_map_eq (φ := fun z => h * z) (g := fun y => f (y⁻¹ * h)) (measurable_const_mul h)
              (hνl h hh) (hf.comp (measurable_inv.mul_const h))).symm
        _ = ∫⁻ z, f z⁻¹ ∂ν := lintegral_congr fun z => by rw [show (h * z)⁻¹ * h = z⁻¹ by group]
    exact (lintegral_map hf (measurable_mul_const h)).trans
      ((hint (fun x => f (x * h)) (hf.comp (measurable_mul_const h))).trans
        ((congrArg (fun c => μ Set.univ * c) hstep).trans (hint f hf).symm))
  · apply Measure.ext_of_lintegral
    intro f hf
    have hstep2 : ∫⁻ y, f y⁻¹⁻¹ ∂ν = ∫⁻ y, f y⁻¹ ∂ν := by
      simp only [inv_inv]
      conv_lhs => rw [hνeq]
      rw [lintegral_map hf (measurable_inv : Measurable fun x : G => x⁻¹)]
    exact (lintegral_map hf measurable_inv).trans
      ((hint (fun x => f x⁻¹) (hf.comp measurable_inv)).trans
        ((congrArg (fun c => μ Set.univ * c) hstep2).trans (hint f hf).symm))

end Abs

section Glob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def HuSub (hD : SDecomp) {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) :
    Subgroup X.B.I.Ginf where
  carrier := Hu X u
  mul_mem' {a b} ha hb := (hD D X u).2.2.2.2.2.2.2.2.2.1 a ha b hb
  one_mem' := (hD D X u).2.2.2.2.2.2.2.2.1
  inv_mem' {a} ha := (hD D X u).2.2.2.2.2.2.2.2.2.2.1 a ha

/- English proof (translation)
Introduce `D X u`. Take `⟨hsf, _, hc, hl⟩` from `X.muH_haar u`. Use `haveI := hsf`. Establish `hd` using `hD D X u`. Establish `hcomp : IsCompact (Hu X u)` using `hd.2.2.2.2.2.2.2.1`.

Establish `hinv : ∀ a ∈ Hu X u, a⁻¹ ∈ Hu X u` using `hd.2.2.2.2.2.2.2.2.2.2.1`. Establish `hHm : MeasurableSet (Hu X u)` using `hcomp.isClosed.measurableSet`. Set `K` to `HuSub hD X u`. Use `haveI : CompactSpace K := isCompact_iff_compactSpace.mp hcomp`. Set `μK : Measure K` to `haarMeasure ⊤`.

Establish `hμK1 : μK Set.univ = 1`. Establish `h` using `haarMeasure_self (G := K) (K₀ := ⊤)`. Rewrite `h` using `[TopologicalSpace.PositiveCompacts.coe_top]`. Then use the resulting hypothesis. Set `ν : Measure X.B.I.Ginf` to `μK.map Subtype.val`. Use `haveI : IsProbabilityMeasure ν := ⟨by rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ]; exact hμK1⟩`.

Establish `hνc : ν (Hu X u)ᶜ = 0`. Rewrite using `[Measure.map_apply measurable_subtype_coe hHm.compl]`. Establish `he : (Subtype.val ⁻¹' (Hu X u)ᶜ : Set K) = ∅`. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]`.

Conclude with `x.2`. Rewrite using `[he, measure_empty]`. Establish `hνl : ∀ h ∈ Hu X u, ν.map (fun x => h * x) = ν`. Introduce `h hh`. Rewrite using `[Measure.map_map (measurable_const_mul h) measurable_subtype_coe]`.

Establish `he : (fun x => h * x) ∘ (Subtype.val : K → X.B.I.Ginf) = Subtype.val ∘ (fun y : K => (⟨h, hh⟩ : K) * y)` using `rfl`. Rewrite using `[he, ← Measure.map_map measurable_subtype_coe (measurable_const_mul _), map_mul_left_eq_self]`. Take `⟨h1, h2, h3⟩` from `finite_bi hHm hinv hc hl hνc hνl`. Conclude with `⟨h1, h2, h3⟩`.
-/
theorem measH_of (hD : SDecomp) : MeasH := by
  intro D X u
  obtain ⟨hsf, _, hc, hl⟩ := X.muH_haar u
  haveI := hsf
  have hd := hD D X u
  have hcomp : IsCompact (Hu X u) := hd.2.2.2.2.2.2.2.1
  have hinv : ∀ a ∈ Hu X u, a⁻¹ ∈ Hu X u := hd.2.2.2.2.2.2.2.2.2.2.1
  have hHm : MeasurableSet (Hu X u) := hcomp.isClosed.measurableSet
  let K := HuSub hD X u
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hcomp
  let μK : Measure K := haarMeasure ⊤
  have hμK1 : μK Set.univ = 1 := by
    have h := haarMeasure_self (G := K) (K₀ := ⊤)
    rwa [TopologicalSpace.PositiveCompacts.coe_top] at h
  let ν : Measure X.B.I.Ginf := μK.map Subtype.val
  haveI : IsProbabilityMeasure ν :=
    ⟨by rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ]; exact hμK1⟩
  have hνc : ν (Hu X u)ᶜ = 0 := by
    rw [Measure.map_apply measurable_subtype_coe hHm.compl]
    have he : (Subtype.val ⁻¹' (Hu X u)ᶜ : Set K) = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
      exact x.2
    rw [he, measure_empty]
  have hνl : ∀ h ∈ Hu X u, ν.map (fun x => h * x) = ν := by
    intro h hh
    rw [Measure.map_map (measurable_const_mul h) measurable_subtype_coe]
    have he : (fun x => h * x) ∘ (Subtype.val : K → X.B.I.Ginf) =
        Subtype.val ∘ (fun y : K => (⟨h, hh⟩ : K) * y) := rfl
    rw [he, ← Measure.map_map measurable_subtype_coe (measurable_const_mul _), map_mul_left_eq_self]
  obtain ⟨h1, h2, h3⟩ := finite_bi hHm hinv hc hl hνc hνl
  exact ⟨h1, h2, h3⟩

end Glob

end Formalism.L2.S.Pv.HaarSubS
