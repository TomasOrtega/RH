import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormModerateGrowthCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalWhittakerCoefficientLinearArchimedeanKerneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanKernelSpanCuspFormRightInvariantOpenStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory Topology

namespace GlobalTheory.JSW.MirSemi

open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Unfold `whit whittaker`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `X`. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_assoc]`.
-/
theorem whit_smul_fun (c : ℂ) (F : GA E a → ℂ) (g : GA E a) : whit (c • F) g = c * whit F g := by
  unfold whit whittaker
  rw [← integral_const_mul]
  congr 1
  funext X
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

/- English proof (translation)
Simplify using `only [whit, whittaker, mul_assoc]`.
-/
theorem whit_mul_right_fun (F : GA E a → ℂ) (g h : GA E a) : whit F (g * h) = whit (fun z => F (z * h)) g := by
  simp only [whit, whittaker, mul_assoc]

/- English proof (translation)
Unfold `height`. Establish `h1 : Continuous fun y : GL (Fin a) (Cinf E) => toL y.val` using `continuous_pi fun i => continuous_pi fun j => Units.continuous_val.matrix_elem i j`. Establish `h2 : Continuous fun y : GL (Fin a) (Cinf E) => toL (y⁻¹).val` using `continuous_pi fun i => continuous_pi fun j => Units.continuous_coe_inv.matrix_elem i j`. Conclude with `(continuous_const.add h1.norm).add h2.norm`.
-/
theorem continuous_heightInf : Continuous (fun y : GL (Fin a) (Cinf E) => height y) := by
  unfold height
  have h1 : Continuous fun y : GL (Fin a) (Cinf E) => toL y.val :=
    continuous_pi fun i => continuous_pi fun j => Units.continuous_val.matrix_elem i j
  have h2 : Continuous fun y : GL (Fin a) (Cinf E) => toL (y⁻¹).val :=
    continuous_pi fun i => continuous_pi fun j => Units.continuous_coe_inv.matrix_elem i j
  exact (continuous_const.add h1.norm).add h2.norm

/- English proof (translation)
Unfold `height`. Check the signs of the components of the expression.
-/
theorem height_pos_inf (y : GL (Fin a) (Cinf E)) : 0 < height y := by
  unfold height; positivity

/- English proof (translation)
Use `set K : Set (GA E a) := (fun X => uGL X * g) '' closure (vecDomain E (Pos a)) with hKdef`. Establish `hK : IsCompact K` using `isCompact_closure_vecDomain.image (continuous_uGL.mul continuous_const)`. Take `⟨C, N, hC⟩` from `hg K hK`. Use `set f : GL (Fin a) (Cinf E) → (Pos a → Ad E) → ℂ := fun y X => F (uGL X * (g * infGL E a y)) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) with hfdef`. Establish `hwf : ∀ y, whit F (g * infGL E a y) = ∫ X in vecDomain E (Pos a), f y X ∂vecMeasure E (Pos a)` using `fun y => rfl`.

Establish `hb : ∀ y, ∀ X ∈ vecDomain E (Pos a), ‖f y X‖ ≤ C * height y ^ N`. Introduce `y X hX`. Simplify using `only [hfdef]`. Rewrite using `[norm_mul, Circle.norm_coe, mul_one, ← mul_assoc]`. Conclude with `hC _ ⟨X, subset_closure hX, rfl⟩ y`.

Establish `hbound : ∀ y, ‖whit F (g * infGL E a y)‖ ≤ C * height y ^ N`. Introduce `y`. Establish `h` using `norm_setIntegral_le_of_norm_le_const (μ := vecMeasure E (Pos a)) (s := vecDomain E (Pos a)) (C := C * height y ^ N) (f := f y) (by rw [vecMeasure_vecDomain]; exact ENNReal.one_lt_top) (hb y)`. Rewrite `h` using `[measureReal_def, vecMeasure_vecDomain, ENNReal.toReal_one, mul_one, ← hwf]`. Then use the resulting hypothesis. Use `⟨?_, C, N, hbound⟩` and prove the remaining obligations.

Use `haveI : IsFiniteMeasure ((vecMeasure E (Pos a)).restrict (vecDomain E (Pos a))) := ⟨by rw [Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩`. Establish `hchar : Continuous fun X : Pos a → Ad E => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ)` using `continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg)`. Establish `hfc : ∀ y, Continuous (f y)` using `fun y => (hc.comp (continuous_uGL.mul continuous_const)).mul hchar`. Use `haveI : FirstCountableTopology (MulOpposite (Matrix (Fin a) (Fin a) (Cinf E))) := (MulOpposite.opHomeomorph (M := Matrix (Fin a) (Fin a) (Cinf E))).symm.isInducing.firstCountableTopology`. Use `haveI : FirstCountableTopology (GL (Fin a) (Cinf E)) := Units.isEmbedding_embedProduct.isInducing.firstCountableTopology`.

Rewrite using `[continuous_iff_continuousAt]`. Introduce `y₀`. Establish `hev : ∀ᶠ y in 𝓝 y₀, height y < height y₀ + 1` using `continuous_heightInf.continuousAt.eventually (gt_mem_nhds (lt_add_one _))`. Simplify using `only [hwf]`. Use `continuousAt_of_dominated (bound := fun _ => max C 0 * (height y₀ + 1) ^ N) ?_ ?_ (integrable_const _) ?_` and prove the remaining obligations.

Conclude with `Filter.Eventually.of_forall fun y => (hfc y).aestronglyMeasurable`. Use `filter_upwards [hev] with y hy`. Use `ae_restrict_of_forall_mem measurableSet_vecDomain fun X hX => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `Filter.Eventually.of_forall fun X => ?_` and prove the remaining obligations.

Establish `: Continuous fun y : GL (Fin a) (Cinf E) => f y X` using `(hc.comp (continuous_const.mul (continuous_const.mul GlobalTheory.ConstTermSmooth.continuous_infGL))).mul continuous_const`. Conclude with `this.continuousAt`.
-/
theorem whit_infGL_growth {F : GA E a → ℂ} (hc : Continuous F)
    (hg : ∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
      ‖F (g * infGL E a y)‖ ≤ C * height y ^ N) (g : GA E a) :
    Continuous (fun y : GL (Fin a) (Cinf E) => whit F (g * infGL E a y)) ∧
      ∃ (C : ℝ) (N : ℕ), ∀ y, ‖whit F (g * infGL E a y)‖ ≤ C * height y ^ N := by
  set K : Set (GA E a) := (fun X => uGL X * g) '' closure (vecDomain E (Pos a)) with hKdef
  have hK : IsCompact K := isCompact_closure_vecDomain.image (continuous_uGL.mul continuous_const)
  obtain ⟨C, N, hC⟩ := hg K hK
  set f : GL (Fin a) (Cinf E) → (Pos a → Ad E) → ℂ := fun y X =>
    F (uGL X * (g * infGL E a y)) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) with hfdef
  have hwf : ∀ y, whit F (g * infGL E a y) = ∫ X in vecDomain E (Pos a), f y X ∂vecMeasure E (Pos a) :=
    fun y => rfl
  have hb : ∀ y, ∀ X ∈ vecDomain E (Pos a), ‖f y X‖ ≤ C * height y ^ N := by
    intro y X hX
    simp only [hfdef]
    rw [norm_mul, Circle.norm_coe, mul_one, ← mul_assoc]
    exact hC _ ⟨X, subset_closure hX, rfl⟩ y
  have hbound : ∀ y, ‖whit F (g * infGL E a y)‖ ≤ C * height y ^ N := by
    intro y
    have h := norm_setIntegral_le_of_norm_le_const (μ := vecMeasure E (Pos a)) (s := vecDomain E (Pos a))
      (C := C * height y ^ N) (f := f y) (by rw [vecMeasure_vecDomain]; exact ENNReal.one_lt_top) (hb y)
    rwa [measureReal_def, vecMeasure_vecDomain, ENNReal.toReal_one, mul_one, ← hwf] at h
  refine ⟨?_, C, N, hbound⟩
  haveI : IsFiniteMeasure ((vecMeasure E (Pos a)).restrict (vecDomain E (Pos a))) :=
    ⟨by rw [Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  have hchar : Continuous fun X : Pos a → Ad E => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
    continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg)
  have hfc : ∀ y, Continuous (f y) := fun y =>
    (hc.comp (continuous_uGL.mul continuous_const)).mul hchar
  haveI : FirstCountableTopology (MulOpposite (Matrix (Fin a) (Fin a) (Cinf E))) :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin a) (Fin a) (Cinf E))).symm.isInducing.firstCountableTopology
  haveI : FirstCountableTopology (GL (Fin a) (Cinf E)) :=
    Units.isEmbedding_embedProduct.isInducing.firstCountableTopology
  rw [continuous_iff_continuousAt]
  intro y₀
  have hev : ∀ᶠ y in 𝓝 y₀, height y < height y₀ + 1 :=
    continuous_heightInf.continuousAt.eventually (gt_mem_nhds (lt_add_one _))
  simp only [hwf]
  refine continuousAt_of_dominated (bound := fun _ => max C 0 * (height y₀ + 1) ^ N) ?_ ?_ (integrable_const _) ?_
  · exact Filter.Eventually.of_forall fun y => (hfc y).aestronglyMeasurable
  · filter_upwards [hev] with y hy
    refine ae_restrict_of_forall_mem measurableSet_vecDomain fun X hX => ?_
    calc ‖f y X‖ ≤ C * height y ^ N := hb y X hX
      _ ≤ max C 0 * height y ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (height_pos_inf y).le _)
      _ ≤ max C 0 * (height y₀ + 1) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos_inf y).le hy.le _) (le_max_right _ _)
  · refine Filter.Eventually.of_forall fun X => ?_
    have : Continuous fun y : GL (Fin a) (Cinf E) => f y X :=
      (hc.comp (continuous_const.mul (continuous_const.mul GlobalTheory.ConstTermSmooth.continuous_infGL))).mul
        continuous_const
    exact this.continuousAt

end GlobalTheory.JSW.MirSemi

open GlobalTheory.JSW.MirSemi in

/- English proof (translation)
Introduce `E _ _ _ m S π φ hφ`. Establish `hreg` using `GlobalTheory.T.cusp_form_moderate_growth_compact E (m + 1) S π φ hφ`. Set `𝒲 : Submodule ℂ (GA E (m + 1) → ℂ)` to `{ carrier := {W | ∃ F ∈ locSpan S φ.1, GlobalTheory.JSW.whit F = W} add_mem' := by`. Introduce and unpack `_ _ ⟨F, hF, rfl⟩ ⟨G, hG, rfl⟩`. Use `⟨F + G, add_mem hF hG, funext fun g => ?_⟩` and prove the remaining obligations.

Establish `h` using `((GlobalTheory.T.globalWhittakerCoefficient_linear_archimedeanKernel E (m + 1) F G (hreg F hF).1 (hreg G hG).1 (hreg F hF).2 (hreg G hG).2).1 1 g)`. Simplify using `only [one_mul] at h`. Conclude with `h`. Use the proof step `zero_mem' := ⟨0, zero_mem _, funext fun g => by`. Simplify using `using whit_smul_fun (0 : ℂ) (0 : GA E (m + 1) → ℂ) g⟩`.

Use the proof step `smul_mem' := by`. Introduce and unpack `c _ ⟨F, hF, rfl⟩`. Conclude with `⟨c • F, Submodule.smul_mem _ c hF, funext fun g => whit_smul_fun c F g⟩ }`. Use `⟨𝒲, ⟨φ.1, self_mem_locSpan, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨F, hF, rfl⟩ u hu g`.

Conclude with `GlobalTheory.JSW.WhitModel.whit_mul (hreg F hF).1 (fun γ g => GlobalTheory.JSW.rspan_left π (locSpan_le_rspan hφ hF) γ g) hu g`. Introduce and unpack `_ ⟨F, hF, rfl⟩ h hh`. Conclude with `⟨_, rt_mem_locSpan hF hh, funext fun g => (whit_mul_right_fun F g h).symm⟩`. Introduce and unpack `_ ⟨F, hF, rfl⟩ X _ ν _ k γ hk`. Use `⟨GlobalTheory.JSW.kerInf ν k γ F, kerInf_mem_locSpan hF ν hk, funext fun g => ?_⟩` and prove the remaining obligations.

Rewrite using `[(GlobalTheory.T.globalWhittakerCoefficient_linear_archimedeanKernel E (m + 1) F F (hreg F hF).1 (hreg F hF).1 (hreg F hF).2 (hreg F hF).2).2 X ν k γ hk g]`. Both sides reduce to the same expression. Introduce and unpack `_ ⟨F, hF, rfl⟩ g`. Conclude with `whit_infGL_growth (hreg F hF).1 (hreg F hF).2 g`. Introduce and unpack `_ ⟨F, hF, rfl⟩`.

Take `⟨U, hU, hinv⟩` from `GlobalTheory.T.archimedeanKernelSpan_cuspForm_right_invariant_open E (m + 1) S π φ hφ F hF`. Use `⟨U, hU, fun u hu g => ?_⟩` and prove the remaining obligations. Rewrite using `[whit_mul_right_fun]`. Use `congr 1`. Use function extensionality and compare the values at `z`.

Conclude with `hinv u hu z`. Introduce and unpack `_ ⟨F, hF, rfl⟩`. Conclude with `⟨F, hF, fun g => rfl⟩`.
-/
theorem GlobalTheory.JSW.MirSemi.whitSpace_exists : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → ∃ 𝒲 : Submodule ℂ (GA E (m + 1) → ℂ), GlobalTheory.JSW.whit φ.1 ∈ 𝒲 ∧ (∀ W ∈ 𝒲, ∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) ∧ (∀ W ∈ 𝒲, ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, (fun g => W (g * h)) ∈ 𝒲) ∧ (∀ W ∈ 𝒲, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.JSW.kerInf ν k γ W ∈ 𝒲) ∧ (∀ W ∈ 𝒲, ∀ g, Continuous (fun y : GL (Fin (m + 1)) (Cinf E) => W (g * infGL E (m + 1) y)) ∧ ∃ (C : ℝ) (N : ℕ), ∀ y, ‖W (g * infGL E (m + 1) y)‖ ≤ C * height y ^ N) ∧ (∀ W ∈ 𝒲, ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, W (g * finGL E (m + 1) u) = W g) ∧ ∀ W ∈ 𝒲, ∃ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∀ g, GlobalTheory.JSW.whit F g = W g := by
  intro E _ _ _ m S π φ hφ
  have hreg := GlobalTheory.T.cusp_form_moderate_growth_compact E (m + 1) S π φ hφ
  let 𝒲 : Submodule ℂ (GA E (m + 1) → ℂ) :=
    { carrier := {W | ∃ F ∈ locSpan S φ.1, GlobalTheory.JSW.whit F = W}
      add_mem' := by
        rintro _ _ ⟨F, hF, rfl⟩ ⟨G, hG, rfl⟩
        refine ⟨F + G, add_mem hF hG, funext fun g => ?_⟩
        have h := ((GlobalTheory.T.globalWhittakerCoefficient_linear_archimedeanKernel E (m + 1) F G (hreg F hF).1 (hreg G hG).1 (hreg F hF).2 (hreg G hG).2).1 1 g)
        simp only [one_mul] at h
        exact h
      zero_mem' := ⟨0, zero_mem _, funext fun g => by
        simpa using whit_smul_fun (0 : ℂ) (0 : GA E (m + 1) → ℂ) g⟩
      smul_mem' := by
        rintro c _ ⟨F, hF, rfl⟩
        exact ⟨c • F, Submodule.smul_mem _ c hF, funext fun g => whit_smul_fun c F g⟩ }
  refine ⟨𝒲, ⟨φ.1, self_mem_locSpan, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨F, hF, rfl⟩ u hu g
    exact GlobalTheory.JSW.WhitModel.whit_mul (hreg F hF).1
      (fun γ g => GlobalTheory.JSW.rspan_left π (locSpan_le_rspan hφ hF) γ g) hu g
  · rintro _ ⟨F, hF, rfl⟩ h hh
    exact ⟨_, rt_mem_locSpan hF hh, funext fun g => (whit_mul_right_fun F g h).symm⟩
  · rintro _ ⟨F, hF, rfl⟩ X _ ν _ k γ hk
    refine ⟨GlobalTheory.JSW.kerInf ν k γ F, kerInf_mem_locSpan hF ν hk, funext fun g => ?_⟩
    rw [(GlobalTheory.T.globalWhittakerCoefficient_linear_archimedeanKernel E (m + 1) F F (hreg F hF).1 (hreg F hF).1 (hreg F hF).2 (hreg F hF).2).2 X ν k γ hk g]
    rfl
  · rintro _ ⟨F, hF, rfl⟩ g
    exact whit_infGL_growth (hreg F hF).1 (hreg F hF).2 g
  · rintro _ ⟨F, hF, rfl⟩
    obtain ⟨U, hU, hinv⟩ := GlobalTheory.T.archimedeanKernelSpan_cuspForm_right_invariant_open E (m + 1) S π φ hφ F hF
    refine ⟨U, hU, fun u hu g => ?_⟩
    rw [whit_mul_right_fun]
    congr 1
    funext z
    exact hinv u hu z
  · rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, hF, fun g => rfl⟩
