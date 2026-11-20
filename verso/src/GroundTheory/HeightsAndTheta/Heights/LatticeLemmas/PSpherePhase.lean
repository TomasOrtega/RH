import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsSphereLaw
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PPointwiseLelong
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ProbabilityTheory Real

noncomputable section

/- English proof (translation)
Establish `: Fact (0 < 2 * π)` using `⟨two_pi_pos⟩`. Establish `hI : Set.Ioc (-π) (-π + 2 * π) = Set.Ioc (-π) π` using `by ring_nf`. Establish `h1` using `AddCircle.measurePreserving_mk (2 * π) (-π)`. Rewrite `h1` using `[hI]`. Establish `h2` using `measurePreserving_add_right (volume : Measure (AddCircle (2 * π))) ((Complex.arg c : ℝ) : AddCircle (2 * π))`.

Establish `h3` using `AddCircle.measurePreserving_equivIoc (T := 2 * π) (a := -π)`. Establish `h4 : MeasurePreserving (Subtype.val : Set.Ioc (-π) (-π + 2 * π) → ℝ) (Measure.comap Subtype.val volume) (volume.restrict (Set.Ioc (-π) π))` using `⟨measurable_subtype_coe, by rw [map_comap_subtype_coe measurableSet_Ioc, hI]⟩`. Establish `hcomp` using `h4.comp (h3.comp (h2.comp h1))`. Establish `hfun : (fun θ : ℝ ↦ Complex.arg (Complex.exp (θ * Complex.I) * c)) = Subtype.val ∘ (AddCircle.equivIoc (2 * π) (-π)) ∘ (fun x ↦ x + ((Complex.arg c : ℝ) : AddCircle (2 * π))) ∘ ((↑) : ℝ → AddCircle (2 * π))`. Use function extensionality and compare the values at `θ`.

Establish `hc' : 0 < ‖c‖` using `norm_pos_iff.mpr hc`. Establish `he : Complex.exp (θ * Complex.I) * c = (‖c‖ : ℂ) * Complex.exp (((θ + Complex.arg c : ℝ) : ℂ) * Complex.I)` using `by conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I c]`. Rewrite using `[mul_left_comm, ← Complex.exp_add]`. Use `push_cast`. Put the polynomial expressions in normal form.

Rewrite using `[Function.comp_apply, Function.comp_apply, Function.comp_apply, he, Complex.arg_real_mul _ hc', Complex.arg_exp]`. Simplify using `only [Complex.mul_I_im, Complex.ofReal_re]`. Rewrite using `[← AddCircle.coe_add]`. Both sides reduce to the same expression. Rewrite using `[hfun]`.

Establish `hmeas : Measurable (Subtype.val ∘ (AddCircle.equivIoc (2 * π) (-π)) ∘ (fun x ↦ x + ((Complex.arg c : ℝ) : AddCircle (2 * π))) ∘ ((↑) : ℝ → AddCircle (2 * π)))` using `hcomp.measurable`. Rewrite using `[phaseLaw, ProbabilityTheory.cond, Measure.map_smul, hcomp.map_eq]`.
-/
theorem phaseLaw_map_arg_exp_mul {c : ℂ} (hc : c ≠ 0) :
    phaseLaw.map (fun θ : ℝ ↦ Complex.arg (Complex.exp (θ * Complex.I) * c)) = phaseLaw := by
  have : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
  have hI : Set.Ioc (-π) (-π + 2 * π) = Set.Ioc (-π) π := by ring_nf
  have h1 := AddCircle.measurePreserving_mk (2 * π) (-π)
  rw [hI] at h1
  have h2 := measurePreserving_add_right (volume : Measure (AddCircle (2 * π)))
    ((Complex.arg c : ℝ) : AddCircle (2 * π))
  have h3 := AddCircle.measurePreserving_equivIoc (T := 2 * π) (a := -π)
  have h4 : MeasurePreserving (Subtype.val : Set.Ioc (-π) (-π + 2 * π) → ℝ)
      (Measure.comap Subtype.val volume) (volume.restrict (Set.Ioc (-π) π)) :=
    ⟨measurable_subtype_coe, by rw [map_comap_subtype_coe measurableSet_Ioc, hI]⟩
  have hcomp := h4.comp (h3.comp (h2.comp h1))
  have hfun : (fun θ : ℝ ↦ Complex.arg (Complex.exp (θ * Complex.I) * c)) =
      Subtype.val ∘ (AddCircle.equivIoc (2 * π) (-π)) ∘
        (fun x ↦ x + ((Complex.arg c : ℝ) : AddCircle (2 * π))) ∘
        ((↑) : ℝ → AddCircle (2 * π)) := by
    funext θ
    have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have he : Complex.exp (θ * Complex.I) * c =
        (‖c‖ : ℂ) * Complex.exp (((θ + Complex.arg c : ℝ) : ℂ) * Complex.I) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I c]
      rw [mul_left_comm, ← Complex.exp_add]
      push_cast
      ring_nf
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, he,
      Complex.arg_real_mul _ hc', Complex.arg_exp]
    simp only [Complex.mul_I_im, Complex.ofReal_re]
    rw [← AddCircle.coe_add]
    rfl
  rw [hfun]
  have hmeas : Measurable (Subtype.val ∘ (AddCircle.equivIoc (2 * π) (-π)) ∘
        (fun x ↦ x + ((Complex.arg c : ℝ) : AddCircle (2 * π))) ∘
        ((↑) : ℝ → AddCircle (2 * π))) := hcomp.measurable
  rw [phaseLaw, ProbabilityTheory.cond, Measure.map_smul, hcomp.map_eq]

/- English proof (translation)
Introduce `N p hp hN`. Establish `hμ : IsProbabilityMeasure (sphereLaw N)` using `(h1 N (by omega)).1`. Establish `hph : IsProbabilityMeasure phaseLaw` using `PointwiseLelong.isProbabilityMeasure_phaseLaw`. Establish `hA : Continuous (coordAlong p)` using `PointwiseLelong.continuous_coordAlong p`. Establish `hG : Measurable fun z ↦ (‖coordAlong p z‖, orthoDir p z)` using `(continuous_norm.comp hA).measurable.prodMk (PointwiseLelong.measurable_orthoDir p)`.

Set `L : (Fin N → ℂ) →ₗ[ℂ] ℂ` to `{ toFun := coordAlong p map_add' := fun x y ↦ by simp [coordAlong, add_mul, Finset.sum_add_distrib] map_smul' := fun c x ↦ by simp [coordAlong, Finset.mul_sum, mul_assoc] }`. Establish `hL : ∀ z, L z = coordAlong p z` using `fun _ ↦ rfl`. Establish `hpp : coordAlong p p = 1`. Establish `: ∀ j, p j * star (p j) = ((‖p j‖ ^ 2 : ℝ) : ℂ)` using `fun j ↦ by`. Rewrite using `[Complex.star_def, Complex.mul_conj']`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [coordAlong, this]`. Rewrite using `[← Complex.ofReal_sum, hp]`. Simplify using the standard rewrite rules.

Establish `key : ∀ (x : ℂ) (w : Fin N → ℂ), coordAlong p w = 0 → ∑ j, ‖x * p j + w j‖ ^ 2 = ‖x‖ ^ 2 + ∑ j, ‖w j‖ ^ 2`. Introduce `x w hw`. Establish `hp' : ∑ j, Complex.normSq (p j) = 1` using `by simpa [Complex.sq_norm] using hp`. Establish `hcross : ∑ j, (x * p j * (starRingEnd ℂ) (w j)).re = 0`. Rewrite using `[← Complex.re_sum]`.

Establish `: ∑ j, x * p j * (starRingEnd ℂ) (w j) = x * (starRingEnd ℂ) (coordAlong p w)`. Simplify using `[coordAlong, map_sum, Finset.mul_sum, mul_comm, mul_assoc]`. Rewrite using `[this, hw]`. Simplify using the standard rewrite rules. Simplify using `only [Complex.sq_norm, Complex.normSq_add, Complex.normSq_mul, Finset.sum_add_distrib]`.

Rewrite using `[← Finset.mul_sum, hp', ← Finset.mul_sum, hcross]`. Expand and normalize the polynomial expressions, which then agree. Set `R : ℝ → (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ)` to `fun θ ↦ LinearMap.id + ((Complex.exp (θ * Complex.I) - 1) • L).smulRight p`. Establish `hR : ∀ θ z, R θ z = z + ((Complex.exp (θ * Complex.I) - 1) * coordAlong p z) • p` using `fun θ z ↦ rfl`. Establish `hRa : ∀ θ z, coordAlong p (R θ z) = Complex.exp (θ * Complex.I) * coordAlong p z`.

Introduce `θ z`. Rewrite using `[← hL, hR, map_add, map_smul, smul_eq_mul, hL, hL, hpp]`. Expand and normalize the polynomial expressions, which then agree. Establish `hRw : ∀ θ z, R θ z - coordAlong p (R θ z) • p = z - coordAlong p z • p`. Introduce `θ z`.

Rewrite using `[hRa, hR]`. Use extensionality with `j`. Simplify using `only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hRo : ∀ θ z, orthoDir p (R θ z) = orthoDir p z`.

Introduce `θ z`. Rewrite using `[orthoDir, orthoDir, hRw]`. Establish `hRn : ∀ θ v, ∑ j, ‖R θ v j‖ ^ 2 = ∑ j, ‖v j‖ ^ 2`. Introduce `θ v`. Establish `hw0 : coordAlong p (v - coordAlong p v • p) = 0`.

Rewrite using `[← hL, map_sub, map_smul, smul_eq_mul, hL, hL, hpp]`. Expand and normalize the polynomial expressions, which then agree. Establish `s1 : ∑ j, ‖R θ v j‖ ^ 2 = ∑ j, ‖(Complex.exp (θ * Complex.I) * coordAlong p v) * p j + (v - coordAlong p v • p) j‖ ^ 2` using `Finset.sum_congr rfl fun j _ ↦ by`. Rewrite using `[hR]`. Simplify using `only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`.

Put the polynomial expressions in normal form. Establish `s2 : ∑ j, ‖v j‖ ^ 2 = ∑ j, ‖coordAlong p v * p j + (v - coordAlong p v • p) j‖ ^ 2` using `Finset.sum_congr rfl fun j _ ↦ by`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Put the polynomial expressions in normal form. Rewrite using `[s1, s2, key _ _ hw0, key _ _ hw0, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]`.

Establish `hinv : ∀ θ : ℝ, (sphereLaw N).map (R θ) = sphereLaw N` using `fun θ ↦ h2 N (R θ) (hRn θ)`. Establish `hne : ∀ᵐ z ∂sphereLaw N, coordAlong p z ≠ 0`. Establish `hker : LinearMap.ker L ≠ ⊤`. Introduce `h`. Establish `hp0 : p ∈ LinearMap.ker L` using `h ▸ Submodule.mem_top`.

Rewrite `hp0` using `[LinearMap.mem_ker, hL, hpp]`. Conclude with `one_ne_zero hp0`. Establish `h0` using `(h1 N (by omega)).2.2 _ hker`. Rewrite using `[ae_iff]`. Establish `hset : {z | ¬coordAlong p z ≠ 0} = (LinearMap.ker L : Set (Fin N → ℂ))`.

Use extensionality with `z`. Simplify using `only [ne_eq, not_not, Set.mem_ofPred_eq, SetLike.mem_coe, LinearMap.mem_ker, hL]`. Rewrite using `[hset, h0]`. Establish `hF : Measurable fun z ↦ (Complex.arg (coordAlong p z), (‖coordAlong p z‖, orthoDir p z))` using `(Complex.measurable_arg.comp hA.measurable).prodMk hG`. Set `Φ : ℝ × (Fin N → ℂ) → ℝ × (ℝ × (Fin N → ℂ))` to `fun q ↦ (Complex.arg (Complex.exp (q.1 * Complex.I) * coordAlong p q.2), (‖coordAlong p q.2‖, orthoDir p q.2))`.

Establish `hΦ : Measurable Φ`. Use `(Complex.measurable_arg.comp ?_).prodMk (hG.comp measurable_snd)` and prove the remaining obligations. Conclude with `((Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)).mul (hA.comp continuous_snd)).measurable`. Use extensionality with `S hS`. Establish `hstep : ∀ θ : ℝ, (sphereLaw N) ((fun z ↦ (Complex.arg (coordAlong p z), (‖coordAlong p z‖, orthoDir p z))) ⁻¹' S) = ∫⁻ z, S.indicator 1 (Φ (θ, z)) ∂sphereLaw N`.

Introduce `θ`. Use `conv_lhs => rw [← hinv θ]`. Rewrite using `[Measure.map_apply (LinearMap.continuous_of_finiteDimensional (R θ)).measurable (hF hS)]`. Establish `hpre : (R θ) ⁻¹' ((fun z ↦ (Complex.arg (coordAlong p z), (‖coordAlong p z‖, orthoDir p z))) ⁻¹' S) = (fun z ↦ Φ (θ, z)) ⁻¹' S`. Use extensionality with `z`.

Simplify using `only [Set.mem_preimage, Φ, hRa, hRo, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]`. Rewrite using `[hpre, ← lintegral_indicator_one (hS.preimage (hΦ.comp measurable_prodMk_left) : MeasurableSet ((fun z ↦ Φ (θ, z)) ⁻¹' S))]`. Both sides reduce to the same expression. Rewrite using `[Measure.map_apply hF hS, Measure.prod_apply_symm hS]`. Combine the equalities or inequalities in the displayed calculation.

Use `lintegral_congr_ae (hne.mono fun z hz ↦ ?_)` and prove the remaining obligations. Establish `hg : Measurable fun θ : ℝ ↦ Complex.arg (Complex.exp (θ * Complex.I) * coordAlong p z)` using `Complex.measurable_arg.comp ((Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).mul continuous_const).measurable`. Use `show ∫⁻ θ, S.indicator 1 (Φ (θ, z)) ∂phaseLaw = phaseLaw ((fun x ↦ (x, (‖coordAlong p z‖, orthoDir p z))) ⁻¹' S)`. Rewrite using `[← lintegral_indicator_one (hS.preimage measurable_prodMk_right : MeasurableSet ((fun x ↦ (x, (‖coordAlong p z‖, orthoDir p z))) ⁻¹' S))]`. Use `conv_rhs => rw [← phaseLaw_map_arg_exp_mul hz]`.

Rewrite using `[lintegral_map ((measurable_one.indicator (hS.preimage measurable_prodMk_right))) hg]`. Both sides reduce to the same expression. Use `_ = ∫⁻ y, phaseLaw ((fun x ↦ (x, y)) ⁻¹' S) ∂(sphereLaw N).map fun z ↦ (‖coordAlong p z‖, orthoDir p z) := (lintegral_map (measurable_measure_prodMk_right hS) hG).symm`.
-/
theorem SpherePhase.proof (h1 : SphereLawBasic.Statement) (h2 : SphereLawUnitary.Statement) :
    SpherePhase.Statement := by
  intro N p hp hN
  have hμ : IsProbabilityMeasure (sphereLaw N) := (h1 N (by omega)).1
  have hph : IsProbabilityMeasure phaseLaw := PointwiseLelong.isProbabilityMeasure_phaseLaw
  have hA : Continuous (coordAlong p) := PointwiseLelong.continuous_coordAlong p
  have hG : Measurable fun z ↦ (‖coordAlong p z‖, orthoDir p z) :=
    (continuous_norm.comp hA).measurable.prodMk (PointwiseLelong.measurable_orthoDir p)

  let L : (Fin N → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := coordAlong p
      map_add' := fun x y ↦ by simp [coordAlong, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x ↦ by simp [coordAlong, Finset.mul_sum, mul_assoc] }
  have hL : ∀ z, L z = coordAlong p z := fun _ ↦ rfl
  have hpp : coordAlong p p = 1 := by
    have : ∀ j, p j * star (p j) = ((‖p j‖ ^ 2 : ℝ) : ℂ) := fun j ↦ by
      rw [Complex.star_def, Complex.mul_conj']; push_cast; ring
    simp only [coordAlong, this]
    rw [← Complex.ofReal_sum, hp]; simp

  have key : ∀ (x : ℂ) (w : Fin N → ℂ), coordAlong p w = 0 →
      ∑ j, ‖x * p j + w j‖ ^ 2 = ‖x‖ ^ 2 + ∑ j, ‖w j‖ ^ 2 := by
    intro x w hw
    have hp' : ∑ j, Complex.normSq (p j) = 1 := by simpa [Complex.sq_norm] using hp
    have hcross : ∑ j, (x * p j * (starRingEnd ℂ) (w j)).re = 0 := by
      rw [← Complex.re_sum]
      have : ∑ j, x * p j * (starRingEnd ℂ) (w j) = x * (starRingEnd ℂ) (coordAlong p w) := by
        simp [coordAlong, map_sum, Finset.mul_sum, mul_comm, mul_assoc]
      rw [this, hw]; simp
    simp only [Complex.sq_norm, Complex.normSq_add, Complex.normSq_mul, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, hp', ← Finset.mul_sum, hcross]
    ring

  let R : ℝ → (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) := fun θ ↦
    LinearMap.id + ((Complex.exp (θ * Complex.I) - 1) • L).smulRight p
  have hR : ∀ θ z, R θ z = z + ((Complex.exp (θ * Complex.I) - 1) * coordAlong p z) • p :=
    fun θ z ↦ rfl
  have hRa : ∀ θ z, coordAlong p (R θ z) = Complex.exp (θ * Complex.I) * coordAlong p z := by
    intro θ z
    rw [← hL, hR, map_add, map_smul, smul_eq_mul, hL, hL, hpp]
    ring
  have hRw : ∀ θ z, R θ z - coordAlong p (R θ z) • p = z - coordAlong p z • p := by
    intro θ z
    rw [hRa, hR]
    ext j
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hRo : ∀ θ z, orthoDir p (R θ z) = orthoDir p z := by
    intro θ z
    rw [orthoDir, orthoDir, hRw]
  have hRn : ∀ θ v, ∑ j, ‖R θ v j‖ ^ 2 = ∑ j, ‖v j‖ ^ 2 := by
    intro θ v
    have hw0 : coordAlong p (v - coordAlong p v • p) = 0 := by
      rw [← hL, map_sub, map_smul, smul_eq_mul, hL, hL, hpp]
      ring
    have s1 : ∑ j, ‖R θ v j‖ ^ 2 = ∑ j,
        ‖(Complex.exp (θ * Complex.I) * coordAlong p v) * p j + (v - coordAlong p v • p) j‖ ^ 2 :=
      Finset.sum_congr rfl fun j _ ↦ by
        rw [hR]
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring_nf
    have s2 : ∑ j, ‖v j‖ ^ 2 = ∑ j, ‖coordAlong p v * p j + (v - coordAlong p v • p) j‖ ^ 2 :=
      Finset.sum_congr rfl fun j _ ↦ by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring_nf
    rw [s1, s2, key _ _ hw0, key _ _ hw0, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hinv : ∀ θ : ℝ, (sphereLaw N).map (R θ) = sphereLaw N := fun θ ↦ h2 N (R θ) (hRn θ)

  have hne : ∀ᵐ z ∂sphereLaw N, coordAlong p z ≠ 0 := by
    have hker : LinearMap.ker L ≠ ⊤ := by
      intro h
      have hp0 : p ∈ LinearMap.ker L := h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, hL, hpp] at hp0
      exact one_ne_zero hp0
    have h0 := (h1 N (by omega)).2.2 _ hker
    rw [ae_iff]
    have hset : {z | ¬coordAlong p z ≠ 0} = (LinearMap.ker L : Set (Fin N → ℂ)) := by
      ext z
      simp only [ne_eq, not_not, Set.mem_ofPred_eq, SetLike.mem_coe, LinearMap.mem_ker, hL]
    rw [hset, h0]

  have hF : Measurable fun z ↦ (Complex.arg (coordAlong p z), (‖coordAlong p z‖, orthoDir p z)) :=
    (Complex.measurable_arg.comp hA.measurable).prodMk hG
  let Φ : ℝ × (Fin N → ℂ) → ℝ × (ℝ × (Fin N → ℂ)) := fun q ↦
    (Complex.arg (Complex.exp (q.1 * Complex.I) * coordAlong p q.2),
      (‖coordAlong p q.2‖, orthoDir p q.2))
  have hΦ : Measurable Φ := by
    refine (Complex.measurable_arg.comp ?_).prodMk (hG.comp measurable_snd)
    exact ((Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_fst).mul
      continuous_const)).mul (hA.comp continuous_snd)).measurable
  ext S hS
  have hstep : ∀ θ : ℝ, (sphereLaw N)
      ((fun z ↦ (Complex.arg (coordAlong p z), (‖coordAlong p z‖, orthoDir p z))) ⁻¹' S) =
      ∫⁻ z, S.indicator 1 (Φ (θ, z)) ∂sphereLaw N := by
    intro θ
    conv_lhs => rw [← hinv θ]
    rw [Measure.map_apply (LinearMap.continuous_of_finiteDimensional (R θ)).measurable (hF hS)]
    have hpre : (R θ) ⁻¹' ((fun z ↦ (Complex.arg (coordAlong p z),
        (‖coordAlong p z‖, orthoDir p z))) ⁻¹' S) = (fun z ↦ Φ (θ, z)) ⁻¹' S := by
      ext z
      simp only [Set.mem_preimage, Φ, hRa, hRo, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    rw [hpre, ← lintegral_indicator_one (hS.preimage (hΦ.comp measurable_prodMk_left) :
      MeasurableSet ((fun z ↦ Φ (θ, z)) ⁻¹' S))]
    rfl
  rw [Measure.map_apply hF hS, Measure.prod_apply_symm hS]
  calc _ = ∫⁻ θ, (sphereLaw N)
          ((fun z ↦ (Complex.arg (coordAlong p z), (‖coordAlong p z‖, orthoDir p z))) ⁻¹' S)
          ∂phaseLaw := by rw [lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ θ, ∫⁻ z, S.indicator 1 (Φ (θ, z)) ∂sphereLaw N ∂phaseLaw :=
        lintegral_congr fun θ ↦ hstep θ
    _ = ∫⁻ z, ∫⁻ θ, S.indicator 1 (Φ (θ, z)) ∂phaseLaw ∂sphereLaw N :=
        lintegral_lintegral_swap ((measurable_one.indicator hS).comp hΦ).aemeasurable
    _ = ∫⁻ z, phaseLaw ((fun x ↦ (x, (‖coordAlong p z‖, orthoDir p z))) ⁻¹' S) ∂sphereLaw N := by
        refine lintegral_congr_ae (hne.mono fun z hz ↦ ?_)
        have hg : Measurable fun θ : ℝ ↦
            Complex.arg (Complex.exp (θ * Complex.I) * coordAlong p z) :=
          Complex.measurable_arg.comp ((Complex.continuous_exp.comp
            (Complex.continuous_ofReal.mul continuous_const)).mul continuous_const).measurable
        show ∫⁻ θ, S.indicator 1 (Φ (θ, z)) ∂phaseLaw =
          phaseLaw ((fun x ↦ (x, (‖coordAlong p z‖, orthoDir p z))) ⁻¹' S)
        rw [← lintegral_indicator_one (hS.preimage measurable_prodMk_right :
          MeasurableSet ((fun x ↦ (x, (‖coordAlong p z‖, orthoDir p z))) ⁻¹' S))]
        conv_rhs => rw [← phaseLaw_map_arg_exp_mul hz]
        rw [lintegral_map ((measurable_one.indicator (hS.preimage measurable_prodMk_right))) hg]
        rfl
    _ = ∫⁻ y, phaseLaw ((fun x ↦ (x, y)) ⁻¹' S)
          ∂(sphereLaw N).map fun z ↦ (‖coordAlong p z‖, orthoDir p z) :=
        (lintegral_map (measurable_measure_prodMk_right hS) hG).symm

end

end GroundTheory.Heights₂.Heights
