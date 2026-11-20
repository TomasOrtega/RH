import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumOneAddNormRpowNegLeEuclidean
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFundamentalDomainIUnion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormSmoothSpanNormLeShortRationalVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.ThetaPoisson GlobalTheory.ShortVecDecay
open scoped ComplexConjugate nonZeroDivisors ENNReal
open GlobalTheory.RSTheta GroundTheory.Global.IdeleGroup

namespace GlobalTheory.RSThetaM

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def measSub (E : Type) [Field E] [NumberField E] (a : ℕ) : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | Measurable F}
  add_mem' hF hG := Measurable.add hF hG
  zero_mem' := measurable_const
  smul_mem' c _ hF := Measurable.const_smul hF c

/- English proof (translation)
Establish `hu : Continuous fun q : invSet E a => (IsUnit.unit (q.2 : IsUnit (Matrix.of q.1)) : GL (Fin a) (Cinf E))`. Use `Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩` and prove the remaining obligations. Use `GlobalTheory.ConstTermSmooth.contDiffOn_invM.continuousOn.comp_continuous (f := fun q : invSet E a => q.1) continuous_subtype_val fun q => q.2` as an intermediate fact. Use `Continuous.congr this fun q => ?_` and prove the remaining obligations. Simplify using `only [Matrix.coe_units_inv]`.

Both sides reduce to the same expression. Establish `hm : Measurable fun x => (⟨toL (γ x).val, (γ x).isUnit⟩ : invSet E a)` using `h.subtype_mk`. Use `hu.measurable.comp hm using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Use `ext1`.

Both sides reduce to the same expression.
-/
theorem measurable_gl_of_matrix {X : Type} [MeasurableSpace X] {γ : X → GL (Fin a) (Cinf E)}
    (h : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) : Measurable γ := by
  have hu : Continuous fun q : invSet E a =>
      (IsUnit.unit (q.2 : IsUnit (Matrix.of q.1)) : GL (Fin a) (Cinf E)) := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    have := GlobalTheory.ConstTermSmooth.contDiffOn_invM.continuousOn.comp_continuous
      (f := fun q : invSet E a => q.1) continuous_subtype_val fun q => q.2
    refine Continuous.congr this fun q => ?_
    simp only [Matrix.coe_units_inv]
    rfl
  have hm : Measurable fun x => (⟨toL (γ x).val, (γ x).isUnit⟩ : invSet E a) := h.subtype_mk
  convert hu.measurable.comp hm using 1
  funext x
  ext1
  rfl

/- English proof (translation)
Establish `hF'` using `hF`. Unfold `GlobalTheory.JSW.mspanR at hF'`. Use `Submodule.mem_sInf.1 hF' (measSub E a) ⟨fun φ hφ => ?_, fun F hF h => ?_, fun F hF X _ ν _ k γ hk => ?_⟩` and prove the remaining obligations. Conclude with `(continuous_of_mem_or (π := π) (Or.inl hφ)).measurable`. Conclude with `(hF : Measurable F).comp (continuous_mul_right h).measurable`.

Establish `hγ : Measurable fun p : GA E a × X => p.1 * infGL E a (γ p.2)` using `measurable_fst.mul ((GlobalTheory.ConstTermSmooth.continuous_infGL.measurable.comp (measurable_gl_of_matrix hk.2.1)).comp measurable_snd)`. Establish `h1 : StronglyMeasurable fun p : GA E a × X => k p.2 * F (p.1 * infGL E a (γ p.2))` using `((hk.1.comp measurable_snd).mul ((hF : Measurable F).comp hγ)).stronglyMeasurable`. Conclude with `(h1.integral_prod_right' (ν := ν)).measurable`.
-/
theorem measurable_of_mem_mspanR (π : CuspSub E a) {F : GA E a → ℂ} (hF : F ∈ GlobalTheory.JSW.mspanR π) : Measurable F := by
  have hF' := hF
  unfold GlobalTheory.JSW.mspanR at hF'
  refine Submodule.mem_sInf.1 hF' (measSub E a) ⟨fun φ hφ => ?_, fun F hF h => ?_,
    fun F hF X _ ν _ k γ hk => ?_⟩
  · exact (continuous_of_mem_or (π := π) (Or.inl hφ)).measurable
  · exact (hF : Measurable F).comp (continuous_mul_right h).measurable
  · have hγ : Measurable fun p : GA E a × X => p.1 * infGL E a (γ p.2) :=
      measurable_fst.mul ((GlobalTheory.ConstTermSmooth.continuous_infGL.measurable.comp
        (measurable_gl_of_matrix hk.2.1)).comp measurable_snd)
    have h1 : StronglyMeasurable fun p : GA E a × X => k p.2 * F (p.1 * infGL E a (γ p.2)) :=
      ((hk.1.comp measurable_snd).mul ((hF : Measurable F).comp hγ)).stronglyMeasurable
    exact (h1.integral_prod_right' (ν := ν)).measurable

/- English proof (translation)
Use `set s : Set (GA E a × (Fin a → Cinf E)) := Set.univ ×ˢ rowSet E ℓ with hsdef`. Establish `hsm : MeasurableSet s` using `(isOpen_univ.prod (isOpen_rowSet ℓ)).measurableSet`. Use `measurable_of_restrict_of_restrict_compl hsm ?_ ?_` and prove the remaining obligations. Establish `hc : Continuous fun p : s => p.1.1 * (infGL E a (rowGL ℓ p.1.2))⁻¹`. Establish `h2 : ContinuousOn (fun p : GA E a × (Fin a → Cinf E) => p.1 * (infGL E a (rowGL ℓ p.2))⁻¹) s` using `continuous_fst.continuousOn.mul ((continuousOn_inv_rowGL ℓ).comp continuous_snd.continuousOn fun p hp => hp.2)`.

Conclude with `h2.restrict`. Establish `hm` using `hc.measurable`. Conclude with `((h.comp hm).mul (Complex.continuous_conj.measurable.comp (h'.comp hm))).mul (hΦ.measurable.comp (measurable_snd.comp measurable_subtype_coe))`. Use `(measurable_const (a := (0 : ℂ)) : Measurable fun _ : (sᶜ : Set (GA E a × (Fin a → Cinf E))) => (0 : ℂ)) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`.

Establish `hp : p.1.2 ∉ tsupport Φ` using `fun hp => p.2 ⟨trivial, hs hp⟩`. Express the relevant statement in the definitionally equal form `rsInf ℓ φ φ' Φ p.1.1 p.1.2 = 0`. Simplify using `[rsInf, image_eq_zero_of_notMem_tsupport hp]`.
-/
theorem measurable_rsInf {ℓ : Fin a} {φ φ' : GA E a → ℂ} {Φ : (Fin a → Cinf E) → ℂ} (h : Measurable φ)
    (h' : Measurable φ') (hΦ : Continuous Φ) (hs : tsupport Φ ⊆ rowSet E ℓ) :
    Measurable fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ φ' Φ p.1 p.2 := by
  set s : Set (GA E a × (Fin a → Cinf E)) := Set.univ ×ˢ rowSet E ℓ with hsdef
  have hsm : MeasurableSet s := (isOpen_univ.prod (isOpen_rowSet ℓ)).measurableSet
  refine measurable_of_restrict_of_restrict_compl hsm ?_ ?_
  · have hc : Continuous fun p : s => p.1.1 * (infGL E a (rowGL ℓ p.1.2))⁻¹ := by
      have h2 : ContinuousOn (fun p : GA E a × (Fin a → Cinf E) => p.1 * (infGL E a (rowGL ℓ p.2))⁻¹) s :=
        continuous_fst.continuousOn.mul ((continuousOn_inv_rowGL ℓ).comp continuous_snd.continuousOn
          fun p hp => hp.2)
      exact h2.restrict
    have hm := hc.measurable
    exact ((h.comp hm).mul (Complex.continuous_conj.measurable.comp (h'.comp hm))).mul
      (hΦ.measurable.comp (measurable_snd.comp measurable_subtype_coe))
  · convert (measurable_const (a := (0 : ℂ)) : Measurable fun _ : (sᶜ : Set (GA E a × (Fin a → Cinf E))) => (0 : ℂ)) using 1
    funext p
    have hp : p.1.2 ∉ tsupport Φ := fun hp => p.2 ⟨trivial, hs hp⟩
    change rsInf ℓ φ φ' Φ p.1.1 p.1.2 = 0
    simp [rsInf, image_eq_zero_of_notMem_tsupport hp]

/- English proof (translation)
Establish `hY : Continuous fun g : GA E a => (fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val` using `continuous_const.matrix_vecMul Units.continuous_val`. Establish `hI : Continuous fun g : GA E a => fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)` using `continuous_pi fun i => GlobalTheory.ShortVecDecay.continuous_pInf.comp ((continuous_apply i).comp hY)`. Establish `hF : Continuous fun g : GA E a => (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)) - η` using `(continuous_pi fun i => (continuous_snd : Continuous (pFin E)).comp ((continuous_apply i).comp hY)).sub continuous_const`. Establish `h3 : Continuous ((latt a J).indicator (1 : (Fin a → Af E) → ℂ))` using `IsClopen.continuous_indicator ⟨isClosed_latt J, isOpen_latt J⟩ continuous_const`. Conclude with `((measurable_rsInf h h' hΦ hs).comp (measurable_id.prodMk hI.measurable)).mul (h3.comp hF).measurable`.
-/
theorem measurable_rsPsi_vecMul {ℓ : Fin a} {φ φ' : GA E a → ℂ} {Φ : (Fin a → Cinf E) → ℂ} (h : Measurable φ)
    (h' : Measurable φ') (hΦ : Continuous Φ) (hs : tsupport Φ ⊆ rowSet E ℓ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) (ξ : Fin a → E) :
    Measurable fun g : GA E a => rsPsi ℓ φ φ' Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) := by
  have hY : Continuous fun g : GA E a => (fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val :=
    continuous_const.matrix_vecMul Units.continuous_val
  have hI : Continuous fun g : GA E a => fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i) :=
    continuous_pi fun i => GlobalTheory.ShortVecDecay.continuous_pInf.comp ((continuous_apply i).comp hY)
  have hF : Continuous fun g : GA E a => (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)) - η :=
    (continuous_pi fun i => (continuous_snd : Continuous (pFin E)).comp ((continuous_apply i).comp hY)).sub
      continuous_const
  have h3 : Continuous ((latt a J).indicator (1 : (Fin a → Af E) → ℂ)) :=
    IsClopen.continuous_indicator ⟨isClosed_latt J, isOpen_latt J⟩ continuous_const
  exact ((measurable_rsInf h h' hΦ hs).comp (measurable_id.prodMk hI.measurable)).mul (h3.comp hF).measurable

/- English proof (translation)
Introduce `E _ _ _ a ℓ π π' hπ hπ' φ φ' hφ hφ' Φ hΦ hc hs J η μ _ 𝓕 h𝓕`. Establish `hdec : ∀ {ρ : CuspSub E a}, ρ.IsUnitary → ∀ {ψ : Sm E a}, (ψ ∈ ρ.V ∨ ψ.1 ∈ GlobalTheory.JSW.mspanR ρ) → Decays ψ.1` using `fun {ρ} hρ {ψ} hψ L hL C₀ hC₀ N => GlobalTheory.T.cuspFormSmoothSpan_norm_le_shortRationalVector E a ρ hρ ψ hψ [] L hL C₀ hC₀ N`. Establish `hmeas : ∀ {ρ : CuspSub E a} {ψ : Sm E a}, (ψ ∈ ρ.V ∨ ψ.1 ∈ GlobalTheory.JSW.mspanR ρ) → Measurable ψ.1` using `fun {ρ} {ψ} hψ => hψ.elim (fun h => (continuous_of_mem_or (π := ρ) (Or.inl h)).measurable) (GlobalTheory.RSThetaM.measurable_of_mem_mspanR ρ)`. Establish `hK` using `isSmallKernel_rsPsi (hdec hπ hφ) (hdec hπ' hφ') hΦ hc hs J η`. Take `⟨C, hC⟩` from `hK.tsum_le (N := 1) le_rfl`.

Take `⟨h1, h2, h3⟩` from `hK.integrableOn μ h𝓕 fun ξ _ => (GlobalTheory.RSThetaM.measurable_rsPsi_vecMul (hmeas hφ) (hmeas hφ') hΦ hs J η ξ).aestronglyMeasurable`. Use `⟨fun g => (hC g).1, h1, h2, h3, (h3.continuous.comp Complex.continuous_ofReal).congr fun x => ?_⟩` and prove the remaining obligations. Use `integral_congr_ae (.of_forall fun g => ?_)` and prove the remaining obligations. Conclude with `congrArg _ (Complex.ofReal_cpow (ideleModule E _).2.le x).symm`.
-/
theorem theta_integral_upper_mspan : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ℓ : Fin a)
    (π π' : CuspSub E a), π.IsUnitary → π'.IsUnitary → ∀ φ φ' : Sm E a,
    (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) → (φ' ∈ π'.V ∨ φ'.1 ∈ GlobalTheory.JSW.mspanR π') →
    ∀ Φ : (Fin a → Cinf E) → ℂ, Continuous Φ → HasCompactSupport Φ → tsupport Φ ⊆ rowSet E ℓ →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)),
    IsFundamentalDomain (ratGL E a).range 𝓕 μ →
    (∀ g : GA E a, Summable fun ξ : {ξ : Fin a → E // ξ ≠ 0} =>
      ‖rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖) ∧
    (∀ x : ℝ, IntegrableOn (fun g : GA E a =>
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖) *
        (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x)
      (𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)}) μ) ∧
    (∀ s : ℂ, IntegrableOn (fun g : GA E a =>
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s)
      (𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)}) μ) ∧
    (Differentiable ℂ fun s : ℂ => ∫ g in 𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)},
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s ∂μ) ∧
    Continuous fun x : ℝ => ∫ g in 𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)},
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
        (((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x : ℝ) : ℂ) ∂μ := by
  intro E _ _ _ a ℓ π π' hπ hπ' φ φ' hφ hφ' Φ hΦ hc hs J η μ _ 𝓕 h𝓕
  have hdec : ∀ {ρ : CuspSub E a}, ρ.IsUnitary → ∀ {ψ : Sm E a}, (ψ ∈ ρ.V ∨ ψ.1 ∈ GlobalTheory.JSW.mspanR ρ) → Decays ψ.1 :=
    fun {ρ} hρ {ψ} hψ L hL C₀ hC₀ N => GlobalTheory.T.cuspFormSmoothSpan_norm_le_shortRationalVector E a ρ hρ ψ hψ [] L hL C₀ hC₀ N
  have hmeas : ∀ {ρ : CuspSub E a} {ψ : Sm E a}, (ψ ∈ ρ.V ∨ ψ.1 ∈ GlobalTheory.JSW.mspanR ρ) → Measurable ψ.1 :=
    fun {ρ} {ψ} hψ => hψ.elim (fun h => (continuous_of_mem_or (π := ρ) (Or.inl h)).measurable)
      (GlobalTheory.RSThetaM.measurable_of_mem_mspanR ρ)
  have hK := isSmallKernel_rsPsi (hdec hπ hφ) (hdec hπ' hφ') hΦ hc hs J η
  obtain ⟨C, hC⟩ := hK.tsum_le (N := 1) le_rfl
  obtain ⟨h1, h2, h3⟩ := hK.integrableOn μ h𝓕 fun ξ _ =>
    (GlobalTheory.RSThetaM.measurable_rsPsi_vecMul (hmeas hφ) (hmeas hφ') hΦ hs J η ξ).aestronglyMeasurable
  refine ⟨fun g => (hC g).1, h1, h2, h3, (h3.continuous.comp Complex.continuous_ofReal).congr fun x => ?_⟩
  refine integral_congr_ae (.of_forall fun g => ?_)
  exact congrArg _ (Complex.ofReal_cpow (ideleModule E _).2.le x).symm

end GlobalTheory.RSThetaM

end
