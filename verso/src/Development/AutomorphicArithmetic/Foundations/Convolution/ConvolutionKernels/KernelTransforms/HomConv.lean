import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
import GroundTheory.AutomorphicForms.TraceFormulaConvolution
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
import GroundTheory.AutomorphicForms.MultiplicityOne.OpenSubgroupRep
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevelGroups
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteAdelicHaar
import GroundTheory.AutomorphicForms.L2LocalComponents.CenterCommute

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

/- English proof (translation)
Introduce `G G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p hp μ _ μ₂ _ f e`. Establish `hf : IsCompact (tsupport f)` using `f.hasCompactSupport.isCompact`. Establish `hS : IsCompact (p '' tsupport f * tsupport e)` using `(hf.image hp).mul e.hasCompactSupport.isCompact`. Establish `hker : Continuous fun q : G × G₂ => f q.2 * e ((p q.2)⁻¹ * q.1)` using `(f.continuous.comp continuous_snd).mul (e.continuous.comp ((hp.comp continuous_snd).inv.mul continuous_fst))`. Establish `hz₂ : ∀ (x : G) (y : G₂), y ∉ tsupport f → f y * e ((p y)⁻¹ * x) = 0` using `fun x y hy => by`.

Rewrite using `[image_eq_zero_of_notMem_tsupport hy, zero_mul]`. Establish `hz₁ : ∀ (x : G) (y : G₂), x ∉ p '' tsupport f * tsupport e → f y * e ((p y)⁻¹ * x) = 0` using `fun x y hx => by`. Assume the negation of the conclusion as `hne`. Take `⟨h1, h2⟩` from `mul_ne_zero_iff.1 hne`. Conclude with `hx ⟨p y, ⟨y, subset_tsupport _ h1, rfl⟩, (p y)⁻¹ * x, subset_tsupport _ h2, mul_inv_cancel_left _ _⟩`.

Establish `hcont : Continuous fun x : G => ∫ y, f y * e ((p y)⁻¹ * x) ∂μ₂`. Rewrite using `[← continuousOn_univ]`. Conclude with `continuousOn_integral_of_compact_support (μ := μ₂) (f := fun (x : G) (y : G₂) => f y * e ((p y)⁻¹ * x)) hf hker.continuousOn fun x y _ hy => hz₂ x y hy`. Establish `hzero : ∀ x : G, x ∉ p '' tsupport f * tsupport e → ∫ y, f y * e ((p y)⁻¹ * x) ∂μ₂ = 0` using `fun x hx => by`. Simplify using `only [hz₁ x _ hx, integral_zero]`.

Use `⟨⟨⟨fun x => ∫ y, f y * e ((p y)⁻¹ * x) ∂μ₂, hcont⟩, HasCompactSupport.intro hS hzero⟩, fun _ => rfl, ?_, ?_⟩` and prove the remaining obligations. Use `closure_minimal (fun x hx => ?_) hS.isClosed` and prove the remaining obligations. Assume the negation of the conclusion as `hx'`. Conclude with `hx (hzero x hx')`. Introduce `H _ _ _ π`.

Use extensionality with `v`. Rewrite using `[ContinuousLinearMap.comp_apply]`. Simplify using `only [UnitaryRep.integrated_ccToL1_apply, UnitaryRep.compHom_apply]`. Express the relevant statement in the definitionally equal form `∫ x, (∫ y, f y * e ((p y)⁻¹ * x) ∂μ₂) • π x v ∂μ = _`. Establish `hint : Integrable (Function.uncurry fun (x : G) (y : G₂) => (f y * e ((p y)⁻¹ * x)) • π x v) (μ.prod μ₂)`.

Use `Continuous.integrable_of_hasCompactSupport (hker.smul ((π.continuous_orbit v).comp continuous_fst)) ?_` and prove the remaining obligations. Use `HasCompactSupport.intro (hS.prod hf) fun q hq => ?_` and prove the remaining obligations. Establish `h0 : f q.2 * e ((p q.2)⁻¹ * q.1) = 0`. Break down `not_and_or.1 (mt Set.mem_prod.2 hq) with h | h` into its components or cases. Conclude with `hz₁ _ _ h`.

Conclude with `hz₂ _ _ h`. Express the relevant statement in the definitionally equal form `(f q.2 * e ((p q.2)⁻¹ * q.1)) • π q.1 v = 0`. Rewrite using `[h0, zero_smul]`. Establish `he : Integrable (fun z => e z • π z v) μ` using `(e.continuous.smul (π.continuous_orbit v)).integrable_of_hasCompactSupport e.hasCompactSupport.smul_right`. Simplify using `only [← integral_smul_const]`.

Rewrite using `[integral_integral_swap hint]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Rewrite using `[← ContinuousLinearMap.integral_comp_comm _ he, ← integral_smul, ← integral_mul_left_eq_self _ (p y)]`. Simplify using `only [inv_mul_cancel_left, UnitaryRep.map_mul_apply, map_smul, smul_smul]`.
-/
theorem UpperTheory.ConvolutionTheory.Tf.homConv :
    ∀ (G G₂ : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] [T2Space G₂] [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂] (p : G₂ →* G) (hp : Continuous p)
      (μ : Measure G) [μ.IsHaarMeasure] (μ₂ : Measure G₂) [μ₂.IsHaarMeasure]
      (f : CompactlySupportedContinuousMap G₂ ℂ) (e : CompactlySupportedContinuousMap G ℂ),
      ∃ g : CompactlySupportedContinuousMap G ℂ, (∀ x, g x = ∫ y, f y * e ((p y)⁻¹ * x) ∂μ₂) ∧
        tsupport g ⊆ p '' tsupport f * tsupport e ∧
        ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H),
          π.integrated μ (UnitaryRep.ccToL1 μ g) =
            (π.compHom p hp).integrated μ₂ (UnitaryRep.ccToL1 μ₂ f) ∘L π.integrated μ (UnitaryRep.ccToL1 μ e) := by
  intro G G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p hp μ _ μ₂ _ f e
  have hf : IsCompact (tsupport f) := f.hasCompactSupport.isCompact
  have hS : IsCompact (p '' tsupport f * tsupport e) :=
    (hf.image hp).mul e.hasCompactSupport.isCompact

  have hker : Continuous fun q : G × G₂ => f q.2 * e ((p q.2)⁻¹ * q.1) :=
    (f.continuous.comp continuous_snd).mul
      (e.continuous.comp ((hp.comp continuous_snd).inv.mul continuous_fst))
  have hz₂ : ∀ (x : G) (y : G₂), y ∉ tsupport f → f y * e ((p y)⁻¹ * x) = 0 := fun x y hy => by
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  have hz₁ : ∀ (x : G) (y : G₂), x ∉ p '' tsupport f * tsupport e →
      f y * e ((p y)⁻¹ * x) = 0 := fun x y hx => by
    by_contra hne
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
    exact hx ⟨p y, ⟨y, subset_tsupport _ h1, rfl⟩, (p y)⁻¹ * x, subset_tsupport _ h2,
      mul_inv_cancel_left _ _⟩
  have hcont : Continuous fun x : G => ∫ y, f y * e ((p y)⁻¹ * x) ∂μ₂ := by
    rw [← continuousOn_univ]
    exact continuousOn_integral_of_compact_support (μ := μ₂)
      (f := fun (x : G) (y : G₂) => f y * e ((p y)⁻¹ * x)) hf hker.continuousOn
      fun x y _ hy => hz₂ x y hy
  have hzero : ∀ x : G, x ∉ p '' tsupport f * tsupport e →
      ∫ y, f y * e ((p y)⁻¹ * x) ∂μ₂ = 0 := fun x hx => by
    simp only [hz₁ x _ hx, integral_zero]
  refine ⟨⟨⟨fun x => ∫ y, f y * e ((p y)⁻¹ * x) ∂μ₂, hcont⟩, HasCompactSupport.intro hS hzero⟩,
    fun _ => rfl, ?_, ?_⟩
  · refine closure_minimal (fun x hx => ?_) hS.isClosed
    by_contra hx'
    exact hx (hzero x hx')
  · intro H _ _ _ π
    ext v
    rw [ContinuousLinearMap.comp_apply]
    simp only [UnitaryRep.integrated_ccToL1_apply, UnitaryRep.compHom_apply]
    change ∫ x, (∫ y, f y * e ((p y)⁻¹ * x) ∂μ₂) • π x v ∂μ = _
    have hint : Integrable
        (Function.uncurry fun (x : G) (y : G₂) => (f y * e ((p y)⁻¹ * x)) • π x v) (μ.prod μ₂) := by
      refine Continuous.integrable_of_hasCompactSupport
        (hker.smul ((π.continuous_orbit v).comp continuous_fst)) ?_
      refine HasCompactSupport.intro (hS.prod hf) fun q hq => ?_
      have h0 : f q.2 * e ((p q.2)⁻¹ * q.1) = 0 := by
        rcases not_and_or.1 (mt Set.mem_prod.2 hq) with h | h
        · exact hz₁ _ _ h
        · exact hz₂ _ _ h
      change (f q.2 * e ((p q.2)⁻¹ * q.1)) • π q.1 v = 0
      rw [h0, zero_smul]
    have he : Integrable (fun z => e z • π z v) μ :=
      (e.continuous.smul (π.continuous_orbit v)).integrable_of_hasCompactSupport
        e.hasCompactSupport.smul_right
    simp only [← integral_smul_const]
    rw [integral_integral_swap hint]
    congr 1
    funext y
    rw [← ContinuousLinearMap.integral_comp_comm _ he, ← integral_smul,
      ← integral_mul_left_eq_self _ (p y)]
    simp only [inv_mul_cancel_left, UnitaryRep.map_mul_apply, map_smul, smul_smul]
