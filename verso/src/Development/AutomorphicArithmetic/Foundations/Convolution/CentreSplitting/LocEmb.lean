import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ClsBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.FormsIrr

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

/- English proof (translation)
Introduce `E _ _ _ n μ _ π V h`. Establish `hcar` using `h.carrier_eq`. Establish `hcen : ∀ ψ : Cm.carrier π, ψ.1 ∈ centralCuspForms E n` using `fun ψ => (hcar.le ψ.2).1`. Establish `hV : ∀ ψ : Cm.carrier π, clsL μ ψ.1 ∈ V` using `fun ψ => (hcar.le ψ.2).2`. Take `⟨hinj, -, heq, -⟩` from `UpperTheory.ConvolutionTheory.Dp.clsBasic E n μ`.

Take `⟨-, -, -, hdense⟩` from `UpperTheory.ConvolutionTheory.Dp.formsIrr E n μ V h.summand`. Set `J0 : Cm.carrier π →ₗ[ℂ] V` to `((clsL μ).comp (Cm.carrier π).subtype).codRestrict V hV`. Establish `hJ0 : ∀ ψ, (J0 ψ).1 = clsL μ ψ.1` using `fun _ => rfl`. Use `⟨J0 ∘ₗ (Cm.carrierEq π).symm.toLinearMap, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hi : Function.Injective J0` using `fun a b hab => by`.

Establish `h0 : clsL μ (a.1 - b.1) = 0`. Rewrite using `[map_sub, ← hJ0, ← hJ0, hab, sub_self]`. Conclude with `Subtype.ext (sub_eq_zero.1 (hinj _ (Submodule.sub_mem _ (hcen a) (hcen b)) h0))`. Conclude with `hi.comp (Cm.carrierEq π).symm.injective`. Introduce `v`.

Rewrite using `[Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]`. Establish `himg : (Subtype.val '' Set.range (J0 ∘ₗ (Cm.carrierEq π).symm.toLinearMap) : Set (LL μ)) = ((formsIn μ V).map (clsL μ) : Submodule ℂ (LL μ))`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨φ, rfl⟩, rfl⟩`.

Conclude with `⟨_, hcar ▸ ((Cm.carrierEq π).symm φ).2, rfl⟩`. Introduce and unpack `⟨ψ, hψ, rfl⟩`. Establish `hψ' : ψ ∈ Cm.carrier π` using `hcar ▸ hψ`. Use `⟨_, ⟨Cm.carrierEq π ⟨ψ, hψ'⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `[hJ0]`.

Establish `hc : (v : LL μ) ∈ closure (((formsIn μ V).map (clsL μ) : Submodule ℂ (LL μ)) : Set (LL μ))` using `hdense.ge v.2`. Rewrite `hc` using `[← himg]`. Conclude with `hc`. Introduce `ψ`. Simplify using `[hJ0]`.

Introduce `w g φ`. Take `⟨ψ, rfl⟩` from `(Cm.carrierEq π).surjective φ`. Apply `Subtype.ext` to reduce the goal to its premises. Use `set ψ' := (Cm.carrierEq π).symm (π.locRep w g (Cm.carrierEq π ψ)) with hψ'`. Establish `hx : ∀ x, ψ'.1.1 x = ψ.1.1 (x * finGL E n (locGL E n w g))` using `fun x => by`.

Establish `h1 : Cm.carrierEq π ψ' = π.locRep w g (Cm.carrierEq π ψ)` using `(Cm.carrierEq π).apply_symm_apply _`. Conclude with `congrArg (fun f : π.V => f.1.1 x) h1`. Establish `h2` using `heq ψ.1 (hcen ψ) ψ'.1 (finGL E n (locGL E n w g)) hx`. Use `show clsL μ ψ'.1 = RG μ (finGL E n (locGL E n w g)) (clsL μ ((Cm.carrierEq π).symm (Cm.carrierEq π ψ)).1)`. Rewrite using `[LinearEquiv.symm_apply_apply]`.

Conclude with `h2`.
-/
theorem UpperTheory.ConvolutionTheory.Dp.locEmb :
    UpperTheory.ConvolutionTheory.Dp.LocEmb := by
  intro E _ _ _ n μ _ π V h
  have hcar := h.carrier_eq
  have hcen : ∀ ψ : Cm.carrier π, ψ.1 ∈ centralCuspForms E n := fun ψ => (hcar.le ψ.2).1
  have hV : ∀ ψ : Cm.carrier π, clsL μ ψ.1 ∈ V := fun ψ => (hcar.le ψ.2).2
  obtain ⟨hinj, -, heq, -⟩ := UpperTheory.ConvolutionTheory.Dp.clsBasic E n μ
  obtain ⟨-, -, -, hdense⟩ := UpperTheory.ConvolutionTheory.Dp.formsIrr E n μ V h.summand
  let J0 : Cm.carrier π →ₗ[ℂ] V := ((clsL μ).comp (Cm.carrier π).subtype).codRestrict V hV
  have hJ0 : ∀ ψ, (J0 ψ).1 = clsL μ ψ.1 := fun _ => rfl
  refine ⟨J0 ∘ₗ (Cm.carrierEq π).symm.toLinearMap, ?_, ?_, ?_, ?_⟩
  · have hi : Function.Injective J0 := fun a b hab => by
      have h0 : clsL μ (a.1 - b.1) = 0 := by
        rw [map_sub, ← hJ0, ← hJ0, hab, sub_self]
      exact Subtype.ext (sub_eq_zero.1 (hinj _ (Submodule.sub_mem _ (hcen a) (hcen b)) h0))
    exact hi.comp (Cm.carrierEq π).symm.injective
  · intro v
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
    have himg : (Subtype.val '' Set.range (J0 ∘ₗ (Cm.carrierEq π).symm.toLinearMap) : Set (LL μ)) =
        ((formsIn μ V).map (clsL μ) : Submodule ℂ (LL μ)) := by
      ext x
      constructor
      · rintro ⟨_, ⟨φ, rfl⟩, rfl⟩
        exact ⟨_, hcar ▸ ((Cm.carrierEq π).symm φ).2, rfl⟩
      · rintro ⟨ψ, hψ, rfl⟩
        have hψ' : ψ ∈ Cm.carrier π := hcar ▸ hψ
        refine ⟨_, ⟨Cm.carrierEq π ⟨ψ, hψ'⟩, rfl⟩, ?_⟩
        simp [hJ0]
    have hc : (v : LL μ) ∈ closure (((formsIn μ V).map (clsL μ) : Submodule ℂ (LL μ)) : Set (LL μ)) :=
      hdense.ge v.2
    rw [← himg] at hc
    exact hc
  · intro ψ
    simp [hJ0]
  · intro w g φ
    obtain ⟨ψ, rfl⟩ := (Cm.carrierEq π).surjective φ
    apply Subtype.ext
    set ψ' := (Cm.carrierEq π).symm (π.locRep w g (Cm.carrierEq π ψ)) with hψ'
    have hx : ∀ x, ψ'.1.1 x = ψ.1.1 (x * finGL E n (locGL E n w g)) := fun x => by
      have h1 : Cm.carrierEq π ψ' = π.locRep w g (Cm.carrierEq π ψ) := (Cm.carrierEq π).apply_symm_apply _
      exact congrArg (fun f : π.V => f.1.1 x) h1
    have h2 := heq ψ.1 (hcen ψ) ψ'.1 (finGL E n (locGL E n w g)) hx
    show clsL μ ψ'.1 = RG μ (finGL E n (locGL E n w g)) (clsL μ ((Cm.carrierEq π).symm (Cm.carrierEq π ψ)).1)
    rw [LinearEquiv.symm_apply_apply]
    exact h2
