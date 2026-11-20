import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsCompactUnitaryPointsAtPlaceFstMemCompact

noncomputable section

namespace PositivityTheory.HtPt.Htat

open GlobalTheory.CompanionTheory.Ar.HT NumberField TensorProduct

/- English proof (translation)
Introduce `A K _ _ _ _ _ E _ _ c p R N W Ω _ _ _ _ _ _ _ _ j hj ρ e h halt hadj hsurj hinj hlin`. Establish `hsym : ∀ w : W, hj.equiv.symm (j w) = (1 : K) ⊗ₜ[A] w`. Introduce `w`. Rewrite using `[LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul]`. Set `T : 𝓞 E →+* Module.End K (K ⊗[A] W)` to `(Module.End.baseChangeHom A K W).toRingHom.comp ρ`.

Establish `hT : ∀ a (w : W), T a ((1 : K) ⊗ₜ[A] w) = (1 : K) ⊗ₜ[A] (ρ a w)` using `fun a w => rfl`. Set `ρΩ : 𝓞 E →+* Module.End K Ω` to `{ toFun := fun a => hj.equiv.toLinearMap ∘ₗ T a ∘ₗ hj.equiv.symm.toLinearMap map_one' := by ext x; simp map_mul' := by intro a b; ext x; simp [Module.End.mul_apply] map_zero' := by ext x; simp map_add' := by intro a b; ext x; simp }`. Establish `hρ : ∀ a w, ρΩ a (j w) = j (ρ a w)`. Introduce `a w`. Use `show hj.equiv (T a (hj.equiv.symm (j w))) = _`.

Rewrite using `[hsym, hT, IsBaseChange.equiv_tmul, one_smul]`. Establish `hinjj : Function.Injective j`. Establish `h1 : Function.Injective ((Algebra.linearMap A K).rTensor W)` using `Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective A K)`. Introduce `x y hxy`. Apply `(TensorProduct.lid A W).symm.injective` to reduce the goal to its premises.

Apply `h1` to reduce the goal to its premises. Apply `hj.equiv.injective` to reduce the goal to its premises. Simplify using `only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one, IsBaseChange.equiv_tmul, one_smul]`. Conclude with `hxy`. Establish `hfg : (LinearMap.range j).FG` using `Module.Finite.iff_fg.mp (Module.Finite.range j)`.

Establish `hspan : Submodule.span K (LinearMap.range j : Set Ω) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `ω hω`. Use `clear hω`. Take `⟨t, rfl⟩` from `hj.equiv.surjective ω`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul s w`. Rewrite using `[IsBaseChange.equiv_tmul]`. Conclude with `Submodule.smul_mem _ s (Submodule.subset_span ⟨w, rfl⟩)`.

Consider the case `add x y hx hy`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Establish `hproj : Module.Projective A (LinearMap.range j)` using `Module.Projective.of_equiv (LinearEquiv.ofInjective j hinjj)`. Use `⟨{ om := LinearMap.range j om_lat := ⟨hfg, hspan⟩ om_proj := hproj ρΩ := ρΩ om_stable := ?_ e := e alt := halt adj := hadj e_surj := hsurj e_inj := hinj h := j.toAddMonoidHom.comp h h_mem := fun x => ⟨h x, rfl⟩ h_lin := ?_ }, rfl, rfl, fun x => rfl, hρ⟩` and prove the remaining obligations.

Introduce and unpack `a x ⟨w, rfl⟩`. Conclude with `⟨ρ a w, (hρ a w).symm⟩`. Introduce `a x`. Take `⟨y, hy⟩` from `hlin a x`. Use `⟨j y, ⟨y, rfl⟩, ?_⟩` and prove the remaining obligations.

Use `show j (h (a • x)) = ρΩ a (j (h x)) + p ^ R • j y`. Rewrite using `[hy, map_add, map_nsmul, hρ]`.
-/
theorem chart_build : ∀ (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (p R N : ℕ) (W Ω : Type) [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Projective A W] [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (j : W →ₗ[A] Ω), IsBaseChange K j → ∀ (ρ : 𝓞 E →+* Module.End A W) (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)) (h : (Fin N → 𝓞 E) →+ W), (∀ x, e x x = 0) → (∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (RingOfIntegers.mapRingEquiv c a • y)) → (∀ φ : (Fin N → 𝓞 E) →+ ZMod (p ^ R), ∃ x, e x = φ) → (∀ x, e x = 0 → ∃ x', x = (p ^ R) • x') → (∀ (a : 𝓞 E) x, ∃ y, h (a • x) = ρ a (h x) + (p ^ R) • y) → ∃ D : HTChart A K c p R N Ω, D.om = LinearMap.range j ∧ D.e = e ∧ (∀ x, D.h x = j (h x)) ∧ ∀ a w, D.ρΩ a (j w) = j (ρ a w) := by
  intro A K _ _ _ _ _ E _ _ c p R N W Ω _ _ _ _ _ _ _ _ j hj ρ e h halt hadj hsurj hinj hlin
  classical
  have hsym : ∀ w : W, hj.equiv.symm (j w) = (1 : K) ⊗ₜ[A] w := by
    intro w
    rw [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul]
  let T : 𝓞 E →+* Module.End K (K ⊗[A] W) := (Module.End.baseChangeHom A K W).toRingHom.comp ρ
  have hT : ∀ a (w : W), T a ((1 : K) ⊗ₜ[A] w) = (1 : K) ⊗ₜ[A] (ρ a w) := fun a w => rfl
  let ρΩ : 𝓞 E →+* Module.End K Ω :=
    { toFun := fun a => hj.equiv.toLinearMap ∘ₗ T a ∘ₗ hj.equiv.symm.toLinearMap
      map_one' := by ext x; simp
      map_mul' := by intro a b; ext x; simp [Module.End.mul_apply]
      map_zero' := by ext x; simp
      map_add' := by intro a b; ext x; simp }
  have hρ : ∀ a w, ρΩ a (j w) = j (ρ a w) := by
    intro a w
    show hj.equiv (T a (hj.equiv.symm (j w))) = _
    rw [hsym, hT, IsBaseChange.equiv_tmul, one_smul]
  have hinjj : Function.Injective j := by
    have h1 : Function.Injective ((Algebra.linearMap A K).rTensor W) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective A K)
    intro x y hxy
    apply (TensorProduct.lid A W).symm.injective
    apply h1
    apply hj.equiv.injective
    simp only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one,
      IsBaseChange.equiv_tmul, one_smul]
    exact hxy
  have hfg : (LinearMap.range j).FG := Module.Finite.iff_fg.mp (Module.Finite.range j)
  have hspan : Submodule.span K (LinearMap.range j : Set Ω) = ⊤ := by
    rw [eq_top_iff]
    intro ω hω
    clear hω
    obtain ⟨t, rfl⟩ := hj.equiv.surjective ω
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s w =>
      rw [IsBaseChange.equiv_tmul]
      exact Submodule.smul_mem _ s (Submodule.subset_span ⟨w, rfl⟩)
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  have hproj : Module.Projective A (LinearMap.range j) :=
    Module.Projective.of_equiv (LinearEquiv.ofInjective j hinjj)
  refine ⟨{ om := LinearMap.range j
            om_lat := ⟨hfg, hspan⟩
            om_proj := hproj
            ρΩ := ρΩ
            om_stable := ?_
            e := e
            alt := halt
            adj := hadj
            e_surj := hsurj
            e_inj := hinj
            h := j.toAddMonoidHom.comp h
            h_mem := fun x => ⟨h x, rfl⟩
            h_lin := ?_ }, rfl, rfl, fun x => rfl, hρ⟩
  · rintro a x ⟨w, rfl⟩
    exact ⟨ρ a w, (hρ a w).symm⟩
  · intro a x
    obtain ⟨y, hy⟩ := hlin a x
    refine ⟨j y, ⟨y, rfl⟩, ?_⟩
    show j (h (a • x)) = ρΩ a (j (h x)) + p ^ R • j y
    rw [hy, map_add, map_nsmul, hρ]

end PositivityTheory.HtPt.Htat
