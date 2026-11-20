import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CancelArtinianNoetherianSummandStatement

namespace GlobalTheory

/- English proof (translation)
Use `letI : Module (FreeAlgebra k ι) W := Module.compHom W φ.toRingHom`. Use `⟨fun c r w => ?_⟩` and prove the remaining obligations. Use `show φ (c • r) w = c • φ r w`. Rewrite using `[map_smul]`. Both sides reduce to the same expression.
-/
theorem freeAlgebra_compHom_isScalarTower {k ι W : Type} [Field k] [AddCommGroup W] [Module k W]
    (φ : FreeAlgebra k ι →ₐ[k] Module.End k W) :
    @IsScalarTower k (FreeAlgebra k ι) W _ (Module.compHom W φ.toRingHom).toSMul _ := by
  letI : Module (FreeAlgebra k ι) W := Module.compHom W φ.toRingHom
  refine ⟨fun c r w => ?_⟩
  show φ (c • r) w = c • φ r w
  rw [map_smul]
  rfl

/- English proof (translation)
Introduce `k ι V V' U _ _ _ _ _ _ _ _ _ _ a b c ⟨e, he⟩`. Set `φa : (FreeAlgebra k ι) →ₐ[k] Module.End k V` to `FreeAlgebra.lift k a`. Set `φb : (FreeAlgebra k ι) →ₐ[k] Module.End k V'` to `FreeAlgebra.lift k b`. Set `φc : (FreeAlgebra k ι) →ₐ[k] Module.End k U` to `FreeAlgebra.lift k c`. Use `letI iV : Module (FreeAlgebra k ι) V := Module.compHom V φa.toRingHom`.

Use `letI iV' : Module (FreeAlgebra k ι) V' := Module.compHom V' φb.toRingHom`. Use `letI iU : Module (FreeAlgebra k ι) U := Module.compHom U φc.toRingHom`. Use `haveI tV : IsScalarTower k (FreeAlgebra k ι) V := freeAlgebra_compHom_isScalarTower φa`. Use `haveI tV' : IsScalarTower k (FreeAlgebra k ι) V' := freeAlgebra_compHom_isScalarTower φb`. Use `haveI tU : IsScalarTower k (FreeAlgebra k ι) U := freeAlgebra_compHom_isScalarTower φc`.

Use `haveI : IsArtinian (FreeAlgebra k ι) U := isArtinian_of_tower k inferInstance`. Use `haveI : IsNoetherian (FreeAlgebra k ι) U := isNoetherian_of_tower k inferInstance`. Establish `key : ∀ r : (FreeAlgebra k ι), ∀ x : V × U, e (φa r x.1, φc r x.2) = (φb r (e x).1, φc r (e x).2)`. Introduce `r`. Proceed by induction on `r using FreeAlgebra.induction with`.

Consider the case `grade0 s`. Introduce `x`. Simplify using `only [φa, φb, φc, AlgHom.commutes, Module.algebraMap_end_apply]`. Conclude with `e.map_smul s x`. Consider the case `grade1 i`.

Introduce `x`. Use `he i x` as an intermediate fact. Simplify using `only [φa, φb, φc, FreeAlgebra.lift_ι_apply]`. Simplify using `using this`. Consider the case `mul r s hr hs`.

Introduce `x`. Establish `h1` using `hs x`. Establish `h2` using `hr (φa s x.1, φc s x.2)`. Simplify using `only [map_mul, Module.End.mul_apply]`. Rewrite using `[h2, h1]`.

Consider the case `add r s hr hs`. Introduce `x`. Establish `h1` using `hr x`. Establish `h2` using `hs x`. Establish `hsum : ((φa (r + s)) x.1, (φc (r + s)) x.2) = ((φa r) x.1, (φc r) x.2) + ((φa s) x.1, (φc s) x.2)`.

Simplify using `[map_add]`. Rewrite using `[hsum, map_add, h1, h2]`. Simplify using `[map_add]`. Set `eR : (V × U) ≃ₗ[(FreeAlgebra k ι)] (V' × U)` to `{ e.toAddEquiv with map_smul' := fun r x => key r x }`. Take `⟨f⟩` from `GlobalTheory.T.cancel_artinian_noetherian_summand (FreeAlgebra k ι) V V' U ⟨eR⟩`.

Use `⟨f.restrictScalars k, fun i x => ?_⟩` and prove the remaining obligations. Establish `h : f (FreeAlgebra.ι k i • x) = FreeAlgebra.ι k i • f x` using `f.map_smul _ _`. Express the relevant statement in the definitionally equal form `f (φa (FreeAlgebra.ι k i) x) = φb (FreeAlgebra.ι k i) (f x) at h`. Simplify using `only [φa, φb, FreeAlgebra.lift_ι_apply] at h`. Conclude with `h`.
-/
theorem endFamily_cancel : ∀ (k ι V V' U : Type) [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    [AddCommGroup U] [Module k U] [FiniteDimensional k U] (a : ι → Module.End k V)
    (b : ι → Module.End k V') (c : ι → Module.End k U),
    (∃ e : (V × U) ≃ₗ[k] (V' × U), ∀ i x, e ((a i).prodMap (c i) x) = (b i).prodMap (c i) (e x)) →
      ∃ e : V ≃ₗ[k] V', ∀ i x, e (a i x) = b i (e x) := by
  intro k ι V V' U _ _ _ _ _ _ _ _ _ _ a b c ⟨e, he⟩
  let φa : (FreeAlgebra k ι) →ₐ[k] Module.End k V := FreeAlgebra.lift k a
  let φb : (FreeAlgebra k ι) →ₐ[k] Module.End k V' := FreeAlgebra.lift k b
  let φc : (FreeAlgebra k ι) →ₐ[k] Module.End k U := FreeAlgebra.lift k c
  letI iV : Module (FreeAlgebra k ι) V := Module.compHom V φa.toRingHom
  letI iV' : Module (FreeAlgebra k ι) V' := Module.compHom V' φb.toRingHom
  letI iU : Module (FreeAlgebra k ι) U := Module.compHom U φc.toRingHom
  haveI tV : IsScalarTower k (FreeAlgebra k ι) V := freeAlgebra_compHom_isScalarTower φa
  haveI tV' : IsScalarTower k (FreeAlgebra k ι) V' := freeAlgebra_compHom_isScalarTower φb
  haveI tU : IsScalarTower k (FreeAlgebra k ι) U := freeAlgebra_compHom_isScalarTower φc
  haveI : IsArtinian (FreeAlgebra k ι) U := isArtinian_of_tower k inferInstance
  haveI : IsNoetherian (FreeAlgebra k ι) U := isNoetherian_of_tower k inferInstance

  have key : ∀ r : (FreeAlgebra k ι), ∀ x : V × U, e (φa r x.1, φc r x.2) = (φb r (e x).1, φc r (e x).2) := by
    intro r
    induction r using FreeAlgebra.induction with
    | grade0 s =>
      intro x
      simp only [φa, φb, φc, AlgHom.commutes, Module.algebraMap_end_apply]
      exact e.map_smul s x
    | grade1 i =>
      intro x
      have := he i x
      simp only [φa, φb, φc, FreeAlgebra.lift_ι_apply]
      simpa using this
    | mul r s hr hs =>
      intro x
      have h1 := hs x
      have h2 := hr (φa s x.1, φc s x.2)
      simp only [map_mul, Module.End.mul_apply]
      rw [h2, h1]
    | add r s hr hs =>
      intro x
      have h1 := hr x
      have h2 := hs x
      have hsum : ((φa (r + s)) x.1, (φc (r + s)) x.2)
          = ((φa r) x.1, (φc r) x.2) + ((φa s) x.1, (φc s) x.2) := by
        simp [map_add]
      rw [hsum, map_add, h1, h2]
      simp [map_add]
  let eR : (V × U) ≃ₗ[(FreeAlgebra k ι)] (V' × U) :=
    { e.toAddEquiv with
      map_smul' := fun r x => key r x }
  obtain ⟨f⟩ := GlobalTheory.T.cancel_artinian_noetherian_summand (FreeAlgebra k ι) V V' U ⟨eR⟩
  refine ⟨f.restrictScalars k, fun i x => ?_⟩
  have h : f (FreeAlgebra.ι k i • x) = FreeAlgebra.ι k i • f x := f.map_smul _ _
  change f (φa (FreeAlgebra.ι k i) x) = φb (FreeAlgebra.ι k i) (f x) at h
  simp only [φa, φb, FreeAlgebra.lift_ι_apply] at h
  exact h

end GlobalTheory
