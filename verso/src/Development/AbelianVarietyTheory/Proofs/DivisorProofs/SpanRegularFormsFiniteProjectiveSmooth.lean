import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraEqRangeExteriorPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraClosurePropertiesStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

/- English proof (translation)
Take `⟨s, hs⟩` from `Module.projective_def'.1 (inferInstance : Module.Projective R V)`. Use `haveI : Module.Free R (⋀[R]^n (V →₀ R)) := exteriorPower.instFree R n`. Use `Module.Projective.of_split (exteriorPower.map n s) (exteriorPower.map n (Finsupp.linearCombination R id)) ?_` and prove the remaining obligations. Rewrite using `[← exteriorPower.map_comp, hs, exteriorPower.map_id]`.
-/
theorem projective_exteriorPower_of_projective (R V : Type) [CommRing R] [AddCommGroup V] [Module R V]
    [Module.Projective R V] (n : ℕ) : Module.Projective R (⋀[R]^n V) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective R V)
  haveI : Module.Free R (⋀[R]^n (V →₀ R)) := exteriorPower.instFree R n
  refine Module.Projective.of_split (exteriorPower.map n s)
    (exteriorPower.map n (Finsupp.linearCombination R id)) ?_
  rw [← exteriorPower.map_comp, hs, exteriorPower.map_id]

/- English proof (translation)
Introduce `k K _ _ _ B _ _ p W _ _ _ _ e he hr`. Take `⟨e', he', hre', -⟩` from `GlobalTheory.T.kahlerFormsOverSubalgebra_eq_range_exteriorPower k K B p`. Establish `hom` using `fun a ha => ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K B p p).2.1 a ha)`. Set `S : Submodule k W` to `(omB k K B p).comap (e.restrictScalars k)`. Set `T : Submodule B W` to `{ carrier := (S : Set W) add_mem' := S.add_mem zero_mem' := S.zero_mem smul_mem' := fun c w hw => by`.

Express the relevant statement in the definitionally equal form `e ((c : K) • w) ∈ omB k K B p`. Rewrite using `[map_smul]`. Conclude with `(hom _ hw).2.2.2 c c.2 }`. Establish `hST : Submodule.span B (S : Set W) = T` using `Submodule.span_eq T`. Express the relevant statement in the definitionally equal form `Module.Finite B (Submodule.span B (S : Set W)) ∧ Module.Projective B (Submodule.span B (S : Set W))`.

Rewrite using `[hST]`. Set `g : T →ₗ[B] DR k K` to `{ toFun := fun w => e w map_add' := fun w w' => by simp map_smul' := fun c w => by`. Express the relevant statement in the definitionally equal form `e ((c : K) • (w : W)) = (c : K) • e w`. Conclude with `e.map_smul (c : K) w }`. Establish `hg : Function.Injective g` using `fun w w' h => Subtype.ext (he h)`.

Establish `hrg : LinearMap.range g = LinearMap.range e'`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, rfl⟩`. Take `⟨z, hz⟩` from `(hre' _).1 w.2`.

Conclude with `⟨z, hz⟩`. Introduce and unpack `⟨z, rfl⟩`. Establish `hy : e' z ∈ omB k K B p` using `(hre' _).2 ⟨z, rfl⟩`. Establish `hy' : e' z ∈ LinearMap.range e` using `by rw [hr]; exact (hom _ hy).2.2.1`. Take `⟨w, hw⟩` from `hy'`.

Establish `hwT : w ∈ T`. Express the relevant statement in the definitionally equal form `e w ∈ omB k K B p`. Rewrite using `[hw]`. Conclude with `hy`. Conclude with `⟨⟨w, hwT⟩, hw⟩`.

Set `E : T ≃ₗ[B] ⋀[B]^p Ω[B⁄k]` to `(LinearEquiv.ofInjective g hg).trans ((LinearEquiv.ofEq _ _ hrg).trans (LinearEquiv.ofInjective e' he').symm)`. Use `haveI : Module.Projective B (⋀[B]^p Ω[B⁄k]) := projective_exteriorPower_of_projective B _ p`. Conclude with `⟨Module.Finite.equiv E.symm, Module.Projective.of_equiv E.symm⟩`.
-/
theorem span_omB_comap_finite_projective : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] [Algebra.Smooth k B] (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → Module.Finite B (Submodule.span B ((omB k K B p).comap (e.restrictScalars k) : Set W)) ∧ Module.Projective B (Submodule.span B ((omB k K B p).comap (e.restrictScalars k) : Set W)) := by
  intro k K _ _ _ B _ _ p W _ _ _ _ e he hr
  obtain ⟨e', he', hre', -⟩ := GlobalTheory.T.kahlerFormsOverSubalgebra_eq_range_exteriorPower k K B p
  have hom := fun a ha => ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K B p p).2.1 a ha)
  let S : Submodule k W := (omB k K B p).comap (e.restrictScalars k)
  let T : Submodule B W :=
    { carrier := (S : Set W)
      add_mem' := S.add_mem
      zero_mem' := S.zero_mem
      smul_mem' := fun c w hw => by
        change e ((c : K) • w) ∈ omB k K B p
        rw [map_smul]
        exact (hom _ hw).2.2.2 c c.2 }
  have hST : Submodule.span B (S : Set W) = T := Submodule.span_eq T
  change Module.Finite B (Submodule.span B (S : Set W)) ∧ Module.Projective B (Submodule.span B (S : Set W))
  rw [hST]
  let g : T →ₗ[B] DR k K :=
    { toFun := fun w => e w
      map_add' := fun w w' => by simp
      map_smul' := fun c w => by
        change e ((c : K) • (w : W)) = (c : K) • e w
        exact e.map_smul (c : K) w }
  have hg : Function.Injective g := fun w w' h => Subtype.ext (he h)
  have hrg : LinearMap.range g = LinearMap.range e' := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨z, hz⟩ := (hre' _).1 w.2
      exact ⟨z, hz⟩
    · rintro ⟨z, rfl⟩
      have hy : e' z ∈ omB k K B p := (hre' _).2 ⟨z, rfl⟩
      have hy' : e' z ∈ LinearMap.range e := by rw [hr]; exact (hom _ hy).2.2.1
      obtain ⟨w, hw⟩ := hy'
      have hwT : w ∈ T := by
        change e w ∈ omB k K B p
        rw [hw]; exact hy
      exact ⟨⟨w, hwT⟩, hw⟩
  let E : T ≃ₗ[B] ⋀[B]^p Ω[B⁄k] :=
    (LinearEquiv.ofInjective g hg).trans ((LinearEquiv.ofEq _ _ hrg).trans (LinearEquiv.ofInjective e' he').symm)
  haveI : Module.Projective B (⋀[B]^p Ω[B⁄k]) := projective_exteriorPower_of_projective B _ p
  exact ⟨Module.Finite.equiv E.symm, Module.Projective.of_equiv E.symm⟩

end GlobalTheory.PD
