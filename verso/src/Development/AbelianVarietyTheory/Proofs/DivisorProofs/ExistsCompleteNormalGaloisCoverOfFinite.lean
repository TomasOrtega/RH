import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionEtaleCompletionToCompleteLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.GalCover

/- English proof (translation)
Introduce `A R _ _ _ _ _ b hA hfin hinj`. Take `⟨hnoeth, hnorm, hcomp, hchar⟩` from `hA`. Use `letI : Algebra A R := b.toAlgebra`. Use `haveI : Module.Finite A R := hfin`. Use `haveI : Algebra.IsIntegral A R := Algebra.IsIntegral.of_finite A R`.

Set `K` to `FractionRing A`. Use `haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective A K)`. Set `Ω` to `AlgebraicClosure K`. Establish `hιK : Function.Injective (algebraMap A Ω)`. Rewrite using `[IsScalarTower.algebraMap_eq A K Ω]`.

Conclude with `(algebraMap K Ω).injective.comp (IsFractionRing.injective A K)`. Use `haveI : Module.IsTorsionFree A R := Module.isTorsionFree_iff_algebraMap_injective.2 hinj`. Use `haveI : Module.IsTorsionFree A Ω := Module.isTorsionFree_iff_algebraMap_injective.2 hιK`. Use `haveI : Algebra.IsAlgebraic A R := Algebra.IsIntegral.isAlgebraic`. Set `φ : R →ₐ[A] Ω` to `IsAlgClosed.lift`.

Establish `hφinj : Function.Injective φ`. Establish `hk : (RingHom.ker (φ : R →+* Ω)).comap (algebraMap A R) = ⊥`. Use `eq_bot_iff.2 fun a ha => ?_` and prove the remaining obligations. Establish `h1 : φ (algebraMap A R a) = 0` using `ha`. Rewrite `h1` using `[φ.commutes]`.

Conclude with `(Ideal.mem_bot).2 (hιK (h1.trans (map_zero _).symm))`. Establish `h2` using `Ideal.eq_bot_of_comap_eq_bot hk`. Conclude with `(RingHom.injective_iff_ker_eq_bot _).2 h2`. Establish `hint : ∀ x : R, IsIntegral A (φ x)` using `fun x => (Algebra.IsIntegral.isIntegral (R := A) x).map φ`. Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := A) (M := R)`.

Set `L : IntermediateField K Ω` to `IntermediateField.adjoin K ((φ '' (s : Set R)) : Set Ω)`. Establish `hintK : ∀ x : R, IsIntegral K (φ x)` using `fun x => (hint x).tower_top`. Use `haveI : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin (by`. Introduce and unpack `_ ⟨x, -, rfl⟩`. Conclude with `hintK x)`.

Establish `hmemL : ∀ x : R, φ x ∈ L` using `fun x => by`. Establish `hx : x ∈ Submodule.span A (s : Set R)` using `hs ▸ Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact IntermediateField.subset_adjoin K _ ⟨y, hy, rfl⟩`. Consider the case `zero => rw [map_zero]`.

Conclude with `zero_mem L`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `add_mem hy hz`. Consider the case `smul r y _ hy`. Rewrite using `[map_smul, Algebra.smul_def]`.

Use `mul_mem ?_ hy` and prove the remaining obligations. Rewrite using `[IsScalarTower.algebraMap_apply A K Ω]`. Conclude with `L.algebraMap_mem _`. Set `M : IntermediateField K Ω` to `IntermediateField.normalClosure K L Ω`. Establish `hmem : ∀ x : R, φ x ∈ M` using `fun x => IntermediateField.le_normalClosure L (hmemL x)`.

Set `W` to `integralClosure A M`. Use `haveI hWf : Module.Finite A W := IsIntegralClosure.finite A K M W`. Use `haveI : IsLocalRing W := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := A) W`. Establish `hAM : Function.Injective (algebraMap A M)`. Rewrite using `[IsScalarTower.algebraMap_eq A K M]`.

Conclude with `(algebraMap K M).injective.comp (IsFractionRing.injective A K)`. Establish `hinjW : Function.Injective (algebraMap A W)` using `fun x y h => hAM (congrArg Subtype.val h)`. Set `φM : R →+* M` to `(φ : R →+* Ω).codRestrict M hmem`. Establish `hran : ∀ x : R, φM x ∈ W` using `fun x => by show IsIntegral A (φM x)`. Conclude with `(isIntegral_algHom_iff ((IntermediateField.val M).restrictScalars A) Subtype.val_injective).1 (hint x)`.

Set `θ : R →+* W` to `φM.codRestrict W hran`. Establish `hθval : ∀ x : R, (((θ x : M)) : Ω) = φ x` using `fun x => rfl`. Establish `hθinj : Function.Injective θ` using `fun x y h => hφinj (by`. Rewrite using `[← hθval, ← hθval, h])`. Establish `hcomm : θ.comp b = algebraMap A W` using `RingHom.ext fun a => by`.

Apply `Subtype.val_injective` to reduce the goal to its premises. Apply `Subtype.val_injective` to reduce the goal to its premises. Conclude with `φ.commutes a`. Use `haveI : CharZero W := charZero_of_injective_algebraMap hinjW`. Establish `hθfin : θ.Finite` using `RingHom.Finite.of_comp_finite (f := b) (by rw [hcomm]; exact RingHom.finite_algebraMap.2 hWf)`.

Establish `hθloc : IsLocalHom θ` using `RingHom.IsIntegral.isLocalHom hθfin.to_isIntegral hθinj`. Set `res : (M ≃ₐ[K] M) →* (W ≃+* W)` to `{ toFun := fun σ => { toFun := fun x => ⟨σ (x : M), x.2.map ((σ : M →ₐ[K] M).restrictScalars A)⟩ invFun := fun x => ⟨σ.symm (x : M), x.2.map ((σ.symm : M →ₐ[K] M).restrictScalars A)⟩ left_inv := fun x => Subtype.ext (σ.symm_apply_apply (x : M)) right_inv := fun x => Subtype.ext ( …`. Use `⟨W, inferInstance, inferInstance, inferInstance, θ, ⟨IsNoetherianRing.of_finite A W, integralClosure.isIntegrallyClosedOfFiniteExtension K, GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local A W, inferInstance⟩, hθloc, hθinj, hθfin, fun r hr => ?_⟩` and prove the remaining obligations. Establish `hfix : ∀ σ : M ≃ₐ[K] M, σ (θ r : M) = (θ r : M)` using `fun σ => by`. Establish `h1` using `hr (res σ) (res.isOfFinOrder (isOfFinOrder_of_finite σ)) (fun a => by`.

Rewrite using `[← RingHom.comp_apply θ b, hcomm]`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show σ (algebraMap A M a) = algebraMap A M a`. Rewrite using `[IsScalarTower.algebraMap_apply A K M]`. Conclude with `σ.commutes _)`.

Conclude with `congrArg Subtype.val h1`. Take `⟨k, hk⟩` from `(IsGalois.mem_range_algebraMap_iff_fixed (F := K) (θ r : M)).2 hfix`. Establish `hkint : IsIntegral A k`. Establish `: IsIntegral A (algebraMap K M k)` using `hk ▸ (θ r).2`. Conclude with `(isIntegral_algHom_iff (IsScalarTower.toAlgHom A K M) (algebraMap K M).injective).1 this`.

Take `⟨a, ha⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hkint`. Use `⟨a, hφinj ?_⟩` and prove the remaining obligations. Use `show φ (algebraMap A R a) = φ r`. Rewrite using `[φ.commutes, ← hθval, ← hk, ← ha, IsScalarTower.algebraMap_apply A K Ω]`. Both sides reduce to the same expression.
-/
theorem exists_isCN_galois_of_finite : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [CommRing R] [IsDomain R] (b : A →+* R), IsCN A → b.Finite → Function.Injective b → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (θ : R →+* R'), IsCN R' ∧ IsLocalHom θ ∧ Function.Injective θ ∧ θ.Finite ∧ ∀ r : R, (∀ σ : R' ≃+* R', IsOfFinOrder σ → (∀ a, σ (θ (b a)) = θ (b a)) → σ (θ r) = θ r) → r ∈ b.range := by
  intro A R _ _ _ _ _ b hA hfin hinj
  obtain ⟨hnoeth, hnorm, hcomp, hchar⟩ := hA
  letI : Algebra A R := b.toAlgebra
  haveI : Module.Finite A R := hfin
  haveI : Algebra.IsIntegral A R := Algebra.IsIntegral.of_finite A R
  let K := FractionRing A
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective A K)
  let Ω := AlgebraicClosure K
  have hιK : Function.Injective (algebraMap A Ω) := by
    rw [IsScalarTower.algebraMap_eq A K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective A K)
  haveI : Module.IsTorsionFree A R := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  haveI : Module.IsTorsionFree A Ω := Module.isTorsionFree_iff_algebraMap_injective.2 hιK
  haveI : Algebra.IsAlgebraic A R := Algebra.IsIntegral.isAlgebraic
  let φ : R →ₐ[A] Ω := IsAlgClosed.lift
  have hφinj : Function.Injective φ := by
    have hk : (RingHom.ker (φ : R →+* Ω)).comap (algebraMap A R) = ⊥ := by
      refine eq_bot_iff.2 fun a ha => ?_
      have h1 : φ (algebraMap A R a) = 0 := ha
      rw [φ.commutes] at h1
      exact (Ideal.mem_bot).2 (hιK (h1.trans (map_zero _).symm))
    have h2 := Ideal.eq_bot_of_comap_eq_bot hk
    exact (RingHom.injective_iff_ker_eq_bot _).2 h2
  have hint : ∀ x : R, IsIntegral A (φ x) := fun x => (Algebra.IsIntegral.isIntegral (R := A) x).map φ
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := R)
  let L : IntermediateField K Ω := IntermediateField.adjoin K ((φ '' (s : Set R)) : Set Ω)
  have hintK : ∀ x : R, IsIntegral K (φ x) := fun x => (hint x).tower_top
  haveI : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨x, -, rfl⟩
    exact hintK x)
  have hmemL : ∀ x : R, φ x ∈ L := fun x => by
    have hx : x ∈ Submodule.span A (s : Set R) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin K _ ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem L
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul r y _ hy =>
      rw [map_smul, Algebra.smul_def]
      refine mul_mem ?_ hy
      rw [IsScalarTower.algebraMap_apply A K Ω]
      exact L.algebraMap_mem _
  let M : IntermediateField K Ω := IntermediateField.normalClosure K L Ω
  have hmem : ∀ x : R, φ x ∈ M := fun x => IntermediateField.le_normalClosure L (hmemL x)
  let W := integralClosure A M
  haveI hWf : Module.Finite A W := IsIntegralClosure.finite A K M W
  haveI : IsLocalRing W := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := A) W
  have hAM : Function.Injective (algebraMap A M) := by
    rw [IsScalarTower.algebraMap_eq A K M]
    exact (algebraMap K M).injective.comp (IsFractionRing.injective A K)
  have hinjW : Function.Injective (algebraMap A W) := fun x y h => hAM (congrArg Subtype.val h)
  let φM : R →+* M := (φ : R →+* Ω).codRestrict M hmem
  have hran : ∀ x : R, φM x ∈ W := fun x => by
    show IsIntegral A (φM x)
    exact (isIntegral_algHom_iff ((IntermediateField.val M).restrictScalars A) Subtype.val_injective).1 (hint x)
  let θ : R →+* W := φM.codRestrict W hran
  have hθval : ∀ x : R, (((θ x : M)) : Ω) = φ x := fun x => rfl
  have hθinj : Function.Injective θ := fun x y h => hφinj (by
    rw [← hθval, ← hθval, h])
  have hcomm : θ.comp b = algebraMap A W := RingHom.ext fun a => by
    apply Subtype.val_injective
    apply Subtype.val_injective
    exact φ.commutes a
  haveI : CharZero W := charZero_of_injective_algebraMap hinjW
  have hθfin : θ.Finite := RingHom.Finite.of_comp_finite (f := b) (by rw [hcomm]; exact RingHom.finite_algebraMap.2 hWf)
  have hθloc : IsLocalHom θ := RingHom.IsIntegral.isLocalHom hθfin.to_isIntegral hθinj

  let res : (M ≃ₐ[K] M) →* (W ≃+* W) :=
    { toFun := fun σ =>
        { toFun := fun x => ⟨σ (x : M), x.2.map ((σ : M →ₐ[K] M).restrictScalars A)⟩
          invFun := fun x => ⟨σ.symm (x : M), x.2.map ((σ.symm : M →ₐ[K] M).restrictScalars A)⟩
          left_inv := fun x => Subtype.ext (σ.symm_apply_apply (x : M))
          right_inv := fun x => Subtype.ext (σ.apply_symm_apply (x : M))
          map_mul' := fun x y => Subtype.ext (map_mul σ (x : M) y)
          map_add' := fun x y => Subtype.ext (map_add σ (x : M) y) }
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨W, inferInstance, inferInstance, inferInstance, θ,
    ⟨IsNoetherianRing.of_finite A W, integralClosure.isIntegrallyClosedOfFiniteExtension K,
      GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local A W, inferInstance⟩,
    hθloc, hθinj, hθfin, fun r hr => ?_⟩
  have hfix : ∀ σ : M ≃ₐ[K] M, σ (θ r : M) = (θ r : M) := fun σ => by
    have h1 := hr (res σ) (res.isOfFinOrder (isOfFinOrder_of_finite σ)) (fun a => by
      rw [← RingHom.comp_apply θ b, hcomm]
      apply Subtype.ext
      show σ (algebraMap A M a) = algebraMap A M a
      rw [IsScalarTower.algebraMap_apply A K M]
      exact σ.commutes _)
    exact congrArg Subtype.val h1
  obtain ⟨k, hk⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (θ r : M)).2 hfix
  have hkint : IsIntegral A k := by
    have : IsIntegral A (algebraMap K M k) := hk ▸ (θ r).2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K M) (algebraMap K M).injective).1 this
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hkint
  refine ⟨a, hφinj ?_⟩
  show φ (algebraMap A R a) = φ r
  rw [φ.commutes, ← hθval, ← hk, ← ha, IsScalarTower.algebraMap_apply A K Ω]
  rfl

end GlobalTheory.GalCover
