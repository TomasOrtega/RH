import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.PrimeElementPlace

/- English proof (translation)
Introduce `L K _ _ cL cK n T hT ψ f _ hc hker hf hR`. Use `haveI hfr : IsFractionRing T L := IsFractionRing.of_field T L fun z => by`. Take `⟨a, ha, b, hb, hb0, e⟩` from `hT.frac z`. Use `⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `z = a / b`.

Rewrite using `[← e, mul_div_cancel_right₀ _ hb0]`. Use `haveI hP : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ`. Set `A : Subalgebra T L` to `Localization.subalgebra.ofField L (RingHom.ker ψ).primeCompl (RingHom.ker ψ).primeCompl_le_nonZeroDivisors`. Use `haveI : IsLocalization.AtPrime A (RingHom.ker ψ) := (inferInstance : IsLocalization (RingHom.ker ψ).primeCompl A)`. Use `haveI : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A (RingHom.ker ψ)`.

Use `letI : Algebra ℂ T := (cL.codRestrict T hT.const_mem).toAlgebra`. Use `haveI : Algebra.EssFiniteType ℂ T := hT.essFiniteType`. Use `haveI : IsNoetherianRing T := Algebra.EssFiniteType.isNoetherianRing ℂ T`. Use `haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing (RingHom.ker ψ).primeCompl A inferInstance`. Establish `hinjA : Function.Injective (algebraMap T A)`.

Introduce `x y h`. Conclude with `Subtype.ext (congrArg (fun z : A => (z : L)) h)`. Establish `hmax : IsLocalRing.maximalIdeal A = Ideal.span {algebraMap T A f}`. Rewrite using `[← IsLocalization.AtPrime.map_eq_maximalIdeal (RingHom.ker ψ) A, hker, Ideal.map_span, Set.image_singleton]`. Establish `hf' : algebraMap T A f ≠ 0` using `fun h => hf (hinjA (h.trans (map_zero _).symm))`.

Establish `hprinc : (IsLocalRing.maximalIdeal A).IsPrincipal` using `⟨⟨_, hmax⟩⟩`. Use `haveI : IsPrincipalIdealRing A := ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (R := A)).out 0 4).2 hprinc`. Use `haveI hdvrA : IsDiscreteValuationRing A := by`. Use `⟨?_⟩` and prove the remaining obligations. Rewrite using `[hmax]`.

Introduce `h`. Conclude with `hf' ((Ideal.span_singleton_eq_bot).1 h)`. Establish `hval : ∀ x : L, x ∈ A.toSubring ∨ x⁻¹ ∈ A.toSubring` using `fun x => by`. Break down `ValuationRing.isInteger_or_isInteger A x with ⟨y, hy⟩ | ⟨y, hy⟩` into its components or cases. Use `left`.

Rewrite using `[← hy]`. Conclude with `y.2`. Use `right`. Rewrite using `[← hy]`. Conclude with `y.2`.

Set `V : ValuationSubring L` to `ValuationSubring.ofSubring A.toSubring hval`. Set `e : A ≃+* V` to `{ toFun := fun x => ⟨x.1, x.2⟩, invFun := fun y => ⟨y.1, y.2⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl, map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl }`. Establish `hTA : ∀ t : L, t ∈ T → t ∈ V` using `fun t ht => A.algebraMap_mem (⟨t, ht⟩ : T)`. Establish `hcV : ∀ a, cL a ∈ V` using `fun a => hTA _ (hT.const_mem a)`. Establish `heft : (cL.codRestrict V hcV).EssFiniteType`.

Establish `h2 : (algebraMap T A).EssFiniteType` using `RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization A (RingHom.ker ψ).primeCompl)`. Establish `h3` using `(hT.essFiniteType.comp h2).comp (RingHom.FiniteType.of_surjective e.toRingHom e.surjective).essFiniteType`. Establish `e' : e.toRingHom.comp ((algebraMap T A).comp (cL.codRestrict T hT.const_mem)) = cL.codRestrict V hcV` using `RingHom.ext fun a => Subtype.ext rfl`. Conclude with `e' ▸ h3`. Set `S : Place cL` to `⟨V, hcV, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, heft⟩`.

Establish `hS : S.IsPrimeOf T`. Use `⟨fun t ht => hTA t ht, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨a, s, hs, rfl⟩` from `hx`. Establish `hs0 : (s : L) ≠ 0` using `fun h => hs (by`. Rewrite using `[show s = 0 from Subtype.ext h]`.

Conclude with `(RingHom.ker ψ).zero_mem)`. Establish `hinv : (s : L)⁻¹ ∈ V` using `⟨1, s, hs, by rw [map_one, one_mul]; rfl⟩`. Establish `hsV : (s : L) ∈ V` using `hTA _ s.2`. Establish `hu : IsUnit (⟨(s : L), hsV⟩ : S.ring)` using `isUnit_iff_exists_inv.2 ⟨⟨(s : L)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hs0)⟩`. Establish `hord : S.ord (s : L) = 0` using `S.ord_eq_zero (u := ⟨(s : L), hsV⟩) hu`.

Use `⟨a, a.2, s, s.2, hs0, hord, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(a : L) * (s : L)⁻¹ * s = a`. Rewrite using `[inv_mul_cancel_right₀ hs0]`. Establish `hunit : ∀ y : (RingHom.ker ψ).primeCompl, IsUnit (ψ y)` using `fun y => isUnit_iff_ne_zero.2 fun h => y.2 (RingHom.mem_ker.2 h)`. Set `ψS : S.ring →+* K` to `(IsLocalization.lift (M := (RingHom.ker ψ).primeCompl) (S := A) hunit).comp e.symm.toRingHom`.

Establish `hgen : ∀ (t : T) (h : (t : L) ∈ S.ring), ψS ⟨t, h⟩ = ψ t`. Introduce `t h`. Establish `h1 : e.symm ⟨t, h⟩ = algebraMap T A t` using `Subtype.ext rfl`. Use `show IsLocalization.lift _ (e.symm ⟨t, h⟩) = ψ t`. Rewrite using `[h1, IsLocalization.lift_eq]`.

Use `⟨S, hS, ψS, fun z => ?_, fun a => ?_, fun t => hgen t _, ?_⟩` and prove the remaining obligations. Take `⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hb0, e1⟩` from `hR.frac z`. Establish `hb : b ∈ (RingHom.ker ψ).primeCompl` using `fun h => hb0 (RingHom.mem_ker.1 h)`. Use `⟨e (IsLocalization.mk' A a ⟨b, hb⟩), ?_⟩` and prove the remaining obligations. Use `show IsLocalization.lift _ (e.symm (e _)) = z`.

Rewrite using `[RingEquiv.symm_apply_apply, IsLocalization.lift_mk'_spec]`. Conclude with `e1.symm.trans (mul_comm _ _)`. Conclude with `(hgen ⟨cL a, hT.const_mem a⟩ _).trans (hc a)`. Establish `h1 : (⟨f, hS.1 f f.2⟩ : S.ring) = e (algebraMap T A f)` using `Subtype.ext rfl`. Rewrite using `[h1, MulEquiv.irreducible_iff]`.

Conclude with `(IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax`.
-/
theorem main : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (T : Subring L) (hT : IsLocModel cL T) (ψ : T →+* K) (f : T), IsIntegrallyClosed T → (∀ a, ψ ⟨cL a, hT.const_mem a⟩ = cK a) → RingHom.ker ψ = Ideal.span {f} → f ≠ 0 → IsLocModel cK ψ.range → ∃ (S : Place cL) (hS : S.IsPrimeOf T) (ψS : S.ring →+* K), Function.Surjective ψS ∧ (∀ a, ψS (S.const a) = cK a) ∧ (∀ t : T, ψS ⟨t, hS.1 t t.2⟩ = ψ t) ∧ Irreducible (⟨f, hS.1 f f.2⟩ : S.ring) := by
  intro L K _ _ cL cK n T hT ψ f _ hc hker hf hR
  classical
  haveI hfr : IsFractionRing T L := IsFractionRing.of_field T L fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hT.frac z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    change z = a / b
    rw [← e, mul_div_cancel_right₀ _ hb0]
  haveI hP : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  let A : Subalgebra T L :=
    Localization.subalgebra.ofField L (RingHom.ker ψ).primeCompl (RingHom.ker ψ).primeCompl_le_nonZeroDivisors
  haveI : IsLocalization.AtPrime A (RingHom.ker ψ) := (inferInstance : IsLocalization (RingHom.ker ψ).primeCompl A)
  haveI : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A (RingHom.ker ψ)
  letI : Algebra ℂ T := (cL.codRestrict T hT.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ T := hT.essFiniteType
  haveI : IsNoetherianRing T := Algebra.EssFiniteType.isNoetherianRing ℂ T
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing (RingHom.ker ψ).primeCompl A inferInstance
  have hinjA : Function.Injective (algebraMap T A) := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : A => (z : L)) h)
  have hmax : IsLocalRing.maximalIdeal A = Ideal.span {algebraMap T A f} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (RingHom.ker ψ) A, hker, Ideal.map_span,
      Set.image_singleton]
  have hf' : algebraMap T A f ≠ 0 := fun h => hf (hinjA (h.trans (map_zero _).symm))
  have hprinc : (IsLocalRing.maximalIdeal A).IsPrincipal := ⟨⟨_, hmax⟩⟩
  haveI : IsPrincipalIdealRing A :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (R := A)).out 0 4).2 hprinc
  haveI hdvrA : IsDiscreteValuationRing A := by
    refine ⟨?_⟩
    rw [hmax]
    intro h
    exact hf' ((Ideal.span_singleton_eq_bot).1 h)
  have hval : ∀ x : L, x ∈ A.toSubring ∨ x⁻¹ ∈ A.toSubring := fun x => by
    rcases ValuationRing.isInteger_or_isInteger A x with ⟨y, hy⟩ | ⟨y, hy⟩
    · left; rw [← hy]; exact y.2
    · right; rw [← hy]; exact y.2
  let V : ValuationSubring L := ValuationSubring.ofSubring A.toSubring hval
  let e : A ≃+* V :=
    { toFun := fun x => ⟨x.1, x.2⟩, invFun := fun y => ⟨y.1, y.2⟩, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl }
  have hTA : ∀ t : L, t ∈ T → t ∈ V := fun t ht => A.algebraMap_mem (⟨t, ht⟩ : T)
  have hcV : ∀ a, cL a ∈ V := fun a => hTA _ (hT.const_mem a)
  have heft : (cL.codRestrict V hcV).EssFiniteType := by
    have h2 : (algebraMap T A).EssFiniteType := RingHom.essFiniteType_algebraMap.2
      (Algebra.EssFiniteType.of_isLocalization A (RingHom.ker ψ).primeCompl)
    have h3 := (hT.essFiniteType.comp h2).comp
      (RingHom.FiniteType.of_surjective e.toRingHom e.surjective).essFiniteType
    have e' : e.toRingHom.comp ((algebraMap T A).comp (cL.codRestrict T hT.const_mem)) =
        cL.codRestrict V hcV := RingHom.ext fun a => Subtype.ext rfl
    exact e' ▸ h3
  let S : Place cL := ⟨V, hcV, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, heft⟩
  have hS : S.IsPrimeOf T := by
    refine ⟨fun t ht => hTA t ht, fun x hx => ?_⟩
    obtain ⟨a, s, hs, rfl⟩ := hx
    have hs0 : (s : L) ≠ 0 := fun h => hs (by
      rw [show s = 0 from Subtype.ext h]; exact (RingHom.ker ψ).zero_mem)
    have hinv : (s : L)⁻¹ ∈ V := ⟨1, s, hs, by rw [map_one, one_mul]; rfl⟩
    have hsV : (s : L) ∈ V := hTA _ s.2
    have hu : IsUnit (⟨(s : L), hsV⟩ : S.ring) :=
      isUnit_iff_exists_inv.2 ⟨⟨(s : L)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hs0)⟩
    have hord : S.ord (s : L) = 0 := S.ord_eq_zero (u := ⟨(s : L), hsV⟩) hu
    refine ⟨a, a.2, s, s.2, hs0, hord, ?_⟩
    change (a : L) * (s : L)⁻¹ * s = a
    rw [inv_mul_cancel_right₀ hs0]
  have hunit : ∀ y : (RingHom.ker ψ).primeCompl, IsUnit (ψ y) := fun y =>
    isUnit_iff_ne_zero.2 fun h => y.2 (RingHom.mem_ker.2 h)
  let ψS : S.ring →+* K :=
    (IsLocalization.lift (M := (RingHom.ker ψ).primeCompl) (S := A) hunit).comp e.symm.toRingHom
  have hgen : ∀ (t : T) (h : (t : L) ∈ S.ring), ψS ⟨t, h⟩ = ψ t := by
    intro t h
    have h1 : e.symm ⟨t, h⟩ = algebraMap T A t := Subtype.ext rfl
    show IsLocalization.lift _ (e.symm ⟨t, h⟩) = ψ t
    rw [h1, IsLocalization.lift_eq]
  refine ⟨S, hS, ψS, fun z => ?_, fun a => ?_, fun t => hgen t _, ?_⟩
  · obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hb0, e1⟩ := hR.frac z
    have hb : b ∈ (RingHom.ker ψ).primeCompl := fun h => hb0 (RingHom.mem_ker.1 h)
    refine ⟨e (IsLocalization.mk' A a ⟨b, hb⟩), ?_⟩
    show IsLocalization.lift _ (e.symm (e _)) = z
    rw [RingEquiv.symm_apply_apply, IsLocalization.lift_mk'_spec]
    exact e1.symm.trans (mul_comm _ _)
  · exact (hgen ⟨cL a, hT.const_mem a⟩ _).trans (hc a)
  · have h1 : (⟨f, hS.1 f f.2⟩ : S.ring) = e (algebraMap T A f) := Subtype.ext rfl
    rw [h1, MulEquiv.irreducible_iff]
    exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax

end GlobalTheory.FieldPair.PrimeElementPlace

end
