import Mathlib
open AlgebraicGeometry CategoryTheory

namespace PositivityTheory.UnitarySelfGeneration

/- English proof (translation)
Introduce `O F L _ _ _ β θ hcl hu hz`. Use `set R : Subring F := β.range with hR`. Establish `hk : ∀ a ∈ RingHom.ker β, θ a = 0` using `fun a ha => hz a ((RingHom.mem_ker).mp ha)`. Set `θR : R →+* L` to `(Ideal.Quotient.lift (RingHom.ker β) θ hk).comp (RingHom.quotientKerEquivRange β).symm.toRingHom`. Establish `hθR : ∀ o : O, θR ⟨β o, o, rfl⟩ = θ o`.

Introduce `o`. Establish `h : (RingHom.quotientKerEquivRange β).symm ⟨β o, o, rfl⟩ = Ideal.Quotient.mk _ o`. Rewrite using `[RingEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Simplify using `only [θR, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, h, Ideal.Quotient.lift_mk]`.

Establish `hunit : ∀ r : nonZeroDivisors R, IsUnit (θR r)`. Introduce `r`. Take `⟨b, hb⟩` from `(r : R).2`. Establish `hne : (r : R) ≠ 0` using `nonZeroDivisors.ne_zero r.2`. Establish `hr : (r : R) = ⟨β b, b, rfl⟩` using `Subtype.ext hb.symm`.

Rewrite using `[hr, hθR]`. Apply `hu` to reduce the goal to its premises. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Rewrite using `[hr]`.

Conclude with `Subtype.ext h0`. Establish `hinj : Function.Injective R.subtype` using `Subtype.val_injective`. Set `ι : FractionRing R →+* F` to `IsFractionRing.lift hinj`. Establish `hsurj : Function.Surjective ι`. Establish `h` using `IsFractionRing.lift_fieldRange (K := FractionRing R) hinj`.

Establish `hcl' : Subfield.closure (R : Set F) = ⊤` using `by rw [hR, RingHom.coe_range]; exact hcl`. Rewrite `h` using `[Subring.range_subtype, hcl']`. Introduce `x`. Establish `hx : x ∈ ι.fieldRange`. Express the relevant statement in the definitionally equal form `x ∈ (IsFractionRing.lift hinj : FractionRing R →+* F).fieldRange`.

Rewrite using `[h]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨y, hy⟩` from `RingHom.mem_fieldRange.mp hx`. Conclude with `⟨y, hy⟩`. Set `e : FractionRing R ≃+* F` to `RingEquiv.ofBijective ι ⟨ι.injective, hsurj⟩`.

Use `⟨(IsLocalization.lift (M := nonZeroDivisors R) (S := FractionRing R) hunit).comp e.symm.toRingHom, ?_⟩` and prove the remaining obligations. Use extensionality with `o`. Establish `he : e.symm (β o) = algebraMap R (FractionRing R) ⟨β o, o, rfl⟩`. Rewrite using `[RingEquiv.symm_apply_eq]`. Use `show β o = ι (algebraMap R (FractionRing R) ⟨β o, o, rfl⟩)`.

Rewrite using `[IsFractionRing.lift_algebraMap]`. Both sides reduce to the same expression. Simplify using `only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, he, IsLocalization.lift_eq, hθR]`.
-/
theorem extends_to_fraction_field : ∀ (O F L : Type) [CommRing O] [Field F] [CommRing L] (β : O →+* F) (θ : O →+* L), Subfield.closure (Set.range β) = ⊤ → (∀ b, β b ≠ 0 → IsUnit (θ b)) → (∀ a, β a = 0 → θ a = 0) → ∃ χ : F →+* L, χ.comp β = θ := by
  intro O F L _ _ _ β θ hcl hu hz
  classical
  set R : Subring F := β.range with hR
  have hk : ∀ a ∈ RingHom.ker β, θ a = 0 := fun a ha => hz a ((RingHom.mem_ker).mp ha)
  let θR : R →+* L :=
    (Ideal.Quotient.lift (RingHom.ker β) θ hk).comp (RingHom.quotientKerEquivRange β).symm.toRingHom
  have hθR : ∀ o : O, θR ⟨β o, o, rfl⟩ = θ o := by
    intro o
    have h : (RingHom.quotientKerEquivRange β).symm ⟨β o, o, rfl⟩ = Ideal.Quotient.mk _ o := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    simp only [θR, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, h,
      Ideal.Quotient.lift_mk]
  have hunit : ∀ r : nonZeroDivisors R, IsUnit (θR r) := by
    intro r
    obtain ⟨b, hb⟩ := (r : R).2
    have hne : (r : R) ≠ 0 := nonZeroDivisors.ne_zero r.2
    have hr : (r : R) = ⟨β b, b, rfl⟩ := Subtype.ext hb.symm
    rw [hr, hθR]
    apply hu
    intro h0
    apply hne
    rw [hr]
    exact Subtype.ext h0
  have hinj : Function.Injective R.subtype := Subtype.val_injective
  let ι : FractionRing R →+* F := IsFractionRing.lift hinj
  have hsurj : Function.Surjective ι := by
    have h := IsFractionRing.lift_fieldRange (K := FractionRing R) hinj
    have hcl' : Subfield.closure (R : Set F) = ⊤ := by rw [hR, RingHom.coe_range]; exact hcl
    rw [Subring.range_subtype, hcl'] at h
    intro x
    have hx : x ∈ ι.fieldRange := by
      change x ∈ (IsFractionRing.lift hinj : FractionRing R →+* F).fieldRange
      rw [h]
      trivial
    obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.mp hx
    exact ⟨y, hy⟩
  let e : FractionRing R ≃+* F := RingEquiv.ofBijective ι ⟨ι.injective, hsurj⟩
  refine ⟨(IsLocalization.lift (M := nonZeroDivisors R) (S := FractionRing R) hunit).comp
    e.symm.toRingHom, ?_⟩
  ext o
  have he : e.symm (β o) = algebraMap R (FractionRing R) ⟨β o, o, rfl⟩ := by
    rw [RingEquiv.symm_apply_eq]
    show β o = ι (algebraMap R (FractionRing R) ⟨β o, o, rfl⟩)
    rw [IsFractionRing.lift_algebraMap]
    rfl
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, he,
    IsLocalization.lift_eq, hθR]

end PositivityTheory.UnitarySelfGeneration
