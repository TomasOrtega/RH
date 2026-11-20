import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CoordRatioDeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace CoordRatioDeg

def ratioField {S M : Type*} [Field M] [CharZero M] (R : S → S → Prop) (z : S → M) : IntermediateField ℚ M :=
  IntermediateField.adjoin ℚ {t | ∃ p q, R p q ∧ t = z p / z q}

/- English proof (translation)
Rewrite using `[ratioField, IntermediateField.adjoin_map, ratioField]`. Use `congr 1`. Use extensionality with `t`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨p, q, h, rfl⟩, rfl⟩`.

Conclude with `⟨p, q, h, by simp⟩`. Introduce and unpack `⟨p, q, h, rfl⟩`. Conclude with `⟨_, ⟨p, q, h, rfl⟩, by simp⟩`.
-/
theorem ratioField_map {S M N : Type*} [Field M] [CharZero M] [Field N] [CharZero N] (R : S → S → Prop)
    (z : S → M) (f : M →ₐ[ℚ] N) : (ratioField R z).map f = ratioField R (f ∘ z) := by
  rw [ratioField, IntermediateField.adjoin_map, ratioField]
  congr 1
  ext t
  constructor
  · rintro ⟨_, ⟨p, q, h, rfl⟩, rfl⟩
    exact ⟨p, q, h, by simp⟩
  · rintro ⟨p, q, h, rfl⟩
    exact ⟨_, ⟨p, q, h, rfl⟩, by simp⟩

/- English proof (translation)
Unfold `ratioField`. Use `congr 1`. Use extensionality with `t`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, q, hpq, rfl⟩`.

Conclude with `⟨p, q, hpq, h p q hpq⟩`. Introduce and unpack `⟨p, q, hpq, rfl⟩`. Conclude with `⟨p, q, hpq, (h p q hpq).symm⟩`.
-/
theorem ratioField_congr {S M : Type*} [Field M] [CharZero M] {R : S → S → Prop} {z w : S → M}
    (h : ∀ p q, R p q → z p / z q = w p / w q) : ratioField R z = ratioField R w := by
  unfold ratioField
  congr 1
  ext t
  constructor
  · rintro ⟨p, q, hpq, rfl⟩
    exact ⟨p, q, hpq, h p q hpq⟩
  · rintro ⟨p, q, hpq, rfl⟩
    exact ⟨p, q, hpq, (h p q hpq).symm⟩

/- English proof (translation)
Introduce `K _ ι _ K' _ ι' _ κ v Ω _ _ y Φ' _ _ x' hv hker`. Set `I : Ideal (MRing ι')` to `mCoordIdeal y`. Set `L` to `FractionRing (MvPolynomial K' Ω)`. Establish `: CharZero L` using `charZero_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial K' Ω) L)`. Establish `h₁ : ∀ a ∈ I, (aeval x' : MRing ι' →ₐ[ℤ] Φ').toRingHom a = 0` using `fun a ha => by`.

Rewrite `ha` using `[show I = _ from hker.symm]`. Conclude with `RingHom.mem_ker.mp ha`. Establish `h₂ : ∀ a ∈ I, (mConeMap y).toRingHom a = 0` using `fun a ha => RingHom.mem_ker.mp ha`. Set `g₁ : MRing ι' ⧸ I →+* Φ'` to `Ideal.Quotient.lift I _ h₁`. Establish `hg₁ : Function.Injective g₁` using `RingHom.lift_injective_of_ker_le_ideal I h₁ fun a ha => by`.

Express the relevant statement in the definitionally equal form `a ∈ mCoordIdeal y`. Rewrite using `[← hker]`. Conclude with `ha`. Set `g₂ : MRing ι' ⧸ I →+* L` to `(algebraMap _ L).comp (Ideal.Quotient.lift I _ h₂)`. Establish `hg₂ : Function.Injective g₂` using `(IsFractionRing.injective _ L).comp (RingHom.lift_injective_of_ker_le_ideal I h₂ fun a ha => ha)`.

Establish `: IsDomain (MRing ι' ⧸ I)` using `hg₁.isDomain g₁`. Set `F` to `FractionRing (MRing ι' ⧸ I)`. Set `f₁ : F →+* Φ'` to `IsFractionRing.lift hg₁`. Establish `: CharZero F` using `⟨fun m n h => by`. Establish `h'` using `congrArg f₁ h`.

Rewrite `h'` using `[map_natCast, map_natCast]`. Conclude with `h'⟩` after adjusting the coercions. Set `f₂ : F →+* L` to `IsFractionRing.lift hg₂`. Set `xb : (Σ k', ι' k') → F` to `fun p => algebraMap _ F (Ideal.Quotient.mk I (X p))`. Establish `e₁ : f₁.toRatAlgHom ∘ xb = x'` using `funext fun p => by`.

Simplify using `[xb, f₁, g₁, IsFractionRing.lift_algebraMap]`. Establish `e₂ : ∀ p, f₂ (xb p) = algebraMap _ L (C (y p) * X p.1)` using `fun p => by`. Simplify using `[xb, f₂, g₂, IsFractionRing.lift_algebraMap, mConeMap]`. Set `c : Ω →ₐ[ℚ] L` to `((algebraMap (MvPolynomial K' Ω) L).comp C).toRatAlgHom`. Establish `hT : ∀ k, algebraMap (MvPolynomial K' Ω) L (X k) ≠ 0` using `fun k => (map_ne_zero_iff _ (IsFractionRing.injective _ L)).mpr (X_ne_zero k)`.

Establish `hr : ∀ p q : Σ k', ι' k', p.1 = q.1 → f₂ (xb p) / f₂ (xb q) = c (y p) / c (y q)`. Introduce `p q h`. Rewrite using `[e₂, e₂, h, map_mul, map_mul, mul_div_mul_right _ _ (hT _)]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `IntermediateField.relfinrank (ratioField (fun p q : Σ k, ι k => p.1 = q.1) (x' ∘ v)) (ratioField (fun p q : Σ k', ι' k' => p.1 = q.1) x') = IntermediateField.relfinrank (ratioField (fun p q : Σ k, ι k => p.1 = q.1) (y ∘ v)) (ratioField (fun p q : Σ k', ι' k' => p.1 = q.1) y)`.

Rewrite using `[← IntermediateField.relfinrank_map_map _ _ c, ratioField_map, ratioField_map, ← e₁, Function.comp_assoc, ← ratioField_map, ← ratioField_map, IntermediateField.relfinrank_map_map, ← IntermediateField.relfinrank_map_map _ _ f₂.toRatAlgHom, ratioField_map, ratioField_map]`. Use `congr 1`. Use `ratioField_congr fun p q h => ?_` and prove the remaining obligations. Simplify using `using hr (v p) (v q) (by rw [hv.2.2.1, hv.2.2.1, h])`. Conclude with `ratioField_congr fun p q h => by simpa using hr p q h`.
-/
theorem proof : CoordRatioDeg.Statement := by
  intro K _ ι _ K' _ ι' _ κ v Ω _ _ y Φ' _ _ x' hv hker
  let I : Ideal (MRing ι') := mCoordIdeal y
  let L := FractionRing (MvPolynomial K' Ω)
  have : CharZero L := charZero_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial K' Ω) L)
  have h₁ : ∀ a ∈ I, (aeval x' : MRing ι' →ₐ[ℤ] Φ').toRingHom a = 0 := fun a ha => by
    rw [show I = _ from hker.symm] at ha
    exact RingHom.mem_ker.mp ha
  have h₂ : ∀ a ∈ I, (mConeMap y).toRingHom a = 0 := fun a ha => RingHom.mem_ker.mp ha
  let g₁ : MRing ι' ⧸ I →+* Φ' := Ideal.Quotient.lift I _ h₁
  have hg₁ : Function.Injective g₁ :=
    RingHom.lift_injective_of_ker_le_ideal I h₁ fun a ha => by
      change a ∈ mCoordIdeal y
      rw [← hker]
      exact ha
  let g₂ : MRing ι' ⧸ I →+* L := (algebraMap _ L).comp (Ideal.Quotient.lift I _ h₂)
  have hg₂ : Function.Injective g₂ :=
    (IsFractionRing.injective _ L).comp (RingHom.lift_injective_of_ker_le_ideal I h₂ fun a ha => ha)
  have : IsDomain (MRing ι' ⧸ I) := hg₁.isDomain g₁
  let F := FractionRing (MRing ι' ⧸ I)
  let f₁ : F →+* Φ' := IsFractionRing.lift hg₁
  have : CharZero F := ⟨fun m n h => by
    have h' := congrArg f₁ h
    rw [map_natCast, map_natCast] at h'
    exact_mod_cast h'⟩
  let f₂ : F →+* L := IsFractionRing.lift hg₂
  let xb : (Σ k', ι' k') → F := fun p => algebraMap _ F (Ideal.Quotient.mk I (X p))
  have e₁ : f₁.toRatAlgHom ∘ xb = x' := funext fun p => by
    simp [xb, f₁, g₁, IsFractionRing.lift_algebraMap]
  have e₂ : ∀ p, f₂ (xb p) = algebraMap _ L (C (y p) * X p.1) := fun p => by
    simp [xb, f₂, g₂, IsFractionRing.lift_algebraMap, mConeMap]
  let c : Ω →ₐ[ℚ] L := ((algebraMap (MvPolynomial K' Ω) L).comp C).toRatAlgHom
  have hT : ∀ k, algebraMap (MvPolynomial K' Ω) L (X k) ≠ 0 := fun k =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ L)).mpr (X_ne_zero k)
  have hr : ∀ p q : Σ k', ι' k', p.1 = q.1 → f₂ (xb p) / f₂ (xb q) = c (y p) / c (y q) := by
    intro p q h
    rw [e₂, e₂, h, map_mul, map_mul, mul_div_mul_right _ _ (hT _)]
    rfl
  change IntermediateField.relfinrank (ratioField (fun p q : Σ k, ι k => p.1 = q.1) (x' ∘ v))
      (ratioField (fun p q : Σ k', ι' k' => p.1 = q.1) x') =
    IntermediateField.relfinrank (ratioField (fun p q : Σ k, ι k => p.1 = q.1) (y ∘ v))
      (ratioField (fun p q : Σ k', ι' k' => p.1 = q.1) y)
  rw [← IntermediateField.relfinrank_map_map _ _ c, ratioField_map, ratioField_map, ← e₁,
    Function.comp_assoc, ← ratioField_map, ← ratioField_map,
    IntermediateField.relfinrank_map_map,
    ← IntermediateField.relfinrank_map_map _ _ f₂.toRatAlgHom, ratioField_map, ratioField_map]
  congr 1
  · refine ratioField_congr fun p q h => ?_
    simpa using hr (v p) (v q) (by rw [hv.2.2.1, hv.2.2.1, h])
  · exact ratioField_congr fun p q h => by simpa using hr p q h

end CoordRatioDeg

end GroundTheory.Heights₂.Heights.Targets
