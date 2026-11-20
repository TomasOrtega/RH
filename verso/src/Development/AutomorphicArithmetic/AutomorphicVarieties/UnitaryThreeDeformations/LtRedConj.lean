import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `a b`. Simplify using `only [Matrix.map_apply]`. Conclude with `Ideal.Quotient.eq.mpr (by simpa [Matrix.sub_apply] using h a b)`.

Introduce `h a b`. Establish `hab` using `congrFun (congrFun h a) b`. Simplify using `only [Matrix.map_apply] at hab`. Simplify `Ideal.Quotient.eq.mp hab` using `[Matrix.sub_apply]`.
-/
private theorem entIn_sub_iff {C : Type} [CommRing C] (I : Ideal C) (X Y : Matrix (Fin 3) (Fin 3) C) :
    EntIn I (X - Y) ↔ X.map (Ideal.Quotient.mk I) = Y.map (Ideal.Quotient.mk I) := by
  constructor
  · intro h
    ext a b
    simp only [Matrix.map_apply]
    exact Ideal.Quotient.eq.mpr (by simpa [Matrix.sub_apply] using h a b)
  · intro h a b
    have hab := congrFun (congrFun h a) b
    simp only [Matrix.map_apply] at hab
    simpa [Matrix.sub_apply] using Ideal.Quotient.eq.mp hab

/- English proof (translation)
Unfold `CongOne`. Rewrite using `[entIn_sub_iff, Matrix.map_one _ (map_zero _) (map_one _)]`. Prove the components needed by the constructor for the conclusion. Introduce `e`. Conclude with `Units.ext e`.

Introduce `e`. Conclude with `congrArg Units.val e`.
-/
private theorem congOne_iff {C : Type} [CommRing C] (I : Ideal C) (h : GL (Fin 3) C) :
    CongOne I h ↔ GeneralLinearGroup.map (Ideal.Quotient.mk I) h = 1 := by
  unfold CongOne
  rw [entIn_sub_iff, Matrix.map_one _ (map_zero _) (map_one _)]
  constructor
  · intro e
    exact Units.ext e
  · intro e
    exact congrArg Units.val e

/- English proof (translation)
Establish `e : GG.map (Ideal.Quotient.mk I) (GG.ofGL h) = 1`. Unfold `GG.map`. Rewrite using `[SemidirectProduct.map_inl, (congOne_iff I h).1 hh, map_one]`. Simplify using `only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, e, one_mul, inv_one, mul_one]`.
-/
private theorem map_conjBy {C D : Type} [CommRing C] [Group D] (I : Ideal C) (h : GL (Fin 3) C)
    (hh : CongOne I h) (r : D →* GG 3 C) (g : D) :
    GG.map (Ideal.Quotient.mk I) (conjBy h r g) = GG.map (Ideal.Quotient.mk I) (r g) := by
  have e : GG.map (Ideal.Quotient.mk I) (GG.ofGL h) = 1 := by
    unfold GG.map
    rw [SemidirectProduct.map_inl, (congOne_iff I h).1 hh, map_one]
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, e,
    one_mul, inv_one, mul_one]

/- English proof (translation)
Simplify using `[mats, GG.mat, conjBy, GG.ofGL, SemidirectProduct.mul_left, Units.val_mul]`.
-/
private theorem mats_conjBy {C D : Type} [CommRing C] [Group D] (h : GL (Fin 3) C) (r : D →* GG 3 C) (g : D) :
    mats (conjBy h r) g =
      (h : Matrix (Fin 3) (Fin 3) C) * mats r g *
        ((sgnAct 3 C (r g).right h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
  simp [mats, GG.mat, conjBy, GG.ofGL, SemidirectProduct.mul_left, Units.val_mul]

/- English proof (translation)
Introduce `O R D _ _ _ _ _ _ _ η Ψ r h hh hr`. Establish `hinv : InHat h⁻¹` using `by show CongOne (maximalIdeal R) h⁻¹`. Rewrite using `[congOne_iff, map_inv, (congOne_iff _ h).mp hh, inv_one]`. Establish `hright : ∀ g, (conjBy h r g).right = (r g).right`. Introduce `g`.

Simplify using `[conjBy, GG.ofGL]`. Use `⟨hinv, ⟨fun g => (hright g).trans (hr.mult g), fun g => ?_⟩, fun hη hm => ?_⟩` and prove the remaining obligations. Rewrite using `[entIn_sub_iff]`. Establish `h0` using `(entIn_sub_iff _ _ _).mp (hr.red g)`. Rewrite using `[← h0, ← GG.map_mat, ← GG.map_mat, map_conjBy _ h hh]`.

Establish `hfun : mats (conjBy h r) = fun g => (h : Matrix (Fin 3) (Fin 3) R) * mats r g * ((sgnAct 3 R (η g) h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)`. Use function extensionality and compare the values at `g`. Rewrite using `[mats_conjBy, hr.mult g]`. Rewrite using `[hfun]`. Conclude with `IsLocallyConstant.comp₂ hm hη fun M s => (h : Matrix (Fin 3) (Fin 3) R) * M * ((sgnAct 3 R s h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)`.
-/
theorem UpperTheory.V.UnitaryThreeInertia.lt_red_conj :
    ∀ {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [Group D] [TopologicalSpace D] (η : D →* ℤˣ) (Ψ : D →* Oˣ) (r : D →* GG 3 R) (h : GL (Fin 3) R),
      InHat h → Red η Ψ r → InHat h⁻¹ ∧ Red η Ψ (conjBy h r) ∧ (IsLocallyConstant η → IsLocallyConstant (mats r) → IsLocallyConstant (mats (conjBy h r))) := by
  intro O R D _ _ _ _ _ _ _ η Ψ r h hh hr
  have hinv : InHat h⁻¹ := by
    show CongOne (maximalIdeal R) h⁻¹
    rw [congOne_iff, map_inv, (congOne_iff _ h).mp hh, inv_one]
  have hright : ∀ g, (conjBy h r g).right = (r g).right := by
    intro g
    simp [conjBy, GG.ofGL]
  refine ⟨hinv, ⟨fun g => (hright g).trans (hr.mult g), fun g => ?_⟩, fun hη hm => ?_⟩
  · rw [entIn_sub_iff]
    have h0 := (entIn_sub_iff _ _ _).mp (hr.red g)
    rw [← h0, ← GG.map_mat, ← GG.map_mat, map_conjBy _ h hh]
  · have hfun : mats (conjBy h r) = fun g =>
        (h : Matrix (Fin 3) (Fin 3) R) * mats r g *
          ((sgnAct 3 R (η g) h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
      funext g
      rw [mats_conjBy, hr.mult g]
    rw [hfun]
    exact IsLocallyConstant.comp₂ hm hη fun M s =>
      (h : Matrix (Fin 3) (Fin 3) R) * M * ((sgnAct 3 R s h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)
