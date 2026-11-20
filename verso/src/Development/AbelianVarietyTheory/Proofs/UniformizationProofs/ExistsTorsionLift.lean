import Mathlib
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UT.ExactTerm

/- English proof (translation)
Establish `: (RingHom.ker φ).IsPrime` using `RingHom.ker_isPrime φ`. Establish `: (RingHom.ker φ).LiesOver (maximalIdeal O)` using `⟨by show maximalIdeal O = Ideal.comap (algebraMap O A) (RingHom.ker φ)`. Rewrite using `[RingHom.comap_ker, hφ, ker_residue]⟩`. Take `⟨P, hPQ, hP, hPlo⟩` from `(RingHom.ker φ).exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal O)) (q := maximalIdeal O) bot_le`. Establish `hjinj : Function.Injective (algebraMap O P.ResidueField)`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`. Establish `h1 : algebraMap O A y ∈ P`. Rewrite using `[← Ideal.algebraMap_residueField_eq_zero, ← IsScalarTower.algebraMap_apply]`. Conclude with `hy`.

Establish `h2 : y ∈ P.under O` using `h1`. Rewrite `h2` using `[← hPlo.over]`. Simplify using `using h2`. Set `: Algebra F P.ResidueField` to `(IsFractionRing.lift (K := F) hjinj).toAlgebra`. Establish `: IsScalarTower O F P.ResidueField` using `IsScalarTower.of_algebraMap_eq fun y => (IsFractionRing.lift_algebraMap hjinj y).symm`.

Establish `hrange : ∀ a : A, ∃ y : O, algebraMap O P.ResidueField y = algebraMap A P.ResidueField a`. Introduce `a`. Establish `hO : IsIntegral O (algebraMap A P.ResidueField a)` using `(Algebra.IsIntegral.isIntegral a).algebraMap`. Establish `hF : IsIntegral F (algebraMap A P.ResidueField a)` using `hO.tower_top`. Take `⟨r, hr⟩` from `(IsAlgClosed.algebraMap_bijective_of_isIntegral (k := F) (K := integralClosure F P.ResidueField)).2 ⟨_, hF⟩`.

Establish `hr' : algebraMap F P.ResidueField r = algebraMap A P.ResidueField a` using `congrArg Subtype.val hr`. Establish `hrO : IsIntegral O r`. Rewrite using `[← isIntegral_algHom_iff (IsScalarTower.toAlgHom O F P.ResidueField) (algebraMap F P.ResidueField).injective]`. Simplify `hO` using `[hr']`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hrO`.

Conclude with `⟨y, by rw [IsScalarTower.algebraMap_apply O F P.ResidueField, hy, hr']⟩`. Set `e : O ≃+* (algebraMap O P.ResidueField).range` to `RingEquiv.ofBijective (algebraMap O P.ResidueField).rangeRestrict ⟨fun a b h => hjinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩`. Set `π' : A →+* (algebraMap O P.ResidueField).range` to `(algebraMap A P.ResidueField).codRestrict _ fun a => by`. Take `⟨y, hy⟩` from `hrange a`. Conclude with `⟨y, hy⟩`.

Establish `key : ∀ a, algebraMap O P.ResidueField (e.symm (π' a)) = algebraMap A P.ResidueField a` using `fun a => congrArg Subtype.val (e.apply_symm_apply (π' a))`. Use `⟨e.symm.toRingHom.comp π', ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Apply `hjinj` to reduce the goal to its premises. Simplify using `only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingHom.id_apply]`.

Rewrite using `[key]`. Conclude with `(IsScalarTower.algebraMap_apply O A P.ResidueField y).symm`. Use extensionality with `a`. Simplify using `only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]`. Establish `hmem : algebraMap O A (e.symm (π' a)) - a ∈ RingHom.ker φ`.

Apply `hPQ` to reduce the goal to its premises. Rewrite using `[← Ideal.algebraMap_residueField_eq_zero, map_sub, ← IsScalarTower.algebraMap_apply, key, sub_self]`. Establish `h1 : φ (algebraMap O A (e.symm (π' a))) = φ a`. Rewrite using `[← sub_eq_zero, ← map_sub]`. Conclude with `(RingHom.mem_ker).mp hmem`.

Rewrite using `[← h1, ← RingHom.comp_apply φ (algebraMap O A), hφ]`.
-/
theorem exists_ringHom_lift (F : Type) [Field F] [IsAlgClosed F] {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O]
    [IsIntegrallyClosed O] [Algebra O F] [IsFractionRing O F] {A : Type} [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A] (φ : A →+* ResidueField O)
    (hφ : φ.comp (algebraMap O A) = residue O) :
    ∃ ψ : A →+* O, ψ.comp (algebraMap O A) = RingHom.id O ∧ (residue O).comp ψ = φ := by
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have : (RingHom.ker φ).LiesOver (maximalIdeal O) := ⟨by
    show maximalIdeal O = Ideal.comap (algebraMap O A) (RingHom.ker φ)
    rw [RingHom.comap_ker, hφ, ker_residue]⟩
  obtain ⟨P, hPQ, hP, hPlo⟩ := (RingHom.ker φ).exists_ideal_le_liesOver_of_le
    (p := (⊥ : Ideal O)) (q := maximalIdeal O) bot_le
  have hjinj : Function.Injective (algebraMap O P.ResidueField) := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have h1 : algebraMap O A y ∈ P := by
      rw [← Ideal.algebraMap_residueField_eq_zero, ← IsScalarTower.algebraMap_apply]
      exact hy
    have h2 : y ∈ P.under O := h1
    rw [← hPlo.over] at h2
    simpa using h2
  let : Algebra F P.ResidueField := (IsFractionRing.lift (K := F) hjinj).toAlgebra
  have : IsScalarTower O F P.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun y => (IsFractionRing.lift_algebraMap hjinj y).symm
  have hrange : ∀ a : A, ∃ y : O, algebraMap O P.ResidueField y = algebraMap A P.ResidueField a := by
    intro a
    have hO : IsIntegral O (algebraMap A P.ResidueField a) :=
      (Algebra.IsIntegral.isIntegral a).algebraMap
    have hF : IsIntegral F (algebraMap A P.ResidueField a) := hO.tower_top
    obtain ⟨r, hr⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := F)
      (K := integralClosure F P.ResidueField)).2 ⟨_, hF⟩
    have hr' : algebraMap F P.ResidueField r = algebraMap A P.ResidueField a := congrArg Subtype.val hr
    have hrO : IsIntegral O r := by
      rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom O F P.ResidueField)
        (algebraMap F P.ResidueField).injective]
      simpa [hr'] using hO
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hrO
    exact ⟨y, by rw [IsScalarTower.algebraMap_apply O F P.ResidueField, hy, hr']⟩
  let e : O ≃+* (algebraMap O P.ResidueField).range :=
    RingEquiv.ofBijective (algebraMap O P.ResidueField).rangeRestrict
      ⟨fun a b h => hjinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  let π' : A →+* (algebraMap O P.ResidueField).range :=
    (algebraMap A P.ResidueField).codRestrict _ fun a => by
      obtain ⟨y, hy⟩ := hrange a
      exact ⟨y, hy⟩
  have key : ∀ a, algebraMap O P.ResidueField (e.symm (π' a)) = algebraMap A P.ResidueField a :=
    fun a => congrArg Subtype.val (e.apply_symm_apply (π' a))
  refine ⟨e.symm.toRingHom.comp π', ?_, ?_⟩
  · ext y
    apply hjinj
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingHom.id_apply]
    rw [key]
    exact (IsScalarTower.algebraMap_apply O A P.ResidueField y).symm
  · ext a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    have hmem : algebraMap O A (e.symm (π' a)) - a ∈ RingHom.ker φ := by
      apply hPQ
      rw [← Ideal.algebraMap_residueField_eq_zero, map_sub, ← IsScalarTower.algebraMap_apply, key,
        sub_self]
    have h1 : φ (algebraMap O A (e.symm (π' a))) = φ a := by
      rw [← sub_eq_zero, ← map_sub]
      exact (RingHom.mem_ker).mp hmem
    rw [← h1, ← RingHom.comp_apply φ (algebraMap O A), hφ]

/- English proof (translation)
Establish `: IsAffine H` using `isAffine_of_isAffineHom f`. Take `⟨φ, hφ⟩ : ∃ φ, Spec.map φ = H.isoSpec.inv ≫ f` from `⟨_, Spec.map_preimage _⟩`. Establish `hfin : φ.hom.Finite`. Rewrite using `[← IsFinite.SpecMap_iff, hφ]`. Use `infer_instance`.

Establish `hflat : φ.hom.Flat`. Rewrite using `[← Flat.SpecMap_iff, hφ]`. Conclude with `MorphismProperty.comp_mem @Flat _ _ (inferInstance : Flat H.isoSpec.inv) ‹Flat f›`. Take `⟨χ, hχ⟩ : ∃ χ, Spec.map χ = p ≫ H.isoSpec.hom` from `⟨_, Spec.map_preimage _⟩`. Set `_` to `φ.hom.toAlgebra`.

Establish `: Module.Finite O Γ(H, ⊤)` using `hfin`. Establish `: Module.Flat O Γ(H, ⊤)` using `hflat`. Establish `hcomp : χ.hom.comp (algebraMap O Γ(H, ⊤)) = residue O`. Establish `h1 : Spec.map (φ ≫ χ) = Spec.map (CommRingCat.ofHom (residue O))`. Rewrite using `[Spec.map_comp, hχ, hφ, Category.assoc, Iso.hom_inv_id_assoc, hp]`.

Conclude with `congrArg CommRingCat.Hom.hom (Spec.map_injective h1)`. Take `⟨ψ, hψ1, hψ2⟩` from `exists_ringHom_lift F χ.hom hcomp`. Use `⟨Spec.map (CommRingCat.ofHom ψ) ≫ H.isoSpec.inv, ?_, ?_⟩` and prove the remaining obligations. Establish `h2 : φ ≫ CommRingCat.ofHom ψ = 𝟙 _`. Conclude with `CommRingCat.hom_ext hψ1`.

Rewrite using `[Category.assoc, ← hφ, ← Spec.map_comp, h2, Spec.map_id]`. Establish `h3 : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (residue O) = χ`. Conclude with `CommRingCat.hom_ext hψ2`. Rewrite using `[← Category.assoc, ← Spec.map_comp, h3, hχ, Category.assoc, Iso.hom_inv_id, Category.comp_id]`.
-/
theorem exists_section_lift {F : Type} [Field F] [IsAlgClosed F] (O : ValuationSubring F) {H : Scheme.{0}}
    (f : H ⟶ Spec (CommRingCat.of O)) [IsFinite f] [Flat f] (p : Spec (CommRingCat.of (ResidueField O)) ⟶ H)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (residue O))) :
    ∃ q : Spec (CommRingCat.of O) ⟶ H, q ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (residue O)) ≫ q = p := by
  have : IsAffine H := isAffine_of_isAffineHom f
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = H.isoSpec.inv ≫ f := ⟨_, Spec.map_preimage _⟩
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  have hflat : φ.hom.Flat := by
    rw [← Flat.SpecMap_iff, hφ]
    exact MorphismProperty.comp_mem @Flat _ _ (inferInstance : Flat H.isoSpec.inv) ‹Flat f›
  obtain ⟨χ, hχ⟩ : ∃ χ, Spec.map χ = p ≫ H.isoSpec.hom := ⟨_, Spec.map_preimage _⟩
  let _ := φ.hom.toAlgebra
  have : Module.Finite O Γ(H, ⊤) := hfin
  have : Module.Flat O Γ(H, ⊤) := hflat
  have hcomp : χ.hom.comp (algebraMap O Γ(H, ⊤)) = residue O := by
    have h1 : Spec.map (φ ≫ χ) = Spec.map (CommRingCat.ofHom (residue O)) := by
      rw [Spec.map_comp, hχ, hφ, Category.assoc, Iso.hom_inv_id_assoc, hp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  obtain ⟨ψ, hψ1, hψ2⟩ := exists_ringHom_lift F χ.hom hcomp
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ H.isoSpec.inv, ?_, ?_⟩
  · have h2 : φ ≫ CommRingCat.ofHom ψ = 𝟙 _ := by
      exact CommRingCat.hom_ext hψ1
    rw [Category.assoc, ← hφ, ← Spec.map_comp, h2, Spec.map_id]
  · have h3 : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (residue O) = χ := by
      exact CommRingCat.hom_ext hψ2
    rw [← Category.assoc, ← Spec.map_comp, h3, hχ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]

/- English proof (translation)
Establish `hpow : ∀ {Y : Over S} (z : Y ⟶ G), z ^ n = z ≫ (𝟙 G) ^ n` using `fun z => by`. Rewrite using `[MonObj.comp_pow, Category.comp_id]`. Establish `hxm : x.left ≫ ((𝟙 G) ^ n : G ⟶ G).left = Spec.map (CommRingCat.ofHom (residue O)) ≫ t ≫ η[G].left`. Establish `h1 : (x ≫ (𝟙 G) ^ n).left = (1 : Over.mk (Spec.map (CommRingCat.ofHom (residue O)) ≫ t) ⟶ G).left`. Rewrite using `[← hpow, hx]`.

Rewrite `h1` using `[Over.comp_left, CategoryTheory.Hom.one_def, Over.comp_left, Over.toUnit_left]`. Rewrite using `[h1]`. Conclude with `Category.assoc _ _ _`. Take `⟨q, hq1, hq2⟩` from `exists_section_lift O (pullback.snd ((𝟙 G) ^ n : G ⟶ G).left (t ≫ η[G].left)) (pullback.lift x.left (Spec.map (CommRingCat.ofHom (residue O))) hxm) (pullback.lift_snd _ _ _)`. Establish `hw : ((𝟙 G) ^ n : G ⟶ G).left ≫ G.hom = G.hom` using `Over.w _`.

Establish `he : η[G].left ≫ G.hom = 𝟙 S` using `Over.w η[G]`. Use `⟨Over.homMk (q ≫ pullback.fst _ _) ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← hw, pullback.condition_assoc, Category.assoc, he, Category.comp_id, ← Category.assoc, hq1]`. Conclude with `Category.id_comp t`. Rewrite using `[hpow, CategoryTheory.Hom.one_def]`.

Use `ext`. Express the relevant statement in the definitionally equal form `(q ≫ pullback.fst _ _) ≫ ((𝟙 G) ^ n : G ⟶ G).left = t ≫ η[G].left`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, hq1]`. Conclude with `Category.id_comp _`. Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom (residue O)) ≫ (q ≫ pullback.fst _ _) = x.left`.

Rewrite using `[← Category.assoc, hq2, pullback.lift_fst]`.
-/
theorem exists_torsion_lift {F : Type} [Field F] [IsAlgClosed F] (O : ValuationSubring F) {S : Scheme.{0}}
    (G : Over S) [GrpObj G] (n : ℕ) [IsFinite ((𝟙 G) ^ n : G ⟶ G).left] [Flat ((𝟙 G) ^ n : G ⟶ G).left]
    (t : Spec (CommRingCat.of O) ⟶ S)
    (x : Over.mk (Spec.map (CommRingCat.ofHom (residue O)) ≫ t) ⟶ G) (hx : x ^ n = 1) :
    ∃ y : Over.mk t ⟶ G, y ^ n = 1 ∧ Spec.map (CommRingCat.ofHom (residue O)) ≫ y.left = x.left := by
  have hpow : ∀ {Y : Over S} (z : Y ⟶ G), z ^ n = z ≫ (𝟙 G) ^ n := fun z => by
    rw [MonObj.comp_pow, Category.comp_id]
  have hxm : x.left ≫ ((𝟙 G) ^ n : G ⟶ G).left =
      Spec.map (CommRingCat.ofHom (residue O)) ≫ t ≫ η[G].left := by
    have h1 : (x ≫ (𝟙 G) ^ n).left = (1 : Over.mk (Spec.map (CommRingCat.ofHom (residue O)) ≫ t) ⟶ G).left := by
      rw [← hpow, hx]
    rw [Over.comp_left, CategoryTheory.Hom.one_def, Over.comp_left, Over.toUnit_left] at h1
    rw [h1]
    exact Category.assoc _ _ _
  obtain ⟨q, hq1, hq2⟩ := exists_section_lift O
    (pullback.snd ((𝟙 G) ^ n : G ⟶ G).left (t ≫ η[G].left))
    (pullback.lift x.left (Spec.map (CommRingCat.ofHom (residue O))) hxm) (pullback.lift_snd _ _ _)
  have hw : ((𝟙 G) ^ n : G ⟶ G).left ≫ G.hom = G.hom := Over.w _
  have he : η[G].left ≫ G.hom = 𝟙 S := Over.w η[G]
  refine ⟨Over.homMk (q ≫ pullback.fst _ _) ?_, ?_, ?_⟩
  · rw [Category.assoc, ← hw, pullback.condition_assoc, Category.assoc, he, Category.comp_id,
      ← Category.assoc, hq1]
    exact Category.id_comp t
  · rw [hpow, CategoryTheory.Hom.one_def]
    ext
    change (q ≫ pullback.fst _ _) ≫ ((𝟙 G) ^ n : G ⟶ G).left = t ≫ η[G].left
    rw [Category.assoc, pullback.condition, ← Category.assoc, hq1]
    exact Category.id_comp _
  · change Spec.map (CommRingCat.ofHom (residue O)) ≫ (q ≫ pullback.fst _ _) = x.left
    rw [← Category.assoc, hq2, pullback.lift_fst]

end GlobalTheory.UT.ExactTerm
end
