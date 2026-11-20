import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

open CategoryTheory AlgebraicGeometry

section Along

variable {T T' Y Z : Scheme.{0}} {F G : Z.Modules}

local notation "along" => GroundTheory.Heights₂.Heights.Model.pullbackIsoAlong

/- English proof (translation)
Simplify using `[GroundTheory.Heights₂.Heights.Model.pullbackIsoAlong, GroundTheory.Heights₂.Heights.Model.pullbackCompIso]`.
-/
theorem along_hom {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e : g ≫ h = k)
    (ψ : (Scheme.Modules.pullback h).obj F ≅ (Scheme.Modules.pullback h).obj G) :
    (along e ψ).hom = (Scheme.Modules.pullbackCongr e).inv.app F ≫
      (Scheme.Modules.pullbackComp g h).inv.app F ≫ (Scheme.Modules.pullback g).map ψ.hom ≫
        (Scheme.Modules.pullbackComp g h).hom.app G ≫ (Scheme.Modules.pullbackCongr e).hom.app G := by
  simp [GroundTheory.Heights₂.Heights.Model.pullbackIsoAlong, GroundTheory.Heights₂.Heights.Model.pullbackCompIso]

/- English proof (translation)
Substitute `hg` using the available equality. Both sides reduce to the same expression.
-/
theorem along_congr {g₁ g₂ : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e₁ : g₁ ≫ h = k) (e₂ : g₂ ≫ h = k)
    (hg : g₁ = g₂)
    (ψ : (Scheme.Modules.pullback h).obj F ≅ (Scheme.Modules.pullback h).obj G) :
    along e₁ ψ = along e₂ ψ := by
  subst hg; rfl

/- English proof (translation)
Substitute `hg` using the available equality. Use `ext1`. Establish `h₁` using `NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality h) F`. Establish `h₂` using `NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality h) G`. Simplify using `only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, eqToHom_app] at h₁ h₂`.

Use `erw [Category.comp_id] at h₁ h₂`. Establish `k₁ : (Scheme.Modules.pullbackComp (𝟙 Y) h).inv.app F = eqToHom (by simp) ≫ (Scheme.Modules.pullbackId Y).inv.app ((Scheme.Modules.pullback h).obj F)`. Rewrite using `[← h₁]`. Simplify using the standard rewrite rules. Establish `k₂ : (Scheme.Modules.pullbackComp (𝟙 Y) h).hom.app G = (Scheme.Modules.pullbackId Y).hom.app ((Scheme.Modules.pullback h).obj G) ≫ eqToHom (by simp)`.

Rewrite using `[← cancel_epi ((Scheme.Modules.pullbackComp (𝟙 Y) h).inv.app G), ← Category.assoc, h₂]`. Simplify using the standard rewrite rules. Establish `n` using `(Scheme.Modules.pullbackId Y).hom.naturality ψ.hom`. Simplify using `only [Functor.id_map] at n`. Rewrite using `[along_hom, k₁, k₂]`.

Simplify using `only [Category.assoc]`. Rewrite using `[reassoc_of% n]`. Simplify using `[Scheme.Modules.pullbackCongr]`.
-/
theorem along_id {g : Y ⟶ Y} {h : Y ⟶ Z} (hg : g = 𝟙 Y) (e : g ≫ h = h)
    (ψ : (Scheme.Modules.pullback h).obj F ≅ (Scheme.Modules.pullback h).obj G) :
    along e ψ = ψ := by
  subst hg
  ext1
  have h₁ := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality h) F
  have h₂ := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality h) G
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    eqToHom_app] at h₁ h₂
  erw [Category.comp_id] at h₁ h₂
  have k₁ : (Scheme.Modules.pullbackComp (𝟙 Y) h).inv.app F =
      eqToHom (by simp) ≫ (Scheme.Modules.pullbackId Y).inv.app ((Scheme.Modules.pullback h).obj F) := by
    rw [← h₁]; simp
  have k₂ : (Scheme.Modules.pullbackComp (𝟙 Y) h).hom.app G =
      (Scheme.Modules.pullbackId Y).hom.app ((Scheme.Modules.pullback h).obj G) ≫ eqToHom (by simp) := by
    rw [← cancel_epi ((Scheme.Modules.pullbackComp (𝟙 Y) h).inv.app G), ← Category.assoc, h₂]
    simp
  have n := (Scheme.Modules.pullbackId Y).hom.naturality ψ.hom
  simp only [Functor.id_map] at n
  rw [along_hom, k₁, k₂]
  simp only [Category.assoc]
  rw [reassoc_of% n]
  simp [Scheme.Modules.pullbackCongr]

/- English proof (translation)
Substitute `e e'` using the available equality. Use `ext1`. Establish `a₁` using `NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity p g h) F`. Establish `a₂` using `NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity p g h) G`. Simplify using `only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app, eqToHom_app, Category.id_comp] at a₁ a₂`.

Establish `k₁ : (Scheme.Modules.pullbackComp p (g ≫ h)).inv.app F ≫ (Scheme.Modules.pullback p).map ((Scheme.Modules.pullbackComp g h).inv.app F) = eqToHom (by simp) ≫ (Scheme.Modules.pullbackComp (p ≫ g) h).inv.app F ≫ (Scheme.Modules.pullbackComp p g).inv.app ((Scheme.Modules.pullback h). …`. Rewrite using `[← cancel_mono ((Scheme.Modules.pullbackComp p g).hom.app ((Scheme.Modules.pullback h).obj F) ≫ (Scheme.Modules.pullbackComp (p ≫ g) h).hom.app F)]`. Simplify using `only [Category.assoc] at a₁ ⊢`. Rewrite using `[a₁]`. Simplify using the standard rewrite rules.

Establish `k₂ : (Scheme.Modules.pullback p).map ((Scheme.Modules.pullbackComp g h).hom.app G) ≫ (Scheme.Modules.pullbackComp p (g ≫ h)).hom.app G = (Scheme.Modules.pullbackComp p g).hom.app ((Scheme.Modules.pullback h).obj G) ≫ (Scheme.Modules.pullbackComp (p ≫ g) h).hom.app G ≫ eqToHom (by …`. Rewrite using `[← cancel_epi ((Scheme.Modules.pullbackComp p (g ≫ h)).inv.app G ≫ (Scheme.Modules.pullback p).map ((Scheme.Modules.pullbackComp g h).inv.app G))]`. Simplify using `only [Category.assoc] at a₂ ⊢`. Rewrite using `[reassoc_of% a₂]`. Simplify using `[← Functor.map_comp_assoc]`.

Establish `n` using `(Scheme.Modules.pullbackComp p g).hom.naturality ψ.hom`. Simplify using `only [Functor.comp_map] at n`. Rewrite using `[along_hom, along_hom, along_hom]`. Simplify using `only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv, Iso.refl_hom, NatTrans.id_app, Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]`. Rewrite using `[reassoc_of% k₁, k₂, reassoc_of% n]`.

Simplify using the standard rewrite rules.
-/
theorem along_assoc {p : T' ⟶ T} {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} {k' : T' ⟶ Z}
    (e : g ≫ h = k) (e' : p ≫ k = k') (e'' : (p ≫ g) ≫ h = k')
    (ψ : (Scheme.Modules.pullback h).obj F ≅ (Scheme.Modules.pullback h).obj G) :
    along e' (along e ψ) = along e'' ψ := by
  subst e e'
  ext1
  have a₁ := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity p g h) F
  have a₂ := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity p g h) G
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, eqToHom_app, Category.id_comp] at a₁ a₂
  have k₁ : (Scheme.Modules.pullbackComp p (g ≫ h)).inv.app F ≫
      (Scheme.Modules.pullback p).map ((Scheme.Modules.pullbackComp g h).inv.app F) =
      eqToHom (by simp) ≫ (Scheme.Modules.pullbackComp (p ≫ g) h).inv.app F ≫
        (Scheme.Modules.pullbackComp p g).inv.app ((Scheme.Modules.pullback h).obj F) := by
    rw [← cancel_mono ((Scheme.Modules.pullbackComp p g).hom.app ((Scheme.Modules.pullback h).obj F) ≫
      (Scheme.Modules.pullbackComp (p ≫ g) h).hom.app F)]
    simp only [Category.assoc] at a₁ ⊢
    rw [a₁]
    simp
  have k₂ : (Scheme.Modules.pullback p).map ((Scheme.Modules.pullbackComp g h).hom.app G) ≫
      (Scheme.Modules.pullbackComp p (g ≫ h)).hom.app G =
      (Scheme.Modules.pullbackComp p g).hom.app ((Scheme.Modules.pullback h).obj G) ≫
        (Scheme.Modules.pullbackComp (p ≫ g) h).hom.app G ≫ eqToHom (by simp) := by
    rw [← cancel_epi ((Scheme.Modules.pullbackComp p (g ≫ h)).inv.app G ≫
      (Scheme.Modules.pullback p).map ((Scheme.Modules.pullbackComp g h).inv.app G))]
    simp only [Category.assoc] at a₂ ⊢
    rw [reassoc_of% a₂]
    simp [← Functor.map_comp_assoc]
  have n := (Scheme.Modules.pullbackComp p g).hom.naturality ψ.hom
  simp only [Functor.comp_map] at n
  rw [along_hom, along_hom, along_hom]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  rw [reassoc_of% k₁, k₂, reassoc_of% n]
  simp

/- English proof (translation)
Establish `e' : inv ρ ≫ k' = k` using `by rw [← e, IsIso.inv_hom_id_assoc]`. Establish `e'' : (inv ρ ≫ ρ) ≫ k = k` using `by rw [IsIso.inv_hom_id, Category.id_comp]`. Use `congrArg (along e') H` as an intermediate fact. Rewrite `this` using `[along_assoc e e' e'', along_assoc e e' e'', along_id (IsIso.inv_hom_id ρ), along_id (IsIso.inv_hom_id ρ)]`. Then use the resulting hypothesis.
-/
theorem along_cancel {ρ : T' ⟶ T} [IsIso ρ] {k : T ⟶ Z} {k' : T' ⟶ Z} (e : ρ ≫ k = k')
    {φ₁ φ₂ : (Scheme.Modules.pullback k).obj F ≅ (Scheme.Modules.pullback k).obj G}
    (H : along e φ₁ = along e φ₂) : φ₁ = φ₂ := by
  have e' : inv ρ ≫ k' = k := by rw [← e, IsIso.inv_hom_id_assoc]
  have e'' : (inv ρ ≫ ρ) ≫ k = k := by rw [IsIso.inv_hom_id, Category.id_comp]
  have := congrArg (along e') H
  rwa [along_assoc e e' e'', along_assoc e e' e'', along_id (IsIso.inv_hom_id ρ),
    along_id (IsIso.inv_hom_id ρ)] at this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H ext1`. Rewrite using `[along_hom, along_hom, H]`. Simplify using `[pbSquare, Scheme.Modules.pullbackCongr]`. Introduce `H`.

Establish `key : (Scheme.Modules.pullback q).map f.hom = (Scheme.Modules.pullbackComp q j).hom.app F ≫ (Scheme.Modules.pullbackCongr hsq).hom.app F ≫ (along hsq f).hom ≫ (Scheme.Modules.pullbackCongr hsq).inv.app G ≫ (Scheme.Modules.pullbackComp q j).inv.app G`. Rewrite using `[along_hom]`. Simplify using the standard rewrite rules. Rewrite using `[key, H, along_hom]`. Simplify using `[pbSquare, Scheme.Modules.pullbackCongr]`.
-/
theorem pbSquare_iff {A B C : Scheme.{0}} (q : A ⟶ B) (j : B ⟶ Z) (k : A ⟶ C) (r : C ⟶ Z)
    (hsq : q ≫ j = k ≫ r) (f : (Scheme.Modules.pullback j).obj F ≅ (Scheme.Modules.pullback j).obj G)
    (ψ : (Scheme.Modules.pullback r).obj F ≅ (Scheme.Modules.pullback r).obj G) :
    (Scheme.Modules.pullback q).map f.hom = (pbSquare q j k r hsq F).hom ≫
        (Scheme.Modules.pullback k).map ψ.hom ≫ (pbSquare q j k r hsq G).inv ↔
      along hsq f = along (rfl : k ≫ r = k ≫ r) ψ := by
  constructor
  · intro H
    ext1
    rw [along_hom, along_hom, H]
    simp [pbSquare, Scheme.Modules.pullbackCongr]
  · intro H
    have key : (Scheme.Modules.pullback q).map f.hom =
        (Scheme.Modules.pullbackComp q j).hom.app F ≫ (Scheme.Modules.pullbackCongr hsq).hom.app F ≫
          (along hsq f).hom ≫ (Scheme.Modules.pullbackCongr hsq).inv.app G ≫
            (Scheme.Modules.pullbackComp q j).inv.app G := by
      rw [along_hom]; simp
    rw [key, H, along_hom]
    simp [pbSquare, Scheme.Modules.pullbackCongr]

end Along

section Facts

variable (X : Scheme.{0})

/- English proof (translation)
Establish `hu : IsUnit (((m : ℤ) : ℚ))` using `GroundTheory.Heights₂.Heights.Model.isUnit_intCast_rat m (by exact_mod_cast hm)`. Use `GroundTheory.Heights₂.Heights.Model.range_baseChangeMap_subset (toSpecZ X) ℚ (m : ℤ) hu ⟨x, rfl⟩` as an intermediate fact. Rewrite `this` using `[Scheme.Opens.range_ι]`. Conclude with `this`.
-/
theorem genTo_mem_invOpen {m : ℕ} (hm : m ≠ 0) (x : genFib X) : (genTo X).base x ∈ invOpen X m := by
  have hu : IsUnit (((m : ℤ) : ℚ)) :=
    GroundTheory.Heights₂.Heights.Model.isUnit_intCast_rat m (by exact_mod_cast hm)
  have := GroundTheory.Heights₂.Heights.Model.range_baseChangeMap_subset (toSpecZ X) ℚ (m : ℤ) hu ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι] at this
  exact this

/- English proof (translation)
Assemble the required witnesses or components as `⟨IsOpenImmersion.lift _ _ (by rw [Scheme.Opens.range_ι] rintro _ ⟨x, rfl⟩ exact genTo_mem_invOpen X hm x), IsOpenImmersion.lift_fac _ _ _⟩`.
-/
theorem exists_genFib_to {m : ℕ} (hm : m ≠ 0) :
    ∃ t : genFib X ⟶ (invOpen X m).toScheme, t ≫ (invOpen X m).ι = genTo X :=
  ⟨IsOpenImmersion.lift _ _ (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact genTo_mem_invOpen X hm x), IsOpenImmersion.lift_fac _ _ _⟩

/- English proof (translation)
The claim follows from `isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by rw [Scheme.Opens.opensRange_ι] exact top_unique fun x _ => genTo_mem_invOpen X ha.ne' x)`.
-/
theorem isIso_genOpen_ι {a : ℕ} (ha : 0 < a) : IsIso (genOpen X a).ι :=
  isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by
    rw [Scheme.Opens.opensRange_ι]
    exact top_unique fun x _ => genTo_mem_invOpen X ha.ne' x)

/- English proof (translation)
The claim follows from `morphismRestrict_ι (genTo X) (invOpen X a)`.
-/
theorem genRes_ι (a : ℕ) : genRes X a ≫ (invOpen X a).ι = (genOpen X a).ι ≫ genTo X :=
  morphismRestrict_ι (genTo X) (invOpen X a)

/- English proof (translation)
Rewrite using `[← cancel_mono (invOpen X a).ι, Category.assoc, ht, genRes_ι]`.
-/
theorem genOpen_ι_comp {a : ℕ} {t : genFib X ⟶ (invOpen X a).toScheme}
    (ht : t ≫ (invOpen X a).ι = genTo X) : (genOpen X a).ι ≫ t = genRes X a := by
  rw [← cancel_mono (invOpen X a).ι, Category.assoc, ht, genRes_ι]

/- English proof (translation)
The claim follows from `isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by rw [Scheme.Opens.opensRange_ι] refine top_unique fun x _ => ?_ show ((genRes X a ≫ (invOpen X a).ι)).base x ∈ invOpen X (a * m') rw [genRes_ι] exact genTo_mem_invOpen X (Nat.mul_ne_zero ha.ne' hm'.ne') _)`.
-/
theorem isIso_subPre_ι {a m' : ℕ} (ha : 0 < a) (hm' : 0 < m') :
    IsIso (genRes X a ⁻¹ᵁ subOpen X a m').ι :=
  isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by
    rw [Scheme.Opens.opensRange_ι]
    refine top_unique fun x _ => ?_
    show ((genRes X a ≫ (invOpen X a).ι)).base x ∈ invOpen X (a * m')
    rw [genRes_ι]
    exact genTo_mem_invOpen X (Nat.mul_ne_zero ha.ne' hm'.ne') _)

/- English proof (translation)
Rewrite using `[invOpen_mul]`. Conclude with `inf_le_left`.
-/
theorem invOpen_le (a m' : ℕ) : invOpen X (a * m') ≤ invOpen X a := by
  rw [invOpen_mul]; exact inf_le_left

/- English proof (translation)
Use `⟨IsOpenImmersion.lift (invOpen X (a * m')).ι ((subOpen X a m').ι ≫ (invOpen X a).ι) ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨s, rfl⟩`. Establish `hs : (subOpen X a m').ι.base s ∈ subOpen X a m'` using `(Scheme.Opens.range_ι (subOpen X a m')).subset ⟨s, rfl⟩`. Conclude with `hs`.

Rewrite using `[← cancel_mono (invOpen X a).ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac]`.
-/
theorem exists_sub_to (a m' : ℕ) :
    ∃ w : (subOpen X a m').toScheme ⟶ (invOpen X (a * m')).toScheme,
      w ≫ X.homOfLE (invOpen_le X a m') = (subOpen X a m').ι := by
  refine ⟨IsOpenImmersion.lift (invOpen X (a * m')).ι ((subOpen X a m').ι ≫ (invOpen X a).ι) ?_, ?_⟩
  · rw [Scheme.Opens.range_ι]
    rintro _ ⟨s, rfl⟩
    have hs : (subOpen X a m').ι.base s ∈ subOpen X a m' :=
      (Scheme.Opens.range_ι (subOpen X a m')).subset ⟨s, rfl⟩
    exact hs
  · rw [← cancel_mono (invOpen X a).ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac]

/- English proof (translation)
Use `⟨IsOpenImmersion.lift (subOpen X a m').ι (X.homOfLE (invOpen_le X a m')) ?_, IsOpenImmersion.lift_fac _ _ _⟩` and prove the remaining obligations. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨y, rfl⟩`. Use `show ((X.homOfLE (invOpen_le X a m') ≫ (invOpen X a).ι)).base y ∈ invOpen X (a * m')`. Rewrite using `[Scheme.homOfLE_ι]`.

Conclude with `(Scheme.Opens.range_ι _).subset ⟨y, rfl⟩`.
-/
theorem exists_to_sub (a m' : ℕ) :
    ∃ w' : (invOpen X (a * m')).toScheme ⟶ (subOpen X a m').toScheme,
      w' ≫ (subOpen X a m').ι = X.homOfLE (invOpen_le X a m') := by
  refine ⟨IsOpenImmersion.lift (subOpen X a m').ι (X.homOfLE (invOpen_le X a m')) ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨y, rfl⟩
  show ((X.homOfLE (invOpen_le X a m') ≫ (invOpen X a).ι)).base y ∈ invOpen X (a * m')
  rw [Scheme.homOfLE_ι]
  exact (Scheme.Opens.range_ι _).subset ⟨y, rfl⟩

end Facts

section Equiv

local notation "along" => GroundTheory.Heights₂.Heights.Model.pullbackIsoAlong

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hA X hX a ha F G hF hG t ht α`. Use `hX.1` as an intermediate fact. Use `hX.2` as an intermediate fact. Establish `hu : IsUnit (((a : ℤ) : ℚ))` using `GroundTheory.Heights₂.Heights.Model.isUnit_intCast_rat a (by exact_mod_cast ha.ne')`.

Take `rfl : t = GroundTheory.Heights₂.Heights.Model.toInvOpen (toSpecZ X) ℚ (a : ℤ) hu` from `(cancel_mono (invOpen X a).ι).mp (ht.trans (GroundTheory.Heights₂.Heights.Model.toInvOpen_ι (toSpecZ X) ℚ (a : ℤ) hu).symm)`. Take `⟨m', hm', ψ, hrel⟩` from `hA X (toSpecZ X) a ha F G hF hG α`. Use `⟨m', hm', ψ, fun t' e => ?_⟩` and prove the remaining obligations. Establish `ht' : t' ≫ (invOpen X (a * m')).ι = genTo X`. Use `congrArg (· ≫ (invOpen X a).ι) e` as an intermediate fact.

Simplify using `only [Category.assoc, Scheme.homOfLE_ι] at this`. Conclude with `this.trans ht`. Establish `hu' : IsUnit ((((a : ℤ) * (m' : ℤ) : ℤ) : ℚ))` using `GroundTheory.Heights₂.Heights.Model.isUnit_intCast_rat _ (by positivity)`. Take `rfl : t' = GroundTheory.Heights₂.Heights.Model.toInvOpen (toSpecZ X) ℚ ((a : ℤ) * (m' : ℤ)) hu'` from `(cancel_mono (invOpen X (a * m')).ι).mp (ht'.trans (GroundTheory.Heights₂.Heights.Model.toInvOpen_ι (toSpecZ X) ℚ _ hu').symm)`. Conclude with `hrel`.

Introduce `H X f _ _ a ha F G hF hG α`. Take `rfl : f = toSpecZ X` from `specZ_hom_ext _ _`. Establish `hu : IsUnit (((a : ℤ) : ℚ))` using `GroundTheory.Heights₂.Heights.Model.isUnit_intCast_rat a (by exact_mod_cast ha.ne')`. Take `⟨m', hm', ψ, h⟩` from `H X ⟨‹_›, ‹_›⟩ a ha F G hF hG (GroundTheory.Heights₂.Heights.Model.toInvOpen (toSpecZ X) ℚ (a : ℤ) hu) (GroundTheory.Heights₂.Heights.Model.toInvOpen_ι (toSpecZ X) ℚ (a : ℤ) hu) α`. Conclude with `⟨m', hm', ψ, h _ (GroundTheory.Heights₂.Heights.Model.toInvOpen_homOfLE (toSpecZ X) ℚ (GroundTheory.Heights₂.Heights.Model.isUnit_intCast_rat _ (by positivity)) hu (GroundTheory.Heights₂.Heights.Model.invOpen_mul_le_left (toSpecZ X) a m'))⟩`.
-/
theorem spreadIso_model_iff : GroundTheory.Heights₂.Heights.Model.SpreadIso.Statement ↔
    ∀ (X : Scheme.{0}), IsFiniteTypeOverZ X → ∀ (a : ℕ), 0 < a →
    ∀ (F G : (invOpen X a).toScheme.Modules), IsVectorBundle F → IsVectorBundle G →
    ∀ (t : genFib X ⟶ (invOpen X a).toScheme), t ≫ (invOpen X a).ι = genTo X →
    ∀ α : (Scheme.Modules.pullback t).obj F ≅ (Scheme.Modules.pullback t).obj G,
    ∃ m' : ℕ, 0 < m' ∧ ∃ ψ : (Scheme.Modules.pullback (X.homOfLE (invOpen_le X a m'))).obj F ≅
        (Scheme.Modules.pullback (X.homOfLE (invOpen_le X a m'))).obj G,
      ∀ (t' : genFib X ⟶ (invOpen X (a * m')).toScheme)
        (e : t' ≫ X.homOfLE (invOpen_le X a m') = t), along e ψ = α := by
  constructor
  · intro hA X hX a ha F G hF hG t ht α
    have := hX.1
    have := hX.2
    have hu : IsUnit (((a : ℤ) : ℚ)) :=
      GroundTheory.Heights₂.Heights.Model.isUnit_intCast_rat a (by exact_mod_cast ha.ne')
    obtain rfl : t = GroundTheory.Heights₂.Heights.Model.toInvOpen (toSpecZ X) ℚ (a : ℤ) hu :=
      (cancel_mono (invOpen X a).ι).mp
        (ht.trans (GroundTheory.Heights₂.Heights.Model.toInvOpen_ι (toSpecZ X) ℚ (a : ℤ) hu).symm)
    obtain ⟨m', hm', ψ, hrel⟩ := hA X (toSpecZ X) a ha F G hF hG α
    refine ⟨m', hm', ψ, fun t' e => ?_⟩
    have ht' : t' ≫ (invOpen X (a * m')).ι = genTo X := by
      have := congrArg (· ≫ (invOpen X a).ι) e
      simp only [Category.assoc, Scheme.homOfLE_ι] at this
      exact this.trans ht
    have hu' : IsUnit ((((a : ℤ) * (m' : ℤ) : ℤ) : ℚ)) :=
      GroundTheory.Heights₂.Heights.Model.isUnit_intCast_rat _ (by positivity)
    obtain rfl : t' = GroundTheory.Heights₂.Heights.Model.toInvOpen (toSpecZ X) ℚ ((a : ℤ) * (m' : ℤ)) hu' :=
      (cancel_mono (invOpen X (a * m')).ι).mp
        (ht'.trans (GroundTheory.Heights₂.Heights.Model.toInvOpen_ι (toSpecZ X) ℚ _ hu').symm)
    exact hrel
  · intro H X f _ _ a ha F G hF hG α
    obtain rfl : f = toSpecZ X := specZ_hom_ext _ _
    have hu : IsUnit (((a : ℤ) : ℚ)) :=
      GroundTheory.Heights₂.Heights.Model.isUnit_intCast_rat a (by exact_mod_cast ha.ne')
    obtain ⟨m', hm', ψ, h⟩ := H X ⟨‹_›, ‹_›⟩ a ha F G hF hG
      (GroundTheory.Heights₂.Heights.Model.toInvOpen (toSpecZ X) ℚ (a : ℤ) hu)
      (GroundTheory.Heights₂.Heights.Model.toInvOpen_ι (toSpecZ X) ℚ (a : ℤ) hu) α
    exact ⟨m', hm', ψ, h _ (GroundTheory.Heights₂.Heights.Model.toInvOpen_homOfLE (toSpecZ X) ℚ
      (GroundTheory.Heights₂.Heights.Model.isUnit_intCast_rat _ (by positivity)) hu
      (GroundTheory.Heights₂.Heights.Model.invOpen_mul_le_left (toSpecZ X) a m'))⟩

/- English proof (translation)
Rewrite using `[spreadIso_model_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hA X hX a ha F G hF hG ψ`. Use `isIso_genOpen_ι X ha` as an intermediate fact. Take `⟨t, ht⟩` from `exists_genFib_to X ha.ne'`.

Establish `e2` using `genOpen_ι_comp X ht`. Establish `e1 : inv (genOpen X a).ι ≫ genRes X a = t` using `by rw [← e2, IsIso.inv_hom_id_assoc]`. Take `⟨m', hm', ψA, hrel⟩` from `hA X hX a ha F G hF hG t ht (along e1 ψ)`. Use `isIso_subPre_ι X ha hm'` as an intermediate fact. Take `⟨t', ht'⟩` from `exists_genFib_to X (Nat.mul_ne_zero ha.ne' hm'.ne')`.

Establish `et' : t' ≫ X.homOfLE (invOpen_le X a m') = t`. Rewrite using `[← cancel_mono (invOpen X a).ι, Category.assoc, Scheme.homOfLE_ι, ht', ht]`. Take `⟨w, ew⟩` from `exists_sub_to X a m'`. Use `⟨m', hm', along ew ψA, ?_⟩` and prove the remaining obligations. Rewrite using `[pbSquare_iff]`.

Establish `hψ : ψ = along e2 (along e1 ψ)` using `((along_assoc e1 e2 (by rw [IsIso.hom_inv_id, Category.id_comp]) ψ).trans (along_id (IsIso.hom_inv_id _) _ ψ)).symm`. Establish `M1 : subRes X a m' ≫ w = (genRes X a ⁻¹ᵁ subOpen X a m').ι ≫ (genOpen X a).ι ≫ t'`. Rewrite using `[← cancel_mono (invOpen X (a * m')).ι, Category.assoc, Category.assoc, Category.assoc, ht', ← Scheme.homOfLE_ι X (invOpen_le X a m'), reassoc_of% ew, reassoc_of% (subRes_square X a m'), genRes_ι]`. Rewrite using `[hψ, ← hrel t' et', along_assoc ew (subRes_square X a m') (by rw [Category.assoc, ew, subRes_square]), along_assoc et' e2 (by rw [Category.assoc, et', e2]), along_assoc _ rfl (by rw [Category.assoc, Category.assoc, et', e2])]`. Conclude with `along_congr _ _ M1 _`.

Introduce `hB X hX a ha F G hF hG t ht α`. Use `isIso_genOpen_ι X ha` as an intermediate fact. Establish `e2` using `genOpen_ι_comp X ht`. Take `⟨m', hm', fB, hrel⟩` from `hB X hX a ha F G hF hG (along e2 α)`. Rewrite `hrel` using `[pbSquare_iff]`.

Use `isIso_subPre_ι X ha hm'` as an intermediate fact. Take `⟨w', ew'⟩` from `exists_to_sub X a m'`. Use `⟨m', hm', along ew' fB, fun t' e => ?_⟩` and prove the remaining obligations. Establish `eρ : ((genRes X a ⁻¹ᵁ subOpen X a m').ι ≫ (genOpen X a).ι) ≫ t = (genRes X a ⁻¹ᵁ subOpen X a m').ι ≫ genRes X a` using `by rw [Category.assoc, e2]`. Establish `E1 : (t' ≫ w') ≫ (subOpen X a m').ι = t` using `by rw [Category.assoc, ew', e]`.

Establish `M2 : ((genRes X a ⁻¹ᵁ subOpen X a m').ι ≫ (genOpen X a).ι) ≫ t' ≫ w' = subRes X a m'`. Rewrite using `[← cancel_mono (subOpen X a m').ι, subRes_square]`. Simplify using `only [Category.assoc]`. Rewrite using `[ew', e, e2]`. Use `along_cancel eρ ?_` and prove the remaining obligations.

Rewrite using `[along_assoc ew' e E1, along_assoc E1 eρ (by rw [Category.assoc, E1, eρ]), along_congr _ (subRes_square X a m') M2, hrel, along_assoc e2 rfl eρ]`.
-/
theorem SpreadIso.equiv :
    GroundTheory.Heights₂.Heights.Model.SpreadIso.Statement ↔ SpreadIso.Statement := by
  rw [spreadIso_model_iff]
  constructor
  · intro hA X hX a ha F G hF hG ψ
    have := isIso_genOpen_ι X ha
    obtain ⟨t, ht⟩ := exists_genFib_to X ha.ne'
    have e2 := genOpen_ι_comp X ht
    have e1 : inv (genOpen X a).ι ≫ genRes X a = t := by rw [← e2, IsIso.inv_hom_id_assoc]
    obtain ⟨m', hm', ψA, hrel⟩ := hA X hX a ha F G hF hG t ht (along e1 ψ)
    have := isIso_subPre_ι X ha hm'
    obtain ⟨t', ht'⟩ := exists_genFib_to X (Nat.mul_ne_zero ha.ne' hm'.ne')
    have et' : t' ≫ X.homOfLE (invOpen_le X a m') = t := by
      rw [← cancel_mono (invOpen X a).ι, Category.assoc, Scheme.homOfLE_ι, ht', ht]
    obtain ⟨w, ew⟩ := exists_sub_to X a m'
    refine ⟨m', hm', along ew ψA, ?_⟩
    rw [pbSquare_iff]
    have hψ : ψ = along e2 (along e1 ψ) :=
      ((along_assoc e1 e2 (by rw [IsIso.hom_inv_id, Category.id_comp]) ψ).trans
        (along_id (IsIso.hom_inv_id _) _ ψ)).symm
    have M1 : subRes X a m' ≫ w = (genRes X a ⁻¹ᵁ subOpen X a m').ι ≫ (genOpen X a).ι ≫ t' := by
      rw [← cancel_mono (invOpen X (a * m')).ι, Category.assoc, Category.assoc, Category.assoc, ht',
        ← Scheme.homOfLE_ι X (invOpen_le X a m'), reassoc_of% ew, reassoc_of% (subRes_square X a m'),
        genRes_ι]
    rw [hψ, ← hrel t' et', along_assoc ew (subRes_square X a m')
        (by rw [Category.assoc, ew, subRes_square]),
      along_assoc et' e2 (by rw [Category.assoc, et', e2]),
      along_assoc _ rfl (by rw [Category.assoc, Category.assoc, et', e2])]
    exact along_congr _ _ M1 _
  · intro hB X hX a ha F G hF hG t ht α
    have := isIso_genOpen_ι X ha
    have e2 := genOpen_ι_comp X ht
    obtain ⟨m', hm', fB, hrel⟩ := hB X hX a ha F G hF hG (along e2 α)
    rw [pbSquare_iff] at hrel
    have := isIso_subPre_ι X ha hm'
    obtain ⟨w', ew'⟩ := exists_to_sub X a m'
    refine ⟨m', hm', along ew' fB, fun t' e => ?_⟩
    have eρ : ((genRes X a ⁻¹ᵁ subOpen X a m').ι ≫ (genOpen X a).ι) ≫ t =
        (genRes X a ⁻¹ᵁ subOpen X a m').ι ≫ genRes X a := by rw [Category.assoc, e2]
    have E1 : (t' ≫ w') ≫ (subOpen X a m').ι = t := by rw [Category.assoc, ew', e]
    have M2 : ((genRes X a ⁻¹ᵁ subOpen X a m').ι ≫ (genOpen X a).ι) ≫ t' ≫ w' = subRes X a m' := by
      rw [← cancel_mono (subOpen X a m').ι, subRes_square]
      simp only [Category.assoc]
      rw [ew', e, e2]
    refine along_cancel eρ ?_
    rw [along_assoc ew' e E1, along_assoc E1 eρ (by rw [Category.assoc, E1, eρ]),
      along_congr _ (subRes_square X a m') M2, hrel, along_assoc e2 rfl eρ]

end Equiv

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
