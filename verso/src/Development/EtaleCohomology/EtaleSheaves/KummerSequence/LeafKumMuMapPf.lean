import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuUnitsPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.H2CurveOrder.LeafKumMuMapPf

/- English proof (translation)
Take `⟨g, hg⟩` from `Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ`. Establish `h` using `congrArg (Polynomial.aeval ζ.1) hg`. Simplify `h` using `[sub_eq_zero, ζ.2.2]`.
-/
theorem prim_pow (q : ℕ) {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨g, hg⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hg
  simpa [sub_eq_zero, ζ.2.2] using h

variable (q : ℕ) [NeZero q]

def unitOf {A : Type} [CommRing A] (ζ : Prim q A) : Aˣ :=
  (IsUnit.of_pow_eq_one (prim_pow q ζ) (NeZero.ne q)).unit

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem unitOf_val {A : Type} [CommRing A] (ζ : Prim q A) : ((unitOf q ζ : Aˣ) : A) = ζ.1 := rfl

/- English proof (translation)
The claim follows from `Units.ext (by simp [prim_pow])`.
-/
theorem unitOf_pow {A : Type} [CommRing A] (ζ : Prim q A) : unitOf q ζ ^ q = 1 :=
  Units.ext (by simp [prim_pow])

def gOf {A : Type} [CommRing A] (ζ : Prim q A) : ZMod q →+ Additive Aˣ :=
  ZMod.lift q ⟨zmultiplesHom _ (Additive.ofMul (unitOf q ζ)), by
    change ((q : ℤ) • Additive.ofMul (unitOf q ζ)) = 0
    rw [natCast_zsmul, ← ofMul_pow, unitOf_pow]; rfl⟩

/- English proof (translation)
Simplify using `[gOf, ZMod.lift_coe]`.
-/
theorem gOf_int {A : Type} [CommRing A] (ζ : Prim q A) (n : ℤ) :
    gOf q ζ (n : ZMod q) = n • Additive.ofMul (unitOf q ζ) := by
  simp [gOf, ZMod.lift_coe]

/- English proof (translation)
Use `gOf_int q ζ 1` as an intermediate fact. Simplify using `using this`.
-/
theorem gOf_one {A : Type} [CommRing A] (ζ : Prim q A) : gOf q ζ 1 = Additive.ofMul (unitOf q ζ) := by
  have := gOf_int q ζ 1
  simpa using this

def nuA (A : Type) [CommRing A] : (Prim q A →₀ ULift.{1} (ZMod q)) →+ Additive Aˣ :=
  Finsupp.liftAddHom (fun ζ => (gOf q ζ).comp (AddEquiv.ulift.toAddMonoidHom))

/- English proof (translation)
Simplify using `[nuA]`. Both sides reduce to the same expression.
-/
theorem nuA_single (A : Type) [CommRing A] (ζ : Prim q A) (b : ULift.{1} (ZMod q)) :
    nuA q A (Finsupp.single ζ b) = gOf q ζ b.down := by
  simp [nuA]; rfl

/- English proof (translation)
Proceed by induction on `x using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]`. Consider the case `single ζ b`. Rewrite using `[Finsupp.smul_single, nuA_single, nuA_single, ← map_zsmul]`.

Use `congr 1`. Express the relevant statement in the definitionally equal form `(n : ZMod q) * b.down = n • b.down`. Rewrite using `[zsmul_eq_mul]`.
-/
theorem nuA_smul (A : Type) [CommRing A] (n : ℤ) (x : Prim q A →₀ ULift.{1} (ZMod q)) :
    nuA q A ((ULift.up (n : ZMod q) : ULift.{1} (ZMod q)) • x) = n • nuA q A x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | single ζ b =>
    rw [Finsupp.smul_single, nuA_single, nuA_single, ← map_zsmul]
    congr 1
    change (n : ZMod q) * b.down = n • b.down
    rw [zsmul_eq_mul]

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨ζ, ξ, a, h, rfl⟩` from `hx`. Rewrite using `[map_sub, nuA_single, nuA_single, zpow_one]`.

Express the relevant statement in the definitionally equal form `gOf q ξ 1 - gOf q ζ (a : ZMod q) = 0`. Establish `ha : ((a : ZMod q)) = (((a : ZMod q).val : ℤ) : ZMod q)` using `by simp`. Rewrite using `[ha, gOf_int, gOf_one, sub_eq_zero, natCast_zsmul, ← ofMul_pow]`. Use `congr 1`. Conclude with `Units.ext (by simp [h])`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]`. Consider the case `smul c x _ hx`. Establish `hc : c = ULift.up (((c.down.cast : ℤ)) : ZMod q)` using `by ext; simp`. Rewrite using `[hc, nuA_smul, hx, smul_zero]`.
-/
theorem nuA_rel (A : Type) [CommRing A] : ∀ x ∈ twRel q 1 A, nuA q A x = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ζ, ξ, a, h, rfl⟩ := hx
    rw [map_sub, nuA_single, nuA_single, zpow_one]
    change gOf q ξ 1 - gOf q ζ (a : ZMod q) = 0
    have ha : ((a : ZMod q)) = (((a : ZMod q).val : ℤ) : ZMod q) := by simp
    rw [ha, gOf_int, gOf_one, sub_eq_zero, natCast_zsmul, ← ofMul_pow]
    congr 1
    exact Units.ext (by simp [h])
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx =>
    have hc : c = ULift.up (((c.down.cast : ℤ)) : ZMod q) := by
      ext; simp
    rw [hc, nuA_smul, hx, smul_zero]

def nuQ (A : CommRingCat.{0}) : (twF q 1).obj A →+ Additive Aˣ :=
  QuotientAddGroup.lift (twRel q 1 A).toAddSubgroup (nuA q A) (fun x hx => nuA_rel q A x hx)

/- English proof (translation)
Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H x => exact nuA_smul q A n x`.
-/
theorem nuQ_smul (A : CommRingCat.{0}) (n : ℤ) (x : (twF q 1).obj A) :
    nuQ q A ((ULift.up (n : ZMod q) : ULift.{1} (ZMod q)) • x) = n • nuQ q A x := by
  induction x using Submodule.Quotient.induction_on with
  | H x => exact nuA_smul q A n x

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
theorem unitOf_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (ζ : Prim q A) :
    unitOf q (ζ.map f) = Units.map f.toMonoidHom (unitOf q ζ) := Units.ext rfl

/- English proof (translation)
Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H x`. Express the relevant statement in the definitionally equal form `nuA q B (Finsupp.mapDomain (Prim.map f.hom) x) = MonoidHom.toAdditive (Units.map f.hom.toMonoidHom) (nuA q A x)`. Proceed by induction on `x using Finsupp.induction_linear with`. Consider the case `zero => simp`.

Consider the case `add x y hx hy => rw [Finsupp.mapDomain_add, map_add, map_add, map_add, hx, hy]`. Consider the case `single ζ b`. Rewrite using `[Finsupp.mapDomain_single, nuA_single, nuA_single]`. Establish `hb : b.down = ((b.down.cast : ℤ) : ZMod q)` using `by simp`. Rewrite using `[hb, gOf_int, gOf_int, map_zsmul, unitOf_map]`.

Both sides reduce to the same expression.
-/
theorem nuQ_nat {A B : CommRingCat.{0}} (f : A ⟶ B) (x : (twF q 1).obj A) :
    nuQ q B (((twF q 1).map f).hom x) = MonoidHom.toAdditive (Units.map f.hom.toMonoidHom) (nuQ q A x) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change nuA q B (Finsupp.mapDomain (Prim.map f.hom) x) = MonoidHom.toAdditive (Units.map f.hom.toMonoidHom) (nuA q A x)
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [Finsupp.mapDomain_add, map_add, map_add, map_add, hx, hy]
    | single ζ b =>
      rw [Finsupp.mapDomain_single, nuA_single, nuA_single]
      have hb : b.down = ((b.down.cast : ℤ) : ZMod q) := by simp
      rw [hb, gOf_int, gOf_int, map_zsmul, unitOf_map]
      rfl

abbrev fq : ULift.{1} ℤ →+* ULift.{1} (ZMod q) :=
  (ULift.ringEquiv.symm : ZMod q ≃+* ULift.{1} (ZMod q)).toRingHom.comp
    ((Int.castRingHom (ZMod q)).comp (ULift.ringEquiv : ULift.{1} ℤ ≃+* ℤ).toRingHom)

def nuR : twF q 1 ⋙ ModuleCat.restrictScalars.{1} (fq q) ⟶ unitsF where
  app A :=
    letI : Module (ULift.{1} ℤ) ((twF q 1).obj A) := Module.compHom _ (fq q)
    ModuleCat.ofHom (show (ModuleCat.restrictScalars.{1} (fq q)).obj ((twF q 1).obj A) →ₗ[ULift.{1} ℤ]
      ULift.{1} (Additive (A : Type)ˣ) from
    { toFun := fun x => ULift.up (nuQ q A x)
      map_add' := fun x y => congrArg ULift.up (map_add _ x y)
      map_smul' := fun c x => congrArg ULift.up (nuQ_smul q A c.down x) })
  naturality A B f := by
    ext x
    exact congrArg ULift.up (nuQ_nat q f x)

/- English proof (translation)
Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H x`. Express the relevant statement in the definitionally equal form `q • nuA q A x = 0`. Proceed by induction on `x using Finsupp.induction_linear with`. Consider the case `zero => simp`.

Consider the case `add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]`. Consider the case `single ζ b`. Rewrite using `[nuA_single, ← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero]`.
-/
theorem nuQ_q (A : CommRingCat.{0}) (x : (twF q 1).obj A) : q • nuQ q A x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change q • nuA q A x = 0
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]
    | single ζ b =>
      rw [nuA_single, ← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero]

/- English proof (translation)
Use extensionality with `A x`. Conclude with `congrArg ULift.up (nuQ_q q A x)`.
-/
theorem nuR_pow : nuR q ≫ LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powNat q = 0 := by
  ext A x
  exact congrArg ULift.up (nuQ_q q A x)

abbrev rs := ModuleCat.restrictScalars.{1} (fq q)
abbrev cs := ModuleCat.coextendScalars.{1, 1, 1} (fq q)

instance : (cs q).IsRightAdjoint := (ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} (fq q)).isRightAdjoint

abbrev adjW := Adjunction.whiskerRight Scheme.{0}ᵒᵖ (ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} (fq q))

/- English proof (translation)
Use extensionality with `U x`. Both sides reduce to the same expression.
-/
theorem wr_zero {X Y : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))} :
    ((Functor.whiskeringRight _ _ _).obj (rs q)).map (0 : X ⟶ Y) = 0 := by
  ext U x
  rfl

abbrev nuP : Scheme.Γ ⋙ twF q 1 ⋙ rs q ⟶ Scheme.Γ ⋙ unitsF := Functor.whiskerLeft Scheme.Γ (nuR q)

abbrev tG : Scheme.Γ ⋙ unitsF ⟶ Gm.obj := toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ unitsF)

abbrev psi : Scheme.Γ ⋙ twF q 1 ⟶ Gm.obj ⋙ cs q :=
  (adjW q).homEquiv _ _ (nuP q ≫ tG)

/- English proof (translation)
The claim follows from `((sheafCompose Scheme.etaleTopology.{0} (cs q)).obj Gm).property`.
-/
theorem hC : Presheaf.IsSheaf Scheme.etaleTopology.{0} (Gm.obj ⋙ cs q) :=
  ((sheafCompose Scheme.etaleTopology.{0} (cs q)).obj Gm).property

abbrev psi' : sheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ twF q 1) ⟶ Gm.obj ⋙ cs q :=
  sheafifyLift Scheme.etaleTopology.{0} (psi q) (hC q)

def kappa : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm :=
  ⟨((adjW q).homEquiv _ _).symm (psi' q)⟩

/- English proof (translation)
Express the relevant statement in the definitionally equal form `((Functor.whiskeringRight _ _ _).obj (rs q)).map (toSheafify _ _) ≫ ((adjW q).homEquiv _ _).symm (psi' q) = _`. Rewrite using `[← Adjunction.homEquiv_naturality_left_symm, toSheafify_sheafifyLift]`. Conclude with `Equiv.symm_apply_apply _ _`.
-/
theorem key : Functor.whiskerRight (toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ twF q 1)) (rs q) ≫ (kappa q).hom =
    nuP q ≫ tG := by
  change ((Functor.whiskeringRight _ _ _).obj (rs q)).map (toSheafify _ _) ≫ ((adjW q).homEquiv _ _).symm (psi' q) = _
  rw [← Adjunction.homEquiv_naturality_left_symm, toSheafify_sheafifyLift]
  exact Equiv.symm_apply_apply _ _

/- English proof (translation)
Establish `h : (0 : ((Functor.whiskeringRight _ _ _).obj (rs q)).obj X ⟶ Y) = ((Functor.whiskeringRight _ _ _).obj (rs q)).map (0 : X ⟶ X) ≫ 0` using `by rw [wr_zero, zero_comp]`. Rewrite using `[h, Adjunction.homEquiv_naturality_left, zero_comp]`.
-/
theorem homEquiv_zero {X : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))} {Y : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} ℤ)} :
    (adjW q).homEquiv X Y 0 = 0 := by
  have h : (0 : ((Functor.whiskeringRight _ _ _).obj (rs q)).obj X ⟶ Y) =
      ((Functor.whiskeringRight _ _ _).obj (rs q)).map (0 : X ⟶ X) ≫ 0 := by rw [wr_zero, zero_comp]
  rw [h, Adjunction.homEquiv_naturality_left, zero_comp]

/- English proof (translation)
Rewrite using `[← homEquiv_zero q, Equiv.symm_apply_apply]`.
-/
theorem homEquiv_symm_zero {X : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))} {Y : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} ℤ)} :
    ((adjW q).homEquiv X Y).symm 0 = 0 := by
  rw [← homEquiv_zero q, Equiv.symm_apply_apply]

omit [NeZero q] in
/- English proof (translation)
The claim follows from `(toSheafify_naturality _ _).symm`.
-/
theorem hpv : tG ≫ (LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q).hom = Functor.whiskerLeft Scheme.Γ (LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powNat q) ≫ tG :=
  (toSheafify_naturality _ _).symm

/- English proof (translation)
Apply `(sheafToPresheaf Scheme.etaleTopology.{0} _).map_injective` to reduce the goal to its premises. Rewrite using `[Functor.map_comp, Functor.map_zero]`. Express the relevant statement in the definitionally equal form `((adjW q).homEquiv _ _).symm (psi' q) ≫ (LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q).hom = 0`. Rewrite using `[← Adjunction.homEquiv_naturality_right_symm]`. Establish `h0 : psi' q ≫ ((Functor.whiskeringRight _ _ _).obj (cs q)).map (LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q).hom = 0`.

Apply `sheafify_hom_ext _ _ _ (hC q)` to reduce the goal to its premises. Rewrite using `[comp_zero, ← Category.assoc, toSheafify_sheafifyLift, ← Adjunction.homEquiv_naturality_right, Category.assoc, hpv, ← Category.assoc, ← Functor.whiskerLeft_comp, nuR_pow]`. Establish `hz : Functor.whiskerLeft Scheme.Γ (0 : twF q 1 ⋙ rs q ⟶ unitsF) = 0` using `by ext U x; rfl`. Rewrite using `[hz, zero_comp, homEquiv_zero]`. Rewrite using `[h0, homEquiv_symm_zero]`.
-/
theorem kappa_pow : kappa q ≫ LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q = 0 := by
  apply (sheafToPresheaf Scheme.etaleTopology.{0} _).map_injective
  rw [Functor.map_comp, Functor.map_zero]
  change ((adjW q).homEquiv _ _).symm (psi' q) ≫ (LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q).hom = 0
  rw [← Adjunction.homEquiv_naturality_right_symm]
  have h0 : psi' q ≫ ((Functor.whiskeringRight _ _ _).obj (cs q)).map (LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q).hom = 0 := by
    apply sheafify_hom_ext _ _ _ (hC q)
    rw [comp_zero, ← Category.assoc, toSheafify_sheafifyLift, ← Adjunction.homEquiv_naturality_right,
      Category.assoc, hpv, ← Category.assoc, ← Functor.whiskerLeft_comp, nuR_pow]
    have hz : Functor.whiskerLeft Scheme.Γ (0 : twF q 1 ⋙ rs q ⟶ unitsF) = 0 := by ext U x; rfl
    rw [hz, zero_comp, homEquiv_zero]
  rw [h0, homEquiv_symm_zero]

/- English proof (translation)
Introduce `U ζ u hu`. Use `congrArg (fun η => (η.app (op U)).hom (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q 1).obj Γ(U, ⊤))) (key q)` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Conclude with `congrArg (fun y => ((toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ unitsF)).app (op U)).hom y) (congrArg ULift.up ((nuA_single q _ ζ 1).trans ((gOf_one q ζ).trans (congrArg _ (Units.ext hu.symm)))))`.
-/
theorem gen_kappa : LateralTheory.E.H2CurveOrder.LeafKumMuUnitsPf.Gen q (kappa q) := by
  intro U ζ u hu
  have := congrArg (fun η => (η.app (op U)).hom
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q 1).obj Γ(U, ⊤))) (key q)
  refine this.trans ?_
  exact congrArg (fun y => ((toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ unitsF)).app (op U)).hom y)
    (congrArg ULift.up ((nuA_single q _ ζ 1).trans ((gOf_one q ζ).trans (congrArg _ (Units.ext hu.symm)))))

/- English proof (translation)
Introduce `q _ B _ _`. Conclude with `⟨kappa q, kappa_pow q, gen_kappa q⟩`.
-/
theorem LeafKumMuMap_of : LateralTheory.E.H2CurveOrder.LeafKumMuUnitsPf.LeafKumMuMap := by
  intro q _ B _ _
  exact ⟨kappa q, kappa_pow q, gen_kappa q⟩

end LateralTheory.E.H2CurveOrder.LeafKumMuMapPf
