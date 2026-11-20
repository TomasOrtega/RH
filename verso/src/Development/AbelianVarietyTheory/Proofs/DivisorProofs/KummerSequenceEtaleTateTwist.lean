import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigEtaleModuleSheafMonoEpiIffSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.KummerSeq

variable (q : ℕ) [NeZero q]

abbrev ρ : ULift.{1} ℤ →+* ULift.{1} (ZMod q) :=
  (ULift.ringEquiv.symm : ZMod q ≃+* ULift.{1} (ZMod q)).toRingHom.comp
    ((Int.castRingHom (ZMod q)).comp (ULift.ringEquiv : ULift.{1} ℤ ≃+* ℤ).toRingHom)

variable {q}

def pu {A : Type} [CommRing A] (ζ : Prim q A) : Aˣ :=
  Units.ofPowEqOne ζ.1 q ((GlobalTheory.EtC.PrimBasic.prim_basic q A).1 ζ) (NeZero.ne q)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem pu_val {A : Type} [CommRing A] (ζ : Prim q A) : (pu ζ : A) = ζ.1 := rfl

/- English proof (translation)
The claim follows from `Units.ext (by simp [(GlobalTheory.EtC.PrimBasic.prim_basic q A).1 ζ])`.
-/
theorem pu_pow {A : Type} [CommRing A] (ζ : Prim q A) : pu ζ ^ q = 1 :=
  Units.ext (by simp [(GlobalTheory.EtC.PrimBasic.prim_basic q A).1 ζ])

def coefHom {A : Type} [CommRing A] (u : Aˣ) (hu : u ^ q = 1) : ZMod q →+ Additive Aˣ :=
  ZMod.lift q ⟨zmultiplesHom _ (Additive.ofMul u), by
    simp only [zmultiplesHom_apply, natCast_zsmul]
    rw [← ofMul_pow, hu, ofMul_one]⟩

/- English proof (translation)
Establish `: c = ((c.val : ℤ) : ZMod q)` using `by simp`. Use `conv_lhs => rw [this]`. Rewrite using `[coefHom, ZMod.lift_coe, zmultiplesHom_apply, natCast_zsmul]`.
-/
theorem coefHom_apply {A : Type} [CommRing A] (u : Aˣ) (hu : u ^ q = 1) (c : ZMod q) :
    coefHom u hu c = c.val • Additive.ofMul u := by
  have : c = ((c.val : ℤ) : ZMod q) := by simp
  conv_lhs => rw [this]
  rw [coefHom, ZMod.lift_coe, zmultiplesHom_apply, natCast_zsmul]

/- English proof (translation)
Rewrite using `[coefHom, show (1 : ZMod q) = ((1 : ℤ) : ZMod q) from Int.cast_one.symm, ZMod.lift_coe]`. Simplify using the standard rewrite rules.
-/
theorem coefHom_one {A : Type} [CommRing A] (u : Aˣ) (hu : u ^ q = 1) : coefHom u hu 1 = Additive.ofMul u := by
  rw [coefHom, show (1 : ZMod q) = ((1 : ℤ) : ZMod q) from Int.cast_one.symm, ZMod.lift_coe]
  simp

/- English proof (translation)
Establish `: c = ((c.down.val : ℕ) : ULift.{1} (ZMod q))`. Use `ULift.ext _ _ ?_` and prove the remaining obligations. Rewrite using `[ULift.down_natCast, ZMod.natCast_zmod_val]`. Use `conv_lhs => rw [this]`. Rewrite using `[Nat.cast_smul_eq_nsmul]`.
-/
theorem ulift_smul_eq {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (c : ULift.{1} (ZMod q)) (x : M) :
    c • x = c.down.val • x := by
  have : c = ((c.down.val : ℕ) : ULift.{1} (ZMod q)) := by
    refine ULift.ext _ _ ?_
    rw [ULift.down_natCast, ZMod.natCast_zmod_val]
  conv_lhs => rw [this]
  rw [Nat.cast_smul_eq_nsmul]

def gHom (A : Type) [CommRing A] : (Prim q A →₀ ULift.{1} (ZMod q)) →+ Additive Aˣ :=
  Finsupp.liftAddHom fun ζ => (coefHom (pu ζ) (pu_pow ζ)).comp AddEquiv.ulift.toAddMonoidHom

/- English proof (translation)
Simplify using `[gHom]`. Both sides reduce to the same expression.
-/
theorem gHom_single (A : Type) [CommRing A] (ζ : Prim q A) (c : ULift.{1} (ZMod q)) :
    gHom A (Finsupp.single ζ c) = coefHom (pu ζ) (pu_pow ζ) c.down := by
  simp [gHom]; rfl

/- English proof (translation)
Rewrite using `[ulift_smul_eq, map_nsmul]`.
-/
theorem gHom_smul (A : Type) [CommRing A] (c : ULift.{1} (ZMod q)) (x : Prim q A →₀ ULift.{1} (ZMod q)) :
    gHom A (c • x) = c.down.val • gHom A x := by
  rw [ulift_smul_eq, map_nsmul]

def gKer (A : Type) [CommRing A] : Submodule (ULift.{1} (ZMod q)) (Prim q A →₀ ULift.{1} (ZMod q)) where
  carrier := {x | gHom A x = 0}
  add_mem' {a b} ha hb := by simp_all
  zero_mem' := by simp
  smul_mem' c x hx := by
    show gHom A (c • x) = 0
    rw [gHom_smul, show gHom A x = 0 from hx, nsmul_zero]

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨ζ, ξ, a, h, rfl⟩`. Use `show gHom A _ = 0`. Establish `hu : pu ξ = pu ζ ^ (a : ZMod q).val` using `Units.ext (by simp [h])`. Rewrite using `[map_sub, gHom_single, gHom_single, zpow_one]`.

Express the relevant statement in the definitionally equal form `coefHom (pu ξ) (pu_pow ξ) 1 - coefHom (pu ζ) (pu_pow ζ) (a : ZMod q) = 0`. Rewrite using `[coefHom_one, coefHom_apply, hu, ofMul_pow, sub_self]`.
-/
theorem twRel_le_gKer (A : Type) [CommRing A] : twRel q 1 A ≤ gKer A := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  show gHom A _ = 0
  have hu : pu ξ = pu ζ ^ (a : ZMod q).val := Units.ext (by simp [h])
  rw [map_sub, gHom_single, gHom_single, zpow_one]
  change coefHom (pu ξ) (pu_pow ξ) 1 - coefHom (pu ζ) (pu_pow ζ) (a : ZMod q) = 0
  rw [coefHom_one, coefHom_apply, hu, ofMul_pow, sub_self]

def kapA (A : Type) [CommRing A] : ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q 1 A) →+ Additive Aˣ :=
  QuotientAddGroup.lift (twRel q 1 A).toAddSubgroup (gHom A) (fun x hx => twRel_le_gKer A hx)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem kapA_mk (A : Type) [CommRing A] (x : Prim q A →₀ ULift.{1} (ZMod q)) :
    kapA A (Submodule.Quotient.mk x) = gHom A x := rfl

end GlobalTheory.EtC.KummerSeq

noncomputable section
namespace GlobalTheory.EtC.KummerSeq
variable {q : ℕ} [NeZero q]

/- English proof (translation)
Establish `: (ULift.up.{1} (n : ZMod q) : ULift.{1} (ZMod q)) = (n : ULift.{1} (ZMod q))`. Use `ULift.ext _ _ ?_` and prove the remaining obligations. Rewrite using `[ULift.down_intCast]`. Conclude with `(congrArg (fun c => kapA A (c • x)) this).trans (by rw [Int.cast_smul_eq_zsmul, map_zsmul])`.
-/
theorem kapA_smul (A : Type) [CommRing A] (n : ℤ) (x : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q 1 A) :
    kapA A ((ULift.up.{1} (n : ZMod q)) • x) = n • kapA A x := by
  have : (ULift.up.{1} (n : ZMod q) : ULift.{1} (ZMod q)) = (n : ULift.{1} (ZMod q)) := by
    refine ULift.ext _ _ ?_
    rw [ULift.down_intCast]
  exact (congrArg (fun c => kapA A (c • x)) this).trans (by rw [Int.cast_smul_eq_zsmul, map_zsmul])

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
theorem pu_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (ζ : Prim q A) :
    pu (ζ.map f) = Units.map f.toMonoidHom (pu ζ) := Units.ext rfl

/- English proof (translation)
Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H x`. Rewrite using `[Submodule.mapQ_apply, kapA_mk, kapA_mk]`. Proceed by induction on `x using Finsupp.induction_linear with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => rw [map_add, map_add, map_add, ha, hb, map_add]`. Consider the case `single ζ c`. Rewrite using `[Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, gHom_single, gHom_single, coefHom_apply, coefHom_apply, pu_map, map_nsmul]`. Both sides reduce to the same expression.
-/
theorem kapA_nat {A B : CommRingCat.{0}} (f : A ⟶ B) (x : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q 1 A) :
    kapA B (Submodule.mapQ _ _ (Finsupp.lmapDomain _ _ (Prim.map f.hom)) (twRel_le q 1 f.hom) x) =
      MonoidHom.toAdditive (Units.map f.hom.toMonoidHom) (kapA A x) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [Submodule.mapQ_apply, kapA_mk, kapA_mk]
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, map_add]
    | single ζ c =>
      rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, gHom_single, gHom_single, coefHom_apply,
        coefHom_apply, pu_map, map_nsmul]
      rfl

def kapL (A : CommRingCat.{0}) :
    (ModuleCat.restrictScalars.{1} (ρ q)).obj ((twF q 1).obj A) →ₗ[ULift.{1} ℤ] unitsF.obj A where
  toFun x := ULift.up (kapA A x)
  map_add' x y := congrArg ULift.up (map_add (kapA A) x y)
  map_smul' c x := congrArg ULift.up (kapA_smul A c.down x)

def kapN : twF q 1 ⋙ ModuleCat.restrictScalars.{1} (ρ q) ⟶ unitsF where
  app A :=
    letI : Module (ULift.{1} ℤ) ((twF q 1).obj A) := Module.compHom _ (ρ q)
    ModuleCat.ofHom (kapL A)
  naturality A B f := by
    ext x
    exact congrArg ULift.up (kapA_nat f x)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `ULift.up (kapA A (Submodule.Quotient.mk (Finsupp.single ζ 1))) = _`. Rewrite using `[kapA_mk, gHom_single]`. Conclude with `congrArg ULift.up (coefHom_one _ _)`.
-/
theorem kapN_gen (A : CommRingCat.{0}) (ζ : Prim q A) :
    (kapN.app A).hom (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q 1).obj A) =
      ULift.up (Additive.ofMul (pu ζ)) := by
  change ULift.up (kapA A (Submodule.Quotient.mk (Finsupp.single ζ 1))) = _
  rw [kapA_mk, gHom_single]
  exact congrArg ULift.up (coefHom_one _ _)

end GlobalTheory.EtC.KummerSeq

noncomputable section
namespace GlobalTheory.EtC.KummerSeq
variable {q : ℕ} [NeZero q]

abbrev Pz (q : ℕ) [NeZero q] : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} ℤ) :=
  Scheme.Γ ⋙ twF q 1 ⋙ ModuleCat.restrictScalars.{1} (ρ q)

abbrev eta (q : ℕ) [NeZero q] : Pz q ⟶ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)).obj :=
  Functor.whiskerRight (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 1)) (ModuleCat.restrictScalars.{1} (ρ q))

instance : Presheaf.IsLocallyInjective Scheme.etaleTopology (eta q) :=
  ⟨fun x y h => (inferInstance : Presheaf.IsLocallyInjective Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 1))).equalizerSieve_mem x y h⟩

instance : Presheaf.IsLocallySurjective Scheme.etaleTopology (eta q) :=
  ⟨fun s => (inferInstance : Presheaf.IsLocallySurjective Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 1))).imageSieve_mem s⟩

abbrev phi0 (q : ℕ) [NeZero q] : Pz q ⟶ Gm.obj :=
  Functor.whiskerLeft Scheme.Γ kapN ≫ toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)

abbrev Rt (q : ℕ) [NeZero q] : Shv ℤ := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)

/- English proof (translation)
Establish `hW : Scheme.etaleTopology.W (eta q)` using `GrothendieckTopology.W_of_isLocallyBijective _ _`. Take `⟨f, hf⟩` from `(hW Gm.obj Gm.cond).2 (phi0 q)`. Conclude with `⟨⟨f⟩, hf⟩`.
-/
theorem kap_exists (q : ℕ) [NeZero q] :
    ∃ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm, eta q ≫ κ.hom = phi0 q := by
  have hW : Scheme.etaleTopology.W (eta q) := GrothendieckTopology.W_of_isLocallyBijective _ _
  obtain ⟨f, hf⟩ := (hW Gm.obj Gm.cond).2 (phi0 q)
  exact ⟨⟨f⟩, hf⟩

end GlobalTheory.EtC.KummerSeq

noncomputable section
namespace GlobalTheory.EtC.KummerSeq
variable {q : ℕ} [NeZero q]

def kap (q : ℕ) [NeZero q] : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm := (kap_exists q).choose

/- English proof (translation)
The claim follows from `(kap_exists q).choose_spec`.
-/
theorem kap_spec (q : ℕ) [NeZero q] : eta q ≫ (kap q).hom = phi0 q := (kap_exists q).choose_spec

/- English proof (translation)
Use `congrArg (fun f => (f.app (op U)).hom x) (kap_spec q)` as an intermediate fact. Conclude with `this`.
-/
theorem kap_sec (U : Scheme.{0}) (x : (twF q 1).obj Γ(U, ⊤)) :
    Sec.map (kap q) (ofRings.sec (twF q 1) U x : Sec (Rt q) U) =
      ofRings.sec unitsF U ((kapN.app Γ(U, ⊤)).hom x) := by
  have := congrArg (fun f => (f.app (op U)).hom x) (kap_spec q)
  exact this

abbrev gen {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) : Sec (Rt q) U := twGen 1 ζ

/- English proof (translation)
Conclude with `(kap_sec U (Submodule.Quotient.mk (Finsupp.single ζ 1))).trans (congrArg (ofRings.sec unitsF U) (kapN_gen Γ(U, ⊤) ζ))`.
-/
theorem kap_gen (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) :
    Sec.map (kap q) (gen ζ) = unitSec (pu ζ) := by
  exact (kap_sec U (Submodule.Quotient.mk (Finsupp.single ζ 1))).trans
    (congrArg (ofRings.sec unitsF U) (kapN_gen Γ(U, ⊤) ζ))

/- English proof (translation)
Simplify using `[Sec.res]`.
-/
theorem sec_res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res]

/- English proof (translation)
Use `congrArg (fun f => f.hom x) (φ.hom.naturality g.op)` as an intermediate fact. Conclude with `this`.
-/
theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  have := congrArg (fun f => f.hom x) (φ.hom.naturality g.op)
  exact this

/- English proof (translation)
Use `congrArg (fun f => f.hom x) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op)` as an intermediate fact. Conclude with `this.symm`.
-/
theorem ofRings_sec_res {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {V U : Scheme.{0}}
    (g : V ⟶ U) (x : M.obj Γ(U, ⊤)) :
    Sec.res g (ofRings.sec M U x) = ofRings.sec M V ((M.map (CommRingCat.ofHom g.appTop.hom)).hom x) := by
  have := congrArg (fun f => f.hom x) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op)
  exact this.symm

/- English proof (translation)
Conclude with `ofRings_sec_res unitsF g (show unitsF.obj Γ(U, ⊤) from ⟨Additive.ofMul u⟩)`.
-/
theorem unitSec_res {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res g (unitSec u) = unitSec (Units.map g.appTop.hom.toMonoidHom u) := by
  exact ofRings_sec_res unitsF g (show unitsF.obj Γ(U, ⊤) from ⟨Additive.ofMul u⟩)

/- English proof (translation)
Conclude with `map_add (((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom) (show unitsF.obj Γ(U, ⊤) from ⟨Additive.ofMul u⟩) ⟨Additive.ofMul v⟩`.
-/
theorem unitSec_mul {U : Scheme.{0}} (u v : (Γ(U, ⊤))ˣ) : unitSec (u * v) = unitSec u + unitSec v := by
  exact map_add (((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom)
    (show unitsF.obj Γ(U, ⊤) from ⟨Additive.ofMul u⟩) ⟨Additive.ofMul v⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[pow_zero, zero_smul]`. Conclude with `map_zero (((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom)`. Consider the case `succ n ih => rw [pow_succ, unitSec_mul, ih, succ_nsmul]`.
-/
theorem unitSec_pow {U : Scheme.{0}} (u : (Γ(U, ⊤))ˣ) (n : ℕ) : unitSec (u ^ n) = n • unitSec u := by
  induction n with
  | zero =>
    rw [pow_zero, zero_smul]
    exact map_zero (((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom)
  | succ n ih => rw [pow_succ, unitSec_mul, ih, succ_nsmul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sec_map_smul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) (n : ℤ) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (n • φ) x = n • Sec.map φ x := by
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

/- English proof (translation)
The claim follows from `(sec_ext_glue R F U).1 a b (loc_calculus.2.2.2.2.2.2 U _)`.
-/
theorem sec_empty {R : Type} [CommRing R] (F : Shv R) (U : Scheme.{0}) [IsEmpty U] (a b : Sec F U) : a = b :=
  (sec_ext_glue R F U).1 a b (loc_calculus.2.2.2.2.2.2 U _)

end GlobalTheory.EtC.KummerSeq

noncomputable section
namespace GlobalTheory.EtC.KummerSeq
variable {q : ℕ} [NeZero q]

/- English proof (translation)
Rewrite using `[← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]`. Establish `: ((q : ℕ) : ULift.{1} (ZMod q)) = 0`. Use `ULift.ext _ _ ?_` and prove the remaining obligations. Rewrite using `[ULift.down_natCast, ZMod.natCast_self]`. Both sides reduce to the same expression.

Rewrite using `[this, zero_smul]`.
-/
theorem sec_q_smul (F : Shv (ZMod q)) (U : Scheme.{0}) (x : Sec F U) : q • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    refine ULift.ext _ _ ?_
    rw [ULift.down_natCast, ZMod.natCast_self]
    rfl
  rw [this, zero_smul]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Rewrite `hne` using `[not_isEmpty_iff]`. Use `haveI : Nonempty (⊤ : W.Opens) := ⟨⟨hne.some, trivial⟩⟩`. Use `haveI := Scheme.component_nontrivial W ⊤`. Conclude with `not_subsingleton _ h`.
-/
theorem isEmpty_of_sub (W : Scheme.{0}) (h : Subsingleton Γ(W, ⊤)) : IsEmpty W := by
  by_contra hne
  rw [not_isEmpty_iff] at hne
  haveI : Nonempty (⊤ : W.Opens) := ⟨⟨hne.some, trivial⟩⟩
  haveI := Scheme.component_nontrivial W ⊤
  exact not_subsingleton _ h

/- English proof (translation)
Distinguish the cases in `hc : q ∣ c`. Take `⟨m, rfl⟩` from `hc`. Rewrite using `[mul_comm, mul_nsmul, sec_q_smul]`. Establish `hu` using `(GlobalTheory.EtC.PrimBasic.prim_basic q Γ(W, ⊤)).2.2.1 ζ c 0 (by`. Introduce `h'; exact hc (Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using h')))`.

Rewrite `hu` using `[h, pow_zero, sub_self]`. Use `haveI := isEmpty_of_sub W (subsingleton_of_zero_eq_one (isUnit_zero_iff.1 hu))`. Conclude with `sec_empty _ W _ _`.
-/
theorem smul_twGen_eq_zero (W : Scheme.{0}) (ζ : Prim q Γ(W, ⊤)) (c : ℕ) (h : ζ.1 ^ c = 1) :
    c • twGen 1 ζ = 0 := by
  by_cases hc : q ∣ c
  · obtain ⟨m, rfl⟩ := hc
    rw [mul_comm, mul_nsmul, sec_q_smul]
  · have hu := (GlobalTheory.EtC.PrimBasic.prim_basic q Γ(W, ⊤)).2.2.1 ζ c 0 (by
      intro h'; exact hc (Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using h')))
    rw [h, pow_zero, sub_self] at hu
    haveI := isEmpty_of_sub W (subsingleton_of_zero_eq_one (isUnit_zero_iff.1 hu))
    exact sec_empty _ W _ _

/- English proof (translation)
Take `⟨S, hS, hP⟩` from `h`. Use `choose s hs using hP`. Take `⟨a, ha⟩` from `(sec_ext_glue R F U).2 S hS s (by`. Introduce `V W g k hg`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[sec_map_res, hs, hs, sec_res_comp])`. Use `⟨a, (sec_ext_glue R G U).1 _ _ ⟨S, hS, fun V g hg => ?_⟩⟩` and prove the remaining obligations. Use `show Sec.res g (Sec.map φ a) = Sec.res g b`. Rewrite using `[← sec_map_res, ha V g hg, hs]`.
-/
theorem glue_inj {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) (hinj : ∀ U, Function.Injective (Sec.map φ (U := U)))
    (U : Scheme.{0}) (b : Sec G U) (h : Loc U fun V g => ∃ a : Sec F V, Sec.map φ a = Sec.res g b) :
    ∃ a, Sec.map φ a = b := by
  obtain ⟨S, hS, hP⟩ := h
  choose s hs using hP
  obtain ⟨a, ha⟩ := (sec_ext_glue R F U).2 S hS s (by
    intro V W g k hg
    apply hinj
    rw [sec_map_res, hs, hs, sec_res_comp])
  refine ⟨a, (sec_ext_glue R G U).1 _ _ ⟨S, hS, fun V g hg => ?_⟩⟩
  show Sec.res g (Sec.map φ a) = Sec.res g b
  rw [← sec_map_res, ha V g hg, hs]

/- English proof (translation)
Simplify using `[Scheme.Hom.comp_appTop]`. Both sides reduce to the same expression.
-/
theorem appTop_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Γ(U, ⊤)) :
    (k ≫ g).appTop.hom x = k.appTop.hom (g.appTop.hom x) := by
  simp [Scheme.Hom.comp_appTop]
  rfl

end GlobalTheory.EtC.KummerSeq

noncomputable section
namespace GlobalTheory.EtC.KummerSeq
variable {q : ℕ} [NeZero q]

/- English proof (translation)
The claim follows from `loc_calculus.2.1 U P Q h hPQ`.
-/
theorem loc_mono' {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (hPQ : ∀ V g, P V g → Q V g) :
    Loc U Q := loc_calculus.2.1 U P Q h hPQ

/- English proof (translation)
The claim follows from `loc_calculus.2.2.2.2.1 U P h`.
-/
theorem loc_trans' {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U fun V g => Loc V fun W k => P W (k ≫ g)) : Loc U P := loc_calculus.2.2.2.2.1 U P h

/- English proof (translation)
Simplify using `using hq.map g.appTop.hom`.
-/
theorem isUnit_res {V U : Scheme.{0}} (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤))) : IsUnit (q : Γ(V, ⊤)) := by
  simpa using hq.map g.appTop.hom

/- English proof (translation)
The claim follows from `map_nsmul ((kap q).hom.app (op U)).hom c a`.
-/
theorem kap_nsmul {U : Scheme.{0}} (c : ℕ) (a : Sec (Rt q) U) : Sec.map (kap q) (c • a) = c • Sec.map (kap q) a :=
  map_nsmul ((kap q).hom.app (op U)).hom c a

/- English proof (translation)
Use `loc_trans' (loc_mono' ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).1 hq) ?_)` and prove the remaining obligations. Introduce and unpack `W k ⟨ζ⟩`. Establish `hx' : ((Units.map k.appTop.hom.toMonoidHom x : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)) ^ q = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, ← map_pow, hx, map_one, Units.val_one]`. Use `loc_mono' ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q W).2.2.1 ζ _ hx') ?_` and prove the remaining obligations.

Introduce and unpack `W' k' ⟨c, hc⟩`. Use `⟨c • gen (ζ.map k'.appTop.hom), ?_⟩` and prove the remaining obligations. Rewrite using `[kap_nsmul, kap_gen, ← unitSec_pow]`. Use `congr 1`. Use `ext`.

Use `show k'.appTop.hom ζ.1 ^ c = (k' ≫ k).appTop.hom x.1`. Rewrite using `[appTop_comp]`. Conclude with `hc.symm`.
-/
theorem lift_root (V : Scheme.{0}) (x : (Γ(V, ⊤))ˣ) (hq : IsUnit (q : Γ(V, ⊤))) (hx : x ^ q = 1) :
    Loc V fun W k => ∃ a : Sec (Rt q) W, Sec.map (kap q) a = unitSec (Units.map k.appTop.hom.toMonoidHom x) := by
  refine loc_trans' (loc_mono' ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).1 hq) ?_)
  rintro W k ⟨ζ⟩
  have hx' : ((Units.map k.appTop.hom.toMonoidHom x : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)) ^ q = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hx, map_one, Units.val_one]
  refine loc_mono' ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q W).2.2.1 ζ _ hx') ?_
  rintro W' k' ⟨c, hc⟩
  refine ⟨c • gen (ζ.map k'.appTop.hom), ?_⟩
  rw [kap_nsmul, kap_gen, ← unitSec_pow]
  congr 1
  ext
  show k'.appTop.hom ζ.1 ^ c = (k' ≫ k).appTop.hom x.1
  rw [appTop_comp]
  exact hc.symm

end GlobalTheory.EtC.KummerSeq

noncomputable section
namespace GlobalTheory.EtC.KummerSeq
variable {q : ℕ} [NeZero q]

/- English proof (translation)
Use `((GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections ℤ (kap q)).2.1).2 ?_` and prove the remaining obligations. Introduce `U a ha`. Use `loc_trans' (loc_mono' ((GlobalTheory.T.tateTwist_sections_locally_generated q 1).1 U a) ?_)` and prove the remaining obligations. Introduce and unpack `V g (h0 | ⟨ζ, c, hc⟩)`. Use `loc_calculus.1 V _ (fun W k => ?_) show Sec.res (k ≫ g) a = 0` and prove the remaining obligations.

Rewrite using `[sec_res_comp]`. Establish `e : Sec.res (F` using `Rt q) g a = 0 := h0`. Rewrite using `[e]`. Conclude with `map_zero _`. Establish `e : Sec.res (F` using `Rt q) g a = c • gen ζ := hc`.

Establish `h1 : Sec.map (kap q) (Sec.res g a) = 0` using `by rw [sec_map_res, ha]; exact map_zero _`. Rewrite `h1` using `[e, kap_nsmul, kap_gen, ← unitSec_pow]`. Use `loc_mono' ((toSheafify_loc_bij_lift ℤ (Scheme.Γ ⋙ unitsF)).2.1 V _ h1) ?_` and prove the remaining obligations. Introduce `W k hk`. Establish `h2 : Units.map k.appTop.hom.toMonoidHom (pu ζ ^ c) = 1` using `congrArg (fun y => Additive.toMul (ULift.down y)) hk`.

Establish `hz : (ζ.map k.appTop.hom).1 ^ c = 1`. Establish `h3` using `congrArg Units.val h2`. Rewrite `h3` using `[map_pow]`. Conclude with `h3`. Use `show Sec.res (k ≫ g) a = 0`.

Rewrite using `[sec_res_comp, e]`. Use `show ((Rt q).obj.map k.op).hom (c • gen ζ) = 0`. Rewrite using `[map_nsmul]`. Establish `e2 : Sec.res (F` using `Rt q) k (gen ζ) = gen (ζ.map k.appTop.hom) := (GlobalTheory.T.tateTwist_sections_locally_generated q 1).2.2.2.1 W V k ζ`. Conclude with `(congrArg (c • ·) e2).trans (smul_twGen_eq_zero W _ c hz)`.
-/
theorem kap_mono : Mono (kap q) := by
  refine ((GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections ℤ (kap q)).2.1).2 ?_
  intro U a ha
  refine loc_trans' (loc_mono' ((GlobalTheory.T.tateTwist_sections_locally_generated q 1).1 U a) ?_)
  rintro V g (h0 | ⟨ζ, c, hc⟩)
  · refine loc_calculus.1 V _ (fun W k => ?_)
    show Sec.res (k ≫ g) a = 0
    rw [sec_res_comp]
    have e : Sec.res (F := Rt q) g a = 0 := h0
    rw [e]
    exact map_zero _
  · have e : Sec.res (F := Rt q) g a = c • gen ζ := hc
    have h1 : Sec.map (kap q) (Sec.res g a) = 0 := by rw [sec_map_res, ha]; exact map_zero _
    rw [e, kap_nsmul, kap_gen, ← unitSec_pow] at h1
    refine loc_mono' ((toSheafify_loc_bij_lift ℤ (Scheme.Γ ⋙ unitsF)).2.1 V _ h1) ?_
    intro W k hk
    have h2 : Units.map k.appTop.hom.toMonoidHom (pu ζ ^ c) = 1 := congrArg (fun y => Additive.toMul (ULift.down y)) hk
    have hz : (ζ.map k.appTop.hom).1 ^ c = 1 := by
      have h3 := congrArg Units.val h2
      rw [map_pow] at h3
      exact h3
    show Sec.res (k ≫ g) a = 0
    rw [sec_res_comp, e]
    show ((Rt q).obj.map k.op).hom (c • gen ζ) = 0
    rw [map_nsmul]
    have e2 : Sec.res (F := Rt q) k (gen ζ) = gen (ζ.map k.appTop.hom) := (GlobalTheory.T.tateTwist_sections_locally_generated q 1).2.2.2.1 W V k ζ
    exact (congrArg (c • ·) e2).trans (smul_twGen_eq_zero W _ c hz)

/- English proof (translation)
Use `(GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections ℤ _).2.2.2 0 (fun U a => ?_)` and prove the remaining obligations. Rewrite using `[sec_map_comp, sec_map_smul]`. Use `show ((q : ℕ) : ℤ) • Sec.map (kap q) a = Sec.map 0 a`. Establish `h0 : (q • a : Sec (Rt q) U) = 0` using `sec_q_smul (tw q 1) U a`. Rewrite using `[natCast_zsmul, ← kap_nsmul]`.

Use `show ((kap q).hom.app (op U)).hom (q • a) = ((0 : Rt q ⟶ Gm).hom.app (op U)).hom a`. Rewrite using `[h0, map_zero]`. Both sides reduce to the same expression.
-/
theorem kap_q : kap q ≫ ((q : ℤ) • 𝟙 Gm) = 0 := by
  refine (GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections ℤ _).2.2.2 0 (fun U a => ?_)
  rw [sec_map_comp, sec_map_smul]
  show ((q : ℕ) : ℤ) • Sec.map (kap q) a = Sec.map 0 a
  have h0 : (q • a : Sec (Rt q) U) = 0 := sec_q_smul (tw q 1) U a
  rw [natCast_zsmul, ← kap_nsmul]
  show ((kap q).hom.app (op U)).hom (q • a) = ((0 : Rt q ⟶ Gm).hom.app (op U)).hom a
  rw [h0, map_zero]
  rfl

/- English proof (translation)
Establish `hinj` using `((GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections ℤ (kap q)).1).1 kap_mono`. Use `glue_inj (kap q) hinj U b ?_` and prove the remaining obligations. Use `loc_trans' (loc_mono' ((toSheafify_loc_bij_lift ℤ (Scheme.Γ ⋙ unitsF)).1 U b) ?_)` and prove the remaining obligations. Introduce and unpack `V g ⟨(x : ULift.{1} (Additive (Γ(V, ⊤))ˣ)), hx⟩`. Establish `hx' : unitSec (Additive.toMul x.down) = Sec.res (F` using `Gm) g b := hx`.

Establish `hqx : unitSec ((Additive.toMul x.down) ^ q) = 0`. Rewrite using `[unitSec_pow, hx']`. Establish `: q • Sec.res (F` using `Gm) g b = Sec.res g (Sec.map ((q : ℤ) • 𝟙 Gm) b) := by`. Rewrite using `[sec_map_smul]`. Use `show _ = (Gm.obj.map g.op).hom (((q : ℕ) : ℤ) • b)`.

Rewrite using `[map_zsmul, natCast_zsmul]`. Rewrite using `[this, hb]`. Conclude with `map_zero _`. Use `loc_trans' (loc_mono' ((toSheafify_loc_bij_lift ℤ (Scheme.Γ ⋙ unitsF)).2.1 V _ hqx) ?_)` and prove the remaining obligations. Introduce `W k hk`.

Establish `h2 : (Units.map k.appTop.hom.toMonoidHom (Additive.toMul x.down)) ^ q = 1`. Rewrite using `[← map_pow]`. Conclude with `congrArg (fun y => Additive.toMul (ULift.down y)) hk`. Use `loc_mono' (lift_root W _ (isUnit_res (k ≫ g) hq) h2) ?_` and prove the remaining obligations. Introduce and unpack `W' k' ⟨a, ha⟩`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[ha, ← unitSec_res, ← unitSec_res]`. Use `show _ = Sec.res ((k' ≫ k) ≫ g) b`. Rewrite using `[sec_res_comp, sec_res_comp, ← hx']`.
-/
theorem kap_ker (U : Scheme.{0}) (hq : IsUnit (q : Γ(U, ⊤))) (b : Sec Gm U) (hb : Sec.map ((q : ℤ) • 𝟙 Gm) b = 0) :
    ∃ a, Sec.map (kap q) a = b := by
  have hinj := ((GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections ℤ (kap q)).1).1 kap_mono
  refine glue_inj (kap q) hinj U b ?_
  refine loc_trans' (loc_mono' ((toSheafify_loc_bij_lift ℤ (Scheme.Γ ⋙ unitsF)).1 U b) ?_)
  rintro V g ⟨(x : ULift.{1} (Additive (Γ(V, ⊤))ˣ)), hx⟩
  have hx' : unitSec (Additive.toMul x.down) = Sec.res (F := Gm) g b := hx
  have hqx : unitSec ((Additive.toMul x.down) ^ q) = 0 := by
    rw [unitSec_pow, hx']
    have : q • Sec.res (F := Gm) g b = Sec.res g (Sec.map ((q : ℤ) • 𝟙 Gm) b) := by
      rw [sec_map_smul]
      show _ = (Gm.obj.map g.op).hom (((q : ℕ) : ℤ) • b)
      rw [map_zsmul, natCast_zsmul]
    rw [this, hb]
    exact map_zero _
  refine loc_trans' (loc_mono' ((toSheafify_loc_bij_lift ℤ (Scheme.Γ ⋙ unitsF)).2.1 V _ hqx) ?_)
  intro W k hk
  have h2 : (Units.map k.appTop.hom.toMonoidHom (Additive.toMul x.down)) ^ q = 1 := by
    rw [← map_pow]
    exact congrArg (fun y => Additive.toMul (ULift.down y)) hk
  refine loc_mono' (lift_root W _ (isUnit_res (k ≫ g) hq) h2) ?_
  rintro W' k' ⟨a, ha⟩
  refine ⟨a, ?_⟩
  rw [ha, ← unitSec_res, ← unitSec_res]
  show _ = Sec.res ((k' ≫ k) ≫ g) b
  rw [sec_res_comp, sec_res_comp, ← hx']

/- English proof (translation)
Use `loc_trans' (loc_mono' ((toSheafify_loc_bij_lift ℤ (Scheme.Γ ⋙ unitsF)).1 U b) ?_)` and prove the remaining obligations. Introduce and unpack `V g ⟨(x : ULift.{1} (Additive (Γ(V, ⊤))ˣ)), hx⟩`. Establish `hx' : unitSec (Additive.toMul x.down) = Sec.res (F` using `Gm) g b := hx`. Use `loc_mono' ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.2.2 (isUnit_res g hq) (Additive.toMul x.down)) ?_` and prove the remaining obligations. Introduce and unpack `W k ⟨v, hv⟩`.

Use `⟨unitSec v, ?_⟩` and prove the remaining obligations. Rewrite using `[sec_map_smul]`. Use `show ((q : ℕ) : ℤ) • unitSec v = Sec.res (k ≫ g) b`. Rewrite using `[natCast_zsmul, ← unitSec_pow, hv, ← unitSec_res, sec_res_comp, ← hx']`.
-/
theorem kap_roots (U : Scheme.{0}) (hq : IsUnit (q : Γ(U, ⊤))) (b : Sec Gm U) :
    Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b := by
  refine loc_trans' (loc_mono' ((toSheafify_loc_bij_lift ℤ (Scheme.Γ ⋙ unitsF)).1 U b) ?_)
  rintro V g ⟨(x : ULift.{1} (Additive (Γ(V, ⊤))ˣ)), hx⟩
  have hx' : unitSec (Additive.toMul x.down) = Sec.res (F := Gm) g b := hx
  refine loc_mono' ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.2.2 (isUnit_res g hq) (Additive.toMul x.down)) ?_
  rintro W k ⟨v, hv⟩
  refine ⟨unitSec v, ?_⟩
  rw [sec_map_smul]
  show ((q : ℕ) : ℤ) • unitSec v = Sec.res (k ≫ g) b
  rw [natCast_zsmul, ← unitSec_pow, hv, ← unitSec_res, sec_res_comp, ← hx']

end GlobalTheory.EtC.KummerSeq

open GlobalTheory.EtC.KummerSeq in

/- English proof (translation)
Introduce `q _`. Use `⟨kap q, kap_mono, kap_q, ?_, fun U hq b hb => kap_ker U hq b hb, fun U hq b => kap_roots U hq b⟩` and prove the remaining obligations. Introduce `U ζ u hu`. Establish `: u = pu ζ` using `Units.ext hu`. Substitute `this` using the available equality.

Conclude with `kap_gen U ζ`.
-/
theorem GlobalTheory.EtC.kummer_sequence : ∀ (q : ℕ) [NeZero q], ∃ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm, Mono κ ∧ κ ≫ ((q : ℤ) • 𝟙 Gm) = 0 ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) ∧ (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map κ a = b) ∧ ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b := by
  intro q _
  refine ⟨kap q, kap_mono, kap_q, ?_, fun U hq b hb => kap_ker U hq b hb, fun U hq b => kap_roots U hq b⟩
  intro U ζ u hu
  have : u = pu ζ := Units.ext hu
  subst this
  exact kap_gen U ζ
