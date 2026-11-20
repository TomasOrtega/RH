import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughExtendScalarsZmod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendChainMapAlongQuasiIsoKInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoExtendScalarsTateTwistAugmentationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedExists

def constCx {R : Type} [CommRing R] (F : Shv R) : Cx R where
  X _ := F
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

/- English proof (translation)
Set `ρ : SemiMap (constCx F) (constCx G)` to `{ app := fun U _ => f U nat := fun g _ a => hf _ _ g a comm := fun U s t a => by show Sec.map (0 : G ⟶ G) (f U a) = f U (Sec.map (0 : F ⟶ F) a)`. Simplify using `[Sec.map]`. Conclude with `((f U).map_zero).symm }`. Conclude with `⟨FactorExt.term _ (FactorExt.intCast_surj Q) ρ 0, fun U a => FactorExt.term_sec _ (FactorExt.intCast_surj Q) ρ 0 U a⟩`.
-/
theorem ext_map (Q q : ℕ) (hq : q ∣ Q) (F : Shv (ZMod Q)) (G : Shv (ZMod q))
    (f : ∀ U : Scheme.{0}, Sec F U →+ Sec G U)
    (hf : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (a : Sec F U), Sec.res g (f U a) = f V (Sec.res g a)) :
    ∃ α : (extSh (ZMod.castHom hq (ZMod q))).obj F ⟶ G, ∀ (U : Scheme.{0}) (a : Sec F U),
      Sec.map α (extSh.sec (ZMod.castHom hq (ZMod q)) F U a) = f U a := by
  let ρ : SemiMap (constCx F) (constCx G) :=
    { app := fun U _ => f U
      nat := fun g _ a => hf _ _ g a
      comm := fun U s t a => by
        show Sec.map (0 : G ⟶ G) (f U a) = f U (Sec.map (0 : F ⟶ F) a)
        simp [Sec.map]
        exact ((f U).map_zero).symm }
  exact ⟨FactorExt.term _ (FactorExt.intCast_surj Q) ρ 0,
    fun U a => FactorExt.term_sec _ (FactorExt.intCast_surj Q) ρ 0 U a⟩

def semiOfExt {Q q : ℕ} (hq : q ∣ Q) {I : Cx (ZMod Q)} {K : Cx (ZMod q)}
    (m : extCx (ZMod.castHom hq (ZMod q)) I ⟶ K) : SemiMap I K where
  app U s := ((m.f s).hom.app (op U)).hom.toAddMonoidHom.comp ((extπ (ZMod.castHom hq (ZMod q)) I).app U s)
  nat g s a := by
    have h := (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ((m.f s).hom.naturality g.op))
      ((extπ (ZMod.castHom hq (ZMod q)) I).app _ s a)).symm
    refine h.trans ?_
    exact congrArg (fun x => ((m.f s).hom.app (op _)).hom x) ((extπ (ZMod.castHom hq (ZMod q)) I).nat g s a)
  comm U s t a := by
    have h := congrArg (fun k => ((k.hom.app (op U)).hom ((extπ (ZMod.castHom hq (ZMod q)) I).app U s a))) (m.comm s t)
    refine Eq.trans ?_ (h.trans ?_)
    · rfl
    · exact congrArg (fun x => ((m.f t).hom.app (op U)).hom x) ((extπ (ZMod.castHom hq (ZMod q)) I).comm U s t a)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem semiOfExt_app {Q q : ℕ} (hq : q ∣ Q) {I : Cx (ZMod Q)} {K : Cx (ZMod q)}
    (m : extCx (ZMod.castHom hq (ZMod q)) I ⟶ K) (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U) :
    (semiOfExt hq m).app U s a = Sec.map (m.f s) (extSh.sec (ZMod.castHom hq (ZMod q)) (I.X s) U a) := rfl

def powPrim {Q q : ℕ} [NeZero Q] (hq : q ∣ Q) {A : Type} [CommRing A] (ζ : Prim Q A) : Prim q A :=
  ⟨ζ.1 ^ (Q / q), by
    obtain ⟨ξ, h⟩ := (GlobalTheory.EtC.PrimBasic.prim_basic Q A).2.2.2.2.2 q hq ζ
    rw [← h]
    exact ξ.2⟩

/- English proof (translation)
The claim follows from `Subtype.ext (map_pow φ _ _)`.
-/
theorem powPrim_map {Q q : ℕ} [NeZero Q] (hq : q ∣ Q) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
    (ζ : Prim Q A) : (powPrim hq ζ).map φ = powPrim hq (ζ.map φ) :=
  Subtype.ext (map_pow φ _ _)

/- English proof (translation)
Establish `hq : q • x = 0`. Rewrite using `[← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]`. Establish `: ((q : ℕ) : ULift.{1} (ZMod q)) = 0` using `ULift.ext _ _ (by simp)`. Rewrite using `[this, zero_smul]`. Use `conv_lhs => rw [← Nat.mod_add_div n q]`.

Rewrite using `[add_nsmul, mul_comm q, mul_smul, hq, smul_zero, add_zero]`.
-/
theorem nsmul_mod_of {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (x : M) (n : ℕ) :
    n • x = (n % q) • x := by
  have hq : q • x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
    have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := ULift.ext _ _ (by simp)
    rw [this, zero_smul]
  conv_lhs => rw [← Nat.mod_add_div n q]
  rw [add_nsmul, mul_comm q, mul_smul, hq, smul_zero, add_zero]

/- English proof (translation)
Introduce `Q q _ _ hq i`. Set `M : Shv (ZMod Q)` to `(restr (ZMod.castHom hq (ZMod q))).obj (tw q i)`. Set `e : ∀ U : Scheme.{0}, Prim Q Γ(U, ⊤) → Sec M U` to `fun U ζ => (twGen i (powPrim hq ζ) : Sec (tw q i) U)`. Establish `ts` using `GlobalTheory.T.tateTwist_sections_locally_generated q i`. Establish `he1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim Q Γ(U, ⊤)), Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom)`.

Introduce `V U g ζ`. Use `ts.2.2.2.1 V U g (powPrim hq ζ)` as an intermediate fact. Rewrite `this` using `[powPrim_map]`. Conclude with `this`. Establish `hcast : ∀ u : (ZMod Q)ˣ, ((ZMod.unitsMap hq u : (ZMod q)ˣ) : ZMod q).val = (u : ZMod Q).val % q`.

Introduce `u`. Use `show (ZMod.castHom hq (ZMod q) (u : ZMod Q)).val = _`. Rewrite using `[ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]`. Establish `he2 : ∀ (U : Scheme.{0}) (ζ ξ : Prim Q Γ(U, ⊤)) (a : (ZMod Q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod Q).val → e U ξ = ((a ^ i : (ZMod Q)ˣ) : ZMod Q).val • e U ζ`. Introduce `U ζ ξ a h`.

Establish `hq1 : (ζ.1 ^ (Q / q)) ^ q = 1` using `(GlobalTheory.EtC.PrimBasic.prim_basic q _).1 (powPrim hq ζ)`. Establish `hpw : (powPrim hq ξ).1 = (powPrim hq ζ).1 ^ ((ZMod.unitsMap hq a : (ZMod q)ˣ) : ZMod q).val`. Rewrite using `[hcast]`. Use `show ξ.1 ^ (Q / q) = (ζ.1 ^ (Q / q)) ^ ((a : ZMod Q).val % q)`. Rewrite using `[h, ← pow_mul, mul_comm, pow_mul]`.

Use `conv_lhs => rw [← Nat.mod_add_div (a : ZMod Q).val q]`. Rewrite using `[pow_add, pow_mul, hq1, one_pow, mul_one]`. Establish `h5` using `ts.2.2.2.2.1 U (powPrim hq ζ) (powPrim hq ξ) (ZMod.unitsMap hq a) hpw`. Use `show (twGen i (powPrim hq ξ) : Sec (tw q i) U) = ((a ^ i : (ZMod Q)ˣ) : ZMod Q).val • (twGen i (powPrim hq ζ) : Sec (tw q i) U)`. Establish `hm : (((ZMod.unitsMap hq a) ^ i : (ZMod q)ˣ) : ZMod q).val % q = ((a ^ i : (ZMod Q)ˣ) : ZMod Q).val % q`.

Rewrite using `[show (ZMod.unitsMap hq a) ^ i = ZMod.unitsMap hq (a ^ i) from (map_zpow _ _ _).symm, hcast, Nat.mod_mod]`. Rewrite using `[h5, nsmul_mod_of (q := q) (twGen i (powPrim hq ζ)), hm, ← nsmul_mod_of (q := q)]`. Take `⟨β, hβ, -⟩` from `(GlobalTheory.T.tateTwist_sections_locally_generated Q i).2.2.2.2.2 M e he1 he2`. Use `⟨fun U => ⟨⟨fun a => ((β.hom.app (op U)).hom a : Sec (tw q i) U), (β.hom.app (op U)).hom.map_zero⟩, fun a b => (β.hom.app (op U)).hom.map_add a b⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `V U g a`.

Conclude with `(LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (β.hom.naturality g.op)) a).symm`. Introduce `U ζ ξ h`. Establish `h1` using `hβ U ζ`. Establish `h2 : powPrim hq ζ = ξ` using `Subtype.ext h.symm`. Conclude with `h1.trans (congrArg (twGen i) h2)`.
-/
theorem twRed_sec : ∀ (Q q : ℕ) [NeZero Q] [NeZero q], q ∣ Q → ∀ (i : ℤ), ∃ f : ∀ U : Scheme.{0}, Sec (tw Q i) U →+ Sec (tw q i) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (a : Sec (tw Q i) U), Sec.res g (f U a) = f V (Sec.res g a)) ∧
    ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) → f U (twGen i ζ) = twGen i ξ := by
  intro Q q _ _ hq i
  let M : Shv (ZMod Q) := (restr (ZMod.castHom hq (ZMod q))).obj (tw q i)
  let e : ∀ U : Scheme.{0}, Prim Q Γ(U, ⊤) → Sec M U := fun U ζ => (twGen i (powPrim hq ζ) : Sec (tw q i) U)
  have ts := GlobalTheory.T.tateTwist_sections_locally_generated q i
  have he1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim Q Γ(U, ⊤)), Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom) := by
    intro V U g ζ
    have := ts.2.2.2.1 V U g (powPrim hq ζ)
    rw [powPrim_map] at this
    exact this
  have hcast : ∀ u : (ZMod Q)ˣ, ((ZMod.unitsMap hq u : (ZMod q)ˣ) : ZMod q).val = (u : ZMod Q).val % q := by
    intro u
    show (ZMod.castHom hq (ZMod q) (u : ZMod Q)).val = _
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  have he2 : ∀ (U : Scheme.{0}) (ζ ξ : Prim Q Γ(U, ⊤)) (a : (ZMod Q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod Q).val →
      e U ξ = ((a ^ i : (ZMod Q)ˣ) : ZMod Q).val • e U ζ := by
    intro U ζ ξ a h
    have hq1 : (ζ.1 ^ (Q / q)) ^ q = 1 := (GlobalTheory.EtC.PrimBasic.prim_basic q _).1 (powPrim hq ζ)
    have hpw : (powPrim hq ξ).1 = (powPrim hq ζ).1 ^ ((ZMod.unitsMap hq a : (ZMod q)ˣ) : ZMod q).val := by
      rw [hcast]
      show ξ.1 ^ (Q / q) = (ζ.1 ^ (Q / q)) ^ ((a : ZMod Q).val % q)
      rw [h, ← pow_mul, mul_comm, pow_mul]
      conv_lhs => rw [← Nat.mod_add_div (a : ZMod Q).val q]
      rw [pow_add, pow_mul, hq1, one_pow, mul_one]
    have h5 := ts.2.2.2.2.1 U (powPrim hq ζ) (powPrim hq ξ) (ZMod.unitsMap hq a) hpw
    show (twGen i (powPrim hq ξ) : Sec (tw q i) U) =
      ((a ^ i : (ZMod Q)ˣ) : ZMod Q).val • (twGen i (powPrim hq ζ) : Sec (tw q i) U)
    have hm : (((ZMod.unitsMap hq a) ^ i : (ZMod q)ˣ) : ZMod q).val % q = ((a ^ i : (ZMod Q)ˣ) : ZMod Q).val % q := by
      rw [show (ZMod.unitsMap hq a) ^ i = ZMod.unitsMap hq (a ^ i) from (map_zpow _ _ _).symm, hcast, Nat.mod_mod]
    rw [h5, nsmul_mod_of (q := q) (twGen i (powPrim hq ζ)), hm, ← nsmul_mod_of (q := q)]
  obtain ⟨β, hβ, -⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated Q i).2.2.2.2.2 M e he1 he2
  refine ⟨fun U => ⟨⟨fun a => ((β.hom.app (op U)).hom a : Sec (tw q i) U), (β.hom.app (op U)).hom.map_zero⟩,
    fun a b => (β.hom.app (op U)).hom.map_add a b⟩, ?_, ?_⟩
  · intro V U g a
    exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (β.hom.naturality g.op)) a).symm
  · intro U ζ ξ h
    have h1 := hβ U ζ
    have h2 : powPrim hq ζ = ξ := Subtype.ext h.symm
    exact h1.trans (congrArg (twGen i) h2)

/- English proof (translation)
Take `⟨f, hf, hfg⟩` from `twRed_sec Q q hq i`. Take `⟨α, hα⟩` from `ext_map Q q hq (tw Q i) (tw q i) f hf`. Take `⟨hKI, -, hGE, -, hι, -⟩` from `GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q i)`. Establish `hQ` using `GlobalTheory.T.quasiIso_extendScalars_tateTwist_augmentation Q q hq i`. Take `⟨m, hm⟩` from `(GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective (ZMod q) ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i)) (extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i))) (res _ (tw q i)) (extAug (ZMod.castHom hq (ZMod q)) (tw Q i))).1 ((CochainComplex.singleFunctor (Shv (ZMod q)) …`.

Use `⟨semiOfExt hq m, fun U ζ ξ h => ?_⟩` and prove the remaining obligations. Establish `hv : (extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ m).f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫ (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ m.f 0`. Establish `hs` using `HomologicalComplex.singleMapHomologicalComplex_inv_app_self (extSh (ZMod.castHom hq (ZMod q))) (ComplexShape.up ℤ) 0 (tw Q i)`. Express the relevant statement in the definitionally equal form `(((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q))) (ComplexShape.up ℤ) 0).inv.app (tw Q i)).f 0 ≫ (extSh (ZMod.castHom hq (ZMod q))).map ((resAug (tw Q i)).f 0)) ≫ m.f 0 = _`. Establish `hs' : ((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q))) (ComplexShape.up ℤ) 0).inv.app (tw Q i)).f 0 ≫ (extSh (ZMod.castHom hq (ZMod q))).map ((resAug (tw Q i)).f 0) = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom …`.

Rewrite using `[hs]`. Conclude with `(Category.assoc _ _ _).trans (congrArg _ (Functor.map_comp _ _ _).symm)`. Conclude with `(congrArg (· ≫ m.f 0) hs').trans (Category.assoc _ _ _)`. Establish `hw : ((CochainComplex.singleFunctor (Shv (ZMod q)) 0).map α ≫ resAug (tw q i)).f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫ α ≫ resι _ (tw q i)`. Rewrite using `[HomologicalComplex.comp_f, ← hι]`.

Express the relevant statement in the definitionally equal form `((HomologicalComplex.single (Shv (ZMod q)) (ComplexShape.up ℤ) 0).map α).f 0 ≫ _ = _`. Rewrite using `[HomologicalComplex.single_map_f_self]`. Use `(Category.assoc _ _ _).trans ?_` and prove the remaining obligations. Use `congrArg (_ ≫ ·) ?_` and prove the remaining obligations. Conclude with `Category.assoc _ _ _`.

Establish `key : (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ m.f 0 = α ≫ resι _ (tw q i)`. Establish `e : (extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ m).f 0 = ((CochainComplex.singleFunctor (Shv (ZMod q)) 0).map α ≫ resAug (tw q i)).f 0` using `by rw [hm]`. Rewrite `e` using `[hv, hw]`. Conclude with `(cancel_epi _).1 e`. Rewrite using `[semiOfExt_app]`.

Express the relevant statement in the definitionally equal form `Sec.map (m.f 0) (extSh.sec _ _ U (Sec.map (resι _ (tw Q i)) (twGen i ζ))) = Sec.map (resι _ (tw q i)) (twGen i ξ)`. Rewrite using `[← extSh.sec_map, ← hfg U ζ ξ h, ← hα]`. Establish `e2` using `congrArg (fun k => Sec.map k (extSh.sec (ZMod.castHom hq (ZMod q)) (tw Q i) U (twGen i ζ))) key`. Conclude with `e2`.
-/
theorem redMap_exists (Q q : ℕ) [NeZero Q] [NeZero q] (hq : q ∣ Q) (i : ℤ) :
    ∃ ρ : SemiMap (res _ (tw Q i)) (res _ (tw q i)), ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)),
      ξ.1 = ζ.1 ^ (Q / q) → ρ.app U 0 (resGen i ζ) = resGen i ξ := by
  obtain ⟨f, hf, hfg⟩ := twRed_sec Q q hq i
  obtain ⟨α, hα⟩ := ext_map Q q hq (tw Q i) (tw q i) f hf
  obtain ⟨hKI, -, hGE, -, hι, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q i)
  have hQ := GlobalTheory.T.quasiIso_extendScalars_tateTwist_augmentation Q q hq i
  obtain ⟨m, hm⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective (ZMod q) ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))
    (extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i))) (res _ (tw q i))
    (extAug (ZMod.castHom hq (ZMod q)) (tw Q i))).1
    ((CochainComplex.singleFunctor (Shv (ZMod q)) 0).map α ≫ resAug (tw q i))
  refine ⟨semiOfExt hq m, fun U ζ ξ h => ?_⟩
  have hv : (extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ m).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
        (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ m.f 0 := by
    have hs := HomologicalComplex.singleMapHomologicalComplex_inv_app_self (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0 (tw Q i)
    change (((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0).inv.app (tw Q i)).f 0 ≫ (extSh (ZMod.castHom hq (ZMod q))).map ((resAug (tw Q i)).f 0)) ≫
        m.f 0 = _
    have hs' : ((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
        (ComplexShape.up ℤ) 0).inv.app (tw Q i)).f 0 ≫ (extSh (ZMod.castHom hq (ZMod q))).map ((resAug (tw Q i)).f 0) =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
          (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) := by
      rw [hs]
      exact (Category.assoc _ _ _).trans (congrArg _ (Functor.map_comp _ _ _).symm)
    exact (congrArg (· ≫ m.f 0) hs').trans (Category.assoc _ _ _)
  have hw : ((CochainComplex.singleFunctor (Shv (ZMod q)) 0).map α ≫ resAug (tw q i)).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
        α ≫ resι _ (tw q i) := by
    rw [HomologicalComplex.comp_f, ← hι]
    change ((HomologicalComplex.single (Shv (ZMod q)) (ComplexShape.up ℤ) 0).map α).f 0 ≫ _ = _
    rw [HomologicalComplex.single_map_f_self]
    refine (Category.assoc _ _ _).trans ?_
    refine congrArg (_ ≫ ·) ?_
    exact Category.assoc _ _ _
  have key : (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ m.f 0 = α ≫ resι _ (tw q i) := by
    have e : (extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ m).f 0 =
        ((CochainComplex.singleFunctor (Shv (ZMod q)) 0).map α ≫ resAug (tw q i)).f 0 := by rw [hm]
    rw [hv, hw] at e
    exact (cancel_epi _).1 e
  rw [semiOfExt_app]
  change Sec.map (m.f 0) (extSh.sec _ _ U (Sec.map (resι _ (tw Q i)) (twGen i ζ))) = Sec.map (resι _ (tw q i)) (twGen i ξ)
  rw [← extSh.sec_map, ← hfg U ζ ξ h, ← hα]
  have e2 := congrArg (fun k => Sec.map k (extSh.sec (ZMod.castHom hq (ZMod q)) (tw Q i) U (twGen i ζ))) key
  exact e2

/- English proof (translation)
Introduce `Q q _ _ hq i U ζ ξ h`. Conclude with `pick_spec (redMap_exists Q q hq i) U ζ ξ h`.
-/
theorem red_exists : ∀ (Q q : ℕ) [NeZero Q] [NeZero q], q ∣ Q → ∀ (i : ℤ) (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤))
    (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) → (redMap Q q i).app U 0 (resGen i ζ) = resGen i ξ := by
  intro Q q _ _ hq i U ζ ξ h
  exact pick_spec (redMap_exists Q q hq i) U ζ ξ h

end GlobalTheory.EtC.RedExists
