import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKummerTorsorSplittingKummerTorsorSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerClassOfUnitCocycleNaturalAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSequenceEtaleTateTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsResolutionMapAugmentationSpecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsUnitEqMultiplicativeGroupSection
import Development.AutomorphicArithmetic.CommutativeAlgebra.KummerMapAddOfUnitSecAdd
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsInjectiveH1GmToPic
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace UpperTheory.Kum1

private abbrev RT (q : ℕ) [NeZero q] : Shv ℤ := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)

private abbrev II (q : ℕ) [NeZero q] : Cx (ZMod q) := res _ (tw q 1)

private abbrev JJ : Cx ℤ := res ℤ Gm

/- English proof (translation)
The claim follows from `(congrArg (fun f => ModuleCat.Hom.hom f x) (φ.hom.naturality g.op)).symm`.
-/
private theorem sec_nat {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (congrArg (fun f => ModuleCat.Hom.hom f x) (φ.hom.naturality g.op)).symm

/- English proof (translation)
Simplify using `[Sec.res]`.
-/
private theorem sec_res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.res (𝟙 U) x = x := by
  simp [Sec.res]

/- English proof (translation)
Simplify using `[Sec.res]`.
-/
private theorem sec_res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (x : Sec F U) : Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res]

/- English proof (translation)
The claim follows from `map_add (φ.hom.app (op U)).hom a b`.
-/
private theorem sm_add {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add (φ.hom.app (op U)).hom a b

/- English proof (translation)
The claim follows from `map_sub (φ.hom.app (op U)).hom a b`.
-/
private theorem sm_sub {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a - b) = Sec.map φ a - Sec.map φ b := map_sub (φ.hom.app (op U)).hom a b

/- English proof (translation)
The claim follows from `map_zero (φ.hom.app (op U)).hom`.
-/
private theorem sm_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := map_zero (φ.hom.app (op U)).hom

/- English proof (translation)
The claim follows from `map_nsmul (φ.hom.app (op U)).hom n a`.
-/
private theorem sm_nsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (n : ℕ) (a : Sec F U) :
    Sec.map φ (n • a) = n • Sec.map φ a := map_nsmul (φ.hom.app (op U)).hom n a

/- English proof (translation)
The claim follows from `map_add (F.obj.map g.op).hom a b`.
-/
private theorem sr_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a + b) = Sec.res g a + Sec.res g b := map_add (F.obj.map g.op).hom a b

/- English proof (translation)
The claim follows from `map_nsmul (F.obj.map g.op).hom n a`.
-/
private theorem sr_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (a : Sec F U) :
    Sec.res g (n • a) = n • Sec.res g a := map_nsmul (F.obj.map g.op).hom n a

/- English proof (translation)
The claim follows from `(congrArg (fun f => ModuleCat.Hom.hom f (ULift.up (Additive.ofMul u))) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality g.op)).symm`.
-/
private theorem unitSec_res {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res g (unitSec u) = unitSec (Units.map g.appTop.hom.toMonoidHom u) :=
  (congrArg (fun f => ModuleCat.Hom.hom f (ULift.up (Additive.ofMul u)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality g.op)).symm

/- English proof (translation)
The claim follows from `map_add ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom (ULift.up (Additive.ofMul u)) (ULift.up (Additive.ofMul v))`.
-/
private theorem unitSec_mul {U : Scheme.{0}} (u v : (Γ(U, ⊤))ˣ) : unitSec (u * v) = unitSec u + unitSec v :=
  map_add ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom
    (ULift.up (Additive.ofMul u)) (ULift.up (Additive.ofMul v))

/- English proof (translation)
Establish `h` using `unitSec_mul (1 : (Γ(U, ⊤))ˣ) 1`. Rewrite `h` using `[mul_one]`. Conclude with `left_eq_add.mp h`.
-/
private theorem unitSec_one {U : Scheme.{0}} : unitSec (1 : (Γ(U, ⊤))ˣ) = 0 := by
  have h := unitSec_mul (1 : (Γ(U, ⊤))ˣ) 1
  rw [mul_one] at h
  exact left_eq_add.mp h

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using unitSec_one`. Consider the case `succ n ih => rw [pow_succ, unitSec_mul, ih, succ_nsmul]`.
-/
private theorem unitSec_pow {U : Scheme.{0}} (v : (Γ(U, ⊤))ˣ) (n : ℕ) : unitSec (v ^ n) = n • unitSec v := by
  induction n with
  | zero => simpa using unitSec_one
  | succ n ih => rw [pow_succ, unitSec_mul, ih, succ_nsmul]

/- English proof (translation)
Establish `h0 : unitSec (u * u'⁻¹) = 0`. Establish `h1 : unitSec (u'⁻¹) + unitSec u' = 0`. Rewrite using `[← unitSec_mul, inv_mul_cancel, unitSec_one]`. Rewrite using `[unitSec_mul, h, add_comm]`. Conclude with `h1`.

Establish `h2` using `(GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift ℤ (Scheme.Γ ⋙ unitsF)).2.1 U (ULift.up (Additive.ofMul (u * u'⁻¹))) h0`. Use `GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U _ _ h2 ?_` and prove the remaining obligations. Introduce `V g hg`. Establish `h3 : Units.map g.appTop.hom.toMonoidHom (u * u'⁻¹) = 1` using `Additive.ofMul.injective (congrArg ULift.down hg)`. Rewrite `h3` using `[map_mul, map_inv]`.

Conclude with `mul_inv_eq_one.mp h3`.
-/
private theorem unitSec_loc {U : Scheme.{0}} (u u' : (Γ(U, ⊤))ˣ) (h : unitSec u = unitSec u') :
    Loc U fun _ g => Units.map g.appTop.hom.toMonoidHom u = Units.map g.appTop.hom.toMonoidHom u' := by
  have h0 : unitSec (u * u'⁻¹) = 0 := by
    have h1 : unitSec (u'⁻¹) + unitSec u' = 0 := by
      rw [← unitSec_mul, inv_mul_cancel, unitSec_one]
    rw [unitSec_mul, h, add_comm]
    exact h1
  have h2 := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift ℤ (Scheme.Γ ⋙ unitsF)).2.1 U (ULift.up (Additive.ofMul (u * u'⁻¹))) h0
  refine GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U _ _ h2 ?_
  intro V g hg
  have h3 : Units.map g.appTop.hom.toMonoidHom (u * u'⁻¹) = 1 :=
    Additive.ofMul.injective (congrArg ULift.down hg)
  rw [map_mul, map_inv] at h3
  exact mul_inv_eq_one.mp h3

/- English proof (translation)
Rewrite using `[← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) q y]`. Establish `: ((q : ℕ) : ULift.{1} (ZMod q)) = 0`. Apply `ULift.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Rewrite using `[this, zero_smul]`.
-/
private theorem q_smul_zero (q : ℕ) [NeZero q] {s : ℤ} {U : Scheme.{0}} (y : Sec ((II q).X s) U) : q • y = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) q y]
  have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    simp
  rw [this, zero_smul]

/- English proof (translation)
Use `⟨fun U s => (((resMap ℤ κ).f s).hom.app (op U)).hom.toAddMonoidHom.comp ((restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U s), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `V U g s a`. Express the relevant statement in the definitionally equal form `Sec.res g (Sec.map ((resMap ℤ κ).f s) _) = Sec.map ((resMap ℤ κ).f s) _`. Rewrite using `[sec_nat, SemiMap.nat]`. Introduce `U s t a`.

Express the relevant statement in the definitionally equal form `Sec.map _ (Sec.map ((resMap ℤ κ).f s) _) = Sec.map ((resMap ℤ κ).f t) _`. Rewrite using `[← SemiMap.comm]`. Conclude with `congrArg (fun f => Sec.map f ((restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U s a)) ((resMap ℤ κ).comm s t)`. Introduce `U a`. Express the relevant statement in the definitionally equal form `Sec.map ((resMap ℤ κ).f 0) _ = _`.

Rewrite using `[GlobalTheory.T.restrictScalarsResolutionMap_augmentation_spec]`. Take `⟨-, -, -, -, -, -, -, h⟩` from `GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ (RT q)`. Conclude with `congrArg (fun f => Sec.map f (show Sec (RT q) U from a)) (h Gm κ).2`.
-/
private theorem rho_ex (q : ℕ) [NeZero q] (κ : RT q ⟶ Gm) :
    ∃ ρ : ∀ (U : Scheme.{0}) (s : ℤ), Sec ((II q).X s) U →+ Sec (JJ.X s) U,
      (∀ {V U : Scheme.{0}} (g : V ⟶ U) (s : ℤ) (a : Sec ((II q).X s) U),
        Sec.res g (ρ U s a) = ρ V s (Sec.res g a)) ∧
      (∀ (U : Scheme.{0}) (s t : ℤ) (a : Sec ((II q).X s) U),
        Sec.map (JJ.d s t) (ρ U s a) = ρ U t (Sec.map ((II q).d s t) a)) ∧
      ∀ (U : Scheme.{0}) (a : Sec (tw q 1) U), ρ U 0 (Sec.map (resι _ (tw q 1)) a) =
        Sec.map (resι ℤ Gm) (Sec.map κ (show Sec (RT q) U from a)) := by
  refine ⟨fun U s => (((resMap ℤ κ).f s).hom.app (op U)).hom.toAddMonoidHom.comp
    ((restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U s), ?_, ?_, ?_⟩
  · intro V U g s a
    change Sec.res g (Sec.map ((resMap ℤ κ).f s) _) = Sec.map ((resMap ℤ κ).f s) _
    rw [sec_nat, SemiMap.nat]
  · intro U s t a
    change Sec.map _ (Sec.map ((resMap ℤ κ).f s) _) = Sec.map ((resMap ℤ κ).f t) _
    rw [← SemiMap.comm]
    exact congrArg (fun f => Sec.map f ((restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U s a))
      ((resMap ℤ κ).comm s t)
  · intro U a
    change Sec.map ((resMap ℤ κ).f 0) _ = _
    rw [GlobalTheory.T.restrictScalarsResolutionMap_augmentation_spec]
    obtain ⟨-, -, -, -, -, -, -, h⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ (RT q)
    exact congrArg (fun f => Sec.map f (show Sec (RT q) U from a)) (h Gm κ).2

/- English proof (translation)
Take `⟨φ, hφ⟩` from `UpperTheory.exists_injective_h1_gm_to_pic A`. Apply `hφ` to reduce the goal to its premises. Rewrite using `[map_zero]`. Establish `h1 : q • φ c = 0` using `by rw [← map_nsmul, h, map_zero]`. Establish `h2` using `hpic (Additive.toMul (φ c)) (by`.

Rewrite using `[← toMul_nsmul, h1]`. Use the proof step `rfl)`. Conclude with `congrArg Additive.ofMul h2`.
-/
private theorem tors_zero (q : ℕ) (A : Type) [CommRing A] (hpic : ∀ c : CommRing.Pic A, c ^ q = 1 → c = 1)
    (c : H ℤ (sp A) Gm 1) (h : q • c = 0) : c = 0 := by
  obtain ⟨φ, hφ⟩ := UpperTheory.exists_injective_h1_gm_to_pic A
  apply hφ
  rw [map_zero]
  have h1 : q • φ c = 0 := by rw [← map_nsmul, h, map_zero]
  have h2 := hpic (Additive.toMul (φ c)) (by
    rw [← toMul_nsmul, h1]; rfl)
  exact congrArg Additive.ofMul h2

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Rewrite using `[zero_smul, zero_smul]`. Use `symm`. Rewrite using `[CohomologyClass.mk_eq_zero_iff]`.

Conclude with `zero_mem _`. Consider the case `succ m ih => rw [succ_nsmul, succ_nsmul, ih, CohomologyClass.mk_add]`.
-/
private theorem mk_nsmul {K L : Cx ℤ} {n : ℤ} (α : Cocycle K L n) (m : ℕ) :
    m • CohomologyClass.mk α = CohomologyClass.mk (m • α) := by
  induction m with
  | zero =>
    rw [zero_smul, zero_smul]
    symm
    rw [CohomologyClass.mk_eq_zero_iff]
    exact zero_mem _
  | succ m ih => rw [succ_nsmul, succ_nsmul, ih, CohomologyClass.mk_add]

/- English proof (translation)
Establish `h` using `(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := I) (n := 1)).2.1 α 0 1 (by simp) V X g (𝟙 X)`. Rewrite using `[h]`. Establish `h2 : (Sx.res g (show Sx (sch.obj X) 0 X from 𝟙 X)) = g`. Express the relevant statement in the definitionally equal form `g ≫ 𝟙 X = g`. Simplify using the standard rewrite rules.

Rewrite using `[h2]`.
-/
private theorem ev_id_res {R : Type} [CommRing R] {I : Cx R} {X V : Scheme.{0}} (g : V ⟶ X)
    (α : Cochain ((chains R).obj (sch.obj X)) I 1) :
    Sec.res g (ev α 0 1 (by simp) X (𝟙 X)) = ev α 0 1 (by simp) V g := by
  have h := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := I) (n := 1)).2.1 α 0 1 (by simp) V X g (𝟙 X)
  rw [h]
  have h2 : (Sx.res g (show Sx (sch.obj X) 0 X from 𝟙 X)) = g := by
    change g ≫ 𝟙 X = g
    simp
  rw [h2]

private def Good (q : ℕ) [NeZero q] {X : Scheme.{0}}
    (ρ : ∀ (U : Scheme.{0}) (s : ℤ), Sec ((II q).X s) U →+ Sec (JJ.X s) U)
    (z : Sec ((II q).X 1) X) (w : Sec (JJ.X 0) X) (V : Scheme.{0}) (g : V ⟶ X)
    (Y : Sec ((II q).X 0) V) : Prop :=
  ∃ (y : Sec ((II q).X 0) V) (v : (Γ(V, ⊤))ˣ), Sec.map ((II q).d 0 1) y = Sec.res g z ∧
    ρ V 0 y + Sec.map (resι ℤ Gm) (unitSec v) = Sec.res g w ∧ Y = y + kumT q V v

section
variable {q : ℕ} [NeZero q] {X : Scheme.{0}}
  {ρ : ∀ (U : Scheme.{0}) (s : ℤ), Sec ((II q).X s) U →+ Sec (JJ.X s) U}
  (ρnat : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (s : ℤ) (a : Sec ((II q).X s) U),
    Sec.res g (ρ U s a) = ρ V s (Sec.res g a))
  (ρd : ∀ (U : Scheme.{0}) (s t : ℤ) (a : Sec ((II q).X s) U),
    Sec.map (JJ.d s t) (ρ U s a) = ρ U t (Sec.map ((II q).d s t) a))
  {z : Sec ((II q).X 1) X} {w : Sec (JJ.X 0) X}

include ρnat ρd in
/- English proof (translation)
Establish `h0` using `(GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness (ZMod q) (tw q 1) X).2.2.1 0 1 2 (by norm_num) (by norm_num) z (by norm_num) hz`. Use `GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 X _ _ h0 ?_` and prove the remaining obligations. Introduce and unpack `V g ⟨y, hy⟩`. Establish `he : Sec.map (JJ.d 0 1) (Sec.res g w - ρ V 0 y) = 0`. Rewrite using `[sm_sub, ← sec_nat, hw, ρd, hy, ρnat, sub_self]`.

Take `⟨a, ha⟩` from `((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ Gm V).1 _).1 he`. Take `⟨v, rfl⟩` from `UpperTheory.exists_unit_eq_multiplicativeGroup_section V a`. Conclude with `⟨_, y, v, hy, by rw [ha]; abel, rfl⟩`.
-/
private theorem good_ex (hz : Sec.map ((II q).d 1 2) z = 0) (hw : Sec.map (JJ.d 0 1) w = ρ X 1 z) :
    Loc X fun V g => ∃ Y, Good q ρ z w V g Y := by
  have h0 := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness (ZMod q) (tw q 1) X).2.2.1 0 1 2 (by norm_num) (by norm_num) z (by norm_num) hz
  refine GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 X _ _ h0 ?_
  rintro V g ⟨y, hy⟩
  have he : Sec.map (JJ.d 0 1) (Sec.res g w - ρ V 0 y) = 0 := by
    rw [sm_sub, ← sec_nat, hw, ρd, hy, ρnat, sub_self]
  obtain ⟨a, ha⟩ := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ Gm V).1 _).1 he
  obtain ⟨v, rfl⟩ := UpperTheory.exists_unit_eq_multiplicativeGroup_section V a
  exact ⟨_, y, v, hy, by rw [ha]; abel, rfl⟩

include ρnat in
/- English proof (translation)
Take `⟨y, v, h1, h2, rfl⟩` from `h`. Establish `hqV : IsUnit (q : Γ(V, ⊤))` using `by simpa using hq.map g.appTop.hom`. Use `⟨Sec.res k y, Units.map k.appTop.hom.toMonoidHom v, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← sec_nat, h1, sec_res_comp]`. Rewrite using `[← ρnat, ← unitSec_res, ← sec_nat, ← sr_add, h2, sec_res_comp]`.

Rewrite using `[sr_add, (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 W V k v hqV]`.
-/
private theorem good_res (hq : IsUnit (q : Γ(X, ⊤))) {V W : Scheme.{0}} (g : V ⟶ X) (k : W ⟶ V)
    {Y : Sec ((II q).X 0) V} (h : Good q ρ z w V g Y) : Good q ρ z w W (k ≫ g) (Sec.res k Y) := by
  obtain ⟨y, v, h1, h2, rfl⟩ := h
  have hqV : IsUnit (q : Γ(V, ⊤)) := by simpa using hq.map g.appTop.hom
  refine ⟨Sec.res k y, Units.map k.appTop.hom.toMonoidHom v, ?_, ?_, ?_⟩
  · rw [← sec_nat, h1, sec_res_comp]
  · rw [← ρnat, ← unitSec_res, ← sec_nat, ← sr_add, h2, sec_res_comp]
  · rw [sr_add, (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 W V k v hqV]

/- English proof (translation)
Take `⟨y, v, h1, h2, rfl⟩` from `h`. Take `⟨y', v', h1', h2', rfl⟩` from `h'`. Establish `hqV : IsUnit (q : Γ(V, ⊤))` using `by simpa using hq.map g.appTop.hom`. Establish `hd : Sec.map ((II q).d 0 1) (y - y') = 0` using `by rw [sm_sub, h1, h1', sub_self]`. Take `⟨s, hs⟩` from `((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness (ZMod q) (tw q 1) V).1 _).1 hd`.

Establish `hρ : Sec.map (resι ℤ Gm) (Sec.map κ (show Sec (RT q) V from s) + unitSec v) = Sec.map (resι ℤ Gm) (unitSec v')`. Establish `h5` using `ρι V s`. Rewrite `h5` using `[hs, map_sub]`. Rewrite using `[sm_add, ← h5, sub_add_eq_add_sub, h2.trans h2'.symm, add_sub_cancel_left]`. Establish `hk` using `(GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ Gm V).2.1 hρ`.

Use `UpperTheory.kummerMap_add_of_unitSec_add q κ hκ V hqV v v' s hk` as an intermediate fact. Rewrite using `[this, hs]`. Normalize the expressions using the abelian group laws.
-/
private theorem good_unique (κ : RT q ⟶ Gm)
    (hκ : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 →
      Sec.map κ (show Sec (RT q) U from twGen 1 ζ) = unitSec u)
    (ρι : ∀ (U : Scheme.{0}) (a : Sec (tw q 1) U), ρ U 0 (Sec.map (resι _ (tw q 1)) a) =
        Sec.map (resι ℤ Gm) (Sec.map κ (show Sec (RT q) U from a)))
    (hq : IsUnit (q : Γ(X, ⊤))) {V : Scheme.{0}} (g : V ⟶ X)
    {Y Y' : Sec ((II q).X 0) V} (h : Good q ρ z w V g Y) (h' : Good q ρ z w V g Y') : Y = Y' := by
  obtain ⟨y, v, h1, h2, rfl⟩ := h
  obtain ⟨y', v', h1', h2', rfl⟩ := h'
  have hqV : IsUnit (q : Γ(V, ⊤)) := by simpa using hq.map g.appTop.hom
  have hd : Sec.map ((II q).d 0 1) (y - y') = 0 := by rw [sm_sub, h1, h1', sub_self]
  obtain ⟨s, hs⟩ := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness (ZMod q) (tw q 1) V).1 _).1 hd
  have hρ : Sec.map (resι ℤ Gm) (Sec.map κ (show Sec (RT q) V from s) + unitSec v) =
      Sec.map (resι ℤ Gm) (unitSec v') := by
    have h5 := ρι V s
    rw [hs, map_sub] at h5
    rw [sm_add, ← h5, sub_add_eq_add_sub, h2.trans h2'.symm, add_sub_cancel_left]
  have hk := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ Gm V).2.1 hρ
  have := UpperTheory.kummerMap_add_of_unitSec_add q κ hκ V hqV v v' s hk
  rw [this, hs]
  abel

end

section
variable {q : ℕ} [NeZero q] {X : Scheme.{0}}
  {ρ : ∀ (U : Scheme.{0}) (s : ℤ), Sec ((II q).X s) U →+ Sec (JJ.X s) U}
  {z : Sec ((II q).X 1) X} {w : Sec (JJ.X 0) X}

/- English proof (translation)
Take `⟨S, hS, hP⟩` from `good_ex ρnat ρd hz hw`. Use `choose s hs using hP`. Take `⟨Y, hY⟩` from `(GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) ((II q).X 0) X).2 S hS s (fun V W g k hg => good_unique κ hκ ρι hq (k ≫ g) (good_res ρnat hq g k (hs V g hg)) (hs W (k ≫ g) _))`. Use `⟨Y, ?_⟩` and prove the remaining obligations. Apply `(GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) ((II q).X 1) X).1` to reduce the goal to its premises.

Use `GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.1 X _ ⟨S, hS, ?_⟩` and prove the remaining obligations. Introduce `V g hg`. Take `⟨y, v, h1, h2, h3⟩` from `hs V g hg`. Establish `hq1 : unitSec (v ^ q) = unitSec (Units.map g.appTop.hom.toMonoidHom u)`. Apply `(GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ Gm V).2.1` to reduce the goal to its premises.

Rewrite using `[← unitSec_res, ← sec_nat, hu, unitSec_pow, sm_nsmul, sr_nsmul, ← h2, smul_add, ← map_nsmul (ρ V 0), q_smul_zero, map_zero, zero_add]`. Use `GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 V _ _ (unitSec_loc _ _ hq1) ?_` and prove the remaining obligations. Introduce `W k hk`. Establish `hqV : IsUnit (q : Γ(V, ⊤))` using `by simpa using hq.map g.appTop.hom`. Establish `hc : Units.map (k ≫ g).appTop.hom.toMonoidHom u = Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u)`.

Establish `e : (k ≫ g).appTop = g.appTop ≫ k.appTop` using `Scheme.Hom.comp_appTop _ _`. Use `ext`. Rewrite using `[e]`. Both sides reduce to the same expression. Establish `hv : (Units.map k.appTop.hom.toMonoidHom v) ^ q = Units.map (k ≫ g).appTop.hom.toMonoidHom u`.

Rewrite using `[hc, ← hk, map_pow]`. Establish `hY' : Sec.res (k ≫ g) Y = Sec.res k y + kumT q W (Units.map k.appTop.hom.toMonoidHom v)`. Rewrite using `[sec_res_comp, hY V g hg, h3, sr_add, (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 W V k v hqV]`. Rewrite using `[sec_nat, hY', sm_add, ← hzu W (k ≫ g) _ hv, sr_add, ← sec_nat, h1, sec_res_comp, sec_res_comp]`.
-/
private theorem glue (κ : RT q ⟶ Gm)
    (hκ : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 →
      Sec.map κ (show Sec (RT q) U from twGen 1 ζ) = unitSec u)
    (ρnat : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (s : ℤ) (a : Sec ((II q).X s) U),
      Sec.res g (ρ U s a) = ρ V s (Sec.res g a))
    (ρd : ∀ (U : Scheme.{0}) (s t : ℤ) (a : Sec ((II q).X s) U),
      Sec.map (JJ.d s t) (ρ U s a) = ρ U t (Sec.map ((II q).d s t) a))
    (ρι : ∀ (U : Scheme.{0}) (a : Sec (tw q 1) U), ρ U 0 (Sec.map (resι _ (tw q 1)) a) =
        Sec.map (resι ℤ Gm) (Sec.map κ (show Sec (RT q) U from a)))
    (hq : IsUnit (q : Γ(X, ⊤))) (hz : Sec.map ((II q).d 1 2) z = 0)
    (hw : Sec.map (JJ.d 0 1) w = ρ X 1 z) (u : (Γ(X, ⊤))ˣ)
    (hu : Sec.map (resι ℤ Gm) (unitSec u) = q • w) (zu : Sec ((II q).X 1) X)
    (hzu : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
      Sec.res x zu = Sec.map ((II q).d 0 1) (kumT q U v)) :
    ∃ Y : Sec ((II q).X 0) X, Sec.map ((II q).d 0 1) Y = z + zu := by
  obtain ⟨S, hS, hP⟩ := good_ex ρnat ρd hz hw
  choose s hs using hP
  obtain ⟨Y, hY⟩ := (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) ((II q).X 0) X).2 S hS s (fun V W g k hg =>
    good_unique κ hκ ρι hq (k ≫ g) (good_res ρnat hq g k (hs V g hg)) (hs W (k ≫ g) _))
  refine ⟨Y, ?_⟩
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) ((II q).X 1) X).1
  refine GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.1 X _ ⟨S, hS, ?_⟩
  intro V g hg
  obtain ⟨y, v, h1, h2, h3⟩ := hs V g hg
  have hq1 : unitSec (v ^ q) = unitSec (Units.map g.appTop.hom.toMonoidHom u) := by
    apply (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ Gm V).2.1
    rw [← unitSec_res, ← sec_nat, hu, unitSec_pow, sm_nsmul, sr_nsmul, ← h2, smul_add, ← map_nsmul (ρ V 0),
      q_smul_zero, map_zero, zero_add]
  refine GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 V _ _ (unitSec_loc _ _ hq1) ?_
  intro W k hk
  have hqV : IsUnit (q : Γ(V, ⊤)) := by simpa using hq.map g.appTop.hom
  have hc : Units.map (k ≫ g).appTop.hom.toMonoidHom u =
      Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) := by
    have e : (k ≫ g).appTop = g.appTop ≫ k.appTop := Scheme.Hom.comp_appTop _ _
    ext
    rw [e]
    rfl
  have hv : (Units.map k.appTop.hom.toMonoidHom v) ^ q = Units.map (k ≫ g).appTop.hom.toMonoidHom u := by
    rw [hc, ← hk, map_pow]
  have hY' : Sec.res (k ≫ g) Y = Sec.res k y + kumT q W (Units.map k.appTop.hom.toMonoidHom v) := by
    rw [sec_res_comp, hY V g hg, h3, sr_add, (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 W V k v hqV]
  rw [sec_nat, hY', sm_add, ← hzu W (k ≫ g) _ hv, sr_add, ← sec_nat, h1, sec_res_comp, sec_res_comp]

end

end UpperTheory.Kum1

open UpperTheory.Kum1 in
/- English proof (translation)
Introduce `q _ A _ hq hpic x`. Take `⟨κ, -, -, hκ, -, -⟩` from `GlobalTheory.T.kummer_sequence_etale_tateTwist q`. Take `⟨ρ, ρnat, ρd, ρι⟩` from `rho_ex q κ`. Establish `hqX : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤))`. Simplify using `using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom`.

Take `⟨α, rfl⟩` from `x.mk_surjective`. Establish `T1` using `GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff (ZMod q) (Spec (CommRingCat.of A)) (II q) 0 1 2 (by norm_num) (by norm_num)`. Establish `T2` using `GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff ℤ (Spec (CommRingCat.of A)) JJ 0 1 2 (by norm_num) (by norm_num)`. Establish `hz` using `(T1.2 α).1`. Establish `hz' : Sec.map (JJ.d 1 2) (ρ _ 1 (ev α.1 0 1 (by simp) (Spec (CommRingCat.of A)) (𝟙 _))) = 0`.

Rewrite using `[ρd, hz, map_zero]`. Take `⟨α', hα', -⟩` from `T2.1 _ hz'`. Establish `hid` using `hα' (Spec (CommRingCat.of A)) (𝟙 _)`. Rewrite `hid` using `[sec_res_id]`. Establish `hqz' : q • ρ _ 1 (ev α.1 0 1 (by simp) (Spec (CommRingCat.of A)) (𝟙 _)) = 0`.

Rewrite using `[← map_nsmul, q_smul_zero, map_zero]`. Establish `hc : CohomologyClass.mk α' = 0`. Apply `tors_zero q A hpic` to reduce the goal to its premises. Rewrite using `[mk_nsmul, (T2.2 (q • α')).2]`. Use `⟨0, ?_⟩` and prove the remaining obligations.

Establish `e : ((q • α' : Cocycle _ _ 1)).1 = ((q : ℤ) • α'.1)`. Rewrite using `[natCast_zsmul]`. Both sides reduce to the same expression. Establish `e3 : ev ((q : ℤ) • α'.1) 0 1 (by simp) (Spec (CommRingCat.of A)) (𝟙 (Spec (CommRingCat.of A))) = (q : ℤ) • ev α'.1 0 1 (by simp) (Spec (CommRingCat.of A)) (𝟙 (Spec (CommRingCat.of A)))` using `((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties ℤ).1 α'.1 α'.1 0 1 (by simp) _ _).2.2.2 (q : ℤ)`. Rewrite using `[sm_zero, e, e3, hid, natCast_zsmul, hqz']`.

Take `⟨w, hw⟩` from `((T2.2 α').2).1 hc`. Rewrite `hw` using `[hid]`. Establish `hqw : Sec.map (JJ.d 0 1) (q • w) = 0` using `by rw [sm_nsmul, hw, hqz']`. Take `⟨b, hb⟩` from `((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ Gm _).1 (q • w)).1 hqw`. Take `⟨u, rfl⟩` from `UpperTheory.exists_unit_eq_multiplicativeGroup_section _ b`.

Establish `K` using `GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q`. Take `⟨γ, hγ, -, hγ2⟩` from `K.1 _ u hqX`. Take `⟨Y, hY⟩` from `glue κ hκ ρnat ρd ρι hqX hz hw u hb (ev γ.1 0 1 (by simp) _ (𝟙 _)) (fun U x v hv => by rw [ev_id_res]; exact hγ2 U x v hv)`. Establish `h0 : CohomologyClass.mk (α + γ) = 0` using `((T1.2 (α + γ)).2).2 ⟨Y, hY.trans ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).1 α.1 γ.1 0 1 (by simp) _ (𝟙 _)).1.symm⟩`. Rewrite `h0` using `[CohomologyClass.mk_add, hγ]`.

Use `⟨u⁻¹, ?_⟩` and prove the remaining obligations. Establish `h1` using `(K.2.2 u u⁻¹ hqX).1`. Establish `h2` using `(K.2.2 (1 : (Γ(Spec (CommRingCat.of A), ⊤))ˣ) 1 hqX).1`. Rewrite `h2` using `[mul_one]`. Establish `k1` using `left_eq_add.mp h2`.

Rewrite `h1` using `[mul_inv_cancel, k1]`. Establish `e1 : kum q u⁻¹ = -kum q u`. Rewrite using `[eq_neg_iff_add_eq_zero, add_comm]`. Conclude with `h1.symm`. Rewrite using `[e1, eq_neg_of_add_eq_zero_left h0]`.
-/
theorem UpperTheory.Cb.exists_unit_kummer_eq_of_picard_torsionFree :
    ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → (∀ c : CommRing.Pic A, c ^ q = 1 → c = 1) → ∀ x : Ht q (sp A) 1 1, ∃ u : (Γ(Spec (CommRingCat.of A), ⊤))ˣ, kum q u = x := by
  intro q _ A _ hq hpic x
  obtain ⟨κ, -, -, hκ, -, -⟩ := GlobalTheory.T.kummer_sequence_etale_tateTwist q
  obtain ⟨ρ, ρnat, ρd, ρι⟩ := rho_ex q κ
  have hqX : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  obtain ⟨α, rfl⟩ := x.mk_surjective
  have T1 := GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff (ZMod q) (Spec (CommRingCat.of A)) (II q) 0 1 2 (by norm_num) (by norm_num)
  have T2 := GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff ℤ (Spec (CommRingCat.of A)) JJ 0 1 2 (by norm_num) (by norm_num)
  have hz := (T1.2 α).1
  have hz' : Sec.map (JJ.d 1 2) (ρ _ 1 (ev α.1 0 1 (by simp) (Spec (CommRingCat.of A)) (𝟙 _))) = 0 := by
    rw [ρd, hz, map_zero]
  obtain ⟨α', hα', -⟩ := T2.1 _ hz'
  have hid := hα' (Spec (CommRingCat.of A)) (𝟙 _)
  rw [sec_res_id] at hid
  have hqz' : q • ρ _ 1 (ev α.1 0 1 (by simp) (Spec (CommRingCat.of A)) (𝟙 _)) = 0 := by
    rw [← map_nsmul, q_smul_zero, map_zero]
  have hc : CohomologyClass.mk α' = 0 := by
    apply tors_zero q A hpic
    rw [mk_nsmul, (T2.2 (q • α')).2]
    refine ⟨0, ?_⟩
    have e : ((q • α' : Cocycle _ _ 1)).1 = ((q : ℤ) • α'.1) := by
      rw [natCast_zsmul]; rfl
    have e3 : ev ((q : ℤ) • α'.1) 0 1 (by simp) (Spec (CommRingCat.of A)) (𝟙 (Spec (CommRingCat.of A))) =
        (q : ℤ) • ev α'.1 0 1 (by simp) (Spec (CommRingCat.of A)) (𝟙 (Spec (CommRingCat.of A))) :=
      ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties ℤ).1 α'.1 α'.1 0 1 (by simp) _ _).2.2.2 (q : ℤ)
    rw [sm_zero, e, e3, hid, natCast_zsmul, hqz']
  obtain ⟨w, hw⟩ := ((T2.2 α').2).1 hc
  rw [hid] at hw
  have hqw : Sec.map (JJ.d 0 1) (q • w) = 0 := by rw [sm_nsmul, hw, hqz']
  obtain ⟨b, hb⟩ := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ Gm _).1 (q • w)).1 hqw
  obtain ⟨u, rfl⟩ := UpperTheory.exists_unit_eq_multiplicativeGroup_section _ b
  have K := GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q
  obtain ⟨γ, hγ, -, hγ2⟩ := K.1 _ u hqX
  obtain ⟨Y, hY⟩ := glue κ hκ ρnat ρd ρι hqX hz hw u hb (ev γ.1 0 1 (by simp) _ (𝟙 _))
    (fun U x v hv => by rw [ev_id_res]; exact hγ2 U x v hv)
  have h0 : CohomologyClass.mk (α + γ) = 0 :=
    ((T1.2 (α + γ)).2).2 ⟨Y, hY.trans ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).1 α.1 γ.1 0 1 (by simp) _ (𝟙 _)).1.symm⟩
  rw [CohomologyClass.mk_add, hγ] at h0
  refine ⟨u⁻¹, ?_⟩
  have h1 := (K.2.2 u u⁻¹ hqX).1
  have h2 := (K.2.2 (1 : (Γ(Spec (CommRingCat.of A), ⊤))ˣ) 1 hqX).1
  rw [mul_one] at h2
  have k1 := left_eq_add.mp h2
  rw [mul_inv_cancel, k1] at h1
  have e1 : kum q u⁻¹ = -kum q u := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact h1.symm
  rw [e1, eq_neg_of_add_eq_zero_left h0]
