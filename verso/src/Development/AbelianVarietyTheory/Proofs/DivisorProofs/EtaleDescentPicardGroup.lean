import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDegreeClassesDieOnEtaleCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFaithfullyFlatRefiningEtaleSurjectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCocycleCoboundaryIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveMultiplicativeGroupSectionsUnitsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicFaithfullyFlatDescentUnitCocyclesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFaithfullyFlatPicMapAlgebraEqOneStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.PicardFirstCohomology

def gsi (C : CommRingCat.{0}) : Γ(Spec C, ⊤) ≃+* C := (Scheme.ΓSpecIso C).commRingCatIsoToRingEquiv

def gmOf (C : CommRingCat.{0}) : Additive Cˣ →+ (onRings Gm).obj C :=
  ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op (Spec C))).hom.toAddMonoidHom.comp
    ((AddEquiv.ulift.{0, 1}.symm : Additive Γ(Spec C, ⊤)ˣ ≃+ ULift.{1} (Additive Γ(Spec C, ⊤)ˣ)).toAddMonoidHom.comp
      (MulEquiv.toAdditive (Units.mapEquiv (gsi C).symm.toMulEquiv)).toAddMonoidHom)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gmOf_apply (C : CommRingCat.{0}) (a : Additive Cˣ) :
    gmOf C a = ofRings.sec unitsF (Spec C) (ULift.up (Additive.ofMul (Units.mapEquiv (gsi C).symm.toMulEquiv a.toMul))) := rfl

/- English proof (translation)
Establish `h` using `GlobalTheory.T.bijective_multiplicativeGroup_sections_units (Spec C)`. Establish `h2 : Function.Bijective (fun a : Additive Cˣ => (ULift.up (Additive.ofMul (Units.mapEquiv (gsi C).symm.toMulEquiv a.toMul)) : ULift.{1} (Additive Γ(Spec C, ⊤)ˣ)))` using `((MulEquiv.toAdditive (Units.mapEquiv (gsi C).symm.toMulEquiv)).toEquiv.trans Equiv.ulift.symm).bijective`. Conclude with `h.comp h2`.
-/
theorem gmOf_bijective (C : CommRingCat.{0}) : Function.Bijective (gmOf C) := by
  have h := GlobalTheory.T.bijective_multiplicativeGroup_sections_units (Spec C)
  have h2 : Function.Bijective (fun a : Additive Cˣ =>
      (ULift.up (Additive.ofMul (Units.mapEquiv (gsi C).symm.toMulEquiv a.toMul)) : ULift.{1} (Additive Γ(Spec C, ⊤)ˣ))) :=
    ((MulEquiv.toAdditive (Units.mapEquiv (gsi C).symm.toMulEquiv)).toEquiv.trans Equiv.ulift.symm).bijective
  exact h.comp h2

/- English proof (translation)
Establish `h` using `congrArg (fun φ => φ.hom (ULift.up (Additive.ofMul (Units.mapEquiv (gsi C).symm.toMulEquiv a.toMul)) : ULift.{1} (Additive Γ(Spec C, ⊤)ˣ))) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality (Spec.map f).op)`. Simplify using `only [ModuleCat.hom_comp] at h`. Use `h.symm.trans ?_` and prove the remaining obligations. Use `congrArg (fun y => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op (Spec D))).hom y) ?_` and prove the remaining obligations. Apply `ULift.ext` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Use `congrArg (fun φ => φ.hom ((a.toMul : Cˣ) : C)) (Scheme.ΓSpecIso_inv_naturality f)` as an intermediate fact. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at this`. Conclude with `this.symm`.
-/
theorem gmOf_nat {C D : CommRingCat.{0}} (f : C ⟶ D) (a : Additive Cˣ) :
    ((onRings Gm).map f).hom (gmOf C a) = gmOf D (MonoidHom.toAdditive (Units.map f.hom.toMonoidHom) a) := by
  have h := congrArg (fun φ => φ.hom (ULift.up (Additive.ofMul (Units.mapEquiv (gsi C).symm.toMulEquiv a.toMul)) :
      ULift.{1} (Additive Γ(Spec C, ⊤)ˣ)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality (Spec.map f).op)
  simp only [ModuleCat.hom_comp] at h
  refine h.symm.trans ?_
  refine congrArg (fun y => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op (Spec D))).hom y) ?_
  apply ULift.ext
  apply Units.ext
  have := congrArg (fun φ => φ.hom ((a.toMul : Cˣ) : C)) (Scheme.ΓSpecIso_inv_naturality f)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this.symm

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]

/- English proof (translation)
Unfold `Z1 UCoc`. Express the relevant statement in the definitionally equal form `(_ = _) ↔ _`. Rewrite using `[AddMonoidHom.add_apply]`. Use `erw [gmOf_nat, gmOf_nat, gmOf_nat]`. Rewrite using `[← map_add, (gmOf_bijective _).1.eq_iff]`.

Simplify using `only [MonoidHom.toAdditive_apply_apply, toMul_ofMul]`. Rewrite using `[← ofMul_mul, EmbeddingLike.apply_eq_iff_eq, Units.ext_iff]`. Simplify using the standard rewrite rules.
-/
theorem mem_cocycles_units_iff (w : (B ⊗[A] B)ˣ) :
    gmOf (CommRingCat.of (B ⊗[A] B)) (Additive.ofMul w) ∈ Z1 Gm A B ↔ UCoc A B w := by
  unfold Z1 UCoc
  change (_ = _) ↔ _
  rw [AddMonoidHom.add_apply]
  erw [gmOf_nat, gmOf_nat, gmOf_nat]
  rw [← map_add, (gmOf_bijective _).1.eq_iff]
  simp only [MonoidHom.toAdditive_apply_apply, toMul_ofMul]
  rw [← ofMul_mul, EmbeddingLike.apply_eq_iff_eq, Units.ext_iff]
  simp

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]

def zOf {w : (B ⊗[A] B)ˣ} (hw : UCoc A B w) : Z1 Gm A B :=
  ⟨gmOf (CommRingCat.of (B ⊗[A] B)) (Additive.ofMul w), (mem_cocycles_units_iff w).2 hw⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem zOf_coe {w : (B ⊗[A] B)ˣ} (hw : UCoc A B w) :
    (zOf hw : (onRings Gm).obj (CommRingCat.of (B ⊗[A] B))) = gmOf (CommRingCat.of (B ⊗[A] B)) (Additive.ofMul w) := rfl

/- English proof (translation)
Rewrite using `[← mem_cocycles_units_iff, ofMul_mul, map_add]`. Conclude with `add_mem ((mem_cocycles_units_iff w).2 hw) ((mem_cocycles_units_iff v).2 hv)`.
-/
theorem UCoc_mul {w v : (B ⊗[A] B)ˣ} (hw : UCoc A B w) (hv : UCoc A B v) : UCoc A B (w * v) := by
  rw [← mem_cocycles_units_iff, ofMul_mul, map_add]
  exact add_mem ((mem_cocycles_units_iff w).2 hw) ((mem_cocycles_units_iff v).2 hv)

/- English proof (translation)
Rewrite using `[← mem_cocycles_units_iff, ofMul_inv, map_neg]`. Conclude with `neg_mem ((mem_cocycles_units_iff w).2 hw)`.
-/
theorem UCoc_inv {w : (B ⊗[A] B)ˣ} (hw : UCoc A B w) : UCoc A B w⁻¹ := by
  rw [← mem_cocycles_units_iff, ofMul_inv, map_neg]
  exact neg_mem ((mem_cocycles_units_iff w).2 hw)

/- English proof (translation)
The claim follows from `Subtype.ext (by rw [zOf_coe, ofMul_mul, map_add]; rfl)`.
-/
theorem zOf_mul {w v : (B ⊗[A] B)ˣ} (hw : UCoc A B w) (hv : UCoc A B v) :
    zOf (UCoc_mul hw hv) = zOf hw + zOf hv :=
  Subtype.ext (by rw [zOf_coe, ofMul_mul, map_add]; rfl)

/- English proof (translation)
The claim follows from `Subtype.ext (by rw [zOf_coe, ofMul_inv, map_neg]; rfl)`.
-/
theorem zOf_inv {w : (B ⊗[A] B)ˣ} (hw : UCoc A B w) : zOf (UCoc_inv hw) = - zOf hw :=
  Subtype.ext (by rw [zOf_coe, ofMul_inv, map_neg]; rfl)

/- English proof (translation)
Establish `e1 : ∀ t : B ⊗[A] B, Algebra.TensorProduct.map (AlgHom.id A B') (Algebra.TensorProduct.includeRight : B' →ₐ[A] B' ⊗[A] B') (Algebra.TensorProduct.map φ φ t) = Algebra.TensorProduct.map φ (Algebra.TensorProduct.map φ φ) (Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorPro …`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Establish `e2 : ∀ t : B ⊗[A] B, Algebra.TensorProduct.map (AlgHom.id A B') (Algebra.TensorProduct.includeLeft : B' →ₐ[A] B' ⊗[A] B') (Algebra.TensorProduct.map φ φ t) = Algebra.TensorProduct.map φ (Algebra.TensorProduct.map φ φ) (Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProd …`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a b => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Establish `e3 : ∀ t : B ⊗[A] B, (Algebra.TensorProduct.includeRight : B' ⊗[A] B' →ₐ[A] B' ⊗[A] (B' ⊗[A] B')) (Algebra.TensorProduct.map φ φ t) = Algebra.TensorProduct.map φ (Algebra.TensorProduct.map φ φ) ((Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)) t)`. Introduce `t`. Simplify using the standard rewrite rules.

Unfold `UCoc at hw ⊢`. Rewrite using `[hw', e1, e2, e3, ← map_mul, hw]`.
-/
theorem UCoc_map {B' : Type} [CommRing B'] [Algebra A B'] (φ : B →ₐ[A] B') {w : (B ⊗[A] B)ˣ} (hw : UCoc A B w)
    {w' : (B' ⊗[A] B')ˣ} (hw' : (w' : B' ⊗[A] B') = Algebra.TensorProduct.map φ φ (w : B ⊗[A] B)) : UCoc A B' w' := by
  have e1 : ∀ t : B ⊗[A] B, Algebra.TensorProduct.map (AlgHom.id A B')
      (Algebra.TensorProduct.includeRight : B' →ₐ[A] B' ⊗[A] B') (Algebra.TensorProduct.map φ φ t) =
      Algebra.TensorProduct.map φ (Algebra.TensorProduct.map φ φ) (Algebra.TensorProduct.map (AlgHom.id A B)
      (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have e2 : ∀ t : B ⊗[A] B, Algebra.TensorProduct.map (AlgHom.id A B')
      (Algebra.TensorProduct.includeLeft : B' →ₐ[A] B' ⊗[A] B') (Algebra.TensorProduct.map φ φ t) =
      Algebra.TensorProduct.map φ (Algebra.TensorProduct.map φ φ) (Algebra.TensorProduct.map (AlgHom.id A B)
      (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have e3 : ∀ t : B ⊗[A] B, (Algebra.TensorProduct.includeRight : B' ⊗[A] B' →ₐ[A] B' ⊗[A] (B' ⊗[A] B'))
      (Algebra.TensorProduct.map φ φ t) = Algebra.TensorProduct.map φ (Algebra.TensorProduct.map φ φ)
      ((Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)) t) := by
    intro t
    simp
  unfold UCoc at hw ⊢
  rw [hw', e1, e2, e3, ← map_mul, hw]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb⟩`. Establish `e : w = r (Additive.toMul b) / l (Additive.toMul b)` using `congrArg Additive.toMul hb`. Use `⟨(Additive.toMul b)⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[e, map_inv, map_inv, div_mul_eq_mul_div, mul_inv_cancel, one_div]`.

Introduce and unpack `⟨b, hb⟩`. Use `⟨Additive.ofMul b⁻¹, Additive.toMul.injective ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `w = r b⁻¹ / l b⁻¹`. Rewrite using `[map_inv, map_inv, inv_div_inv, ← hb]`. Conclude with `(mul_div_cancel_right _ _).symm`.
-/
theorem cobd_iff {G K : Type} [CommGroup G] [CommGroup K] (r l : K →* G) (w : G) :
    (∃ b : Additive K, Additive.ofMul w = MonoidHom.toAdditive r b - MonoidHom.toAdditive l b) ↔
      ∃ b : K, w * r b = l b := by
  constructor
  · rintro ⟨b, hb⟩
    have e : w = r (Additive.toMul b) / l (Additive.toMul b) := congrArg Additive.toMul hb
    refine ⟨(Additive.toMul b)⁻¹, ?_⟩
    rw [e, map_inv, map_inv, div_mul_eq_mul_div, mul_inv_cancel, one_div]
  · rintro ⟨b, hb⟩
    refine ⟨Additive.ofMul b⁻¹, Additive.toMul.injective ?_⟩
    change w = r b⁻¹ / l b⁻¹
    rw [map_inv, map_inv, inv_div_inv, ← hb]
    exact (mul_div_cancel_right _ _).symm

variable (A : Type) [CommRing A]

def cg : ∀ (B : Type) [CommRing B] [Algebra A B], Z1 Gm A B →+ H ℤ (sp A) Gm 1 :=
  Classical.choose (GlobalTheory.T.etale_cocycle_coboundary_iff ℤ Gm A)

def cd : ∀ (B : Type) [CommRing B] [Algebra A B], (B ⊗[A] B)ˣ → CommRing.Pic A :=
  Classical.choose (GlobalTheory.T.pic_faithfullyFlat_descent_unitCocycles A)

variable {A} {B : Type} [CommRing B] [Algebra A B]

/- English proof (translation)
The claim follows from `(Classical.choose_spec (GlobalTheory.T.pic_faithfullyFlat_descent_unitCocycles A) B).1 w v hw hv`.
-/
theorem cd_mul [Module.FaithfullyFlat A B] {w v : (B ⊗[A] B)ˣ} (hw : UCoc A B w) (hv : UCoc A B v) :
    cd A B (w * v) = cd A B w * cd A B v :=
  (Classical.choose_spec (GlobalTheory.T.pic_faithfullyFlat_descent_unitCocycles A) B).1 w v hw hv

/- English proof (translation)
Unfold `cg cd`. Rewrite using `[(Classical.choose_spec (GlobalTheory.T.etale_cocycle_coboundary_iff ℤ Gm A) B).1, (Classical.choose_spec (GlobalTheory.T.pic_faithfullyFlat_descent_unitCocycles A) B).2.1 w hw]`. Combine the equalities or inequalities in the displayed calculation. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv⟩`.

Take `⟨b, rfl⟩` from `(gmOf_bijective _).2 v`. Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite `hv` using `[zOf_coe, gmOf_nat, gmOf_nat, ← map_sub]`. Conclude with `(gmOf_bijective _).1 hv`. Introduce and unpack `⟨b, hb⟩`.

Use `⟨gmOf _ b, ?_⟩` and prove the remaining obligations. Rewrite using `[zOf_coe, gmOf_nat, gmOf_nat, ← map_sub]`. Conclude with `congrArg _ hb`. Use `_ ↔ _ := cobd_iff _ _ w`. Use `_ ↔ _ := by simp [Units.ext_iff]`.
-/
theorem cg_zero_iff [Algebra.Etale A B] [Module.FaithfullyFlat A B] {w : (B ⊗[A] B)ˣ} (hw : UCoc A B w) :
    cg A B (zOf hw) = 0 ↔ cd A B w = 1 := by
  unfold cg cd
  rw [(Classical.choose_spec (GlobalTheory.T.etale_cocycle_coboundary_iff ℤ Gm A) B).1, (Classical.choose_spec (GlobalTheory.T.pic_faithfullyFlat_descent_unitCocycles A) B).2.1 w hw]
  calc _ ↔ ∃ b : Additive Bˣ, Additive.ofMul w =
        MonoidHom.toAdditive (Units.map (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom.toMonoidHom) b -
        MonoidHom.toAdditive (Units.map (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toRingHom.toMonoidHom) b := by
        constructor
        · rintro ⟨v, hv⟩
          obtain ⟨b, rfl⟩ := (gmOf_bijective _).2 v
          refine ⟨b, ?_⟩
          rw [zOf_coe, gmOf_nat, gmOf_nat, ← map_sub] at hv
          exact (gmOf_bijective _).1 hv
        · rintro ⟨b, hb⟩
          refine ⟨gmOf _ b, ?_⟩
          rw [zOf_coe, gmOf_nat, gmOf_nat, ← map_sub]
          exact congrArg _ hb
    _ ↔ _ := cobd_iff _ _ w
    _ ↔ _ := by simp [Units.ext_iff]

/- English proof (translation)
Take `⟨u, hu⟩` from `(Classical.choose_spec (GlobalTheory.T.etale_cocycle_coboundary_iff ℤ Gm A) B).2.1 x hx`. Take `⟨b, hb⟩` from `(gmOf_bijective _).2 (u : (onRings Gm).obj (CommRingCat.of (B ⊗[A] B)))`. Establish `hw : UCoc A B (Additive.toMul b)` using `(mem_cocycles_units_iff _).1 (by rw [ofMul_toMul, hb]; exact u.2)`. Establish `hz : zOf hw = u` using `Subtype.ext hb`. Conclude with `⟨_, hw, (congrArg _ hz).trans hu⟩`.
-/
theorem cg_range [Algebra.Etale A B] [Module.FaithfullyFlat A B] (x : H ℤ (sp A) Gm 1)
    (hx : pull ℤ (spMap (algebraMap A B)) Gm 1 x = 0) : ∃ (w : (B ⊗[A] B)ˣ) (hw : UCoc A B w), cg A B (zOf hw) = x := by
  obtain ⟨u, hu⟩ := (Classical.choose_spec (GlobalTheory.T.etale_cocycle_coboundary_iff ℤ Gm A) B).2.1 x hx
  obtain ⟨b, hb⟩ := (gmOf_bijective _).2 (u : (onRings Gm).obj (CommRingCat.of (B ⊗[A] B)))
  have hw : UCoc A B (Additive.toMul b) := (mem_cocycles_units_iff _).1 (by rw [ofMul_toMul, hb]; exact u.2)
  have hz : zOf hw = u := Subtype.ext hb
  exact ⟨_, hw, (congrArg _ hz).trans hu⟩

/- English proof (translation)
The claim follows from `(Classical.choose_spec (GlobalTheory.T.pic_faithfullyFlat_descent_unitCocycles A) B).2.2.1 c hc`.
-/
theorem cd_range [Module.FaithfullyFlat A B] (c : CommRing.Pic A) (hc : CommRing.Pic.mapAlgebra A B c = 1) :
    ∃ w, UCoc A B w ∧ cd A B w = c :=
  (Classical.choose_spec (GlobalTheory.T.pic_faithfullyFlat_descent_unitCocycles A) B).2.2.1 c hc

/- English proof (translation)
Establish `hC : UCoc A C (Units.map (Algebra.TensorProduct.map φ φ).toRingHom.toMonoidHom w)` using `UCoc_map φ hw rfl`. Use `⟨_, hC, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Classical.choose_spec (GlobalTheory.T.etale_cocycle_coboundary_iff ℤ Gm A) B).2.2.2 C φ (zOf hw) (zOf hC) (by rw [zOf_coe, zOf_coe, gmOf_nat]; rfl)`. Conclude with `(Classical.choose_spec (GlobalTheory.T.pic_faithfullyFlat_descent_unitCocycles A) B).2.2.2.2 C φ w _ hw rfl`.
-/
theorem push {C : Type} [CommRing C] [Algebra A C] [Algebra.Etale A B] [Module.FaithfullyFlat A B]
    [Algebra.Etale A C] [Module.FaithfullyFlat A C] (φ : B →ₐ[A] C) {w : (B ⊗[A] B)ˣ} (hw : UCoc A B w) :
    ∃ (wC : (C ⊗[A] C)ˣ) (hC : UCoc A C wC), cg A C (zOf hC) = cg A B (zOf hw) ∧ cd A C wC = cd A B w := by
  have hC : UCoc A C (Units.map (Algebra.TensorProduct.map φ φ).toRingHom.toMonoidHom w) := UCoc_map φ hw rfl
  refine ⟨_, hC, ?_, ?_⟩
  · exact (Classical.choose_spec (GlobalTheory.T.etale_cocycle_coboundary_iff ℤ Gm A) B).2.2.2 C φ (zOf hw) (zOf hC)
      (by rw [zOf_coe, zOf_coe, gmOf_nat]; rfl)
  · exact (Classical.choose_spec (GlobalTheory.T.pic_faithfullyFlat_descent_unitCocycles A) B).2.2.2.2 C φ w _ hw rfl

variable {A : Type} [CommRing A]

def Rep (x : H ℤ (sp A) Gm 1) (c : CommRing.Pic A) : Prop :=
  ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra.Etale A B) (_ : Module.FaithfullyFlat A B)
    (w : (B ⊗[A] B)ˣ) (hw : UCoc A B w), cg A B (zOf hw) = x ∧ cd A B w = c

/- English proof (translation)
Use `haveI : Algebra.Etale B (B ⊗[A] C) := inferInstance`. Conclude with `Algebra.Etale.comp A B _`.
-/
theorem etale_tensor (B C : Type) [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] [Algebra.Etale A B]
    [Algebra.Etale A C] : Algebra.Etale A (B ⊗[A] C) := by
  haveI : Algebra.Etale B (B ⊗[A] C) := inferInstance
  exact Algebra.Etale.comp A B _

/- English proof (translation)
Use `haveI : Module.FaithfullyFlat B (B ⊗[A] C) := inferInstance`. Conclude with `Module.FaithfullyFlat.trans A B _`.
-/
theorem ff_tensor (B C : Type) [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] [Module.FaithfullyFlat A B]
    [Module.FaithfullyFlat A C] : Module.FaithfullyFlat A (B ⊗[A] C) := by
  haveI : Module.FaithfullyFlat B (B ⊗[A] C) := inferInstance
  exact Module.FaithfullyFlat.trans A B _

/- English proof (translation)
Take `⟨B, _, _, _, _, w, hw, rfl, rfl⟩` from `hx`. Take `⟨B', _, _, _, _, v, hv, rfl, rfl⟩` from `hy`. Use `haveI := etale_tensor (A := A) B B'`. Use `haveI := ff_tensor (A := A) B B'`. Take `⟨w', hw', e1, f1⟩` from `push (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B') hw`.

Take `⟨v', hv', e2, f2⟩` from `push (Algebra.TensorProduct.includeRight : B' →ₐ[A] B ⊗[A] B') hv`. Conclude with `⟨B ⊗[A] B', inferInstance, inferInstance, inferInstance, inferInstance, w', hw', v', hv', e1, f1, e2, f2⟩`.
-/
theorem common {x y : H ℤ (sp A) Gm 1} {c d : CommRing.Pic A} (hx : Rep x c) (hy : Rep y d) :
    ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra.Etale A C) (_ : Module.FaithfullyFlat A C)
      (w : (C ⊗[A] C)ˣ) (hw : UCoc A C w) (v : (C ⊗[A] C)ˣ) (hv : UCoc A C v),
      cg A C (zOf hw) = x ∧ cd A C w = c ∧ cg A C (zOf hv) = y ∧ cd A C v = d := by
  obtain ⟨B, _, _, _, _, w, hw, rfl, rfl⟩ := hx
  obtain ⟨B', _, _, _, _, v, hv, rfl, rfl⟩ := hy
  haveI := etale_tensor (A := A) B B'
  haveI := ff_tensor (A := A) B B'
  obtain ⟨w', hw', e1, f1⟩ := push (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B') hw
  obtain ⟨v', hv', e2, f2⟩ := push (Algebra.TensorProduct.includeRight : B' →ₐ[A] B ⊗[A] B') hv
  exact ⟨B ⊗[A] B', inferInstance, inferInstance, inferInstance, inferInstance, w', hw', v', hv', e1, f1, e2, f2⟩

/- English proof (translation)
Take `⟨C, _, _, _, _, w, hw, v, hv, e1, rfl, e2, rfl⟩` from `common h h'`. Establish `hq` using `UCoc_mul hw (UCoc_inv hv)`. Establish `h0 : cg A C (zOf hq) = 0` using `by rw [zOf_mul hw (UCoc_inv hv), zOf_inv hv, map_add, map_neg, e1, e2, add_neg_cancel]`. Rewrite `h0` using `[cg_zero_iff]`. Establish `: w = (w * v⁻¹) * v` using `by rw [inv_mul_cancel_right]`.

Rewrite using `[this, cd_mul hq hv, h0, one_mul]`.
-/
theorem rep_unique {x : H ℤ (sp A) Gm 1} {c c' : CommRing.Pic A} (h : Rep x c) (h' : Rep x c') : c = c' := by
  obtain ⟨C, _, _, _, _, w, hw, v, hv, e1, rfl, e2, rfl⟩ := common h h'
  have hq := UCoc_mul hw (UCoc_inv hv)
  have h0 : cg A C (zOf hq) = 0 := by rw [zOf_mul hw (UCoc_inv hv), zOf_inv hv, map_add, map_neg, e1, e2, add_neg_cancel]
  rw [cg_zero_iff] at h0
  have : w = (w * v⁻¹) * v := by rw [inv_mul_cancel_right]
  rw [this, cd_mul hq hv, h0, one_mul]

/- English proof (translation)
Take `⟨C, _, _, _, _, w, hw, v, hv, e1, f1, e2, f2⟩` from `common hx hy`. Use `⟨C, inferInstance, inferInstance, inferInstance, inferInstance, w * v, UCoc_mul hw hv, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[zOf_mul hw hv, map_add, e1, e2]`. Rewrite using `[cd_mul hw hv, f1, f2]`.
-/
theorem rep_add {x y : H ℤ (sp A) Gm 1} {c d : CommRing.Pic A} (hx : Rep x c) (hy : Rep y d) : Rep (x + y) (c * d) := by
  obtain ⟨C, _, _, _, _, w, hw, v, hv, e1, f1, e2, f2⟩ := common hx hy
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, w * v, UCoc_mul hw hv, ?_, ?_⟩
  · rw [zOf_mul hw hv, map_add, e1, e2]
  · rw [cd_mul hw hv, f1, f2]

/- English proof (translation)
Take `⟨Y, f, hf, hs, hx⟩` from `GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover ℤ (Spec (CommRingCat.of A)) Gm 1 one_pos x`. Take `⟨B, g, h, hg, hh⟩` from `GlobalTheory.T.exists_etaleFaithfullyFlat_refining_etale_surjection (CommRingCat.of A) Y f hf hs`. Use `letI : Algebra A B := g.hom.toAlgebra`. Use `haveI : Algebra.Etale A B := hg.1`. Use `haveI : Module.FaithfullyFlat A B := hg.2`.

Establish `hx' : pull ℤ (spMap (algebraMap A B)) Gm 1 x = 0`. Express the relevant statement in the definitionally equal form `pull ℤ (sch.map (Spec.map g)) Gm 1 x = 0`. Rewrite using `[← hh, Functor.map_comp, pull_comp, hx, map_zero]`. Take `⟨w, hw, hwx⟩` from `cg_range x hx'`. Conclude with `⟨cd A B w, B, inferInstance, inferInstance, inferInstance, inferInstance, w, hw, hwx, rfl⟩`.
-/
theorem rep_exists (x : H ℤ (sp A) Gm 1) : ∃ c, Rep x c := by
  obtain ⟨Y, f, hf, hs, hx⟩ := GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover ℤ (Spec (CommRingCat.of A)) Gm 1 one_pos x
  obtain ⟨B, g, h, hg, hh⟩ := GlobalTheory.T.exists_etaleFaithfullyFlat_refining_etale_surjection (CommRingCat.of A) Y f hf hs
  letI : Algebra A B := g.hom.toAlgebra
  haveI : Algebra.Etale A B := hg.1
  haveI : Module.FaithfullyFlat A B := hg.2
  have hx' : pull ℤ (spMap (algebraMap A B)) Gm 1 x = 0 := by
    change pull ℤ (sch.map (Spec.map g)) Gm 1 x = 0
    rw [← hh, Functor.map_comp, pull_comp, hx, map_zero]
  obtain ⟨w, hw, hwx⟩ := cg_range x hx'
  exact ⟨cd A B w, B, inferInstance, inferInstance, inferInstance, inferInstance, w, hw, hwx, rfl⟩

/- English proof (translation)
Take `⟨B, _, _, _, _, hB⟩` from `GlobalTheory.T.exists_etale_faithfullyFlat_picMapAlgebra_eq_one A c`. Take `⟨w, hw, hc⟩` from `cd_range c hB`. Conclude with `⟨cg A B (zOf hw), B, inferInstance, inferInstance, inferInstance, inferInstance, w, hw, rfl, hc⟩`.
-/
theorem rep_surj (c : CommRing.Pic A) : ∃ x, Rep x c := by
  obtain ⟨B, _, _, _, _, hB⟩ := GlobalTheory.T.exists_etale_faithfullyFlat_picMapAlgebra_eq_one A c
  obtain ⟨w, hw, hc⟩ := cd_range c hB
  exact ⟨cg A B (zOf hw), B, inferInstance, inferInstance, inferInstance, inferInstance, w, hw, rfl, hc⟩

/- English proof (translation)
Take `⟨B, _, _, _, _, w, hw, rfl, hc⟩` from `h`. Conclude with `(cg_zero_iff hw).2 hc`.
-/
theorem rep_one {x : H ℤ (sp A) Gm 1} (h : Rep x 1) : x = 0 := by
  obtain ⟨B, _, _, _, _, w, hw, rfl, hc⟩ := h
  exact (cg_zero_iff hw).2 hc

end GlobalTheory.EtC.PicardFirstCohomology

namespace GlobalTheory.EtC

open PicardFirstCohomology in

/- English proof (translation)
Introduce `A _`. Use `choose e he using rep_exists (A := A)`. Set `f : H ℤ (sp A) Gm 1 →+ Additive (CommRing.Pic A)` to `AddMonoidHom.mk' (fun x => Additive.ofMul (e x)) (fun x y => by`. Rewrite using `[← ofMul_mul]`. Conclude with `congrArg Additive.ofMul (rep_unique (he (x + y)) (rep_add (he x) (he y))))`.

Use `⟨AddEquiv.ofBijective f ⟨(injective_iff_map_eq_zero f).2 fun x hx => rep_one ?_, fun c => ?_⟩⟩` and prove the remaining obligations. Establish `: e x = 1` using `congrArg Additive.toMul hx`. Conclude with `this ▸ he x`. Take `⟨x, hx⟩` from `rep_surj (Additive.toMul c)`. Conclude with `⟨x, congrArg Additive.ofMul (rep_unique (he x) hx)⟩`.
-/
theorem b6pic_holds : DivisorPicardCompatibility := by
  intro A _
  choose e he using rep_exists (A := A)
  let f : H ℤ (sp A) Gm 1 →+ Additive (CommRing.Pic A) :=
    AddMonoidHom.mk' (fun x => Additive.ofMul (e x)) (fun x y => by
      rw [← ofMul_mul]
      exact congrArg Additive.ofMul (rep_unique (he (x + y)) (rep_add (he x) (he y))))
  refine ⟨AddEquiv.ofBijective f ⟨(injective_iff_map_eq_zero f).2 fun x hx => rep_one ?_, fun c => ?_⟩⟩
  · have : e x = 1 := congrArg Additive.toMul hx
    exact this ▸ he x
  · obtain ⟨x, hx⟩ := rep_surj (Additive.toMul c)
    exact ⟨x, congrArg Additive.ofMul (rep_unique (he x) hx)⟩

end GlobalTheory.EtC

end
