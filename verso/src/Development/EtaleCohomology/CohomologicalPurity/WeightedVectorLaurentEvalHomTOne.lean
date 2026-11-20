import Development.EtaleCohomology.CohomologicalPurity.LeafWCechRec

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.ExcisionChartRatio

def toS {U : Scheme.{0}} {A : Type} [CommRing A] (φ : A →+* Γ(U, ⊤)) : U ⟶ Spec (CommRingCat.of A) :=
  U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)

def ofS {U : Scheme.{0}} {A : Type} [CommRing A] (f : U ⟶ Spec (CommRingCat.of A)) : A →+* Γ(U, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
theorem ofS_toS {U : Scheme.{0}} {A : Type} [CommRing A] (φ : A →+* Γ(U, ⊤)) : ofS (toS φ) = φ := by
  have h := Scheme.ΓSpecIso_naturality (R := CommRingCat.of A) (S := Γ(U, ⊤)) (CommRingCat.ofHom φ)
  have e : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (toS φ).appTop = CommRingCat.ofHom φ := by
    rw [toS, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, h, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  unfold ofS; rw [e]; rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem toS_ofS {U : Scheme.{0}} {A : Type} [CommRing A] (f : U ⟶ Spec (CommRingCat.of A)) : toS (ofS f) = f := by
  unfold toS ofS
  rw [CommRingCat.ofHom_hom, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem toS_inj {U : Scheme.{0}} {A : Type} [CommRing A] {φ ψ : A →+* Γ(U, ⊤)} (h : toS φ = toS ψ) : φ = ψ := by
  rw [← ofS_toS φ, h, ofS_toS]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem ofS_comp {V U : Scheme.{0}} {A : Type} [CommRing A] (h : V ⟶ U) (f : U ⟶ Spec (CommRingCat.of A)) :
    ofS (h ≫ f) = h.appTop.hom.comp (ofS f) := by
  unfold ofS; rw [Scheme.Hom.comp_appTop]; rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem comp_toS {V U : Scheme.{0}} {A : Type} [CommRing A] (h : V ⟶ U) (φ : A →+* Γ(U, ⊤)) :
    h ≫ toS φ = toS (h.appTop.hom.comp φ) := by
  rw [← toS_ofS (h ≫ toS φ), ofS_comp, ofS_toS]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem ofS_comp_spec {U : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (f : U ⟶ Spec (CommRingCat.of A))
    (ψ : B →+* A) : ofS (f ≫ Spec.map (CommRingCat.ofHom ψ)) = (ofS f).comp ψ := by
  unfold ofS
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]; rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem toS_comp_spec {U : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (φ : A →+* Γ(U, ⊤))
    (ψ : B →+* A) : toS φ ≫ Spec.map (CommRingCat.ofHom ψ) = toS (φ.comp ψ) := by
  rw [← toS_ofS (toS φ ≫ _), ofS_comp_spec, ofS_toS]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Simplify to obtain the desired conclusion from the available facts.
-/
theorem laurent_ext {A S : Type} [CommRing A] [CommRing S] {f g : LaurentPolynomial A →+* S}
    (hC : f.comp LaurentPolynomial.C = g.comp LaurentPolynomial.C) (hT : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) :
    f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial A))
  apply Polynomial.ringHom_ext
  · intro a
    have := RingHom.congr_fun hC a
    simpa [LaurentPolynomial.algebraMap_eq_toLaurent] using this
  · simpa [LaurentPolynomial.algebraMap_eq_toLaurent] using hT

abbrev ev (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}ᵒᵖ) : Spc ⥤ Type := (evaluation _ _).obj n ⋙ (evaluation _ _).obj U

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem ev_fst {X Y : Spc} (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}ᵒᵖ) (w : ((X ⨯ Y).obj n).obj U) :
    limit.π (pair X Y ⋙ ev n U) ⟨WalkingPair.left⟩ ((preservesLimitIso (ev n U) (pair X Y)).hom w) =
      ((prod.fst : X ⨯ Y ⟶ X).app n).app U w := by
  have e := preservesLimitIso_hom_π (ev n U) (pair X Y) ⟨WalkingPair.left⟩
  exact ConcreteCategory.congr_hom e w

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem ev_snd {X Y : Spc} (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}ᵒᵖ) (w : ((X ⨯ Y).obj n).obj U) :
    limit.π (pair X Y ⋙ ev n U) ⟨WalkingPair.right⟩ ((preservesLimitIso (ev n U) (pair X Y)).hom w) =
      ((prod.snd : X ⨯ Y ⟶ Y).app n).app U w := by
  have e := preservesLimitIso_hom_π (ev n U) (pair X Y) ⟨WalkingPair.right⟩
  exact ConcreteCategory.congr_hom e w

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem pr_ext {X Y : Spc} (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}ᵒᵖ) (w w' : ((X ⨯ Y).obj n).obj U)
    (h1 : ((prod.fst : X ⨯ Y ⟶ X).app n).app U w = ((prod.fst : X ⨯ Y ⟶ X).app n).app U w')
    (h2 : ((prod.snd : X ⨯ Y ⟶ Y).app n).app U w = ((prod.snd : X ⨯ Y ⟶ Y).app n).app U w') : w = w' := by
  apply (mono_iff_injective (preservesLimitIso (ev n U) (pair X Y)).hom).1 inferInstance
  apply Types.limit_ext
  rintro ⟨_ | _⟩
  · rw [ev_fst, ev_fst, h1]
  · rw [ev_snd, ev_snd, h2]

/- English proof (translation)
Introduce a local definition for the expression. Treat this case separately. Treat this case separately. Introduce a local definition for the expression. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem pr_mk {X Y : Spc} (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}ᵒᵖ) (a : (X.obj n).obj U) (b : (Y.obj n).obj U) :
    ∃ w : ((X ⨯ Y).obj n).obj U, ((prod.fst : X ⨯ Y ⟶ X).app n).app U w = a ∧
      ((prod.snd : X ⨯ Y ⟶ Y).app n).app U w = b := by
  let x : ∀ j, (pair X Y ⋙ ev n U).obj j := fun j => match j with
    | ⟨WalkingPair.left⟩ => a
    | ⟨WalkingPair.right⟩ => b
  let l := Types.Limit.mk (pair X Y ⋙ ev n U) x (by
    rintro ⟨j⟩ ⟨j'⟩ ⟨⟨h⟩⟩
    obtain rfl : j = j' := h
    exact ConcreteCategory.congr_hom ((pair X Y ⋙ ev n U).map_id ⟨j⟩) (x ⟨j⟩))
  obtain ⟨w, hw⟩ : ∃ w, (preservesLimitIso (ev n U) (pair X Y)).hom w = l :=
    ⟨(preservesLimitIso (ev n U) (pair X Y)).inv l, ConcreteCategory.congr_hom (preservesLimitIso (ev n U) (pair X Y)).inv_hom_id l⟩
  refine ⟨w, ?_, ?_⟩
  · rw [← ev_fst, hw]; exact Types.Limit.π_mk _ _ _ _
  · rw [← ev_snd, hw]; exact Types.Limit.π_mk _ _ _ _

variable {d : ℕ}

def ratio {U : Scheme.{0}} (v : WVec d U) (k : Fin d) : Γ(U, ⊤) := v.1.1 k.succ * ↑(v.2.unit⁻¹)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem ratio_spec {U : Scheme.{0}} (v : WVec d U) (k : Fin d) : ratio v k * v.1.1 0 = v.1.1 k.succ := by
  rw [ratio, mul_assoc, IsUnit.val_inv_mul, mul_one]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem ratio_unique {U : Scheme.{0}} (v : WVec d U) (k : Fin d) (r : Γ(U, ⊤)) (h : r * v.1.1 0 = v.1.1 k.succ) :
    ratio v k = r := by
  rw [← v.2.mul_left_inj, ratio_spec, h]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ratio_hom {U : Scheme.{0}} {v w : WVec d U} (u : v ⟶ w) : ratio v = ratio w := by
  funext k
  apply ratio_unique
  have h0 := u.2 0
  have hk := u.2 k.succ
  change v.1.1 0 = _ at h0
  change v.1.1 k.succ = _ at hk
  rw [h0, hk, ← ratio_spec w k]; ring

instance {U : Scheme.{0}} (v w : WVec d U) : Subsingleton (v ⟶ w) where
  allEq u u' := by
    apply Subtype.ext; apply Units.ext
    have h := (u.2 0).symm.trans (u'.2 0)
    exact w.2.mul_left_inj.1 h

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem ratio_map {V U : Scheme.{0}} (f : V ⟶ U) (v : WVec d U) (k : Fin d) :
    ratio ((WVec.map d f).obj v) k = f.appTop.hom (ratio v k) := by
  apply ratio_unique
  change f.appTop.hom (ratio v k) * f.appTop.hom (v.1.1 0) = f.appTop.hom (v.1.1 k.succ)
  rw [← map_mul, ratio_spec]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem wvec_ext {U : Scheme.{0}} {v w : WVec d U} (h0 : v.1.1 0 = w.1.1 0) (hr : ratio v = ratio w) : v = w := by
  apply Subtype.ext; apply Subtype.ext; funext j
  refine Fin.cases h0 (fun k => ?_) j
  rw [← ratio_spec v k, ← ratio_spec w k, h0, hr]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem chain_ratio {U : Scheme.{0}} {n : ℕ} (c : ComposableArrows (WVec d U) n) (j : Fin (n + 1)) :
    ratio (c.obj j) = ratio (c.obj 0) :=
  (ratio_hom (c.map (homOfLE (Fin.zero_le j)))).symm

variable {R : Type} [CommRing R]

def rhom {U : Scheme.{0}} (v : WVec d U) (s : R →+* Γ(U, ⊤)) : MvPolynomial (Fin d) R →+* Γ(U, ⊤) :=
  MvPolynomial.eval₂Hom s (ratio v)

def ghom {U : Scheme.{0}} (v : WVec d U) (s : R →+* Γ(U, ⊤)) :
    LaurentPolynomial (MvPolynomial (Fin d) R) →+* Γ(U, ⊤) :=
  LaurentPolynomial.eval₂ (rhom v s) v.2.unit

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem rhom_congr {U : Scheme.{0}} {v v' : WVec d U} (h : ratio v = ratio v') (s : R →+* Γ(U, ⊤)) :
    rhom v s = rhom v' s := by simp only [rhom, h]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem rhom_map {V U : Scheme.{0}} (f : V ⟶ U) (v : WVec d U) (s : R →+* Γ(U, ⊤)) :
    rhom ((WVec.map d f).obj v) (f.appTop.hom.comp s) = f.appTop.hom.comp (rhom v s) := by
  apply MvPolynomial.ringHom_ext
  · intro r; simp [rhom]
  · intro k; simp [rhom, ratio_map]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ghom_C {U : Scheme.{0}} (v : WVec d U) (s : R →+* Γ(U, ⊤)) :
    (ghom v s).comp LaurentPolynomial.C = rhom v s := by
  exact RingHom.ext fun a => LaurentPolynomial.eval₂_C _ _ a

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem weighted_vector_laurent_eval_hom_T_one {U : Scheme.{0}} (v : WVec d U) (s : R →+* Γ(U, ⊤)) :
    ghom v s (LaurentPolynomial.T 1) = v.1.1 0 := by
  rw [ghom, LaurentPolynomial.eval₂_T, zpow_one, IsUnit.unit_spec]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem ghom_map {V U : Scheme.{0}} (f : V ⟶ U) (v : WVec d U) (s : R →+* Γ(U, ⊤)) :
    ghom ((WVec.map d f).obj v) (f.appTop.hom.comp s) = f.appTop.hom.comp (ghom v s) := by
  apply laurent_ext
  · rw [ghom_C, RingHom.comp_assoc, ghom_C, rhom_map]
  · rw [weighted_vector_laurent_eval_hom_T_one, RingHom.comp_apply, weighted_vector_laurent_eval_hom_T_one]; rfl

variable (d R) in
abbrev AP : Type := MvPolynomial (Fin d) R

section elems
variable {n : SimplexCategoryᵒᵖ} {U : Scheme.{0}ᵒᵖ}

abbrev cW (w : ((W d R).obj n).obj U) : ComposableArrows (WVec d U.unop) n.unop.len :=
  ((prod.fst : W d R ⟶ Wsp d).app n).app U w

abbrev sW (w : ((W d R).obj n).obj U) : U.unop ⟶ Spec (CommRingCat.of R) :=
  ((prod.snd : W d R ⟶ sp R).app n).app U w

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cW_natU {V : Scheme.{0}ᵒᵖ} (f : U ⟶ V) (w : ((W d R).obj n).obj U) :
    cW (((W d R).obj n).map f w) = (((Wsp d).obj n).map f (cW w) : ComposableArrows (WVec d V.unop) _) :=
  ConcreteCategory.congr_hom (((prod.fst : W d R ⟶ Wsp d).app n).naturality f) w

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sW_natU {V : Scheme.{0}ᵒᵖ} (f : U ⟶ V) (w : ((W d R).obj n).obj U) :
    sW (((W d R).obj n).map f w) = f.unop ≫ sW w :=
  ConcreteCategory.congr_hom (((prod.snd : W d R ⟶ sp R).app n).naturality f) w

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cW_natn {m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (w : ((W d R).obj n).obj U) :
    cW (((W d R).map θ).app U w) = (((Wsp d).map θ).app U (cW w) : ComposableArrows (WVec d U.unop) _) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app ((prod.fst : W d R ⟶ Wsp d).naturality θ) U) w

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sW_natn {m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (w : ((W d R).obj n).obj U) :
    sW (((W d R).map θ).app U w) = sW w :=
  ConcreteCategory.congr_hom (NatTrans.congr_app ((prod.snd : W d R ⟶ sp R).naturality θ) U) w

end elems

variable (d R) in

def rW : W d R ⟶ disc.obj (yoneda.obj (Spec (CommRingCat.of (AP d R)))) where
  app n :=
    { app := fun U => TypeCat.ofHom fun w => toS (rhom ((cW w).obj 0) (ofS (sW w)))
      naturality := fun U V f => by
        ext w
        change toS (rhom ((cW (((W d R).obj n).map f w)).obj 0) (ofS (sW (((W d R).obj n).map f w)))) =
          f.unop ≫ toS (rhom ((cW w).obj 0) (ofS (sW w)))
        rw [cW_natU, sW_natU, ofS_comp, comp_toS, ← rhom_map]
        rfl }
  naturality n m θ := by
    ext U w
    change toS (rhom ((cW (((W d R).map θ).app U w)).obj 0) (ofS (sW (((W d R).map θ).app U w)))) =
      toS (rhom ((cW w).obj 0) (ofS (sW w)))
    rw [cW_natn, sW_natn]
    exact congrArg toS (rhom_congr (chain_ratio (cW w) _) _)

variable (d R) in

def gW : (W d R).obj (op (SimplexCategory.mk 0)) ⟶
    yoneda.obj (Spec (CommRingCat.of (LaurentPolynomial (AP d R)))) where
  app U := TypeCat.ofHom fun w => toS (ghom ((cW w).obj 0) (ofS (sW w)))
  naturality U V f := by
    ext w
    change toS (ghom ((cW (((W d R).obj _).map f w)).obj 0) (ofS (sW (((W d R).obj _).map f w)))) =
      f.unop ≫ toS (ghom ((cW w).obj 0) (ofS (sW w)))
    rw [cW_natU, sW_natU, ofS_comp, comp_toS, ← ghom_map]
    rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ratio_wvec1 {A : Type} [CommRing A] (x : Fin d → A) (k : Fin d) :
    ratio (wvec1 x) k = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (x k) := by
  apply ratio_unique
  show (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (x k) *
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Fin.cons 1 x : Fin (d + 1) → A) 0) =
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Fin.cons 1 x : Fin (d + 1) → A) k.succ)
  rw [Fin.cons_zero, Fin.cons_succ, map_one, mul_one]

/- English proof (translation)
By extensionality, compare the relevant components. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem wa_rW : wa d R ≫ rW d R = 𝟙 _ := by
  ext n U f
  revert f; intro (f : U.unop ⟶ Spec (CommRingCat.of (AP d R)))
  change toS (rhom ((cW (((wa d R).app n).app U f)).obj 0) (ofS (sW (((wa d R).app n).app U f)))) = f
  have hc : cW (((wa d R).app n).app U f) = ((Wpt (wvec1 (MvPolynomial.X : Fin d → AP d R))).app n).app U f :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app (prod.lift_fst (Wpt (wvec1 (MvPolynomial.X : Fin d → AP d R))) (spMap (MvPolynomial.C : R →+* AP d R))) n) U) f
  have hs : sW (((wa d R).app n).app U f) = f ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* AP d R)) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app (prod.lift_snd (Wpt (wvec1 (MvPolynomial.X : Fin d → AP d R))) (spMap (MvPolynomial.C : R →+* AP d R))) n) U) f
  have hv : (cW (((wa d R).app n).app U f)).obj 0 =
      (WVec.map d (f : U.unop ⟶ Spec (CommRingCat.of (AP d R)))).obj (wvec1 (MvPolynomial.X : Fin d → AP d R)) :=
    congrArg (fun c : ComposableArrows (WVec d U.unop) n.unop.len => c.obj 0) hc
  rw [hv, hs, ofS_comp_spec]
  conv_rhs => rw [← toS_ofS f]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro a; simp [rhom]
  · intro k
    rw [rhom, MvPolynomial.eval₂Hom_X', ratio_map, ratio_wvec1]
    rfl

/- English proof (translation)
By extensionality, compare the relevant components. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem gW_fW : gW d R ≫ yoneda.map (fW d R) = (rW d R).app (op (SimplexCategory.mk 0)) := by
  ext U w
  change toS (ghom ((cW w).obj 0) (ofS (sW w))) ≫ fW d R = toS (rhom ((cW w).obj 0) (ofS (sW w)))
  rw [fW, toS_comp_spec, ghom_C]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem gW_inj (n : ℕ) (U : Scheme.{0}ᵒᵖ) (x x' : ((W d R).obj (op (SimplexCategory.mk n))).obj U)
    (h : ∀ i, (gW d R).app U (((W d R).map (vtx n i).op).app U x) =
      (gW d R).app U (((W d R).map (vtx n i).op).app U x')) : x = x' := by
  have key : ∀ i, ghom ((cW x).obj i) (ofS (sW x)) = ghom ((cW x').obj i) (ofS (sW x')) := by
    intro i
    have := h i
    change toS (ghom ((cW (((W d R).map (vtx n i).op).app U x)).obj 0) (ofS (sW (((W d R).map (vtx n i).op).app U x)))) =
      toS (ghom ((cW (((W d R).map (vtx n i).op).app U x')).obj 0) (ofS (sW (((W d R).map (vtx n i).op).app U x')))) at this
    rw [cW_natn, cW_natn, sW_natn, sW_natn] at this
    exact toS_inj this
  have hs : ofS (sW x) = ofS (sW x') := by
    have := congrArg (fun φ => (φ.comp LaurentPolynomial.C).comp MvPolynomial.C) (key 0)
    simpa only [ghom_C, rhom, MvPolynomial.eval₂Hom_comp_C] using this
  have hobj : ∀ i, (cW x).obj i = (cW x').obj i := by
    intro i
    apply wvec_ext
    · have := congrArg (fun φ => φ (LaurentPolynomial.T 1)) (key i)
      simpa only [weighted_vector_laurent_eval_hom_T_one] using this
    · funext k
      have := RingHom.congr_fun (congrArg (fun φ => φ.comp LaurentPolynomial.C) (key i)) (MvPolynomial.X k)
      simpa only [ghom_C, rhom, MvPolynomial.eval₂Hom_X'] using this
  have hc : cW x = cW x' := ComposableArrows.ext hobj (fun _ _ => Subsingleton.elim _ _)
  have hs' : sW x = sW x' := by rw [← toS_ofS (sW x), hs, toS_ofS]
  exact pr_ext _ U x x' hc hs'

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem mul_eq_mul_unit_inv_mul_mul_of_isUnit {S : Type} [CommRing S] (p q c : S) (hq : IsUnit q) : p * c = p * ↑hq.unit⁻¹ * (q * c) := by
  rw [mul_assoc, ← mul_assoc _ q, IsUnit.val_inv_mul, one_mul]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression.

Establish an intermediate fact. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem gW_surj (n : ℕ) (U : Scheme.{0}ᵒᵖ)
    (y : Fin (n + 1) → (yoneda.obj (Spec (CommRingCat.of (LaurentPolynomial (AP d R))))).obj U)
    (z : (yoneda.obj (Spec (CommRingCat.of (AP d R)))).obj U)
    (hy : ∀ i, (yoneda.map (fW d R)).app U (y i) = z) :
    ∃ x, ∀ i, (gW d R).app U (((W d R).map (vtx n i).op).app U x) = y i := by
  have hC : ∀ i, (ofS (y i)).comp LaurentPolynomial.C = ofS z := fun i => by
    rw [← ofS_comp_spec]; exact congrArg ofS (hy i)
  let t : Fin (n + 1) → Γ(U.unop, ⊤) := fun i => ofS (y i) (LaurentPolynomial.T 1)
  have ht : ∀ i, IsUnit (t i) := fun i => (LaurentPolynomial.isUnit_T 1).map (ofS (y i))
  let e : Fin (d + 1) → Γ(U.unop, ⊤) := Fin.cons 1 (fun k => ofS z (MvPolynomial.X k))
  have hu : ∀ i, IsUnit (t i * e 0) := fun i => by
    simp only [e, Fin.cons_zero, mul_one]; exact ht i
  let v : Fin (n + 1) → WVec d U.unop := fun i =>
    ⟨⟨fun l => t i * e l, fun p => ⟨0, Nat.zero_le _, by rw [Scheme.basicOpen_of_isUnit _ (hu i)]; trivial⟩⟩, hu i⟩
  let ms : ∀ j : Fin n, v j.castSucc ⟶ v j.succ := fun j =>
    ⟨(ht j.castSucc).unit * (ht j.succ).unit⁻¹, fun l => by
      rw [Units.val_mul, IsUnit.unit_spec]; exact mul_eq_mul_unit_inv_mul_mul_of_isUnit _ _ _ (ht j.succ)⟩
  let chain : ComposableArrows (WVec d U.unop) n := ComposableArrows.mkOfObjOfMapSucc v ms
  obtain ⟨w, hw1, hw2⟩ := pr_mk (X := Wsp d) (Y := sp R) (op (SimplexCategory.mk n)) U chain
    (z ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* AP d R)))
  refine ⟨w, fun i => ?_⟩
  have e1 : cW w = chain := hw1
  have e2 : sW w = z ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* AP d R)) := hw2
  change toS (ghom ((cW (((W d R).map (vtx n i).op).app U w)).obj 0) (ofS (sW (((W d R).map (vtx n i).op).app U w)))) = y i
  rw [cW_natn, sW_natn, e1, e2, ofS_comp_spec]
  change toS (ghom (v i) ((ofS z).comp MvPolynomial.C)) = y i
  conv_rhs => rw [← toS_ofS (y i)]
  congr 1
  apply laurent_ext
  · rw [ghom_C, hC i]
    apply MvPolynomial.ringHom_ext
    · intro a; simp [rhom]
    · intro k
      rw [rhom, MvPolynomial.eval₂Hom_X']
      apply ratio_unique
      change ofS z (MvPolynomial.X k) * (t i * e 0) = t i * e k.succ
      simp only [e, Fin.cons_zero, Fin.cons_succ]; ring
  · rw [weighted_vector_laurent_eval_hom_T_one]
    change t i * e 0 = t i
    simp only [e, Fin.cons_zero, mul_one]

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart.ExcisionChartRatio

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem LeafWData_of : LeafWData := by
  intro d R _
  exact ⟨ExcisionChartRatio.rW d R, ExcisionChartRatio.gW d R, ExcisionChartRatio.wa_rW, ExcisionChartRatio.gW_fW, ExcisionChartRatio.gW_inj, ExcisionChartRatio.gW_surj⟩

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
