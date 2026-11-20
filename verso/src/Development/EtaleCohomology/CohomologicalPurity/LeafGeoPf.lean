import Development.EtaleCohomology.CohomologicalPurity.LeafThomCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.GeoPf

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem vec_map_comp {N k : ℕ} {Z Y X : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (v : Vec N k X) :
    (Vec.map N k (g ≫ f)).obj v = (Vec.map N k g).obj ((Vec.map N k f).obj v) := by
  apply Subtype.ext
  funext i
  change (g ≫ f).appTop.hom (v.1 i) = g.appTop.hom (f.appTop.hom (v.1 i))
  rw [Scheme.Hom.comp_appTop]
  rfl

/- English proof (translation)
By extensionality, compare the relevant components. Express the relevant assertion in an equivalent form by its definition. A detailed English derivation is pending.
-/
theorem sch_map_pt {N k : ℕ} {Y X : Scheme.{0}} (f : Y ⟶ X) (v : Vec N k X) :
    sch.map f ≫ Pj.pt v = Pj.pt ((Vec.map N k f).obj v) := by
  ext n U g
  change (Functor.const (Fin (n.unop.len + 1))).obj ((Vec.map N k (g ≫ f)).obj v) =
    (Functor.const (Fin (n.unop.len + 1))).obj ((Vec.map N k g).obj ((Vec.map N k f).obj v))
  exact congrArg (Functor.const (Fin (n.unop.len + 1))).obj (vec_map_comp (show U.unop ⟶ Y from g) f v)

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument.

Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Reduce the equality to equality of the corresponding arguments. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem part3 (d : ℕ) (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (x : Fin d → A) :
    spMap φ ≫ Pj.pt (vec1 x) = Pj.pt (vec1 (φ ∘ x)) := by
  change sch.map _ ≫ _ = _
  rw [sch_map_pt]
  congr 1
  apply Subtype.ext
  funext i
  change (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Fin.cons 1 x : Fin (d + 1) → A) i)) =
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ((Fin.cons 1 (φ ∘ x) : Fin (d + 1) → B) i)
  have key := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  have := congrArg (fun g => g.hom ((Fin.cons 1 x : Fin (d + 1) → A) i)) key
  refine this.symm.trans ?_
  change (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (φ ((Fin.cons 1 x : Fin (d + 1) → A) i)) = _
  congr 1
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem part2 (q N k : ℕ) (R : Type) [CommRing R] (hq : IsUnit (q : R)) : Inv q (PR N k R) := by
  intro U ⟨y⟩
  let f : U ⟶ Spec (CommRingCat.of R) := ((prod.snd : PR N k R ⟶ sp R).app _).app (op U) y
  have h := (hq.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).map f.appTop.hom
  rwa [map_natCast, map_natCast] at h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem comp_val {N k : ℕ} {U : Scheme.{0}} {a b c : Vec N k U} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).1 = g.1 * f.1 := rfl

/- English proof (translation)
Substitute using the available equality. Both sides reduce to the same expression.
-/
theorem eqToHom_val {N k : ℕ} {U : Scheme.{0}} {a b : Vec N k U} (e : a = b) : (eqToHom e).1 = 1 := by
  subst e; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem incl_map_val {N : ℕ} {U : Scheme.{0}} {a b : Vec N 1 U} (u : a ⟶ b) : ((Vec.incl N U).map u).1 = u.1 := rfl

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem incl_cancel {N : ℕ} {U : Scheme.{0}} {J : Type} [Category J] (F G : J ⥤ Vec N 1 U)
    (h : F ⋙ Vec.incl N U = G ⋙ Vec.incl N U) : F = G := by
  have hobj : ∀ j, F.obj j = G.obj j := fun j => Subtype.ext (by have := congrArg Subtype.val (Functor.congr_obj h j); exact this)
  refine CategoryTheory.Functor.ext hobj (fun a b f => ?_)
  apply Subtype.ext
  have h2 := congrArg Subtype.val (Functor.congr_hom h f)
  simp only [Functor.comp_map, comp_val, eqToHom_val, incl_map_val, mul_one, one_mul] at h2 ⊢
  exact h2

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem incl_mono (N : ℕ) : Mono (Pj.incl N) := by
  have : ∀ n, Mono ((Pj.incl N).app n) := fun n => by
    have : ∀ U, Mono (((Pj.incl N).app n).app U) := fun U => by
      rw [mono_iff_injective]
      intro F G h
      exact incl_cancel (U := U.unop) F G h
    exact NatTrans.mono_of_mono_app _
  exact NatTrans.mono_of_mono_app _

/- English proof (translation)
Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. A detailed English derivation is pending.
-/
theorem part1 (d : ℕ) (R : Type) [CommRing R] : Mono (pr d R).hom := by
  have := incl_mono (d + 1)
  change Mono (prod.map _ _)
  infer_instance

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pt_incl {N : ℕ} {X : Scheme.{0}} (v : Vec N 1 X) :
    Pj.pt v ≫ Pj.incl N = Pj.pt ((Vec.incl N X).obj v) := rfl

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction.

Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem part4 (d : ℕ) (A : Type) [CommRing A] (I : Ideal A) (x : Fin d → A) (hI : Ideal.span (Set.range x) = I) :
    ∃ Φ : opn (off A I) ⟶ pr d A, Φ.right = chart x := by
  let w : Vec (d + 1) 1 (off A I).toScheme := ⟨((Vec.map (d + 1) 0 (off A I).ι).obj (vec1 x)).1, fun p => by
    have hp : ¬ (Ideal.span (Set.range x) ≤ ((off A I).ι p).asIdeal) := by rw [hI]; exact p.2
    rw [Ideal.span_le] at hp
    obtain ⟨j, hj⟩ : ∃ j, x j ∉ ((off A I).ι p).asIdeal := by
      by_contra hc
      push Not at hc
      exact hp (by rintro _ ⟨j, rfl⟩; exact hc j)
    refine ⟨j.succ, by simp, ?_⟩
    change p ∈ (off A I).toScheme.basicOpen ((off A I).ι.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Fin.cons 1 x : Fin (d + 1) → A) j.succ)))
    rw [← Scheme.preimage_basicOpen_top]
    change (off A I).ι p ∈ (Spec (CommRingCat.of A)).basicOpen _
    rw [basicOpen_eq_of_affine]
    simp only [Fin.cons_succ]
    exact hj⟩
  refine ⟨Arrow.homMk (prod.lift (Pj.pt w) (sch.map (off A I).ι)) (chart x) ?_, rfl⟩
  apply prod.hom_ext
  · change prod.lift (Pj.pt w) (sch.map (off A I).ι) ≫ prod.map (Pj.incl (d + 1)) (𝟙 _) ≫ prod.fst =
      sch.map (off A I).ι ≫ chart x ≫ prod.fst
    rw [prod.map_fst, prod.lift_fst_assoc, chart, prod.lift_fst, pt_incl, sch_map_pt]
    rfl
  · change prod.lift (Pj.pt w) (sch.map (off A I).ι) ≫ prod.map (Pj.incl (d + 1)) (𝟙 _) ≫ prod.snd =
      sch.map (off A I).ι ≫ chart x ≫ prod.snd
    rw [prod.map_snd, prod.lift_snd_assoc, chart, prod.lift_snd]

end LateralTheory.CohomologicalPurity.Thom.GeoPf

namespace LateralTheory.CohomologicalPurity.Thom

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem LeafGeo_of : LeafGeo :=
  ⟨GeoPf.part1, GeoPf.part2, GeoPf.part3, GeoPf.part4⟩

end LateralTheory.CohomologicalPurity.Thom

namespace LateralTheory.CohomologicalPurity.Thom.GeoPf

end LateralTheory.CohomologicalPurity.Thom.GeoPf
