import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FreeHom

variable {R : Type} [CommRing R]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_eq {P : PSh} {G : Shv R} (s : (free R).obj P ⟶ G) (U : Scheme.{0}) (x : P.obj (op U)) :
    val s U x = ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom).app (op U)).hom
      (ModuleCat.freeMk (ULift.up x)) := rfl

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. A detailed English derivation is pending.
-/
theorem freePresheaf_map_freeMk (P : PSh) {U V : Scheme.{0}ᵒᵖ} (g : U ⟶ V) (x : P.obj U) :
    (((freeP R).obj P).map g).hom (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (P.map g x)) := by
  change ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map (P.map g))).hom (ModuleCat.freeMk (ULift.up x)) = _
  exact ModuleCat.free_map_apply _ _

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. A detailed English derivation is pending.
-/
theorem freePresheaf_map_app_freeMk {P P' : PSh} (f : P' ⟶ P) (U : Scheme.{0}ᵒᵖ) (x : P'.obj U) :
    (((freeP R).map f).app U).hom (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (f.app U x)) := by
  change ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map (f.app U))).hom (ModuleCat.freeMk (ULift.up x)) = _
  exact ModuleCat.free_map_apply _ _

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem ext {P : PSh} {G : Shv R} (s s' : (free R).obj P ⟶ G) (h : ∀ U x, val s U x = val s' U x) : s = s' := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ G.property
  apply NatTrans.ext
  funext U
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  have hx := h U.unop x
  rw [val_eq, val_eq] at hx
  exact hx

def descP (P : PSh) (G : Shv R) (φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hφ : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), φ V (P.map g.op x) = Sec.res g (φ U x)) :
    (freeP R).obj P ⟶ G.obj where
  app U := ModuleCat.freeDesc (TypeCat.ofHom fun x => φ U.unop x.down)
  naturality U V g := by
    apply ModuleCat.free_hom_ext
    rintro ⟨x⟩
    change (ModuleCat.freeDesc _).hom ((((freeP R).obj P).map g).hom (ModuleCat.freeMk (ULift.up x))) =
      (G.obj.map g).hom ((ModuleCat.freeDesc _).hom (ModuleCat.freeMk (ULift.up x)))
    rw [freePresheaf_map_freeMk]
    erw [ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact hφ V.unop U.unop g.unop x

def desc (P : PSh) (G : Shv R) (φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hφ : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), φ V (P.map g.op x) = Sec.res g (φ U x)) :
    (free R).obj P ⟶ G :=
  ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).symm (descP P G φ hφ)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem val_desc (P : PSh) (G : Shv R) (φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hφ : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), φ V (P.map g.op x) = Sec.res g (φ U x))
    (U : Scheme.{0}) (x : P.obj (op U)) : val (desc P G φ hφ) U x = φ U x := by
  rw [val_eq]
  have key : toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ (desc P G φ hφ).hom = descP P G φ hφ := by
    have hs := ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).apply_symm_apply
      (descP P G φ hφ)
    rw [Adjunction.homEquiv_unit] at hs
    exact hs
  rw [key]
  change (ModuleCat.freeDesc _).hom (ModuleCat.freeMk (ULift.up x)) = _
  erw [ModuleCat.freeDesc_apply]
  rfl

/- English proof (translation)
Chain the equalities or inequalities of the calculation.
-/
private theorem val_nat_lemma {P : PSh} {F : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (η : (freeP R).obj P ⟶ F)
    {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (η.app (op V)).hom (ModuleCat.freeMk (ULift.up (P.map g.op x))) =
      (F.map g.op).hom ((η.app (op U)).hom (ModuleCat.freeMk (ULift.up x))) :=
  calc (η.app (op V)).hom (ModuleCat.freeMk (ULift.up (P.map g.op x)))
      = (η.app (op V)).hom ((((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x))) :=
        congrArg (η.app (op V)).hom (freePresheaf_map_freeMk P g.op x).symm
    _ = _ := congrArg (fun k => k.hom (ModuleCat.freeMk (ULift.up x))) (η.naturality g.op)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem val_nat {P : PSh} {G : Shv R} (s : (free R).obj P ⟶ G) (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)) :
    val s V (P.map g.op x) = Sec.res g (val s U x) := by
  rw [val_eq, val_eq]
  exact val_nat_lemma _ g x

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
theorem val_free_map {P P' : PSh} (f : P' ⟶ P) {G : Shv R} (s : (free R).obj P ⟶ G) (U : Scheme.{0}) (x : P'.obj (op U)) :
    val ((free R).map f ≫ s) U x = val s U (f.app (op U) x) := by
  rw [val_eq, val_eq]
  have hn : toSheafify Scheme.etaleTopology ((freeP R).obj P') ≫ ((free R).map f ≫ s).hom
      = (freeP R).map f ≫ toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom :=
    (toSheafify_naturality_assoc Scheme.etaleTopology ((freeP R).map f) s.hom).symm
  rw [hn]
  change ((toSheafify _ _ ≫ s.hom).app (op U)).hom ((((freeP R).map f).app (op U)).hom (ModuleCat.freeMk (ULift.up x))) = _
  rw [freePresheaf_map_app_freeMk]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_comp {P : PSh} {G G' : Shv R} (s : (free R).obj P ⟶ G) (ψ : G ⟶ G') (U : Scheme.{0}) (x : P.obj (op U)) :
    val (s ≫ ψ) U x = Sec.map ψ (val s U x) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_add {P : PSh} {G : Shv R} (s s' : (free R).obj P ⟶ G) (U : Scheme.{0}) (x : P.obj (op U)) :
    val (s + s') U x = val s U x + val s' U x := rfl

def valHom (P : PSh) (G : Shv R) (U : Scheme.{0}) (x : P.obj (op U)) : ((free R).obj P ⟶ G) →+ Sec G U :=
  AddMonoidHom.mk' (fun s => val s U x) (fun s s' => val_add s s' U x)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem val_zsmul {P : PSh} {G : Shv R} (s : (free R).obj P ⟶ G) (m : ℤ) (U : Scheme.{0}) (x : P.obj (op U)) :
    val (m • s) U x = m • val s U x := by
  exact map_zsmul (valHom P G U x) m s

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem main : ∀ (R : Type) [CommRing R] (P : PSh) (G : Shv R), (∀ s s' : (free R).obj P ⟶ G, (∀ U x, val s U x = val s' U x) → s = s') ∧ (∀ φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), φ V (P.map g.op x) = Sec.res g (φ U x)) → ∃ s : (free R).obj P ⟶ G, ∀ U x, val s U x = φ U x) ∧ (∀ (s : (free R).obj P ⟶ G) (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), val s V (P.map g.op x) = Sec.res g (val s U x)) ∧ (∀ (P' : PSh) (f : P' ⟶ P) (s : (free R).obj P ⟶ G) U x, val ((free R).map f ≫ s) U x = val s U (f.app (op U) x)) ∧ (∀ (G' : Shv R) (ψ : G ⟶ G') (s : (free R).obj P ⟶ G) U x, val (s ≫ ψ) U x = Sec.map ψ (val s U x)) ∧ ∀ (s s' : (free R).obj P ⟶ G) (m : ℤ) U x, val (s + s') U x = val s U x + val s' U x ∧ val (m • s) U x = m • val s U x := by
  intro R _ P G
  exact ⟨fun s s' h => ext s s' h, fun φ hφ => ⟨desc P G φ hφ, val_desc P G φ hφ⟩,
    fun s V U g x => val_nat s V U g x, fun P' f s U x => val_free_map f s U x,
    fun G' ψ s U x => val_comp s ψ U x, fun s s' m U x => ⟨val_add s s' U x, val_zsmul s m U x⟩⟩

end GlobalTheory.EtC.FreeHom
