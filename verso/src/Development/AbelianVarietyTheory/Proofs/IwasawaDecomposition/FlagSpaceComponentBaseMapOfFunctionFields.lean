import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyFlagRefinementBundleOfGoodModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Z F _ e C X j _ hj f hf hl`. Establish `hs : f ≫ X.str = C.Y.str`. Rewrite using `[← hj, ← C.π_str, ← hf, Category.assoc]`. Set `K : Type` to `AlgebraicClosure X.Fn`. Set `a : X.Fn →+* K` to `algebraMap X.Fn K`.

Set `x : Sp K ⟶ X.X` to `spMap a ≫ genericPt X`. Establish `h1 : genericPt X ≫ X.str = spMap (algebraMap F X.Fn)` using `(ratOf X).pt_s`. Establish `h2 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _`. Rewrite using `[← Spec.map_comp]`. Conclude with `(congrArg Spec.map (CommRingCat.hom_ext (RingEquiv.toRingHom_comp_symm_toRingHom e))).trans (Spec.map_id _)`.

Establish `hg0 : (genericPt X ≫ j) ≫ genStr Z = spMap (constF e X)`. Establish `: spMap (constF e X) = spMap (algebraMap F X.Fn) ≫ spMap e.symm.toRingHom`. Rewrite using `[constF, ← Spec.map_comp]`. Both sides reduce to the same expression. Rewrite using `[this, ← h1, ← hj]`.

Simplify using `only [Category.assoc, h2, Category.comp_id]`. Set `χ : c.F →+* K` to `a.comp (constF e X)`. Establish `hx : (x ≫ j) ≫ genStr Z = spMap χ`. Establish `: spMap χ = spMap a ≫ spMap (constF e X)` using `by rw [← Spec.map_comp]; rfl`. Rewrite using `[this, ← hg0]`.

Simplify using `only [x, Category.assoc]`. Take `⟨g⟩` from `GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z K χ (x ≫ j) hx`. Rewrite `g`, `hx` using `[Category.assoc]`. Take `⟨p, ⟨hp, -⟩, -⟩` from `hl K χ x hx g`. Establish `hpt : f (p (IsLocalRing.closedPoint K)) = genericPoint X.X`.

Establish `hc : (p ≫ f) (IsLocalRing.closedPoint K) = f (p (IsLocalRing.closedPoint K))` using `Scheme.Hom.comp_apply _ _ _`. Rewrite using `[← hc, hp]`. Use `show (ratOf X).pt (spMap a (IsLocalRing.closedPoint K)) = _`. Conclude with `(ratOf X).pt_apply _`. Establish `hsp : f (genericPoint C.Y.X) ⤳ genericPoint X.X` using `hpt ▸ (genericPoint_specializes (p (IsLocalRing.closedPoint K))).map f.continuous`.

Conclude with `exists_isHom_of_generic (ratOf X) (ratOf C.Y) f hs (hsp.antisymm (genericPoint_specializes _)).eq`.
-/
theorem GlobalTheory.FlagBundle.exists_isHom_base_of_lifts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∃ φ : X.Fn →ₐ[F] C.Y.Fn, (ratOf X).IsHom (ratOf C.Y) φ f := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C X j _ hj f hf hl
  have hs : f ≫ X.str = C.Y.str := by
    rw [← hj, ← C.π_str, ← hf, Category.assoc]

  let K : Type := AlgebraicClosure X.Fn
  let a : X.Fn →+* K := algebraMap X.Fn K
  let x : Sp K ⟶ X.X := spMap a ≫ genericPt X
  have h1 : genericPt X ≫ X.str = spMap (algebraMap F X.Fn) := (ratOf X).pt_s
  have h2 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
    rw [← Spec.map_comp]
    exact (congrArg Spec.map (CommRingCat.hom_ext (RingEquiv.toRingHom_comp_symm_toRingHom e))).trans (Spec.map_id _)
  have hg0 : (genericPt X ≫ j) ≫ genStr Z = spMap (constF e X) := by
    have : spMap (constF e X) = spMap (algebraMap F X.Fn) ≫ spMap e.symm.toRingHom := by
      rw [constF, ← Spec.map_comp]; rfl
    rw [this, ← h1, ← hj]
    simp only [Category.assoc, h2, Category.comp_id]
  let χ : c.F →+* K := a.comp (constF e X)
  have hx : (x ≫ j) ≫ genStr Z = spMap χ := by
    have : spMap χ = spMap a ≫ spMap (constF e X) := by rw [← Spec.map_comp]; rfl
    rw [this, ← hg0]
    simp only [x, Category.assoc]
  obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z K χ (x ≫ j) hx
  rw [Category.assoc] at g hx
  obtain ⟨p, ⟨hp, -⟩, -⟩ := hl K χ x hx g

  have hpt : f (p (IsLocalRing.closedPoint K)) = genericPoint X.X := by
    have hc : (p ≫ f) (IsLocalRing.closedPoint K) = f (p (IsLocalRing.closedPoint K)) := Scheme.Hom.comp_apply _ _ _
    rw [← hc, hp]
    show (ratOf X).pt (spMap a (IsLocalRing.closedPoint K)) = _
    exact (ratOf X).pt_apply _
  have hsp : f (genericPoint C.Y.X) ⤳ genericPoint X.X :=
    hpt ▸ (genericPoint_specializes (p (IsLocalRing.closedPoint K))).map f.continuous
  exact exists_isHom_of_generic (ratOf X) (ratOf C.Y) f hs (hsp.antisymm (genericPoint_specializes _)).eq
