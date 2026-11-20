import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineOpenSpreadStalkLieEigenspaceFrameStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfConjEqOne
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NearFrame

/- English proof (translation)
The claim follows from `RingHom.ext fun x => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])`.
-/
theorem dualMap_comp_near {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) :=
  RingHom.ext fun x => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Z F _ e σ X j f₀ Eb A₀ hj hT y A hA`. Take `⟨φz, fz, hx0, hφ0, hv0⟩` from `hT.2 (under y) A hA`. Establish `inj` using `IsFractionRing.injective (X.X.presheaf.stalk (under y)) X.X.functionField`. Establish `hgen : spMap (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField) ≫ stalkPt X (under y) = genericPt X` using `Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes _)`. Establish `hstr : stalkPt X (under y) ≫ j ≫ genStr Z = spMap φz`.

Take `⟨p, hp⟩` from `Spec.map_surjective (stalkPt X (under y) ≫ j ≫ genStr Z)`. Establish `h1 : (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField).comp p.hom = (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField).comp φz`. Use `EigLoc.spMap_inj ?_` and prove the remaining obligations. Rewrite using `[← hφ0, ← TieBase.genericPt_str e X j hj, TieBase.spMap_trans, ← hgen]`. Use `show _ ≫ Spec.map p = _`.

Rewrite using `[hp]`. Simplify using `only [Category.assoc]`. Establish `h2 : p.hom = φz` using `RingHom.ext fun a => inj (RingHom.congr_fun h1 a)`. Rewrite using `[← hp, ← h2]`. Both sides reduce to the same expression.

Take `⟨W, hW, φ, fW, hz, -, hWstr, hmap⟩` from `GlobalTheory.T.exists_affineOpen_spread_stalk_lieEigenspaceFrame E H Dw l Xo c O β Z F X j (under y) φz fz ⊤ trivial hstr`. Establish `hgerm : spMap (X.X.presheaf.germ W (under y) hz).hom ≫ (show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) = stalkPt X (under y)` using `hW.fromSpecStalk_eq_fromSpecStalk hz`. Establish `hφz : φz = (X.X.presheaf.germ W (under y) hz).hom.comp φ`. Use `EigLoc.spMap_inj ?_` and prove the remaining obligations. Rewrite using `[TieBase.spMap_trans, ← hstr, ← hWstr, ← hgerm]`.

Simplify using `only [Category.assoc]`. Use `⟨W, hW, φ, fW, mem_ptsIn.2 hz, fun y' hy' => ?_⟩` and prove the remaining obligations. Establish `hz' : under y' ∈ W` using `mem_ptsIn.1 hy'`. Establish `hp' : spMap (evHom hy') ≫ (show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) = y'.1` using `Points.specMap_valMap_fromSpec hW y'.1 hy'`. Establish `ha : (evHom hy').comp φ = σ`.

Use `EigLoc.spMap_inj ?_` and prove the remaining obligations. Rewrite using `[TieBase.spMap_trans, ← hWstr, ← (cxOf e σ hj y').2]`. Use `show _ = (y'.1 ≫ j) ≫ genStr Z`. Rewrite using `[← hp']`. Simplify using `only [Category.assoc]`.

Use `⟨ha, ?_⟩` and prove the remaining obligations. Take `⟨g, hg⟩` from `EigFrame.exists_isMap fW (evHom hy') (φ' := σ) (x' := (cxOf e σ hj y').1 ≫ genι Z) ha.symm (by show (y'.1 ≫ j) ≫ genι Z = _`. Rewrite using `[← hp']`. Simplify using `only [Category.assoc])`. Use `⟨g, ?_, hg⟩` and prove the remaining obligations.

Set `germ'` to `(X.X.presheaf.germ W (under y') hz').hom`. Set `χ : X.X.presheaf.stalk (under y') →+* ℂ` to `(Scheme.stalkClosedPointTo (R := .of ℂ) y'.1).hom`. Establish `hχ : χ.comp germ' = evHom hy'` using `by show _ = (Points.valMap y'.1 W hy').hom`. Rewrite using `[← CommRingCat.hom_comp]`. Use `congr 1`.

Rewrite using `[Scheme.germ_stalkClosedPointTo]`. Both sides reduce to the same expression. Establish `hgerm' : spMap germ' ≫ (show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) = stalkPt X (under y')` using `hW.fromSpecStalk_eq_fromSpecStalk hz'`. Take `⟨fz', hfz'⟩` from `EigFrame.exists_isMap fW germ' (φ' := germ'.comp φ) (x' := stalkPt X (under y') ≫ j ≫ genι Z) rfl (by rw [← hgerm']; simp only [Category.assoc])`. Establish `hκ : (algebraMap (X.X.presheaf.stalk (under y')) X.X.functionField).comp germ' = (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField).comp (X.X.presheaf.germ W (under y) hz).hom` using `RingHom.ext fun a => (algebraMap_germ hz' a).trans (algebraMap_germ hz a).symm`.

Use `⟨germ'.comp φ, fz', χ, (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of ℂ) y'.1).symm, ⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hx0, ← hgerm, ← hgerm']`. Simplify using `only [← Category.assoc]`. Rewrite using `[← TieBase.spMap_trans, ← TieBase.spMap_trans, hκ]`. Rewrite using `[hφ0, hφz, ← RingHom.comp_assoc, ← RingHom.comp_assoc, hκ]`.

Introduce `τ i`. Establish `e : (fun k => spMap (dualMap (algebraMap (X.X.presheaf.stalk (under y')) X.X.functionField)) ≫ fz'.v τ k) = fun k => spMap (dualMap (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField)) ≫ fz.v τ k`. Use function extensionality and compare the values at `k`. Rewrite using `[hfz' τ k, hmap τ k, ← Category.assoc, ← Category.assoc, ← TieBase.spMap_trans, ← TieBase.spMap_trans, ← dualMap_comp_near, ← dualMap_comp_near, hκ]`. Rewrite using `[e]`.

Conclude with `hv0 τ i`. Introduce `τ i`. Rewrite using `[hg τ i, hfz' τ i, ← Category.assoc, ← TieBase.spMap_trans, ← dualMap_comp_near, hχ]`.
-/
theorem exists_affine_frame_near : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str), Tied e X j f₀ Eb A₀ → ∀ (y : CxPts X.str (σ.comp e.toRingHom)), ∀ A ∈ Eb.S (under y), ∃ (W : X.X.Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(X.X, W)) (fW : EigFrame Z φ (((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genι Z)), y ∈ ptsIn X.str (σ.comp e.toRingHom) W ∧ ∀ y' (hy' : y' ∈ ptsIn X.str (σ.comp e.toRingHom) W), (evHom hy').comp φ = σ ∧ ∃ g : EigFrame Z σ ((cxOf e σ hj y').1 ≫ genι Z), FrameAt e f₀ A₀ A y' g ∧ fW.IsMap (evHom hy') g := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ X j f₀ Eb A₀ hj hT y A hA
  obtain ⟨φz, fz, hx0, hφ0, hv0⟩ := hT.2 (under y) A hA
  have inj := IsFractionRing.injective (X.X.presheaf.stalk (under y)) X.X.functionField
  have hgen : spMap (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField) ≫ stalkPt X (under y) = genericPt X :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes _)
  have hstr : stalkPt X (under y) ≫ j ≫ genStr Z = spMap φz := by
    obtain ⟨p, hp⟩ := Spec.map_surjective (stalkPt X (under y) ≫ j ≫ genStr Z)
    have h1 : (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField).comp p.hom =
        (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField).comp φz := by
      refine EigLoc.spMap_inj ?_
      rw [← hφ0, ← TieBase.genericPt_str e X j hj, TieBase.spMap_trans, ← hgen]
      show _ ≫ Spec.map p = _
      rw [hp]
      simp only [Category.assoc]
    have h2 : p.hom = φz := RingHom.ext fun a => inj (RingHom.congr_fun h1 a)
    rw [← hp, ← h2]
    rfl
  obtain ⟨W, hW, φ, fW, hz, -, hWstr, hmap⟩ := GlobalTheory.T.exists_affineOpen_spread_stalk_lieEigenspaceFrame E H Dw l Xo c O β Z F X j (under y) φz fz ⊤ trivial hstr
  have hgerm : spMap (X.X.presheaf.germ W (under y) hz).hom ≫ (show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) =
      stalkPt X (under y) := hW.fromSpecStalk_eq_fromSpecStalk hz
  have hφz : φz = (X.X.presheaf.germ W (under y) hz).hom.comp φ := by
    refine EigLoc.spMap_inj ?_
    rw [TieBase.spMap_trans, ← hstr, ← hWstr, ← hgerm]
    simp only [Category.assoc]
  refine ⟨W, hW, φ, fW, mem_ptsIn.2 hz, fun y' hy' => ?_⟩
  have hz' : under y' ∈ W := mem_ptsIn.1 hy'
  have hp' : spMap (evHom hy') ≫ (show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) = y'.1 :=
    Points.specMap_valMap_fromSpec hW y'.1 hy'
  have ha : (evHom hy').comp φ = σ := by
    refine EigLoc.spMap_inj ?_
    rw [TieBase.spMap_trans, ← hWstr, ← (cxOf e σ hj y').2]
    show _ = (y'.1 ≫ j) ≫ genStr Z
    rw [← hp']
    simp only [Category.assoc]
  refine ⟨ha, ?_⟩
  obtain ⟨g, hg⟩ := EigFrame.exists_isMap fW (evHom hy') (φ' := σ) (x' := (cxOf e σ hj y').1 ≫ genι Z) ha.symm (by
    show (y'.1 ≫ j) ≫ genι Z = _
    rw [← hp']
    simp only [Category.assoc])
  refine ⟨g, ?_, hg⟩
  let germ' := (X.X.presheaf.germ W (under y') hz').hom
  let χ : X.X.presheaf.stalk (under y') →+* ℂ := (Scheme.stalkClosedPointTo (R := .of ℂ) y'.1).hom
  have hχ : χ.comp germ' = evHom hy' := by
    show _ = (Points.valMap y'.1 W hy').hom
    rw [← CommRingCat.hom_comp]
    congr 1
    rw [Scheme.germ_stalkClosedPointTo]
    rfl
  have hgerm' : spMap germ' ≫ (show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) = stalkPt X (under y') :=
    hW.fromSpecStalk_eq_fromSpecStalk hz'
  obtain ⟨fz', hfz'⟩ := EigFrame.exists_isMap fW germ' (φ' := germ'.comp φ)
    (x' := stalkPt X (under y') ≫ j ≫ genι Z) rfl (by rw [← hgerm']; simp only [Category.assoc])
  have hκ : (algebraMap (X.X.presheaf.stalk (under y')) X.X.functionField).comp germ' =
      (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField).comp (X.X.presheaf.germ W (under y) hz).hom :=
    RingHom.ext fun a => (algebraMap_germ hz' a).trans (algebraMap_germ hz a).symm
  refine ⟨germ'.comp φ, fz', χ, (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of ℂ) y'.1).symm, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hx0, ← hgerm, ← hgerm']
    simp only [← Category.assoc]
    rw [← TieBase.spMap_trans, ← TieBase.spMap_trans, hκ]
  · rw [hφ0, hφz, ← RingHom.comp_assoc, ← RingHom.comp_assoc, hκ]
  · intro τ i
    have e : (fun k => spMap (dualMap (algebraMap (X.X.presheaf.stalk (under y')) X.X.functionField)) ≫ fz'.v τ k) =
        fun k => spMap (dualMap (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField)) ≫ fz.v τ k := by
      funext k
      rw [hfz' τ k, hmap τ k, ← Category.assoc, ← Category.assoc, ← TieBase.spMap_trans, ← TieBase.spMap_trans,
        ← dualMap_comp_near, ← dualMap_comp_near, hκ]
    rw [e]
    exact hv0 τ i
  · intro τ i
    rw [hg τ i, hfz' τ i, ← Category.assoc, ← TieBase.spMap_trans, ← dualMap_comp_near, hχ]

end GlobalTheory.NearFrame
