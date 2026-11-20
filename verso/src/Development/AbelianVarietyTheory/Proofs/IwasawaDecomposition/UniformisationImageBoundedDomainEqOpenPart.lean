import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagComponentPointOverGeometricBasePoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentCarriesEveryFrameFlagStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentUniquePointEachFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMoebZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedComplexPointOfEigenFrameOffBoundary
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option autoImplicit false

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ`. Take `⟨hjo, hfj, -⟩` from `hL`. Establish `hm : Mono j` using `inferInstance`. Establish `hinj : Function.Injective (cxOf e σ hj)` using `fun a b h => Subtype.ext ((cancel_mono j).1 (congrArg Subtype.val h))`. Establish `hp0 : (U.X k).p0 = Dw.p + Dw.q - Dw.p` using `by rw [(hU.2.1 k).1]; omega`.

Establish `hmem : ∀ y : CxPts X.str (σ.comp e.toRingHom), y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j) ↔ ¬ LiesIn (cxOf e σ hj y) (genBd T.Z)`. Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce `h hb`. Establish `h1` using `h (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (Sp ℂ).Opens) from trivial)`.

Conclude with `h1 hb`. Introduce `h pt _`. Take `rfl : pt = IsLocalRing.closedPoint ℂ` from `Subsingleton.elim _ _`. Conclude with `h`. Use extensionality with `y`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, rfl⟩`. Take `⟨x, hx, hxv⟩` from `GlobalTheory.TrueCx.FrameOnto.frame_onto E (Dw.p + Dw.q) Dw.p (U.X k) (Nat.le_add_right _ _) (U.X k).Ψ (Equiv.refl _) hp0 (unflat v) hv`. Establish `hv' : v = flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x)`. Rewrite using `[hxv]`.

Both sides reduce to the same expression. Rewrite using `[hmem, hv', hψ ⟨x, hx⟩]`. Conclude with `not_liesIn_cxPt (Z := T.Z) _`. Introduce `hy`. Rewrite `hy` using `[hmem]`.

Take `⟨g⟩` from `GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β T.Z ℂ σ (cxOf e σ hj y).1 (cxOf e σ hj y).2`. Take `⟨q, hq, -⟩` from `exists_frPt_cxPt_of_eigFrame E H Dw l Xo c O β T.Z σ (cxOf e σ hj y) hy g`. Take `⟨k', x', t, hB⟩` from `hU.2.2.1 q`. Establish `hq' : cxPt T.Z (U.un k' x') = cxOf e σ hj y` using `(cxPt_congr hB.1.symm).trans hq`. Establish `hyχ : y.1 ≫ j ≫ genStr T.Z = spMap σ`.

Establish `h2` using `(cxOf e σ hj y).2`. Simplify `h2` using `[cxOf, Category.assoc]`. Take `⟨p, hp⟩` from `GlobalTheory.FlagCptBase.exists_pt_over_base E H Dw l Xo c O β T.Z F e σ (Dw.p + Dw.q) U Φ k X j hjo hj f hfj (GlobalTheory.T.flagSpaceComponent_carries_every_frame_flag E H Dw l Xo c O β T.Z F e σ (Dw.p + Dw.q) U Φ) (fun i K _ χ p h => GlobalTheory.CarryAll.carry_some E H Dw l X …`. Set `s : Sp (CAt σ)` to `IsLocalRing.closedPoint ℂ`. Take `⟨w', hw'⟩` from `Φ.label k' x' s`.

Establish `hkk : k = k'`. Use `GlobalTheory.FlagCptBase.eq_of_apply_eq Φ (GlobalTheory.T.flagSpaceComponent_carries_every_frame_flag E H Dw l Xo c O β T.Z F e σ (Dw.p + Dw.q) U Φ) (fun i K _ χ p h => GlobalTheory.CarryAll.carry_some E H Dw l Xo c O β T.Z F e (Φ.C i) K χ p h) (p s) w' ?_` and prove the remaining obligations. Rewrite using `[hw']`. Establish `h3 : (GlobalTheory.AllWt.ptF (U.un k' x') ≫ T.Z.jQ) = (cxOf e σ hj y).1` using `congrArg Subtype.val hq'`. Rewrite using `[h3]`.

Use `show (Φ.C k).π (p s) = (y.1 ≫ j) s`. Rewrite using `[← hp, ← hfj]`. Both sides reduce to the same expression. Substitute `hkk` using the available equality. Use `⟨flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x'.1), ?_, hinj ?_⟩` and prove the remaining obligations.

Conclude with `GlobalTheory.TrueCx.domPt_mem (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) hp0 x'.2`. Rewrite using `[hψ x', hq']`.
-/
theorem GlobalTheory.UnifImage.image_domFlat_eq_ptsIn_openPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ψ '' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) = ptsIn X.str (σ.comp e.toRingHom) (openPart j) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  obtain ⟨hjo, hfj, -⟩ := hL
  have hm : Mono j := inferInstance
  have hinj : Function.Injective (cxOf e σ hj) := fun a b h =>
    Subtype.ext ((cancel_mono j).1 (congrArg Subtype.val h))
  have hp0 : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by rw [(hU.2.1 k).1]; omega
  have hmem : ∀ y : CxPts X.str (σ.comp e.toRingHom),
      y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j) ↔ ¬ LiesIn (cxOf e σ hj y) (genBd T.Z) := by
    intro y
    constructor
    · intro h hb
      have h1 := h (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (Sp ℂ).Opens) from trivial)
      exact h1 hb
    · intro h pt _
      obtain rfl : pt = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
      exact h
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨x, hx, hxv⟩ := GlobalTheory.TrueCx.FrameOnto.frame_onto E (Dw.p + Dw.q) Dw.p (U.X k) (Nat.le_add_right _ _)
      (U.X k).Ψ (Equiv.refl _) hp0 (unflat v) hv
    have hv' : v = flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x) := by
      rw [hxv]; rfl
    rw [hmem, hv', hψ ⟨x, hx⟩]
    exact not_liesIn_cxPt (Z := T.Z) _
  · intro hy
    rw [hmem] at hy
    obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β T.Z ℂ σ (cxOf e σ hj y).1 (cxOf e σ hj y).2
    obtain ⟨q, hq, -⟩ := exists_frPt_cxPt_of_eigFrame E H Dw l Xo c O β T.Z σ (cxOf e σ hj y) hy g
    obtain ⟨k', x', t, hB⟩ := hU.2.2.1 q
    have hq' : cxPt T.Z (U.un k' x') = cxOf e σ hj y := (cxPt_congr hB.1.symm).trans hq
    have hyχ : y.1 ≫ j ≫ genStr T.Z = spMap σ := by
      have h2 := (cxOf e σ hj y).2
      simpa [cxOf, Category.assoc] using h2
    obtain ⟨p, hp⟩ := GlobalTheory.FlagCptBase.exists_pt_over_base E H Dw l Xo c O β T.Z F e σ (Dw.p + Dw.q) U Φ k X j hjo hj f hfj
      (GlobalTheory.T.flagSpaceComponent_carries_every_frame_flag E H Dw l Xo c O β T.Z F e σ (Dw.p + Dw.q) U Φ)
      (fun i K _ χ p h => GlobalTheory.CarryAll.carry_some E H Dw l Xo c O β T.Z F e (Φ.C i) K χ p h) ℂ σ y.1 hyχ
    let s : Sp (CAt σ) := IsLocalRing.closedPoint ℂ
    obtain ⟨w', hw'⟩ := Φ.label k' x' s
    have hkk : k = k' := by
      refine GlobalTheory.FlagCptBase.eq_of_apply_eq Φ (GlobalTheory.T.flagSpaceComponent_carries_every_frame_flag E H Dw l Xo c O β T.Z F e σ (Dw.p + Dw.q) U Φ)
        (fun i K _ χ p h => GlobalTheory.CarryAll.carry_some E H Dw l Xo c O β T.Z F e (Φ.C i) K χ p h) (p s) w' ?_
      rw [hw']
      have h3 : (GlobalTheory.AllWt.ptF (U.un k' x') ≫ T.Z.jQ) = (cxOf e σ hj y).1 := congrArg Subtype.val hq'
      rw [h3]
      show (Φ.C k).π (p s) = (y.1 ≫ j) s
      rw [← hp, ← hfj]
      rfl
    subst hkk
    refine ⟨flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x'.1), ?_, hinj ?_⟩
    · exact GlobalTheory.TrueCx.domPt_mem (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) hp0 x'.2
    · rw [hψ x', hq']
