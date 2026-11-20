import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TorRef

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Y Z e he hY`. Use `haveI : IsIso (spMap (RingHom.id c.F)) := by`. Simplify using `only [spMap, CommRingCat.ofHom_id]`. Use `infer_instance`. Use `haveI : AlgebraicGeometry.IsReduced Y.X := by`.

Establish `: ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x)` using `fun x => by`. Use `(Y.normal x).1` as an intermediate fact. Use `infer_instance`. Conclude with `isReduced_of_isReduced_stalk Y.X`. Use `haveI : AlgebraicGeometry.IsReduced (gen Y) := isReduced_of_isOpenImmersion (genι Y)`.

Use `haveI : IsDominant Y.jQ := ⟨Y.jQ_dense⟩`. Establish `h1 : e.hom ≫ genStr Z = genStr Y`. Use `ext_of_isDominant_of_isSeparated (terminal.from _) (terminal.hom_ext _ _) Y.jQ ?_` and prove the remaining obligations. Rewrite using `[reassoc_of% he]`. Simplify using `only [genStr]`.

Rewrite using `[Z.jQ_over, Y.jQ_over]`. Establish `h2 : genStr Z = e.inv ≫ genStr Y` using `by rw [← h1, Iso.inv_hom_id_assoc]`. Rewrite using `[h2]`. Establish `h : SmoothOfRelativeDimension (0 + D.dim) (e.inv ≫ genStr Y)` using `inferInstance`. Simplify using `using h`.
-/
theorem smooth_genStr_of_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : GMod Xo c) (e : gen Y ≅ gen Z), Y.jQ ≫ e.hom = Z.jQ → SmoothOfRelativeDimension D.dim (genStr Y) → SmoothOfRelativeDimension D.dim (genStr Z) := by
  intro E _ _ _ H D l Xo c Y Z e he hY
  haveI : IsIso (spMap (RingHom.id c.F)) := by
    simp only [spMap, CommRingCat.ofHom_id]
    infer_instance
  haveI : AlgebraicGeometry.IsReduced Y.X := by
    have : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x => by
      have := (Y.normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk Y.X
  haveI : AlgebraicGeometry.IsReduced (gen Y) := isReduced_of_isOpenImmersion (genι Y)
  haveI : IsDominant Y.jQ := ⟨Y.jQ_dense⟩
  have h1 : e.hom ≫ genStr Z = genStr Y := by
    refine ext_of_isDominant_of_isSeparated (terminal.from _) (terminal.hom_ext _ _) Y.jQ ?_
    rw [reassoc_of% he]
    simp only [genStr]
    rw [Z.jQ_over, Y.jQ_over]
  have h2 : genStr Z = e.inv ≫ genStr Y := by rw [← h1, Iso.inv_hom_id_assoc]
  rw [h2]
  have h : SmoothOfRelativeDimension (0 + D.dim) (e.inv ≫ genStr Y) := inferInstance
  simpa using h

end GlobalTheory.TorRef
