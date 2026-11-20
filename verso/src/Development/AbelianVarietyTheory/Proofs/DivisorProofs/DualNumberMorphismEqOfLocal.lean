import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DualMapSOfIdToRingHom
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

namespace GlobalTheory.ArLieBase

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Introduce `L _ s hs Y w w' h`. Establish `hs' : Ideal.span (Set.range (fun k : s => (TrivSqZeroExt.inl (k : L) : DualNumber L))) = ⊤`. Use `congrArg (Ideal.map (TrivSqZeroExt.inlHom L L)) hs` as an intermediate fact. Rewrite `this` using `[Ideal.map_span, Ideal.map_top, Set.image_eq_range]`. Conclude with `this`.

Set `𝒰` to `(Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of (DualNumber L)) _ hs').openCover`. Use `Scheme.Cover.hom_ext 𝒰 _ _ fun (k : s) => ?_` and prove the remaining obligations. Establish `hd : Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away (k : L))) = ReciprocityTheory.ChartRestriction.G.Chart.dAway (k : L)`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [Formalism.L2.Pj.dualMap, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]`.

Establish `e : 𝒰.f k = Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Chart.toL (k : L))) ≫ Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Chart.dAway (k : L)))`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, ReciprocityTheory.ChartRestriction.G.Chart.toL_comp]`. Both sides reduce to the same expression. Establish `hk` using `h k`. Rewrite `hk` using `[hd]`.

Rewrite using `[e, Category.assoc, Category.assoc]`. Conclude with `congrArg (_ ≫ ·) hk`.
-/
theorem hom_ext_dualNumber_away : ∀ {L : Type} [CommRing L] {s : Set L}, Ideal.span s = ⊤ → ∀ {Y : Scheme.{0}} {w w' : Sp (DualNumber L) ⟶ Y}, (∀ a : s, spMap (Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away (a : L)))) ≫ w = spMap (Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away (a : L)))) ≫ w') → w = w' := by
  intro L _ s hs Y w w' h
  have hs' : Ideal.span (Set.range (fun k : s => (TrivSqZeroExt.inl (k : L) : DualNumber L))) = ⊤ := by
    have := congrArg (Ideal.map (TrivSqZeroExt.inlHom L L)) hs
    rw [Ideal.map_span, Ideal.map_top, Set.image_eq_range] at this
    exact this
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of (DualNumber L)) _ hs').openCover
  refine Scheme.Cover.hom_ext 𝒰 _ _ fun (k : s) => ?_
  have hd : Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away (k : L))) =
      ReciprocityTheory.ChartRestriction.G.Chart.dAway (k : L) := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [Formalism.L2.Pj.dualMap, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]
  have e : 𝒰.f k = Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Chart.toL (k : L))) ≫
      Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Chart.dAway (k : L))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ReciprocityTheory.ChartRestriction.G.Chart.toL_comp]
    rfl
  have hk := h k
  rw [hd] at hk
  rw [e, Category.assoc, Category.assoc]
  exact congrArg (_ ≫ ·) hk

end GlobalTheory.ArLieBase
