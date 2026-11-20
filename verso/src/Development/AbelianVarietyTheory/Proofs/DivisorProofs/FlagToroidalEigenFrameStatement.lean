import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagToroidalEigenFrame
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellOpenLe
open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagToroidalEigenFrame.lean&line=215#L215)
-/
theorem _root_.GlobalTheory.T.flag_toroidal_eigen_frame : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N} (Φ : FlagTor Z e U) (k : U.Comp) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)} (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (u : Cell.Coord Dw → Γ((Φ.C k).Y.X, Cell.cellOpen (Φ.C k) hV f₀ w)), Cell.IsCoord (Φ.C k) hV f₀ w u → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p q : Spec (.of Ω) ⟶ (Cell.cellOpen (Φ.C k) hV f₀ w).toScheme), p ≫ Cell.cellMap (Φ.C k) hV f₀ w = q ≫ Cell.cellMap (Φ.C k) hV f₀ w → (∀ i, p.appTop (Cell.coordTop (Φ.C k) hV f₀ w u i) = q.appTop (Cell.coordTop (Φ.C k) hV f₀ w u i)) → p = q := by
  first | exact @GlobalTheory.ShFam.Cell.eq_of_cellMap_coords | exact GlobalTheory.ShFam.Cell.eq_of_cellMap_coords | (intros; apply GlobalTheory.ShFam.Cell.eq_of_cellMap_coords <;> assumption)
