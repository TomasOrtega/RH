import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.LiftComb

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Introduce a local definition for the expression.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem lift_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (K : Type) [CommRing K] (yy : Sp K ⟶ Xo'.XF c') (g : ℕ) (e : Fin g → (Sp (DualNumber K) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (yy ≫ Y.j) (e i)) → ∀ (cf : Fin g → K), ∃ w : Sp (DualNumber K) ⟶ Y.oF.t.G.left, IsCombAtG Y.t (yy ≫ Y.j) e cf (w ≫ Y.m.φ) := by
  intro E _ _ _ H Dw l' Xo' c' W Y K _ yy g e he cf
  have hε : ∀ c : K, spMap (epsMul c) ≫ spMap (algebraMap K (DualNumber K)) = spMap (algebraMap K (DualNumber K)) := by
    intro c
    unfold spMap
    rw [← Spec.map_comp]
    congr 1
    ext a
    · simp [epsMul]
    · simp [epsMul]
  let u : Fin g → (tEpsG (yy ≫ Y.j) ⟶ Y.t.G) := fun i => Over.homMk (spMap (epsMul (cf i)) ≫ e i) (by
      simp only [tEpsG, Over.mk_hom, Category.assoc]
      rw [(he i).1]
      simp only [← Category.assoc]
      rw [hε])
  have hv : ((List.ofFn u).prod).left ≫ Y.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ yy ≫ Y.j :=
    Over.w ((List.ofFn u).prod)
  have hc := Y.m.cart.1
  refine ⟨hc.lift ((List.ofFn u).prod).left (spMap (algebraMap K (DualNumber K)) ≫ yy) (by rw [Category.assoc]; exact hv), u, fun i => rfl, ?_⟩
  rw [hc.lift_fst]

end GlobalTheory.FlatModel.LiftComb
