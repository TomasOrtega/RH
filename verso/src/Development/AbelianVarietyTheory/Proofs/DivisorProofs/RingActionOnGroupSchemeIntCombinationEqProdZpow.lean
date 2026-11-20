import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory.ActSum

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem act_sum_zsmul : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (O : Type) [Ring O] (act : O → (A ⟶ A)), IsRAct A act → ∀ (r : ℕ) (e : Fin r → O) (c : Fin r → ℤ), act (∑ k, c k • e k) = ∏ k, act (e k) ^ c k := by
  intro S A _ _ O _ act h r e c
  let f : Multiplicative O →* (A ⟶ A) := MonoidHom.mk' (fun a => act (Multiplicative.toAdd a)) (fun a b => h.2.2.2 _ _)
  have key : ∀ x : O, act x = f (Multiplicative.ofAdd x) := fun x => rfl
  rw [key, ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [ofAdd_zsmul, map_zpow]
  rfl

end GlobalTheory.ActSum
