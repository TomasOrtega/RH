import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymMulPull

open GlobalTheory.MulPull

section Base

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Supply the required witnesses or components.
-/
theorem hasGen_theta (hC : GlobalTheory.Published.CubeTheorem) (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) :
    HasGen L (thφ A (x3 A)) thε := by
  have := hA.comm
  obtain ⟨t, ht⟩ := hC S A hA L hL _ (x3 A 0) (x3 A 1) (x3 A 2)
  obtain ⟨t', ht', -⟩ := exists_gen hL (φ' := thφ A (x3 A)) (ε' := thε) (fun U _ h => by
    have e := prod_cub (x3 A 0) (x3 A 1) (x3 A 2) h
    have i : lift (x3 A 0) (lift (x3 A 1) (x3 A 2)) = 𝟙 _ := by ext <;> simp [x3]
    rw [i] at e
    simp only [Over.id_left, Category.id_comp] at e
    rw [e, Fin.prod_univ_eight]
    simp only [Matrix.cons_val, zpow_one, zpow_neg]) t ht
  exact ⟨t', ht'⟩

end Base

end GlobalTheory.SymMulPull
