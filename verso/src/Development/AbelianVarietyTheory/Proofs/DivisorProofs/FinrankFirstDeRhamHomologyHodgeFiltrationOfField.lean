import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_HdR_Fil_of_field (HF : GlobalTheory.Published.AbelianDeRham.Free)
    (HH : GlobalTheory.Published.AbelianDeRham.Hodge) (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    FiniteDimensional k (HdR A) ∧ Module.finrank k (HdR A) = 2 * g ∧
      Module.finrank k (Fil A) = g := by
  obtain ⟨hfin, -, hrk⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim HF hA hg
  obtain ⟨-, -, hfin1, -, hrk1⟩ := HH k A g hA hg
  have p : PrimeSpectrum k := IsLocalRing.closedPoint k
  have h1 : Module.finrank k (primDR A) = 2 * g := by
    have := hrk p
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have h2 : Module.finrank k (PrimitiveSubmodule A) = g := by
    have := hrk1 p
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have hd : Module.finrank k (HdR A) = 2 * g := by
    change Module.finrank k (Module.Dual k (primDR A)) = 2 * g
    rw [Subspace.dual_finrank_eq, h1]
  refine ⟨?_, hd, ?_⟩
  · change FiniteDimensional k (Module.Dual k (primDR A))
    infer_instance
  · have := Subspace.finrank_add_finrank_dualAnnihilator_eq (PrimitiveSubmodule A)
    rw [h2, h1] at this
    change Module.finrank k (PrimitiveSubmodule A).dualAnnihilator = g
    omega

end GlobalTheory
