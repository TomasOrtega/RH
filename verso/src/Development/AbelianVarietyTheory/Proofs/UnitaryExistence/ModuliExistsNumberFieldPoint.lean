import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ModuliExistsAlgebraicPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

/- English proof (translation)
Introduce `hN E _ _ _ H Dw l Xo c hr`. Take `⟨x⟩` from `(PeriodExists.typeFn_period_exist E H Dw).2.2 hN hr l Xo c`. Take `⟨L, _, _, hfin, y, hy, -⟩` from `moduli_exists_algebraic_point E H Dw l Xo c ⊤ ⟨x, trivial⟩`. Establish `: NumberField L` using `NumberField.of_module_finite c.F L`. Use `⟨L, inferInstance, this, algebraMap c.F L, y ≫ pullback.fst _ _, ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, hy]`. Simplify using `only [sOf, spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem moduli_exists_numberField_point :
    N1c → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → Formalism.L2.PjFree.XoNumPt Xo c := by
  intro hN E _ _ _ H Dw l Xo c hr
  obtain ⟨x⟩ := (PeriodExists.typeFn_period_exist E H Dw).2.2 hN hr l Xo c
  obtain ⟨L, _, _, hfin, y, hy, -⟩ := moduli_exists_algebraic_point E H Dw l Xo c ⊤ ⟨x, trivial⟩
  have : NumberField L := NumberField.of_module_finite c.F L
  refine ⟨L, inferInstance, this, algebraMap c.F L, y ≫ pullback.fst _ _, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hy]
  simp only [sOf, spMap, ← Spec.map_comp]
  rfl

end GlobalTheory
