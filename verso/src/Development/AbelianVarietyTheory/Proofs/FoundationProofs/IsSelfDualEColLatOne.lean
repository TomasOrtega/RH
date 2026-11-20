import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PosDefExistsFrame

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat.Inhabitant

/- English proof (translation)
Unfold `colLat`. Use `congr 2`. Use function extensionality and compare the values at `j a`. Simplify using `[Matrix.one_apply, Pi.single_apply]`.
-/
theorem colLat_one_eq {K : Type} [Field K] [NumberField K] {n : ℕ} :
    colLat (1 : GL (Fin n) K) = Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n))) := by
  unfold colLat
  congr 2
  funext j a
  simp [Matrix.one_apply, Pi.single_apply]

/- English proof (translation)
Rewrite using `[colLat_one_eq, Module.Basis.mem_span_iff_repr_mem]`. Simplify using the standard rewrite rules.
-/
theorem mem_colLat_one {K : Type} [Field K] [NumberField K] {n : ℕ} (x : Fin n → K) :
    x ∈ colLat (1 : GL (Fin n) K) ↔ ∀ a, x a ∈ (algebraMap (𝓞 K) K).range := by
  rw [colLat_one_eq, Module.Basis.mem_span_iff_repr_mem]
  simp

end GlobalTheory.TestLat.Inhabitant
