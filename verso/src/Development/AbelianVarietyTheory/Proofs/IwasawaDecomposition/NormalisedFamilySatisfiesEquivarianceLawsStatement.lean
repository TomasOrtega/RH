import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedFamilySatisfiesEquivarianceLaws
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.NatEqui.eqP` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FNormalisedFamilySatisfiesEquivarianceLaws.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.normalisedFamily_satisfies_equivarianceLaws : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ := by
  first | exact @GlobalTheory.Mem.NatEqui.eqP | exact GlobalTheory.Mem.NatEqui.eqP | (intros; apply GlobalTheory.Mem.NatEqui.eqP <;> assumption)
