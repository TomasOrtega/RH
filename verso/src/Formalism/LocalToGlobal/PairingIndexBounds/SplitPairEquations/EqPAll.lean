import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairOfGen
import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.MemLamOfIff

namespace Formalism.L2.PairingIndexBounds.Eq.SqG

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions.

A detailed English derivation is pending.
-/
theorem eqP_all {D : Formalism.BasicNotions.D7} {cc : Ideal (NumberField.RingOfIntegers D.host.K)} {δ : ℂ}
    (B : Formalism.L2.Ker.Base D cc δ) (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (hS : B.StdOK) (χ : Formalism.MainNotions.TaylorLogMetric.IdE D → ℂ) (hχ : Formalism.MainNotions.TaylorLogMetric.IsChi D χ) (hP : SplitPairGen) : B.EqP χ := by
  have hδ0 : δ ≠ 0 := by
    intro h0
    apply Formalism.L2.PairingIndexBounds.Rec.discrNZ D cc hcc
    rw [← hδ, h0]
    norm_num
  exact eqP_gen B hcc hδ hδ0 hS χ hχ hP

end Formalism.L2.PairingIndexBounds.Eq.SqG
