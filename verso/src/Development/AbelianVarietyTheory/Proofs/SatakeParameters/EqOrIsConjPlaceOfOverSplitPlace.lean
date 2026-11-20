import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitPlaceOver

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem host_conj_eq' (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eq_or_isConjPl : ∀ (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host), NG.OverPl w s.v →
    s.w = w ∨ IsConjPl D.host w s.w := by
  intro D s w hov
  rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE s.w w (hov.trans s.w_under.symm) with e | e
  · exact Or.inl e.symm
  · right
    intro x y hxy
    have hy : y = IsCMField.ringOfIntegersComplexConj D.host.E x := by
      apply RingOfIntegers.ext
      rw [hxy, IsCMField.coe_ringOfIntegersComplexConj, host_conj_eq']
    rw [e, GlobalTheory.SplitConjPlace.mem_conjPlE, hy]

end GlobalTheory.SplitPlaceOver
