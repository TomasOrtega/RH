import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe w v u v' u' v'' u''

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem isRt_rt : IsRt l (rt l) ∧ rt l 0 = pFlat l := by
  refine ⟨fun k => ?_, ?_⟩
  · apply (iterateFrobeniusEquiv (Ob l) l k).injective
    have h1 : iterateFrobeniusEquiv (Ob l) l (k + 1) (rt l (k + 1)) = pFlat l := RingEquiv.apply_symm_apply _ _
    have h2 : iterateFrobeniusEquiv (Ob l) l k (rt l k) = pFlat l := RingEquiv.apply_symm_apply _ _
    rw [h2, ← h1, iterateFrobeniusEquiv_def, iterateFrobeniusEquiv_def, ← pow_mul, pow_succ']
  · change (iterateFrobeniusEquiv (Ob l) l 0).symm (pFlat l) = pFlat l
    rw [iterateFrobeniusEquiv_zero]; rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem toPf_full : (toPf l).Full ∧ (toPf l).Faithful := by
  refine ⟨⟨fun {A B} φ => ⟨⟨φ.hom.hom.toRingHom, RingHom.ext fun c => φ.hom.hom.commutes c⟩, ?_⟩⟩,
    ⟨fun {A B} f g h => ?_⟩⟩
  · exact InducedCategory.hom_ext (CommAlgCat.hom_ext (AlgHom.ext fun x => rfl))
  · have h' := congrArg (fun φ => φ.hom.hom.toRingHom) h
    exact PAlg.Hom.ext h'

end CrystallineSemistableComparison.D
