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
Use `⟨fun k => ?_, ?_⟩` and prove the remaining obligations. Apply `(iterateFrobeniusEquiv (Ob l) l k).injective` to reduce the goal to its premises. Establish `h1 : iterateFrobeniusEquiv (Ob l) l (k + 1) (rt l (k + 1)) = pFlat l` using `RingEquiv.apply_symm_apply _ _`. Establish `h2 : iterateFrobeniusEquiv (Ob l) l k (rt l k) = pFlat l` using `RingEquiv.apply_symm_apply _ _`. Rewrite using `[h2, ← h1, iterateFrobeniusEquiv_def, iterateFrobeniusEquiv_def, ← pow_mul, pow_succ']`.

Express the relevant statement in the definitionally equal form `(iterateFrobeniusEquiv (Ob l) l 0).symm (pFlat l) = pFlat l`. Rewrite using `[iterateFrobeniusEquiv_zero]`. Both sides reduce to the same expression.
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
Use `⟨⟨fun {A B} φ => ⟨⟨φ.hom.hom.toRingHom, RingHom.ext fun c => φ.hom.hom.commutes c⟩, ?_⟩⟩, ⟨fun {A B} f g h => ?_⟩⟩` and prove the remaining obligations. Conclude with `InducedCategory.hom_ext (CommAlgCat.hom_ext (AlgHom.ext fun x => rfl))`. Establish `h'` using `congrArg (fun φ => φ.hom.hom.toRingHom) h`. Conclude with `PAlg.Hom.ext h'`.
-/
theorem toPf_full : (toPf l).Full ∧ (toPf l).Faithful := by
  refine ⟨⟨fun {A B} φ => ⟨⟨φ.hom.hom.toRingHom, RingHom.ext fun c => φ.hom.hom.commutes c⟩, ?_⟩⟩,
    ⟨fun {A B} f g h => ?_⟩⟩
  · exact InducedCategory.hom_ext (CommAlgCat.hom_ext (AlgHom.ext fun x => rfl))
  · have h' := congrArg (fun φ => φ.hom.hom.toRingHom) h
    exact PAlg.Hom.ext h'

end CrystallineSemistableComparison.D
