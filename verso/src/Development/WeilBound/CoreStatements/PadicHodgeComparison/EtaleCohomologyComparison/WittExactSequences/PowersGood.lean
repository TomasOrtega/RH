import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ToPfFull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ExactUpToSpan
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.SplitClause

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe w v u v' u' v'' u''

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Take `⟨_, _, hdiv, -⟩` from `h`. Take `⟨hr, hr0⟩` from `isRt_rt l`. Establish `hrA : IsRt l (fun k => algebraMap (Ob l) A.obj (rt l k))` using `fun k => by`. Simplify using `only [← map_pow, hr k]`. Take `⟨B, _, _, hB, hC, hAIC, hVAL, hS⟩` from `Leaf.cov_tower l A.obj _ A.property hrA`.

Set `_ : Algebra (Ob l) B` to `((algebraMap A.obj B).comp (algebraMap (Ob l) A.obj)).toAlgebra`. Establish `_ : IsScalarTower (Ob l) A.obj B` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Conclude with `powers_abs l (testι l ⋙ toPf l) (rt l) hr (fun a ha => by obtain ⟨M, hM⟩ := hdiv a ha; exact ⟨M, hr0 ▸ hM⟩) N A B hB hC (split_clause l A B hB hS) (test_clause l N M hN B hB hAIC hVAL)`.
-/
theorem powers_good (h : ObFacts l) (N : Type) [AddCommGroup N] [Module (Ob l) N] (M : ℕ) (hN : ∀ x : N, pFlat l ^ M • x = 0)
    (A : PfC l (Ob l)) : ∃ P : Powers (testι l ⋙ toPf l) A,
      P.Good (testι l ⋙ toPf l) (tensF l (Ob l) N) (Ideal.span (Set.range (rt l))) := by
  obtain ⟨_, _, hdiv, -⟩ := h
  obtain ⟨hr, hr0⟩ := isRt_rt l
  have hrA : IsRt l (fun k => algebraMap (Ob l) A.obj (rt l k)) := fun k => by
    simp only [← map_pow, hr k]
  obtain ⟨B, _, _, hB, hC, hAIC, hVAL, hS⟩ := Leaf.cov_tower l A.obj _ A.property hrA
  let _ : Algebra (Ob l) B := ((algebraMap A.obj B).comp (algebraMap (Ob l) A.obj)).toAlgebra
  have _ : IsScalarTower (Ob l) A.obj B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact powers_abs l (testι l ⋙ toPf l) (rt l) hr
    (fun a ha => by obtain ⟨M, hM⟩ := hdiv a ha; exact ⟨M, hr0 ▸ hM⟩) N A B hB hC
    (split_clause l A B hB hS) (test_clause l N M hN B hB hAIC hVAL)

end CrystallineSemistableComparison.D
