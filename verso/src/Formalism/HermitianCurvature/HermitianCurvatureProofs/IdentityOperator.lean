import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellVanishingOfCommute

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ Bs`. Set `T : B.DTerm k r Wp Wq` to `{ coef := fun _ => 1 coefAdj := fun _ => 1 word := [] word_lie := fun X hX => by simp at hX adj_id := fun _ _ _ => rfl }`. Establish `hap : ∀ F, B.opApply [T] F = F`. Introduce `F`. Use function extensionality and compare the values at `g`.

Simplify using `[B.opApply, B.Rw, T]`. Use `⟨[T], ⟨?_, ?_, ?_⟩, hap⟩` and prove the remaining obligations. Introduce `T' hT'`. Simplify using `only [List.mem_singleton] at hT'`. Substitute `hT'` using the available equality.

Apply the tactic sequence `refine ⟨?_, ?_⟩ <;> intro g₀ _ <;>`. Use `⟨Set.univ, fun _ => 1, ?_, Set.mem_univ _, ?_, fun _ _ _ => rfl⟩` and prove the remaining obligations. Apply the tactic sequence `all_goals first`. Consider the case `exact isOpen_univ`. Consider the case `exact contDiffOn_const`.

Consider the case `(open scoped Formalism.FourierDecayAlt.B in exact contDiffOn_const)`. Consider the case `(open scoped Matrix.Norms.Elementwise in exact contDiffOn_const)`. Consider the case `(open scoped Matrix.Norms.Operator in exact contDiffOn_const)`. Consider the case `exact @contDiffOn_const _ _ _ _ _ _ _ _ _ _ _ _`. Introduce `p _ f _ g _`.

Simplify using `only [hap]`. Introduce `T' hT'`. Simplify using `only [List.mem_singleton] at hT'`. Substitute `hT'` using the available equality. Use `⟨fun _ => 1, 0, 0, 0, [], ⟨1, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Simplify using the standard rewrite rules. Introduce `g`. Simplify using the standard rewrite rules. Introduce `l _ _`. Simplify using the standard rewrite rules.

Simplify using `[T]`. Simplify using the standard rewrite rules. Introduce `g _`. Simplify using `[C6.monoM, C6.Epart, T]`.
-/
theorem identity_operator : TL.IdOp := by
  intro k r Wp Wq _ _ _ _ _ Bs
  let T : B.DTerm k r Wp Wq :=
    { coef := fun _ => 1
      coefAdj := fun _ => 1
      word := []
      word_lie := fun X hX => by simp at hX
      adj_id := fun _ _ _ => rfl }
  have hap : ∀ F, B.opApply [T] F = F := by
    intro F
    funext g
    simp [B.opApply, B.Rw, T]
  refine ⟨[T], ⟨?_, ?_, ?_⟩, hap⟩
  · intro T' hT'
    simp only [List.mem_singleton] at hT'
    subst hT'
    refine ⟨?_, ?_⟩ <;> intro g₀ _ <;>
      refine ⟨Set.univ, fun _ => 1, ?_, Set.mem_univ _, ?_, fun _ _ _ => rfl⟩
    all_goals
      first
      | exact isOpen_univ
      | exact contDiffOn_const
      | (open scoped Formalism.FourierDecayAlt.B in exact contDiffOn_const)
      | (open scoped Matrix.Norms.Elementwise in exact contDiffOn_const)
      | (open scoped Matrix.Norms.Operator in exact contDiffOn_const)
      | exact @contDiffOn_const _ _ _ _ _ _ _ _ _ _ _ _
  · intro p _ f _ g _
    simp only [hap]
  · intro T' hT'
    simp only [List.mem_singleton] at hT'
    subst hT'
    refine ⟨fun _ => 1, 0, 0, 0, [], ⟨1, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · simp
    · intro g
      simp
    · intro l _ _
      simp
    · simp [T]
    · simp
    · intro g _
      simp [C6.monoM, C6.Epart, T]

end

end Formalism.FourierDecayAlt.P
