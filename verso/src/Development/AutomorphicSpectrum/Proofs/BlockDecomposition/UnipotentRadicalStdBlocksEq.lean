import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.ParabolicCompare

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem unipRad_stdBlocks_eq_unipotentRadical (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) :
    unipRad k (stdBlocks d hd) = GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd) := by
  ext g
  rw [GlobalTheory.SmGL.mem_unipRad, GroundTheory.Automorphic.Parabolic.mem_unipotentRadical,
    GroundTheory.Automorphic.Iwasawa.mem_blockUpper, GlobalTheory.SmGL.mem_parab]
  refine and_congr Iff.rfl ⟨fun H i j hij => ?_, fun H a i j => ?_⟩
  · obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks d hd).surjective j
    obtain rfl : a = b := by simpa [Zl.JC.blockIdx] using hij
    have := H a i j
    rw [this]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne]
      intro h'
      exact e (by simpa using (stdBlocks d hd).injective h')
  · rw [H _ _ (by simp [Zl.JC.blockIdx])]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne]
      intro h'
      exact e (by simpa using (stdBlocks d hd).injective h')

end GlobalTheory.CompanionTheory.ParabolicCompare
