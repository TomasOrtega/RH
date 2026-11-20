import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.LeviBlockIdx

/- English proof (translation)
Introduce `k _ _ _ _ h N d hd g`. Rewrite using `[GroundTheory.Automorphic.Parabolic.mem_levi]`. Introduce `i j hij`. Take `⟨⟨a, x⟩, rfl⟩` from `(stdBlocks d hd).surjective i`. Take `⟨⟨b, y⟩, rfl⟩` from `(stdBlocks d hd).surjective j`.

Establish `hab : a ≠ b`. Simplify `hij` using `[Zl.JC.blockIdx]`. Conclude with `leviEmb_apply_ne k (stdBlocks d hd) g hab x y`.
-/
theorem leviEmb_mem_levi_blockIdx : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (g : Levi k (fun a => Fin (d a))), leviEmb k (stdBlocks d hd) g ∈ GroundTheory.Automorphic.Parabolic.levi k N (Zl.JC.blockIdx d hd) := by
  intro k _ _ _ _ h N d hd g
  rw [GroundTheory.Automorphic.Parabolic.mem_levi]
  intro i j hij
  obtain ⟨⟨a, x⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := (stdBlocks d hd).surjective j
  have hab : a ≠ b := by
    simpa [Zl.JC.blockIdx] using hij
  exact leviEmb_apply_ne k (stdBlocks d hd) g hab x y

end GlobalTheory.CompanionTheory.LeviBlockIdx
