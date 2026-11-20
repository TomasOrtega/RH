import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HermPartIsHermitian

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

/- English proof (translation)
Use `⟨fun i j h => ?_, fun w => ?_⟩` and prove the remaining obligations. Break down `NumberField.InfinitePlace.mk_eq_iff.1 h with h1 | h1` into its components or cases. Conclude with `e.injective (GlobalTheory.CuspAlgComparison.tau_injective H h1)`. Conclude with `absurd h1.symm (GlobalTheory.CuspAlgComparison.tau_ne_conj H (e j) (e i))`. Take `⟨τ, h | h⟩` from `GlobalTheory.CuspAlgComparison.emb_cases H w.embedding`.

Use `⟨e.symm τ, ?_⟩` and prove the remaining obligations. Rewrite using `[← NumberField.InfinitePlace.mk_embedding w, h]`. Simplify using `only [Equiv.apply_symm_apply]`. Both sides reduce to the same expression. Use `⟨e.symm τ, ?_⟩` and prove the remaining obligations.

Rewrite using `[← NumberField.InfinitePlace.mk_embedding w, h]`. Simplify using `only [Equiv.apply_symm_apply]`. Conclude with `(NumberField.InfinitePlace.mk_conjugate_eq _).symm`.
-/
theorem isCMFam_host (R : Ranks) (H : Host R) (I : Type) (e : I ≃ R.Psi) :
    IsCMFam (fun i => H.emb (e i).1) := by
  refine ⟨fun i j h => ?_, fun w => ?_⟩
  · rcases NumberField.InfinitePlace.mk_eq_iff.1 h with h1 | h1
    · exact e.injective (GlobalTheory.CuspAlgComparison.tau_injective H h1)
    · exact absurd h1.symm (GlobalTheory.CuspAlgComparison.tau_ne_conj H (e j) (e i))
  · obtain ⟨τ, h | h⟩ := GlobalTheory.CuspAlgComparison.emb_cases H w.embedding
    · refine ⟨e.symm τ, ?_⟩
      rw [← NumberField.InfinitePlace.mk_embedding w, h]
      simp only [Equiv.apply_symm_apply]
      rfl
    · refine ⟨e.symm τ, ?_⟩
      rw [← NumberField.InfinitePlace.mk_embedding w, h]
      simp only [Equiv.apply_symm_apply]
      exact (NumberField.InfinitePlace.mk_conjugate_eq _).symm

end GlobalTheory.Mem.Vol
