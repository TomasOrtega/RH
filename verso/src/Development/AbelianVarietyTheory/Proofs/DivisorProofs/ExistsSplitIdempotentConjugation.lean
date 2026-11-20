import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSimR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapInjective
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.CentTorus GlobalTheory.CentAtP
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CentAtP

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_conj_ne (G : HTGroup p) : ∃ x ∈ G.Kq, IsCMField.complexConj G.F x ≠ x := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace G.F) := inferInstance
  obtain ⟨x, hx, him⟩ := G.hKq.2 v.embedding
  refine ⟨x, hx, fun h => him ?_⟩
  have h2 := IsCMField.complexEmbedding_complexConj G.F v.embedding x
  rw [h] at h2
  have := congrArg Complex.im h2
  simp only [Complex.conj_im] at this
  linarith

end GlobalTheory.CentAtP
