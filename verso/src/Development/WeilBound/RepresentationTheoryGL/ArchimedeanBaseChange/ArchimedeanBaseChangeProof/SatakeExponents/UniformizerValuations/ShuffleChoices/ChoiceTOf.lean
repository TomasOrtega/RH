import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Choice

noncomputable section

open PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail

namespace PositivityTheory.Rg.BcB.F.Choice

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Supply the required witnesses or components.
-/
theorem choiceTOf : ChoiceTOf := by
  intro hP hC _hG E _ _ _ n w ι _ s Z α hZ
  have hfin : (⋃ i, (fun p : (Fin (s i).a → ℂˣ) × (Fin (s i).b → ℂˣ) => chiOf w (s i) p.1 p.2) '' Z i).Finite :=
    Set.finite_iUnion (fun i => (hZ i).image _)
  obtain ⟨c, hc, h1, h0⟩ := hP n 2 α (hfin.toFinset.erase α) (by simp)
  refine ⟨c, hc, h1, ?_⟩
  intro i p hp hne
  by_contra hneq
  apply hne
  have key : (c.sum fun x a => a * ↑(∏ k : Fin n, (s i).eps k ^ x k) * ev2 w p.1 p.2 (resL (s i) x) (resR (s i) x))
      = evalGL c (chiOf w (s i) p.1 p.2) := by
    unfold evalGL
    refine Finsupp.sum_congr (fun x _ => ?_)
    rw [mul_assoc, hC E n w (s i) p.1 p.2 x]
  rw [key]
  apply h0
  simp only [Finset.mem_erase, Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_image]
  exact ⟨hneq, i, p, hp, rfl⟩

end PositivityTheory.Rg.BcB.F.Choice

end
