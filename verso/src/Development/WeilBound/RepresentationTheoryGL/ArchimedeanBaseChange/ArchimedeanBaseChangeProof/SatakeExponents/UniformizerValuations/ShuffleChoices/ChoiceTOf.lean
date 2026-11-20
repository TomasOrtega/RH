import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Choice

noncomputable section

open PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail

namespace PositivityTheory.Rg.BcB.F.Choice

/- English proof (translation)
Introduce `hP hC _hG E _ _ _ n w ι _ s Z α hZ`. Establish `hfin : (⋃ i, (fun p : (Fin (s i).a → ℂˣ) × (Fin (s i).b → ℂˣ) => chiOf w (s i) p.1 p.2) '' Z i).Finite` using `Set.finite_iUnion (fun i => (hZ i).image _)`. Take `⟨c, hc, h1, h0⟩` from `hP n 2 α (hfin.toFinset.erase α) (by simp)`. Use `⟨c, hc, h1, ?_⟩` and prove the remaining obligations. Introduce `i p hp hne`.

Assume the negation of the conclusion as `hneq`. Apply `hne` to reduce the goal to its premises. Establish `key : (c.sum fun x a => a * ↑(∏ k : Fin n, (s i).eps k ^ x k) * ev2 w p.1 p.2 (resL (s i) x) (resR (s i) x)) = evalGL c (chiOf w (s i) p.1 p.2)`. Unfold `evalGL`. Use `Finsupp.sum_congr (fun x _ => ?_)` and prove the remaining obligations.

Rewrite using `[mul_assoc, hC E n w (s i) p.1 p.2 x]`. Rewrite using `[key]`. Apply `h0` to reduce the goal to its premises. Simplify using `only [Finset.mem_erase, Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_image]`. Conclude with `⟨hneq, i, p, hp, rfl⟩`.
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
