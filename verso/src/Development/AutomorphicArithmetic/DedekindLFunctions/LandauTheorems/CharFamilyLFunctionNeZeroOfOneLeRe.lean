import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

/- English proof (translation)
Use `haveI := F.nz i`. Break down `F.adm i with h | h` into its components or cases. Establish `key : ∀ (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M), M = 1 → DirichletCharacter.LFunction ψ s ≠ 0`. Introduce `M _ ψ hM`. Substitute `hM` using the available equality.

Rewrite using `[DirichletCharacter.LFunction_modOne_eq]`. Conclude with `riemannZeta_ne_zero_of_one_le_re hs`. Conclude with `key _ (F.χ i) h`. Conclude with `DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (Or.inl h) hs`.
-/
theorem charFamily_LFunction_ne_zero_of_one_le_re (F : CharFamily) (i : F.ι) (s : ℂ) (hs : 1 ≤ s.re) :
    DirichletCharacter.LFunction (F.χ i) s ≠ 0 := by
  haveI := F.nz i
  rcases F.adm i with h | h
  · have key : ∀ (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M), M = 1 →
        DirichletCharacter.LFunction ψ s ≠ 0 := by
      intro M _ ψ hM
      subst hM
      rw [DirichletCharacter.LFunction_modOne_eq]
      exact riemannZeta_ne_zero_of_one_le_re hs
    exact key _ (F.χ i) h
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (Or.inl h) hs

end Deduction

end
