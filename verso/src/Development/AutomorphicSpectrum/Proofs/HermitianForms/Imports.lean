import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankFour

open Matrix

namespace GlobalTheory.CompanionTheory.UnitaryLog

/- English proof (translation)
Introduce `n g`. Establish `hA : (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * (g : Matrix (Fin n) (Fin n) ℂ) = 1` using `Matrix.mem_unitaryGroup_iff'.1 g.2`. Take `⟨B, h1, h2⟩` from `Formalism.FourierDecayAlt.P.HermitianFormRankFour.unitary_log _ hA`. Conclude with `⟨B, h1, h2.symm⟩`.
-/
theorem main : ∀ (n : ℕ) (g : Matrix.unitaryGroup (Fin n) ℂ),
    ∃ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X ∧
      (g : Matrix (Fin n) (Fin n) ℂ) = NormedSpace.exp X := by
  intro n g
  have hA : (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * (g : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 g.2
  obtain ⟨B, h1, h2⟩ := Formalism.FourierDecayAlt.P.HermitianFormRankFour.unitary_log _ hA
  exact ⟨B, h1, h2.symm⟩

end GlobalTheory.CompanionTheory.UnitaryLog
