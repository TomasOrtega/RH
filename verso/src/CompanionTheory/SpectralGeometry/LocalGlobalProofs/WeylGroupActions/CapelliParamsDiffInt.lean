import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShiftAtRExistsEq
import Formalism.HermitianCurvature.FrameExists2
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CommonEigenvectors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HighestWeightPolynomials

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.GapLie

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Supply the required witnesses or components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem capelli_params_diff_int : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (m : Fin n → ℂ), GlRel E → (∀ w v, qdet E w v = Qr.cpol m w • v) → ∀ i j, ∃ N : ℤ, m i - m j = (N : ℂ) := by
  intro V _ _ _ _ n E m hE hq
  obtain ⟨ν, v, -, hv0, hw, -⟩ := Formalism.FourierDecayAlt.P.exists_singular_maximal_vector V n E hE ⊤
    (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
  have hc := Formalism.FourierDecayAlt.P.HighestWeightPolynomials.hw_cpol (m := m) hE (Qr.mem_CapSp.2 fun w => hq w v) hv0 hw
  have hroot : ∀ i, ∃ a : Fin n, m i = ν a - ((a : ℕ) : ℂ) := by
    intro i
    have h1 := hc (-m i)
    unfold Qr.cpol at h1
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by ring)] at h1
    obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 h1.symm
    exact ⟨a, by linear_combination -ha⟩
  have hdom : ∀ a b : Fin n, ∃ N : ℤ, ν a - ν b = (N : ℂ) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · obtain ⟨N, hN⟩ := Formalism.FourierDecayAlt.P.singular_dominant V n E ν v hE hw hv0 a b h
      exact ⟨N, by simpa using hN⟩
    · exact ⟨0, by simp [h]⟩
    · obtain ⟨N, hN⟩ := Formalism.FourierDecayAlt.P.singular_dominant V n E ν v hE hw hv0 b a h
      refine ⟨-N, ?_⟩
      push_cast
      linear_combination -hN
  intro i j
  obtain ⟨a, ha⟩ := hroot i
  obtain ⟨b, hb⟩ := hroot j
  obtain ⟨N, hN⟩ := hdom a b
  refine ⟨N - (a : ℕ) + (b : ℕ), ?_⟩
  push_cast
  linear_combination ha - hb + hN

end GlobalTheory.CompanionTheory.GapLie
