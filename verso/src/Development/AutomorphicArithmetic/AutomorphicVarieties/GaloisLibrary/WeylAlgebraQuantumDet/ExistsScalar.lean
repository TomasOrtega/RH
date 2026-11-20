import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.Scalar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.DegRank
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.TopPol
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.PolPre
open Matrix UpperTheory.V.Weyl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem UpperTheory.V.Weyl.existsScalar :
    ∀ (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ H : ℕ, (∀ k, ν k ≤ H) →
      ∃ Ξ : Pre n, 0 < Ξ.d ∧ Ξ.d ≤ (n * H + 1) ^ (n * n) ∧ Ξ.HasWt fun k => (ν k : ℂ) := by
  intro n ν hν H hH
  obtain ⟨f, hf0, hdeg, hf⟩ := topPol n ν hν H hH
  obtain ⟨Ξ, e, he⟩ := polPre n (n * H)
  let F : MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ (n * H) :=
    ⟨f, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hdeg⟩
  have hF : F ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  have hv : e F ≠ 0 := fun h => hF (e.injective (h.trans e.map_zero.symm))
  have htop : Ξ.IsTop ν (e F) := by
    intro b hb
    rw [he b F ((∏ k, b k k ^ ν k) • F) (hf b hb).symm, map_smul]
  obtain ⟨Ξ', h0, hle, hw⟩ := scalar n Ξ ν (e F) hv htop
  refine ⟨Ξ', h0, hle.trans ?_, hw⟩
  have h1 := e.finrank_eq
  have h2 := degRank n (n * H)
  rw [h1] at h2
  simpa using h2
