import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepArith

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rep_H_smul (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (ξ : ℂ) (z : m → ℂ) :
    stdH L m (ξ • z) (ξ • z) = ξ * conj ξ * stdH L m z z := by
  rw [LinearMap.map_smul₂, LinearMap.map_smulₛₗ]
  simp only [smul_eq_mul]
  ring

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. It suffices to derive a contradiction. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Replace the chosen expression with an arbitrary variable. Use linear arithmetic over natural numbers and integers. Supply the required witnesses or components.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem rep_tau {m : Type} (a : ℕ) (b c : ℤ) (d : ℕ) (hOK : CmOK a b c d) (Λ : AddSubgroup (m → ℂ))
    (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ) {l : ℕ} (hl : l.Prime) :
    ∃ τ : ℂ, ∃ r s : ℤ, τ + conj τ = 1 ∧ τ * conj τ = (r : ℂ) / s ∧ ¬ (l : ℤ) ∣ s ∧
      ∀ v : m → ℂ, SatMem l Λ v → SatMem l Λ (τ • v) := by
  obtain ⟨hac, -, hd8, -⟩ := hOK
  obtain ⟨k, hk⟩ : ∃ k : ℤ, b = 2 * k + 1 := by
    rcases Int.even_or_odd b with ⟨j, hj⟩ | ⟨j, hj⟩
    · exfalso
      have h4 : (d : ℤ) = 4 * ((a : ℤ) * c - j * j) := by
        rw [hj] at hac
        linear_combination -hac
      generalize (a : ℤ) * c - j * j = t at h4
      omega
    · exact ⟨j, hj⟩
  have hadd := rep_theta_add_conj b d
  have hmul := rep_theta_mul_conj a b c d hac
  refine ⟨cmTheta b d - (k : ℂ), a * c - k * b + k ^ 2, 1, ?_, ?_, ?_, ?_⟩
  · rw [map_sub, map_intCast]
    have hb : (b : ℂ) = 2 * k + 1 := by
      rw [hk]
      push_cast
      ring
    linear_combination hadd + hb
  · rw [map_sub, map_intCast]
    push_cast
    rw [div_one]
    linear_combination hmul - (k : ℂ) * hadd
  · intro h
    have h1 := Int.le_of_dvd one_pos h
    have h2 := hl.one_lt
    omega
  · intro v hv
    unfold SatMem at hv ⊢
    obtain ⟨n, hn, hnv⟩ := hv
    refine ⟨n, hn, ?_⟩
    rw [smul_comm, sub_smul, Int.cast_smul_eq_zsmul]
    exact Λ.sub_mem (hθ _ hnv) (Λ.zsmul_mem hnv k)

end PI.UnitaryGroupMassFormula.UnimodLocStd
