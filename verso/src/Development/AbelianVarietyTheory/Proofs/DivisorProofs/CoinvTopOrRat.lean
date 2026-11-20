import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

/- English proof (translation)
Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Prove the second alternative. Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations.

Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coinv_top_or_rat (P Q R S : ℕ) (x : ℂ) :
    coinv P Q R S x = ⊤ ∨ ∃ x' : ℚ, coinv P Q R S x = coinv P Q R S (x' : ℂ) := by
  by_cases hx : ∃ x' : ℚ, x = x'
  · obtain ⟨x', rfl⟩ := hx
    exact Or.inr ⟨x', rfl⟩
  push_neg at hx
  by_cases hI : IsEmpty (Ix P Q)
  · right
    refine ⟨0, ?_⟩
    unfold coinv
    congr 1
    ext g
    simp [Matrix.trace, Finset.univ_eq_empty]
  · left
    rw [not_isEmpty_iff] at hI
    obtain ⟨a⟩ := hI
    let K : Subring ℂ := (Rat.castHom ℂ).range
    have hxK : x ∉ K := by
      rintro ⟨q, hq⟩
      exact hx q hq.symm
    have hsign : ∀ c : Ix R S, lineSign a c ∈ K := by
      intro c
      rcases a with a | a <;> rcases c with c | c <;> simp only [lineSign] <;>
        first | exact K.one_mem | exact K.neg_mem K.one_mem
    have hc : ∀ α : Ln P Q R S →₀ ℕ, (∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) ∈ K := by
      intro α
      refine K.sum_mem fun c _ => K.mul_mem (hsign c) (K.add_mem (natCast_mem K _) ?_)
      exact RingHom.mem_range.mpr ⟨1 / 2, by simp⟩
    have hmon : ∀ α : Ln P Q R S →₀ ℕ, (MvPolynomial.monomial α (1 : ℂ) : Pol P Q R S) ∈ coinv P Q R S x := by
      intro α
      have hne : (∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) - x ≠ 0 := by
        intro h
        apply hxK
        rw [sub_eq_zero] at h
        rw [← h]
        exact hc α
      have hg : fockAct1 P Q R S (Eab a a) (MvPolynomial.monomial α 1) -
          (x * (Eab a a : Mat P Q).trace) • MvPolynomial.monomial α 1 ∈ coinv P Q R S x :=
        Submodule.subset_span ⟨Eab a a, _, rfl⟩
      have htr : (Eab a a : Mat P Q).trace = 1 := by simp [Eab]
      rw [cartan1, htr, mul_one, ← sub_smul] at hg
      have h2 := (coinv P Q R S x).smul_mem ((∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) - x)⁻¹ hg
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
    rw [eq_top_iff]
    intro f _
    rw [f.as_sum]
    refine Submodule.sum_mem _ fun α _ => ?_
    have he : (MvPolynomial.monomial α (MvPolynomial.coeff α f) : Pol P Q R S) =
        MvPolynomial.coeff α f • MvPolynomial.monomial α 1 := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [he]
    exact (coinv P Q R S x).smul_mem _ (hmon α)

end GlobalTheory.HoweR
