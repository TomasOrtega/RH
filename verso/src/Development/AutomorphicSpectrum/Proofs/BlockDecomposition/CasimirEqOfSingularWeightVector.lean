import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqWigMapsValueECas
set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

variable {n : ℕ}

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. Substitute using the available equality. Establish an intermediate fact.

Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cas_mul_sub_mem_Jp (y : U n) (τ : Fin n → ℂ)
    (hd : ∀ k, e (k, k) * y - τ k • y ∈ Jp n)
    (hu : ∀ a : Fin n × Fin n, IsUpper a → e a * y ∈ Jp n) :
    Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) * y - casC τ • y ∈ Jp n := by
  have key : ∀ a b : Fin n, e (a, b) * e (b, a) * y -
      ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) • y ∈ Jp n := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · have hc : e (a, b) * e (b, a) - e (b, a) * e (a, b) = e (a, a) - e (b, b) := by
        simpa using e_mul_sub_mul (a, b) (b, a)
      have hcomm : e (a, b) * e (b, a) = e (b, a) * e (a, b) + (e (a, a) - e (b, b)) := by
        rw [← hc]; abel
      have hval : e (a, b) * e (b, a) * y -
          ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) • y =
          e (b, a) * (e (a, b) * y) + (e (a, a) * y - τ a • y) - (e (b, b) * y - τ b • y) := by
        rw [if_neg h.ne, if_pos h, hcomm, zero_add, sub_smul]
        simp only [add_mul, sub_mul, mul_assoc]
        abel
      rw [hval]
      exact Submodule.sub_mem _ (Submodule.add_mem _ (mul_mem_Jp _ (hu _ h)) (hd a)) (hd b)
    · subst h
      have hval : e (a, a) * e (a, a) * y -
          ((if a = a then τ a ^ 2 else 0) + (if a < a then τ a - τ a else 0)) • y =
          e (a, a) * (e (a, a) * y - τ a • y) + τ a • (e (a, a) * y - τ a • y) := by
        simp only [if_true, lt_irrefl, if_false, add_zero, mul_sub, mul_smul_comm, smul_sub,
          smul_smul, mul_assoc, pow_two]
        abel
      rw [hval]
      exact Submodule.add_mem _ (mul_mem_Jp _ (hd a)) (Submodule.smul_mem _ _ (hd a))
    · have hval : e (a, b) * e (b, a) * y -
          ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) • y =
          e (a, b) * (e (b, a) * y) := by
        rw [if_neg h.ne', if_neg h.not_gt]
        simp [mul_assoc]
      rw [hval]
      exact mul_mem_Jp _ (hu _ h)
  have hsum : casC τ = ∑ a, ∑ b : Fin n,
      ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) := by
    simp only [casC, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hval : Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) * y - casC τ • y =
      ∑ a, ∑ b : Fin n, (e (a, b) * e (b, a) * y -
        ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) • y) := by
    rw [hsum]
    simp only [Formalism.REAL.Cas, Finset.sum_mul, Finset.sum_smul, Finset.sum_sub_distrib]
  rw [hval]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => key a b

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem cas_mul_comm (x : U n) :
    x * Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) =
      Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) * x := by
  have hz : Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) ∈ Subalgebra.center ℂ (U n) :=
    mem_center_of_commute_e fun a => by
      obtain ⟨c, d⟩ := a
      exact (Formalism.FourierDecayAlt.P.WigCas.cas_comm (glRel_e n) c d).symm
  exact (Subalgebra.mem_center_iff.1 hz) x

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem upper_e_mem_Jp (a : Fin n × Fin n) (ha : IsUpper a) : e a ∈ Jp n :=
  vermaIdeal_le_Jp (nPlusU_le_vermaIdeal _ (Submodule.subset_span ⟨1, a, ha, one_mul _⟩))

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem e_sub_rho_mem_Jp (u : U n) (k : Fin n) : u * e (k, k) - rhoVec n k • u ∈ Jp n := by
  have h := vermaIdeal_le_Jp (mul_e_sub_mem_vermaIdeal (rhoVec n) u k)
  have hv : u * (e (k, k) - algebraMap ℂ (U n) (rhoVec n k)) = u * e (k, k) - rhoVec n k • u := by
    rw [mul_sub, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  rwa [hv] at h

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Assume the negation of the conclusion and derive a contradiction.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem casC_rho_add_eq (μ : Fin n → ℤ) (x : U n) (hw : IsAdW μ x)
    (hu : ∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n) (hx : x ∉ Jp n) :
    casC (fun k => rhoVec n k + (μ k : ℂ)) = casC (rhoVec n) := by
  have h1 := cas_mul_sub_mem_Jp (1 : U n) (rhoVec n)
    (fun k => by simpa using e_sub_rho_mem_Jp (1 : U n) k) (fun a ha => by
      rw [mul_one]; exact upper_e_mem_Jp a ha)
  have h2 := cas_mul_sub_mem_Jp x (fun k => rhoVec n k + (μ k : ℂ)) (fun k => by
    have hv : e (k, k) * x - (rhoVec n k + (μ k : ℂ)) • x = x * e (k, k) - rhoVec n k • x := by
      have := hw k
      rw [add_smul, ← this]; abel
    rw [hv]; exact e_sub_rho_mem_Jp x k) hu
  have h3 := mul_mem_Jp x h1
  have hv : x * (Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) * 1 - casC (rhoVec n) • (1 : U n)) -
      (Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) * x -
        casC (fun k => rhoVec n k + (μ k : ℂ)) • x) =
      (casC (fun k => rhoVec n k + (μ k : ℂ)) - casC (rhoVec n)) • x := by
    rw [mul_one, mul_sub, cas_mul_comm, mul_smul_comm, mul_one, sub_smul]; abel
  have h4 := Submodule.sub_mem _ h3 h2
  rw [hv] at h4
  by_contra hne
  apply hx
  have hc : casC (fun k => rhoVec n k + (μ k : ℂ)) - casC (rhoVec n) ≠ 0 := sub_ne_zero.2 hne
  have := Submodule.smul_mem _ (casC (fun k => rhoVec n k + (μ k : ℂ)) - casC (rhoVec n))⁻¹ h4
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

end GlobalTheory.CompanionTheory.PresRho
