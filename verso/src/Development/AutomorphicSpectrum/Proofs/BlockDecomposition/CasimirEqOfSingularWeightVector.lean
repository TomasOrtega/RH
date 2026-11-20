import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqWigMapsValueECas
set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

variable {n : ℕ}

/- English proof (translation)
Establish `key : ∀ a b : Fin n, e (a, b) * e (b, a) * y - ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) • y ∈ Jp n`. Introduce `a b`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Establish `hc : e (a, b) * e (b, a) - e (b, a) * e (a, b) = e (a, a) - e (b, b)`. Simplify using `using e_mul_sub_mul (a, b) (b, a)`.

Establish `hcomm : e (a, b) * e (b, a) = e (b, a) * e (a, b) + (e (a, a) - e (b, b))`. Rewrite using `[← hc]`. Normalize the expressions using the abelian group laws. Establish `hval : e (a, b) * e (b, a) * y - ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) • y = e (b, a) * (e (a, b) * y) + (e (a, a) * y - τ a • y) - (e (b, b) * y - τ b • y)`. Rewrite using `[if_neg h.ne, if_pos h, hcomm, zero_add, sub_smul]`.

Simplify using `only [add_mul, sub_mul, mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[hval]`. Conclude with `Submodule.sub_mem _ (Submodule.add_mem _ (mul_mem_Jp _ (hu _ h)) (hd a)) (hd b)`. Substitute `h` using the available equality.

Establish `hval : e (a, a) * e (a, a) * y - ((if a = a then τ a ^ 2 else 0) + (if a < a then τ a - τ a else 0)) • y = e (a, a) * (e (a, a) * y - τ a • y) + τ a • (e (a, a) * y - τ a • y)`. Simplify using `only [if_true, lt_irrefl, if_false, add_zero, mul_sub, mul_smul_comm, smul_sub, smul_smul, mul_assoc, pow_two]`. Normalize the expressions using the abelian group laws. Rewrite using `[hval]`. Conclude with `Submodule.add_mem _ (mul_mem_Jp _ (hd a)) (Submodule.smul_mem _ _ (hd a))`.

Establish `hval : e (a, b) * e (b, a) * y - ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) • y = e (a, b) * (e (b, a) * y)`. Rewrite using `[if_neg h.ne', if_neg h.not_gt]`. Simplify using `[mul_assoc]`. Rewrite using `[hval]`. Conclude with `mul_mem_Jp _ (hu _ h)`.

Establish `hsum : casC τ = ∑ a, ∑ b : Fin n, ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0))`. Simplify using `only [casC, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Establish `hval : Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) * y - casC τ • y = ∑ a, ∑ b : Fin n, (e (a, b) * e (b, a) * y - ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) • y)`. Rewrite using `[hsum]`. Simplify using `only [Formalism.REAL.Cas, Finset.sum_mul, Finset.sum_smul, Finset.sum_sub_distrib]`.

Rewrite using `[hval]`. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => key a b`.
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
Establish `hz : Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) ∈ Subalgebra.center ℂ (U n)` using `mem_center_of_commute_e fun a => by`. Take `⟨c, d⟩` from `a`. Conclude with `(Formalism.FourierDecayAlt.P.WigCas.cas_comm (glRel_e n) c d).symm`. Conclude with `(Subalgebra.mem_center_iff.1 hz) x`.
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
The claim follows from `vermaIdeal_le_Jp (nPlusU_le_vermaIdeal _ (Submodule.subset_span ⟨1, a, ha, one_mul _⟩))`.
-/
theorem upper_e_mem_Jp (a : Fin n × Fin n) (ha : IsUpper a) : e a ∈ Jp n :=
  vermaIdeal_le_Jp (nPlusU_le_vermaIdeal _ (Submodule.subset_span ⟨1, a, ha, one_mul _⟩))

/- English proof (translation)
Establish `h` using `vermaIdeal_le_Jp (mul_e_sub_mem_vermaIdeal (rhoVec n) u k)`. Establish `hv : u * (e (k, k) - algebraMap ℂ (U n) (rhoVec n k)) = u * e (k, k) - rhoVec n k • u`. Rewrite using `[mul_sub, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]`. Rewrite `h` using `[hv]`. Then use the resulting hypothesis.
-/
theorem e_sub_rho_mem_Jp (u : U n) (k : Fin n) : u * e (k, k) - rhoVec n k • u ∈ Jp n := by
  have h := vermaIdeal_le_Jp (mul_e_sub_mem_vermaIdeal (rhoVec n) u k)
  have hv : u * (e (k, k) - algebraMap ℂ (U n) (rhoVec n k)) = u * e (k, k) - rhoVec n k • u := by
    rw [mul_sub, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  rwa [hv] at h

/- English proof (translation)
Establish `h1` using `cas_mul_sub_mem_Jp (1 : U n) (rhoVec n) (fun k => by simpa using e_sub_rho_mem_Jp (1 : U n) k) (fun a ha => by`. Rewrite using `[mul_one]`. Conclude with `upper_e_mem_Jp a ha)`. Establish `h2` using `cas_mul_sub_mem_Jp x (fun k => rhoVec n k + (μ k : ℂ)) (fun k => by`. Establish `hv : e (k, k) * x - (rhoVec n k + (μ k : ℂ)) • x = x * e (k, k) - rhoVec n k • x`.

Use `hw k` as an intermediate fact. Rewrite using `[add_smul, ← this]`. Normalize the expressions using the abelian group laws. Rewrite using `[hv]`. Conclude with `e_sub_rho_mem_Jp x k) hu`.

Establish `h3` using `mul_mem_Jp x h1`. Establish `hv : x * (Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) * 1 - casC (rhoVec n) • (1 : U n)) - (Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) * x - casC (fun k => rhoVec n k + (μ k : ℂ)) • x) = (casC (fun k => rhoVec n k + (μ k : ℂ)) - casC (rhoVec n)) • x`. Rewrite using `[mul_one, mul_sub, cas_mul_comm, mul_smul_comm, mul_one, sub_smul]`. Normalize the expressions using the abelian group laws. Establish `h4` using `Submodule.sub_mem _ h3 h2`.

Rewrite `h4` using `[hv]`. Assume the negation of the conclusion as `hne`. Apply `hx` to reduce the goal to its premises. Establish `hc : casC (fun k => rhoVec n k + (μ k : ℂ)) - casC (rhoVec n) ≠ 0` using `sub_ne_zero.2 hne`. Use `Submodule.smul_mem _ (casC (fun k => rhoVec n k + (μ k : ℂ)) - casC (rhoVec n))⁻¹ h4` as an intermediate fact.

Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hc, one_smul]`. Then use the resulting hypothesis.
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
