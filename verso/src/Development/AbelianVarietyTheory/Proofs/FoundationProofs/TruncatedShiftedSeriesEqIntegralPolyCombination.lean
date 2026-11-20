import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ChSumSubCMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubOnePowThreeLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

namespace GlobalTheory.KZ.Cmp

/- English proof (translation)
Introduce `l _ c F N hF`. Set `Q : Polynomial c.O` to `∑ n ∈ Finset.range N, Polynomial.C (⟨F.coeff n, hF n⟩ : c.O) * (Polynomial.X - Polynomial.C 1) ^ n`. Use `⟨fun j => ((Q.coeff j : c.O) : Qbar l), fun j => (Q.coeff j).2, fun z => ?_⟩` and prove the remaining obligations. Establish `hdeg : Q.natDegree < N ∨ N = 0`. Break down `Nat.eq_zero_or_pos N with h | h` into its components or cases.

Conclude with `Or.inr h`. Use `left`. Take `⟨k, rfl⟩ : ∃ k, N = k + 1` from `⟨N - 1, by omega⟩`. Use `Nat.lt_succ_of_le (Polynomial.natDegree_sum_le_of_forall_le _ _ fun n hn => ?_)` and prove the remaining obligations. Establish `hn' : n ≤ k` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)`.

Use `(Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_pow_le).trans ?_)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Break down `hdeg with hd | rfl` into its components or cases. Establish `h1` using `Polynomial.aeval_eq_sum_range' (R := c.O) (x := z) hd`. Establish `h2 : Polynomial.aeval z Q = tval F N z`.

Simplify using `[Q, tval, map_sum]`. Rewrite using `[← h2, h1]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression.

Simplify using `[tval]`.
-/
theorem tval_eq_sum_pow_of_integral : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (F : PowerSeries (Qbar l)) (N : ℕ), (∀ n, F.coeff n ∈ c.O) → ∃ a : ℕ → Qbar l, (∀ j, a j ∈ c.O) ∧ ∀ z : Qbar l, tval F N z = ∑ j ∈ Finset.range N, a j * z ^ j := by
  intro l _ c F N hF
  let Q : Polynomial c.O := ∑ n ∈ Finset.range N, Polynomial.C (⟨F.coeff n, hF n⟩ : c.O) * (Polynomial.X - Polynomial.C 1) ^ n
  refine ⟨fun j => ((Q.coeff j : c.O) : Qbar l), fun j => (Q.coeff j).2, fun z => ?_⟩
  have hdeg : Q.natDegree < N ∨ N = 0 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact Or.inr h
    · left
      obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
      refine Nat.lt_succ_of_le (Polynomial.natDegree_sum_le_of_forall_le _ _ fun n hn => ?_)
      have hn' : n ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      refine (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_pow_le).trans ?_)
      calc n * (Polynomial.X - Polynomial.C (1 : c.O)).natDegree ≤ n * 1 :=
            Nat.mul_le_mul_left _ (Polynomial.natDegree_X_sub_C_le _)
        _ ≤ k := by omega
  rcases hdeg with hd | rfl
  · have h1 := Polynomial.aeval_eq_sum_range' (R := c.O) (x := z) hd
    have h2 : Polynomial.aeval z Q = tval F N z := by
      simp [Q, tval, map_sum]
    rw [← h2, h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]
    rfl
  · simp [tval]

end GlobalTheory.KZ.Cmp
