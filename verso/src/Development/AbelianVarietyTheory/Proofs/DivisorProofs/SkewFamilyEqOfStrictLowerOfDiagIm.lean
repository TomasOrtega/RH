import Mathlib
open scoped ComplexConjugate

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem skewFamily_eq_of_strictLower_of_diagIm
    {ι : Type} [Fintype ι] {r : ℕ} (s : Fin r → ℝ) (hs : ∀ a, s a * s a = 1)
    (Y Y' : ι × Fin r × Fin r → ℂ)
    (hY : ∀ τ a b, Y (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y (τ, a, b)))
    (hYt : ∀ τ, ∑ a, Y (τ, a, a) = 0)
    (hY' : ∀ τ a b, Y' (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y' (τ, a, b)))
    (hY't : ∀ τ, ∑ a, Y' (τ, a, a) = 0)
    (hlt : ∀ τ a b, b < a → Y (τ, a, b) = Y' (τ, a, b))
    (him : ∀ τ (a : Fin r), (a : ℕ) + 1 < r → (Y (τ, a, a)).im = (Y' (τ, a, a)).im) :
    Y = Y' := by
  have hre : ∀ (Z : ι × Fin r × Fin r → ℂ),
      (∀ τ a b, Z (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Z (τ, a, b))) →
      ∀ τ a, (Z (τ, a, a)).re = 0 := by
    intro Z hZ τ a
    have h := hZ τ a a
    rw [hs a] at h
    have h2 := congrArg Complex.re h
    simp only [Complex.ofReal_one, neg_mul, one_mul, Complex.neg_re, Complex.conj_re] at h2
    linarith
  have hoff : ∀ τ (c : Fin r), (c : ℕ) + 1 < r → Y (τ, c, c) = Y' (τ, c, c) :=
    fun τ c hc => Complex.ext (by rw [hre Y hY τ c, hre Y' hY' τ c]) (him τ c hc)
  have hdiag : ∀ τ (a : Fin r), Y (τ, a, a) = Y' (τ, a, a) := by
    intro τ a
    by_cases ha : (a : ℕ) + 1 < r
    · exact hoff τ a ha
    · have hsum : ∀ c ∈ Finset.univ.erase a, Y (τ, c, c) = Y' (τ, c, c) := by
        intro c hc
        apply hoff
        have hca : c ≠ a := Finset.ne_of_mem_erase hc
        have hcv : (c : ℕ) ≠ a := fun h => hca (Fin.ext h)
        have := c.isLt
        have := a.isLt
        omega
      have e1 : Y (τ, a, a) + ∑ c ∈ Finset.univ.erase a, Y (τ, c, c) = 0 := by
        exact (Finset.add_sum_erase Finset.univ (fun c => Y (τ, c, c)) (Finset.mem_univ a)).trans (hYt τ)
      have e2 : Y' (τ, a, a) + ∑ c ∈ Finset.univ.erase a, Y' (τ, c, c) = 0 := by
        exact (Finset.add_sum_erase Finset.univ (fun c => Y' (τ, c, c)) (Finset.mem_univ a)).trans (hY't τ)
      rw [Finset.sum_congr rfl hsum] at e1
      linear_combination e1 - e2
  funext p
  obtain ⟨τ, a, b⟩ := p
  rcases lt_trichotomy a b with h | rfl | h
  · rw [hY τ b a, hY' τ b a, hlt τ b a h]
  · exact hdiag τ a
  · exact hlt τ a b h

end GlobalTheory
