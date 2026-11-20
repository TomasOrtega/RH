import Mathlib

namespace KStar.Choice

def oddRad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors.erase 2, p

def modP (q : ℕ) : ℕ := oddRad (q * q.totient)

def hostP (S : Finset ℕ) : ℕ := oddRad (∏ l ∈ S, l * (l - 1))

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Evaluate the decidable proposition.
-/
example : oddRad 90 = 15 := by
  have : (90 : ℕ).primeFactors = {2, 3, 5} := by simp [Nat.primeFactors]
  rw [oddRad, this]; decide

end KStar.Choice
