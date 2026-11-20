import Mathlib.NumberTheory.Bertrand
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Supply the required witnesses or components.
-/
theorem UpperTheory.V.HV.pZeroLe :
    ∀ m : ℕ, 0 < m → (pZero m).Prime ∧ 5 ≤ pZero m ∧ ¬ pZero m ∣ m ∧ pZero m ≤ 2 * m + 10 := by
  intro m hm
  obtain ⟨p, hp, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (m + 5) (by omega)
  have hmem : p ∈ {p : ℕ | p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ m} :=
    ⟨hp, by omega, fun h => by have := Nat.le_of_dvd hm h; omega⟩
  have h3 : UpperTheory.V.HV.pZero m ∈ {p : ℕ | p.Prime ∧ 5 ≤ p ∧ ¬ p ∣ m} := Nat.sInf_mem ⟨p, hmem⟩
  have h4 : UpperTheory.V.HV.pZero m ≤ p := Nat.sInf_le hmem
  exact ⟨h3.1, h3.2.1, h3.2.2, by omega⟩
