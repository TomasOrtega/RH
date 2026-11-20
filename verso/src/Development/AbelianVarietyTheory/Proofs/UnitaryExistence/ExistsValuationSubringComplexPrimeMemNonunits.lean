import Mathlib

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem exists_valuationSubring_complex_prime_mem_nonunits :
    ∀ p : ℕ, p.Prime → ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits := by
  intro p hp
  let A : Subring ℂ := (Int.castRingHom ℂ).range
  have hI : Ideal.span {(p : A)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top, isUnit_iff_exists_inv]
    rintro ⟨⟨b, n, rfl⟩, hb⟩
    have h1 : ((p : ℂ)) * (n : ℂ) = 1 := by
      have := congrArg (Subtype.val) hb
      simpa using this
    have h2 : (p : ℤ) * n = 1 := by exact_mod_cast h1
    have h3 : (p : ℤ) ∣ 1 := ⟨n, h2.symm⟩
    have h4 : p ∣ 1 := by exact_mod_cast h3
    exact hp.one_lt.ne' (Nat.dvd_one.mp h4)
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  refine ⟨B, hB ⟨(p : A), Ideal.subset_span rfl, by simp⟩⟩

end GlobalTheory
