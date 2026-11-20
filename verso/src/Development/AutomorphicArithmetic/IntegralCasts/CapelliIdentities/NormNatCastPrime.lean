import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.CapelliMiscellany.norm_natCast_prime :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)], ‖(↑p : PadicAlgCl p)‖ = (↑p : ℝ)⁻¹ := by
  intro p _
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p]
  exact (PadicAlgCl.norm_extends p (p : ℚ_[p])).trans Padic.norm_p
