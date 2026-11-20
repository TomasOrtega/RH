import Mathlib
import Formalism.GradedWeylDivisibility.StatementA
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylNonDom

namespace GlobalTheory.NonDomZero

/- English proof (translation)
Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem exists_lt_lt_of_not_antitone {N : ℕ} {ν : Fin N → ℕ} (hν : ¬ Antitone ν) :
    ∃ a b : Fin N, a < b ∧ ν a < ν b := by
  simp only [Antitone, not_forall] at hν
  obtain ⟨a, b, hab, hlt⟩ := hν
  refine ⟨a, b, lt_of_le_of_ne hab ?_, lt_of_not_ge hlt⟩
  rintro rfl
  exact hlt le_rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem dualWeyl_eq_bot_of_not_antitone :
    ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ) (ν : Fin N → ℕ),
      ¬ Antitone ν → Formalism.GradedWeylDivisibility.dualWeyl O N N ν = ⊥ := by
  intro O _ _ _ N ν hν
  exact Formalism.GradedWeylDivisibility.dualWeylModuleNonDominant O N N ν (exists_lt_lt_of_not_antitone hν)

end GlobalTheory.NonDomZero
