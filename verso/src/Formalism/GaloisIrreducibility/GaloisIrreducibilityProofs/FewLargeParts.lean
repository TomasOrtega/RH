import Formalism.GaloisIrreducibility.Statement

namespace Formalism.GaloisIrreducibility

open Finset

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. A detailed English derivation is pending.
-/
lemma prod_lpart_dvd (n : ℕ) (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) :
    (∏ l ∈ S, l ^ padicValNat l n) ∣ n := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert l S hl ih =>
    rw [Finset.prod_insert hl]
    have hlp : l.Prime := hS l (Finset.mem_insert_self l S)
    have ih' := ih (fun l' hl' => hS l' (Finset.mem_insert_of_mem hl'))
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    · apply Nat.Coprime.prod_right
      intro l' hl'
      have hl'p : l'.Prime := hS l' (Finset.mem_insert_of_mem hl')
      apply Nat.Coprime.pow
      exact (Nat.coprime_primes hlp hl'p).2 (fun h => hl (h ▸ hl'))
    · exact pow_padicValNat_dvd
    · exact ih'

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.
-/
theorem few_large_cycle_parts : FewLargeParts := by
  intro n B S hn hB hS hne hlarge
  have hdvd := prod_lpart_dvd n S hS
  have hle : (∏ l ∈ S, l ^ padicValNat l n) ≤ n := Nat.le_of_dvd (by omega) hdvd
  calc B ^ S.card = ∏ _l ∈ S, B := by rw [Finset.prod_const]
    _ < ∏ l ∈ S, ((l ^ padicValNat l n : ℕ) : ℝ) :=
        Finset.prod_lt_prod_of_nonempty (fun _ _ => hB) hlarge hne
    _ = ((∏ l ∈ S, l ^ padicValNat l n : ℕ) : ℝ) := by rw [Nat.cast_prod]
    _ ≤ n := by exact_mod_cast hle

end Formalism.GaloisIrreducibility
