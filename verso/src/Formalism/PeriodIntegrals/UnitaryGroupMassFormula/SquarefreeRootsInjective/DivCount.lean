import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.ClaimOf

open Polynomial

noncomputable section

open Classical

namespace PI.SqfRootsInj.W

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. By extensionality, compare the relevant components. Separate the alternatives or extract the components of the hypothesis. Substitute using the available equality.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem divCount {g : ℕ} [Fact g.Prime] (r : ℕ) (T : Finset (ZMod g)[X])
    (hT : ∀ f ∈ T, f.Monic ∧ f.natDegree = r) (h : (ZMod g)[X]) (hh : h.Monic) :
    (T.filter (h ∣ ·)).card ≤ g ^ (r - h.natDegree) := by
  classical
  set k := r - h.natDegree
  let φ : (ZMod g)[X] → (Fin k → ZMod g) := fun f i => (f /ₘ h).coeff i
  have key : ∀ f ∈ T.filter (h ∣ ·), (f /ₘ h).Monic ∧ (f /ₘ h).natDegree = k ∧
      h * (f /ₘ h) = f := by
    intro f hf
    rw [Finset.mem_filter] at hf
    obtain ⟨hfT, hdv⟩ := hf
    obtain ⟨hm, hd⟩ := hT f hfT
    have e1 : h * (f /ₘ h) = f := by
      have := modByMonic_add_div f h
      rw [(modByMonic_eq_zero_iff_dvd hh).2 hdv, zero_add] at this
      exact this
    refine ⟨?_, ?_, e1⟩
    · have hm' : (h * (f /ₘ h)).Monic := by rw [e1]; exact hm
      exact hh.of_mul_monic_left hm'
    · rw [natDegree_divByMonic f hh, hd]
  have hinj : Set.InjOn φ (T.filter (h ∣ ·)) := by
    intro f hf f' hf' heq
    obtain ⟨m1, d1, e1⟩ := key f hf
    obtain ⟨m2, d2, e2⟩ := key f' hf'
    have hq : f /ₘ h = f' /ₘ h := by
      ext n
      rcases lt_trichotomy n k with hn | hn | hn
      · exact congrFun heq ⟨n, hn⟩
      · subst hn
        have a1 := m1.coeff_natDegree
        have a2 := m2.coeff_natDegree
        rw [d1] at a1; rw [d2] at a2
        rw [a1, a2]
      · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
    rw [← e1, ← e2, hq]
  calc (T.filter (h ∣ ·)).card ≤ (Finset.univ : Finset (Fin k → ZMod g)).card :=
        Finset.card_le_card_of_injOn φ (fun _ _ => Finset.mem_univ _) hinj
    _ = g ^ k := by simp [ZMod.card]

end PI.SqfRootsInj.W
