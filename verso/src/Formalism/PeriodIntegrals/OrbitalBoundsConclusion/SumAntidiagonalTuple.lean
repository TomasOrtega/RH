import Mathlib
import Formalism.PeriodIntegrals.SumAntidiagonalTuple

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers.
-/
private theorem sum_range_add_choose_eq_choose_succ (E n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (k + E).choose E = (n + E + 1).choose (E + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, show n + 1 + E + 1 = (n + E + 1) + 1 by omega,
      Nat.choose_succ_succ (n + E + 1) E, show n + 1 + E = n + E + 1 by omega]
    simp only [Nat.succ_eq_add_one]
    omega

/- English proof (translation)
Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
private theorem card_antidiagonal_tuple_succ_eq_sum_range (D k : ℕ) :
    (Finset.Nat.antidiagonalTuple (D + 1) k).card =
      ∑ i ∈ Finset.range (k + 1), (Finset.Nat.antidiagonalTuple D (k - i)).card := by
  calc (Finset.Nat.antidiagonalTuple (D + 1) k).card
      = ((Finset.range (k + 1)).sigma fun i => Finset.Nat.antidiagonalTuple D (k - i)).card := by
        refine Finset.card_nbij' (fun x => ⟨x 0, Fin.tail x⟩) (fun p => Fin.cons p.1 p.2)
          ?_ ?_ ?_ ?_
        · intro x hx
          simp only [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple] at hx
          rw [Fin.sum_univ_succ] at hx
          simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range,
            Finset.Nat.mem_antidiagonalTuple, Fin.tail]
          omega
        · rintro ⟨i, y⟩ hp
          simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range,
            Finset.Nat.mem_antidiagonalTuple] at hp
          simp only [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_succ,
            Fin.cons_zero, Fin.cons_succ]
          omega
        · intro x _
          simp
        · rintro ⟨i, y⟩ _
          simp
    _ = ∑ i ∈ Finset.range (k + 1), (Finset.Nat.antidiagonalTuple D (k - i)).card :=
        Finset.card_sigma _ _

/- English proof (translation)
Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities.
-/
private theorem card_antidiagonal_tuple_succ_eq_choose (D : ℕ) :
    ∀ k, (Finset.Nat.antidiagonalTuple (D + 1) k).card = (k + D).choose D := by
  induction D with
  | zero =>
    intro k
    rw [card_antidiagonal_tuple_succ_eq_sum_range, Finset.sum_eq_single k]
    · simp [Finset.Nat.antidiagonalTuple_zero_zero]
    · intro i hi hik
      simp only [Finset.mem_range] at hi
      obtain ⟨m, hm⟩ : ∃ m, k - i = m + 1 := ⟨k - i - 1, by omega⟩
      rw [hm, Finset.Nat.antidiagonalTuple_zero_succ, Finset.card_empty]
    · intro h
      simp at h
  | succ D ih =>
    intro k
    rw [card_antidiagonal_tuple_succ_eq_sum_range]
    simp only [ih]
    have h : ∑ j ∈ Finset.range (k + 1), (k - j + D).choose D =
        ∑ j ∈ Finset.range (k + 1), (j + D).choose D := by
      have := Finset.sum_range_reflect (fun i => (i + D).choose D) (k + 1)
      simpa only [Nat.add_sub_cancel] using this
    rw [h, sum_range_add_choose_eq_choose_succ, Nat.add_assoc]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data. Treat this case separately. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Treat this case separately. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem sum_antidiagonalTuple : PI.SumAntidiagonalTuple := by
  intro D T hDT
  cases D with
  | zero =>
    obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
    simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.choose_zero_right]
    rw [Finset.sum_range_succ']
    simp [Finset.Nat.antidiagonalTuple_zero_succ, Finset.Nat.antidiagonalTuple_zero_zero]
  | succ E =>
    obtain ⟨n, rfl⟩ : ∃ n, T = n + E + 2 := ⟨T - E - 2, by omega⟩
    have h1 : n + E + 2 - (E + 1) = n + 1 := by omega
    have h2 : n + E + 2 - 1 = n + E + 1 := by omega
    rw [h1, h2]
    simp only [card_antidiagonal_tuple_succ_eq_choose]
    exact sum_range_add_choose_eq_choose_succ E n
