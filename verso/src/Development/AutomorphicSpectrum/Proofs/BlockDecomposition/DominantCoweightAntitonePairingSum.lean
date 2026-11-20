import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.LamGap

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Rewrite the conclusion using the stated equalities.
-/
theorem sum_lt_indicator (N m : ℕ) (h : m ≤ N) :
    (∑ i : Fin N, if (i : ℕ) < m then 1 else 0) = m := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < m then 1 else 0) N, Finset.sum_boole]
  have hf : (Finset.range N).filter (fun i => i < m) = Finset.range m := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hf, Finset.card_range, Nat.cast_id]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Rewrite the conclusion using the stated equalities.
-/
theorem sum_ge_indicator (N m : ℕ) (h : m ≤ N) :
    (∑ i : Fin N, if m ≤ (i : ℕ) then 1 else 0) = N - m := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if m ≤ i then 1 else 0) N, Finset.sum_boole]
  have hf : (Finset.range N).filter (fun i => m ≤ i) = Finset.Ico m N := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hf, Nat.card_Ico, Nat.cast_id]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities.
-/
theorem lamOf_sub {N : ℕ} (g : Fin (N - 1) → ℕ) (i i' : Fin N) (h : i < i') :
    (Zls.lamOf g i - Zls.lamOf g i').toNat
      = ∑ j : Fin (N - 1), if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 := by
  have hii : (i : ℕ) < (i' : ℕ) := h
  have key : Zls.lamOf g i - Zls.lamOf g i'
      = ((∑ j : Fin (N - 1), if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 : ℕ) : ℤ) := by
    simp only [Zls.lamOf]
    rw [← Finset.sum_sub_distrib, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp_all <;> omega
  rw [key, Int.toNat_natCast]

/- English proof (translation)
Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem gap_count (N : ℕ) (c j : ℕ) (hj : j + 1 ≤ N) :
    (∑ i : Fin N, ∑ i' : Fin N, if (i : ℕ) ≤ j ∧ j < (i' : ℕ) then c else 0)
      = c * ((j + 1) * (N - (j + 1))) := by
  calc (∑ i : Fin N, ∑ i' : Fin N, if (i : ℕ) ≤ j ∧ j < (i' : ℕ) then c else 0)
      = ∑ i : Fin N, ∑ i' : Fin N,
          c * ((if (i : ℕ) < j + 1 then 1 else 0) * (if j + 1 ≤ (i' : ℕ) then 1 else 0)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
        have a1 : ((i : ℕ) < j + 1) ↔ (i : ℕ) ≤ j := by omega
        have a2 : (j + 1 ≤ (i' : ℕ)) ↔ j < (i' : ℕ) := by omega
        simp only [a1, a2]
        split_ifs <;> simp_all
    _ = c * ((∑ i : Fin N, if (i : ℕ) < j + 1 then 1 else 0) *
          (∑ i' : Fin N, if j + 1 ≤ (i' : ℕ) then 1 else 0)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ = c * ((j + 1) * (N - (j + 1))) := by
        rw [sum_lt_indicator N (j + 1) hj, sum_ge_indicator N (j + 1) hj]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Use symmetry to reverse the relation. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Use linear arithmetic over natural numbers and integers. Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem lamOf_antitone_gap_sum (N : ℕ) (g : Fin (N - 1) → ℕ) :
    Antitone (Zls.lamOf g) ∧
      (∑ i : Fin N, ∑ i' : Fin N,
          if i < i' then (Zls.lamOf g i - Zls.lamOf g i').toNat else 0)
        = ∑ j : Fin (N - 1), g j * (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) := by
  refine ⟨fun a b hab => ?_, ?_⟩
  · simp only [Zls.lamOf]
    refine Finset.sum_le_sum fun j _ => ?_
    have hab' : (a : ℕ) ≤ (b : ℕ) := hab
    split_ifs <;> omega
  · have step : ∀ i i' : Fin N,
        (if i < i' then (Zls.lamOf g i - Zls.lamOf g i').toNat else 0)
          = ∑ j : Fin (N - 1), if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 := by
      intro i i'
      split_ifs with hlt
      · exact lamOf_sub g i i' hlt
      · symm
        refine Finset.sum_eq_zero fun j _ => ?_
        have hn : ¬ ((i : ℕ) < (i' : ℕ)) := hlt
        rw [if_neg]
        rintro ⟨h1, h2⟩
        omega
    calc (∑ i : Fin N, ∑ i' : Fin N,
            if i < i' then (Zls.lamOf g i - Zls.lamOf g i').toNat else 0)
        = ∑ i : Fin N, ∑ i' : Fin N, ∑ j : Fin (N - 1),
            if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => step i i'
      _ = ∑ i : Fin N, ∑ j : Fin (N - 1), ∑ i' : Fin N,
            if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ j : Fin (N - 1), ∑ i : Fin N, ∑ i' : Fin N,
            if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 :=
          Finset.sum_comm
      _ = ∑ j : Fin (N - 1), g j * (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          exact gap_count N (g j) j (by have := j.isLt; omega)

end GlobalTheory.CompanionTheory.LamGap
