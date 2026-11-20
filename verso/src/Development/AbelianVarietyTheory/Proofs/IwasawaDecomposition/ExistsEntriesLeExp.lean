import Mathlib

namespace GlobalTheory.EntriesExpBound

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Conclude with `⟨0, by rw [hx]; exact zero_le'⟩`. Use `⟨(WithZero.log x).toNat, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_nat_le_exp (x : WithZero (Multiplicative ℤ)) :
    ∃ k : ℕ, x ≤ WithZero.exp (k : ℤ) := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx]; exact zero_le'⟩
  · refine ⟨(WithZero.log x).toNat, ?_⟩
    calc x = WithZero.exp (WithZero.log x) := (WithZero.exp_log hx).symm
      _ ≤ _ := WithZero.exp_le_exp.mpr (Int.self_le_toNat _)

/- English proof (translation)
Use `choose f hf using fun p : Fin m × Fin m => exists_nat_le_exp ((Valued.v : K → WithZero (Multiplicative ℤ)) (A p.1 p.2))`. Use `⟨Finset.univ.sup f, fun r s => (hf (r, s)).trans ?_⟩` and prove the remaining obligations. Conclude with `WithZero.exp_le_exp.mpr (Int.ofNat_le.mpr (Finset.le_sup (f := f) (Finset.mem_univ (r, s))))`.
-/
theorem exists_entries_le_exp {K : Type} [inst : Field K]
    [inst_1 : Valued K (WithZero (Multiplicative ℤ))] {m : ℕ} (A : Matrix (Fin m) (Fin m) K) :
    ∃ (k : ℕ), ∀ (r s : Fin m),
      (Valued.v : K → WithZero (Multiplicative ℤ)) (A r s) ≤ WithZero.exp (↑k : ℤ) := by
  choose f hf using fun p : Fin m × Fin m =>
    exists_nat_le_exp ((Valued.v : K → WithZero (Multiplicative ℤ)) (A p.1 p.2))
  refine ⟨Finset.univ.sup f, fun r s => (hf (r, s)).trans ?_⟩
  exact WithZero.exp_le_exp.mpr
    (Int.ofNat_le.mpr (Finset.le_sup (f := f) (Finset.mem_univ (r, s))))

end GlobalTheory.EntriesExpBound
