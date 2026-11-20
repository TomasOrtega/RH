import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CoeffSingleLawAdd

set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.LowLaw

/- English proof (translation)
Establish `hne : e ≠ 0` using `by rintro rfl; simp at h`. Take `⟨j, hj⟩` from `Finsupp.support_nonempty_iff.mpr hne`. Establish `hle : Finsupp.single j 1 ≤ e`. Rewrite using `[Finsupp.single_le_iff]`. Conclude with `Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)`.

Use `⟨j, ?_⟩` and prove the remaining obligations. Establish `hsum : e = (e - Finsupp.single j 1) + Finsupp.single j 1` using `(tsub_add_cancel_of_le hle).symm`. Establish `hd : (e - Finsupp.single j 1).degree = 0`. Establish `h2` using `congrArg Finsupp.degree hsum`. Rewrite `h2` using `[map_add, Finsupp.degree_single, h]`.

Use linear arithmetic over natural numbers and integers. Rewrite `hd` using `[Finsupp.degree_eq_zero_iff]`. Rewrite using `[hsum, hd, zero_add]`.
-/
theorem eq_single_of_degree_eq_one {σ : Type} {e : σ →₀ ℕ} (h : e.degree = 1) :
    ∃ j, e = Finsupp.single j 1 := by
  classical
  have hne : e ≠ 0 := by rintro rfl; simp at h
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hne
  have hle : Finsupp.single j 1 ≤ e := by
    rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
  refine ⟨j, ?_⟩
  have hsum : e = (e - Finsupp.single j 1) + Finsupp.single j 1 := (tsub_add_cancel_of_le hle).symm
  have hd : (e - Finsupp.single j 1).degree = 0 := by
    have h2 := congrArg Finsupp.degree hsum
    rw [map_add, Finsupp.degree_single, h] at h2
    omega
  rw [Finsupp.degree_eq_zero_iff] at hd
  rw [hsum, hd, zero_add]

/- English proof (translation)
Simplify using `only [addLaw, map_add, coeff_X]`. Distinguish the cases in `h1 : α = Finsupp.single (Sum.inl i) 1`. Establish `h2 : α ≠ Finsupp.single (Sum.inr i) 1`. Rewrite using `[h1]`. Introduce `h`.

Conclude with `Sum.inl_ne_inr ((Finsupp.single_left_inj one_ne_zero).1 h)`. Rewrite using `[if_pos h1, if_neg h2, if_pos (Or.inl h1), add_zero]`. Rewrite using `[if_neg h1, zero_add]`. Distinguish the cases in `h2 : α = Finsupp.single (Sum.inr i) 1`. Rewrite using `[if_pos h2, if_pos (Or.inr h2)]`.

Rewrite using `[if_neg h2, if_neg (by tauto)]`.
-/
theorem coeff_addLaw (R : Type) [CommRing R] (d : ℕ) (i : Fin d) (α : Fin d ⊕ Fin d →₀ ℕ) :
    coeff α (addLaw R d i) =
      if α = Finsupp.single (Sum.inl i) 1 ∨ α = Finsupp.single (Sum.inr i) 1 then 1 else 0 := by
  classical
  simp only [addLaw, map_add, coeff_X]
  by_cases h1 : α = Finsupp.single (Sum.inl i) 1
  · have h2 : α ≠ Finsupp.single (Sum.inr i) 1 := by
      rw [h1]; intro h
      exact Sum.inl_ne_inr ((Finsupp.single_left_inj one_ne_zero).1 h)
    rw [if_pos h1, if_neg h2, if_pos (Or.inl h1), add_zero]
  · rw [if_neg h1, zero_add]
    by_cases h2 : α = Finsupp.single (Sum.inr i) 1
    · rw [if_pos h2, if_pos (Or.inr h2)]
    · rw [if_neg h2, if_neg (by tauto)]

variable {k : Type} [CommRing k] {d : ℕ}

/- English proof (translation)
Establish `hu` using `congrArg (coeff (Finsupp.single j 1)) (congrFun h.unit i)`. Simplify using `only [op, at2] at hu`. Apply the tactic sequence `rw [GlobalTheory.FormalCalc.coeff_single_subst (fun s => by cases s <;> simp), Fintype.sum_sum_type] at hu`. Simplify `hu` using `[coeff_X, Finsupp.single_left_inj]`.
-/
theorem coeff_inl {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (h : IsLaw μ) (i j : Fin d) :
    coeff (Finsupp.single (Sum.inl j) 1) (μ i) = if j = i then 1 else 0 := by
  classical
  have hu := congrArg (coeff (Finsupp.single j 1)) (congrFun h.unit i)
  simp only [op, at2] at hu
  rw [GlobalTheory.FormalCalc.coeff_single_subst (fun s => by cases s <;> simp), Fintype.sum_sum_type] at hu
  simpa [coeff_X, Finsupp.single_left_inj] using hu

/- English proof (translation)
Establish `hc` using `congrArg (coeff (Finsupp.single (Sum.inr j) 1)) (h.comm i)`. Simplify using `only [swap, at2] at hc`. Apply the tactic sequence `rw [GlobalTheory.FormalCalc.coeff_single_subst (fun s => by cases s <;> simp), Fintype.sum_sum_type] at hc`. Rewrite using `[← hc, ← coeff_inl h i j]`. Simplify using `[coeff_X, Finsupp.single_left_inj]`.
-/
theorem coeff_inr {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (h : IsLaw μ) (i j : Fin d) :
    coeff (Finsupp.single (Sum.inr j) 1) (μ i) = if j = i then 1 else 0 := by
  classical
  have hc := congrArg (coeff (Finsupp.single (Sum.inr j) 1)) (h.comm i)
  simp only [swap, at2] at hc
  rw [GlobalTheory.FormalCalc.coeff_single_subst (fun s => by cases s <;> simp), Fintype.sum_sum_type] at hc
  rw [← hc, ← coeff_inl h i j]
  simp [coeff_X, Finsupp.single_left_inj]

end GlobalTheory.Katz.LowLaw

namespace GlobalTheory.Katz

open LowLaw in

/- English proof (translation)
Establish `h1 : coeff α (μ i) = coeff α (addLaw k d i)`. Break down `Nat.le_one_iff_eq_zero_or_eq_one.1 hα with h0 | h1` into its components or cases. Rewrite using `[(Finsupp.degree_eq_zero_iff α).1 h0, coeff_zero_eq_constantCoeff_apply, h.const, coeff_addLaw, if_neg]`. Apply the tactic sequence `rintro (h | h) <;> exact Finsupp.single_ne_zero.2 one_ne_zero h.symm`. Take `⟨s, rfl⟩` from `eq_single_of_degree_eq_one h1`.

Break down `s with j | j` into its components or cases. Rewrite using `[coeff_inl h, coeff_addLaw]`. Simplify using `[Finsupp.single_left_inj]`. Rewrite using `[coeff_inr h, coeff_addLaw]`. Simplify using `[Finsupp.single_left_inj]`.

Use `⟨h1, ?_⟩` and prove the remaining obligations. Rewrite using `[coeff_lift, h1, coeff_addLaw, coeff_addLaw]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem coeff_law_of_degree_le_one (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ)
    (i : Fin d) (α : Fin d ⊕ Fin d →₀ ℕ) (hα : α.degree ≤ 1) :
    coeff α (μ i) = coeff α (addLaw k d i) ∧
      coeff α (Katz.lift p (μ i)) = coeff α (addLaw (Fr p k) d i) := by
  classical
  have h1 : coeff α (μ i) = coeff α (addLaw k d i) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hα with h0 | h1
    · rw [(Finsupp.degree_eq_zero_iff α).1 h0, coeff_zero_eq_constantCoeff_apply, h.const,
        coeff_addLaw, if_neg]
      rintro (h | h) <;> exact Finsupp.single_ne_zero.2 one_ne_zero h.symm
    · obtain ⟨s, rfl⟩ := eq_single_of_degree_eq_one h1
      rcases s with j | j
      · rw [coeff_inl h, coeff_addLaw]; simp [Finsupp.single_left_inj]
      · rw [coeff_inr h, coeff_addLaw]; simp [Finsupp.single_left_inj]
  refine ⟨h1, ?_⟩
  rw [coeff_lift, h1, coeff_addLaw, coeff_addLaw]
  split_ifs <;> simp

end GlobalTheory.Katz
