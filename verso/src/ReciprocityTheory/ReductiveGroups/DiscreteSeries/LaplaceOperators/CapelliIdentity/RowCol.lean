import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.RowAnti
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.ProdOfFnUpdateEq
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.RowColA

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

open ReciprocityTheory.ChartRestriction.DS

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)

/- English proof (translation)
Establish `hne : ((k + 1 : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)`. Establish `h' : ((k + 1 : ℕ) : ℂ) • a = ((k + 1 : ℕ) : ℂ) • b`. Rewrite using `[Nat.cast_smul_eq_nsmul ℂ, Nat.cast_smul_eq_nsmul ℂ]`. Conclude with `h`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem eq_of_succ_nsmul_eq_succ_nsmul {M : Type*} [AddCommGroup M] [Module ℂ M] (k : ℕ) {a b : M}
    (h : (k + 1) • a = (k + 1) • b) : a = b := by
  have hne : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  have h' : ((k + 1 : ℕ) : ℂ) • a = ((k + 1 : ℕ) : ℂ) • b := by
    rw [Nat.cast_smul_eq_nsmul ℂ, Nat.cast_smul_eq_nsmul ℂ]; exact h
  calc a = ((k + 1 : ℕ) : ℂ)⁻¹ • (((k + 1 : ℕ) : ℂ) • a) := (inv_smul_smul₀ hne a).symm
    _ = ((k + 1 : ℕ) : ℂ)⁻¹ • (((k + 1 : ℕ) : ℂ) • b) := by rw [h']
    _ = b := inv_smul_smul₀ hne b

/- English proof (translation)
Simplify using `only [Finset.sum_sub_distrib]`. Establish `h1 : ∑ i : Fin (p + 1), ∑ j : Fin (p + 1), ∑ t : Fin p, T (i.succAbove t) j = ∑ j : Fin (p + 1), p • ∑ s, T s j`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl (fun j _ => sum_sum_succAbove (fun s => T s j))`. Establish `h2 : ∑ i : Fin (p + 1), ∑ j : Fin (p + 1), ∑ t : Fin p, T i (j.succAbove t) = ∑ i : Fin (p + 1), p • ∑ s, T i s` using `Finset.sum_congr rfl (fun i _ => sum_sum_succAbove (fun s => T i s))`.

Rewrite using `[h1, h2, ← Finset.smul_sum, ← Finset.smul_sum, sub_eq_zero]`. Use `congr 1`. Conclude with `Finset.sum_comm`.
-/
private theorem sum_sum_sub_sum_succAbove_eq_zero {M : Type*} [AddCommGroup M] {p : ℕ}
    (T : Fin (p + 1) → Fin (p + 1) → M) :
    ∑ i : Fin (p + 1), ∑ j : Fin (p + 1),
      (∑ t : Fin p, T (i.succAbove t) j - ∑ t : Fin p, T i (j.succAbove t)) = 0 := by
  simp only [Finset.sum_sub_distrib]
  have h1 : ∑ i : Fin (p + 1), ∑ j : Fin (p + 1), ∑ t : Fin p, T (i.succAbove t) j =
      ∑ j : Fin (p + 1), p • ∑ s, T s j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => sum_sum_succAbove (fun s => T s j))
  have h2 : ∑ i : Fin (p + 1), ∑ j : Fin (p + 1), ∑ t : Fin p, T i (j.succAbove t) =
      ∑ i : Fin (p + 1), p • ∑ s, T i s :=
    Finset.sum_congr rfl (fun i _ => sum_sum_succAbove (fun s => T i s))
  rw [h1, h2, ← Finset.smul_sum, ← Finset.smul_sum, sub_eq_zero]
  congr 1
  exact Finset.sum_comm

/- English proof (translation)
Use `revert R C x`. Proceed by induction on `p with`. Consider the case `zero`. Introduce `R C x`. Simplify using `[cminor, rminor]`.

Consider the case `succ p ih`. Introduce `R C x`. Apply the tactic sequence `have hcol : ∑ _j : Fin (p + 1), cminor E R C x = ∑ i : Fin (p + 1), ∑ j : Fin (p + 1), ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) • (capEntry E x (R i) (C j) * cminor E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1)) := by`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl (fun j _ => cminor_col_at E hE R C j x)`.

Apply the tactic sequence `have hrow : ∑ _i : Fin (p + 1), rminor E R C x = ∑ i : Fin (p + 1), ∑ j : Fin (p + 1), ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) • (cminor E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1) * capEntry E x (R i) (C j)) := by`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[rminor_row_at E hE R C i x]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[ih]`.

Apply the tactic sequence `have hij : ∀ i j : Fin (p + 1), ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) • (capEntry E x (R i) (C j) * cminor E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1)) - ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) • (cminor E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1) * capEntry E x (R i) (C j)) = ∑ t, capT …`. Introduce `i j`. Rewrite using `[← smul_sub, capEntry_comm_sub]`. Conclude with `comm_term E hE R C i j (x - 1)`. Establish `hdiff : ∑ _j : Fin (p + 1), cminor E R C x - ∑ _i : Fin (p + 1), rminor E R C x = 0`.

Rewrite using `[hcol, hrow, ← Finset.sum_sub_distrib]`. Simplify using `only [← Finset.sum_sub_distrib, hij]`. Establish `h0` using `sum_sum_sub_sum_succAbove_eq_zero (capT E R C (x - 1))`. Simplify using `only [Finset.sum_sub_distrib] at h0 ⊢`. Conclude with `h0`.

Establish `hs` using `sub_eq_zero.mp hdiff`. Rewrite `hs` using `[Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin]`. Conclude with `eq_of_succ_nsmul_eq_succ_nsmul p hs`.
-/
theorem cminor_eq_rminor (hE : GlRelR E) {p : ℕ} (R C : Fin p → Fin n) (x : ℂ) :
    cminor E R C x = rminor E R C x := by
  revert R C x
  induction p with
  | zero =>
    intro R C x
    simp [cminor, rminor]
  | succ p ih =>
    intro R C x
    have hcol : ∑ _j : Fin (p + 1), cminor E R C x =
        ∑ i : Fin (p + 1), ∑ j : Fin (p + 1), ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
          (capEntry E x (R i) (C j) * cminor E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1)) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun j _ => cminor_col_at E hE R C j x)
    have hrow : ∑ _i : Fin (p + 1), rminor E R C x =
        ∑ i : Fin (p + 1), ∑ j : Fin (p + 1), ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
          (cminor E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1) * capEntry E x (R i) (C j)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [rminor_row_at E hE R C i x]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [ih]
    have hij : ∀ i j : Fin (p + 1),
        ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
            (capEntry E x (R i) (C j) * cminor E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1)) -
          ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
            (cminor E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1) * capEntry E x (R i) (C j)) =
        ∑ t, capT E R C (x - 1) (i.succAbove t) j -
          ∑ t, capT E R C (x - 1) i (j.succAbove t) := by
      intro i j
      rw [← smul_sub, capEntry_comm_sub]
      exact comm_term E hE R C i j (x - 1)
    have hdiff : ∑ _j : Fin (p + 1), cminor E R C x - ∑ _i : Fin (p + 1), rminor E R C x = 0 := by
      rw [hcol, hrow, ← Finset.sum_sub_distrib]
      simp only [← Finset.sum_sub_distrib, hij]
      have h0 := sum_sum_sub_sum_succAbove_eq_zero (capT E R C (x - 1))
      simp only [Finset.sum_sub_distrib] at h0 ⊢
      exact h0
    have hs := sub_eq_zero.mp hdiff
    rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hs
    exact eq_of_succ_nsmul_eq_succ_nsmul p hs

/- English proof (translation)
Rewrite using `[cminor_eq_rminor E hE, rminor_succ_row]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[cminor_eq_rminor E hE]`.
-/
theorem cminor_succ_row (hE : GlRelR E) {p : ℕ} (R C : Fin (p + 1) → Fin n) (x : ℂ) :
    cminor E R C x = ∑ j : Fin (p + 1), ((-1 : ℂ) ^ (j : ℕ)) •
      (capEntry E (x - (p : ℂ)) (R 0) (C j) * cminor E (R ∘ Fin.succ) (C ∘ j.succAbove) x) := by
  rw [cminor_eq_rminor E hE, rminor_succ_row]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [cminor_eq_rminor E hE]

end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
