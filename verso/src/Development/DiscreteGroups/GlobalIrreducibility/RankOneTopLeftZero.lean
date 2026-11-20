import Development.DiscreteGroups.GlobalIrreducibility.EntriesOfMemUnipRad

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

/- English proof (translation)
Use `set X := (x : Matrix (Fin n) (Fin n) k)`. Use `set Y := ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)`. Establish `hYX : Y * X = 1` using `by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `hYC : Y * colM j c = colM j (colMul j Y c)`. Use extensionality with `i b`.

Rewrite using `[mul_apply, colM_apply]`. Distinguish the cases in `hb : b.val = j`. Simplify using `only [colM_apply, hb, and_true]`. Distinguish the cases in `hi : i.val < j`. Rewrite using `[if_pos hi, colMul]`.

Apply the tactic sequence `exact Finset.sum_congr rfl fun a _ => by split_ifs <;> simp`. Rewrite using `[if_neg hi]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Use `split_ifs with ha`. Rewrite using `[hy i a (Or.inl (by omega)), one_apply_ne (by intro e; rw [e] at hi; omega), zero_mul]`.

Rewrite using `[mul_zero]`. Simplify using `[colM_apply, hb]`. Establish `hCX : ∀ d : Fin n → k, colM j d * X = colM j d`. Introduce `d`. Use extensionality with `i l`.

Rewrite using `[mul_apply, Finset.sum_eq_single (⟨j, hj⟩ : Fin n)]`. Rewrite using `[hx _ l (Or.inl le_rfl)]`. Distinguish the cases in `hl : (⟨j, hj⟩ : Fin n) = l`. Rewrite using `[← hl, one_apply_eq, mul_one]`. Rewrite using `[one_apply_ne hl, mul_zero, colM_apply, if_neg (fun h => hl (Fin.ext h.2.symm))]`.

Introduce `b _ hb`. Rewrite using `[colM_apply, if_neg (fun h => hb (Fin.ext h.2)), zero_mul]`. Simplify using the standard rewrite rules. Use extensionality with `: 1`. Rewrite using `[Units.val_mul, Units.val_mul, val_colU, val_colU, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hYX, hYC, hCX]`.
-/
theorem conj_colU (j : ℕ) (hj : j < n) (x : GL (Fin n) k) (hx : TopLeft j (x : Matrix (Fin n) (Fin n) k))
    (hy : TopLeft j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (c : Fin n → k) :
    x⁻¹ * colU j c * x = colU j (colMul j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) c) := by
  set X := (x : Matrix (Fin n) (Fin n) k)
  set Y := ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  have hYX : Y * X = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hYC : Y * colM j c = colM j (colMul j Y c) := by
    ext i b
    rw [mul_apply, colM_apply]
    by_cases hb : b.val = j
    · simp only [colM_apply, hb, and_true]
      by_cases hi : i.val < j
      · rw [if_pos hi, colMul]
        exact Finset.sum_congr rfl fun a _ => by split_ifs <;> simp
      · rw [if_neg hi]
        refine Finset.sum_eq_zero fun a _ => ?_
        split_ifs with ha
        · rw [hy i a (Or.inl (by omega)), one_apply_ne (by intro e; rw [e] at hi; omega), zero_mul]
        · rw [mul_zero]
    · simp [colM_apply, hb]
  have hCX : ∀ d : Fin n → k, colM j d * X = colM j d := by
    intro d
    ext i l
    rw [mul_apply, Finset.sum_eq_single (⟨j, hj⟩ : Fin n)]
    · rw [hx _ l (Or.inl le_rfl)]
      by_cases hl : (⟨j, hj⟩ : Fin n) = l
      · rw [← hl, one_apply_eq, mul_one]
      · rw [one_apply_ne hl, mul_zero, colM_apply, if_neg (fun h => hl (Fin.ext h.2.symm))]
    · intro b _ hb
      rw [colM_apply, if_neg (fun h => hb (Fin.ext h.2)), zero_mul]
    · simp
  ext : 1
  rw [Units.val_mul, Units.val_mul, val_colU, val_colU, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hYX, hYC, hCX]

def i0 (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) : Fin n := ⟨j - 1, by omega⟩

section RankOne

variable (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) (ξ : Fin n → k)

def vrow : Fin n → k := fun l => if l.val < j then ξ l - (if l = i0 j hj hj1 then 1 else 0) else 0

def R1 : Matrix (Fin n) (Fin n) k := Matrix.of fun i l => if i = i0 j hj hj1 then vrow j hj hj1 ξ l else 0

/- English proof (translation)
Use extensionality with `i l`. Rewrite using `[mul_apply, Finset.sum_eq_single (i0 j hj hj1)]`. Apply the tactic sequence `simp only [R1, of_apply, Matrix.smul_apply, smul_eq_mul, if_true] split_ifs <;> ring`. Introduce `b _ hb`. Simplify using `[R1, hb]`.

Simplify using the standard rewrite rules.
-/
theorem rankOne_mul_self : R1 j hj hj1 ξ * R1 j hj hj1 ξ = (vrow j hj hj1 ξ (i0 j hj hj1)) • R1 j hj hj1 ξ := by
  ext i l
  rw [mul_apply, Finset.sum_eq_single (i0 j hj hj1)]
  · simp only [R1, of_apply, Matrix.smul_apply, smul_eq_mul, if_true]
    split_ifs <;> ring
  · intro b _ hb; simp [R1, hb]
  · simp

/- English proof (translation)
Simplify using `[vrow, i0, show j - 1 < j by omega]`.
-/
theorem rowVector_at_index : vrow j hj hj1 ξ (i0 j hj hj1) = ξ (i0 j hj hj1) - 1 := by
  simp [vrow, i0, show j - 1 < j by omega]

/- English proof (translation)
Introduce `i l h`. Simplify using `only [R1, of_apply]`. Use `split_ifs with hi`. Establish `: ¬ l.val < j` using `by rw [hi] at h; simp [i0] at h; omega`. Simplify using `[vrow, this]`.

Both sides reduce to the same expression.
-/
theorem rankOne_top_left_zero : ∀ i l : Fin n, (j ≤ i.val ∨ j ≤ l.val) → R1 j hj hj1 ξ i l = 0 := by
  intro i l h
  simp only [R1, of_apply]
  split_ifs with hi
  · have : ¬ l.val < j := by rw [hi] at h; simp [i0] at h; omega
    simp [vrow, this]
  · rfl

end RankOne

end DiscreteGroups.sglob.LConvGenM
