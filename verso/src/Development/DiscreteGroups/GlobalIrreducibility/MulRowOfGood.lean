import Development.DiscreteGroups.GlobalIrreducibility.ColUSingleOfGe

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

def Nset (m : ℕ) : Set (GL (Fin n) k) :=
  {g | ∀ i l : Fin n, (l ≤ i ∨ l.val < m) → (g : Matrix (Fin n) (Fin n) k) i l = (1 : Matrix (Fin n) (Fin n) k) i l}

def sdS (m : ℕ) (M : Matrix (Fin n) (Fin n) k) : k :=
  ∑ i : Fin n, ∑ l : Fin n, if l.val = i.val + 1 ∧ m ≤ l.val then M i l else 0

def Good (j : ℕ) (x : Matrix (Fin n) (Fin n) k) : Prop :=
  ∀ i l : Fin n, (j ≤ i.val ∨ j + 1 ≤ l.val) → x i l = (1 : Matrix (Fin n) (Fin n) k) i l

/- English proof (translation)
Rewrite using `[mul_apply, Finset.sum_eq_single l]`. Rewrite using `[hY l l (Or.inr hl), one_apply_eq, mul_one]`. Introduce `b _ hb`. Rewrite using `[hY b l (Or.inr hl), one_apply_ne hb, mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem mul_col_of_good {j : ℕ} {Y : Matrix (Fin n) (Fin n) k} (hY : Good j Y) (M : Matrix (Fin n) (Fin n) k)
    {i l : Fin n} (hl : j + 1 ≤ l.val) : (M * Y) i l = M i l := by
  rw [mul_apply, Finset.sum_eq_single l]
  · rw [hY l l (Or.inr hl), one_apply_eq, mul_one]
  · intro b _ hb; rw [hY b l (Or.inr hl), one_apply_ne hb, mul_zero]
  · simp

/- English proof (translation)
Rewrite using `[mul_apply, Finset.sum_eq_single i]`. Rewrite using `[hX i i (Or.inl hi), one_apply_eq, one_mul]`. Introduce `b _ hb`. Rewrite using `[hX i b (Or.inl hi), one_apply_ne (Ne.symm hb), zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem mul_row_of_good {j : ℕ} {X : Matrix (Fin n) (Fin n) k} (hX : Good j X) (M : Matrix (Fin n) (Fin n) k)
    {i l : Fin n} (hi : j ≤ i.val) : (X * M) i l = M i l := by
  rw [mul_apply, Finset.sum_eq_single i]
  · rw [hX i i (Or.inl hi), one_apply_eq, one_mul]
  · intro b _ hb; rw [hX i b (Or.inl hi), one_apply_ne (Ne.symm hb), zero_mul]
  · simp

/- English proof (translation)
Use `set X := (x : Matrix (Fin n) (Fin n) k)`. Use `set Y := ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)`. Use `set G := (g : Matrix (Fin n) (Fin n) k)`. Establish `hXY : X * Y = 1` using `by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `hval : ((x * g * x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = X * G * Y`.

Simplify using `only [Units.val_mul, X, Y, G]`. Establish `hA : ∀ i l : Fin n, l.val < j + 1 → (X * G * Y) i l = (1 : Matrix (Fin n) (Fin n) k) i l`. Introduce `i l hl`. Establish `hGY : ∀ a, (G * Y) a l = Y a l`. Introduce `a`.

Rewrite using `[mul_apply, ← one_mul Y, mul_apply, one_mul]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hb : b.val < j + 1`. Conclude with `congrArg (· * Y b l) (hg a b (Or.inr hb))`. Establish `h1 : Y b l = 0`.

Rewrite using `[hy b l (Or.inl (by omega)), one_apply_ne]; intro h; rw [h] at hb; omega`. Rewrite using `[h1, mul_zero, mul_zero]`. Rewrite using `[Matrix.mul_assoc, mul_apply, ← hXY, mul_apply]`. Conclude with `Finset.sum_congr rfl fun a _ => by rw [hGY]`. Establish `hB : ∀ i l : Fin n, j ≤ i.val → j + 1 ≤ l.val → (X * G * Y) i l = G i l`.

Introduce `i l hi hl`. Rewrite using `[mul_col_of_good hy _ hl, mul_row_of_good hx _ hi]`. Use `⟨fun i l hil => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hval]`. Distinguish the cases in `hl : l.val < j + 1`.

Conclude with `hA i l hl`. Establish `hli : l ≤ i` using `hil.resolve_right hl`. Rewrite using `[hB i l (by rw [Fin.le_iff_val_le_val] at hli; omega) (by omega)]`. Conclude with `hg i l (Or.inl hli)`. Rewrite using `[hval, sdS, sdS]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Conclude with `hB i l (by omega) h.2`. Both sides reduce to the same expression.
-/
theorem good_conj {j : ℕ} (x : GL (Fin n) k) (hx : Good j (x : Matrix (Fin n) (Fin n) k))
    (hy : Good j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) {g : GL (Fin n) k} (hg : g ∈ Nset (j + 1)) :
    x * g * x⁻¹ ∈ Nset (j + 1) ∧ sdS (j + 1) ((x * g * x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      sdS (j + 1) (g : Matrix (Fin n) (Fin n) k) := by
  set X := (x : Matrix (Fin n) (Fin n) k)
  set Y := ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  set G := (g : Matrix (Fin n) (Fin n) k)
  have hXY : X * Y = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hval : ((x * g * x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = X * G * Y := by
    simp only [Units.val_mul, X, Y, G]

  have hA : ∀ i l : Fin n, l.val < j + 1 → (X * G * Y) i l = (1 : Matrix (Fin n) (Fin n) k) i l := by
    intro i l hl
    have hGY : ∀ a, (G * Y) a l = Y a l := by
      intro a
      rw [mul_apply, ← one_mul Y, mul_apply, one_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb : b.val < j + 1
      · exact congrArg (· * Y b l) (hg a b (Or.inr hb))
      · have h1 : Y b l = 0 := by
          rw [hy b l (Or.inl (by omega)), one_apply_ne]; intro h; rw [h] at hb; omega
        rw [h1, mul_zero, mul_zero]
    rw [Matrix.mul_assoc, mul_apply, ← hXY, mul_apply]
    exact Finset.sum_congr rfl fun a _ => by rw [hGY]

  have hB : ∀ i l : Fin n, j ≤ i.val → j + 1 ≤ l.val → (X * G * Y) i l = G i l := by
    intro i l hi hl
    rw [mul_col_of_good hy _ hl, mul_row_of_good hx _ hi]
  refine ⟨fun i l hil => ?_, ?_⟩
  · rw [hval]
    by_cases hl : l.val < j + 1
    · exact hA i l hl
    · have hli : l ≤ i := hil.resolve_right hl
      rw [hB i l (by rw [Fin.le_iff_val_le_val] at hli; omega) (by omega)]
      exact hg i l (Or.inl hli)
  · rw [hval, sdS, sdS]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    split_ifs with h
    · exact hB i l (by omega) h.2
    · rfl

end DiscreteGroups.sglob.LConvGenM
