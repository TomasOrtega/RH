import Development.DiscreteGroups.GlobalIrreducibility.MulRowOfGood

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
Introduce `i l h`. Rewrite using `[val_colU, Matrix.add_apply, colM_apply, if_neg (by omega), add_zero]`.
-/
theorem good_colU (j : ℕ) (c : Fin n → k) : Good j ((colU j c : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro i l h
  rw [val_colU, Matrix.add_apply, colM_apply, if_neg (by omega), add_zero]

/- English proof (translation)
Rewrite using `[colU_inv]`. Conclude with `good_colU j _`.
-/
theorem good_colU_inv (j : ℕ) (c : Fin n → k) :
    Good j (((colU j c)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  rw [colU_inv]; exact good_colU j _

/- English proof (translation)
Rewrite using `[Units.val_mul, colU_mul_apply j hj]`. Both sides reduce to the same expression.
-/
theorem peel_apply (j : ℕ) (hj : j < n) (g : GL (Fin n) k) (i l : Fin n) :
    ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i l =
      (g : Matrix (Fin n) (Fin n) k) i l + (if i.val < j then
        -(g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩ * (g : Matrix (Fin n) (Fin n) k) ⟨j, hj⟩ l else 0) := by
  rw [Units.val_mul, colU_mul_apply j hj]
  rfl

/- English proof (translation)
Establish `hg' : ∀ i l : Fin n, (l ≤ i ∨ l.val < j) → (g : Matrix (Fin n) (Fin n) k) i l = (1 : Matrix (Fin n) (Fin n) k) i l` using `hg`. Establish `hjj : (g : Matrix (Fin n) (Fin n) k) ⟨j, hj⟩ ⟨j, hj⟩ = 1` using `by rw [hg' _ _ (Or.inl le_rfl), one_apply_eq]`. Establish `hrow : ∀ l : Fin n, l.val < j → (g : Matrix (Fin n) (Fin n) k) ⟨j, hj⟩ l = 0` using `fun l hl => by`. Rewrite using `[hg' _ _ (Or.inr hl), one_apply_ne]`. Introduce `h`.

Rewrite `hl` using `[← h]`. Simplify using `at hl`. Establish `hhi : ∀ i l : Fin n, j ≤ i.val → ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i l = (g : Matrix (Fin n) (Fin n) k) i l` using `fun i l hi => by`. Rewrite using `[peel_apply, if_neg (by omega), add_zero]`. Use `⟨fun i l hil => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[peel_apply]`. Distinguish the cases in `hl : l.val < j`. Rewrite using `[hg' i l (Or.inr hl), hrow l hl]`. Simplify using the standard rewrite rules. Distinguish the cases in `hlj : l.val = j`.

Establish `hl' : l = ⟨j, hj⟩` using `Fin.ext hlj`. Substitute `hl'` using the available equality. Distinguish the cases in `hi : i.val < j`. Rewrite using `[if_pos hi, hjj, mul_one, add_neg_cancel, one_apply_ne]`. Introduce `h`.

Rewrite `hi` using `[h]`. Simplify using `at hi`. Rewrite using `[if_neg hi, add_zero]`. Conclude with `hg' i _ (Or.inl (by rw [Fin.le_iff_val_le_val]; simp; omega))`. Establish `hli : l ≤ i` using `hil.resolve_right (by omega)`.

Rewrite using `[if_neg (by rw [Fin.le_iff_val_le_val] at hli; omega), add_zero]`. Conclude with `hg' i l (Or.inl hli)`. Establish `key : ∀ i l : Fin n, (if l.val = i.val + 1 ∧ j ≤ l.val then (g : Matrix (Fin n) (Fin n) k) i l else 0) = (if l.val = i.val + 1 ∧ j + 1 ≤ l.val then ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i l else 0) + (if i …`. Introduce `i l`. Distinguish the cases in `h2 : l.val = i.val + 1 ∧ j + 1 ≤ l.val`.

Rewrite using `[if_pos ⟨h2.1, by omega⟩, if_pos h2, hhi i l (by omega), if_neg (fun h => by rw [Fin.ext_iff] at h; simp at h; omega), add_zero]`. Rewrite using `[if_neg h2, zero_add]`. Distinguish the cases in `h1 : l.val = i.val + 1 ∧ j ≤ l.val`. Establish `e1 : i = ⟨j - 1, by omega⟩` using `Fin.ext (by simp; omega)`. Establish `e2 : l = ⟨j, hj⟩` using `Fin.ext (by simp; omega)`.

Rewrite using `[if_pos h1, if_pos e1, if_pos e2]`. Rewrite using `[if_neg h1]`. Distinguish the cases in `e1 : i = ⟨j - 1, by omega⟩`. Distinguish the cases in `e2 : l = ⟨j, hj⟩`. It suffices to derive a contradiction.

Apply `h1` to reduce the goal to its premises. Rewrite using `[e1, e2]`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_pos e1, if_neg e2]`.

Rewrite using `[if_neg e1]`. Rewrite using `[sdS, sdS]`. Simplify using `only [key, Finset.sum_add_distrib]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem peel_N (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) {g : GL (Fin n) k} (hg : g ∈ Nset j) :
    colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g ∈ Nset (j + 1) ∧
    sdS j (g : Matrix (Fin n) (Fin n) k) =
      sdS (j + 1) ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) + (g : Matrix (Fin n) (Fin n) k) ⟨j - 1, by omega⟩ ⟨j, hj⟩ := by
  have hg' : ∀ i l : Fin n, (l ≤ i ∨ l.val < j) → (g : Matrix (Fin n) (Fin n) k) i l = (1 : Matrix (Fin n) (Fin n) k) i l := hg
  have hjj : (g : Matrix (Fin n) (Fin n) k) ⟨j, hj⟩ ⟨j, hj⟩ = 1 := by rw [hg' _ _ (Or.inl le_rfl), one_apply_eq]
  have hrow : ∀ l : Fin n, l.val < j → (g : Matrix (Fin n) (Fin n) k) ⟨j, hj⟩ l = 0 := fun l hl => by
    rw [hg' _ _ (Or.inr hl), one_apply_ne]; intro h; rw [← h] at hl; simp at hl
  have hhi : ∀ i l : Fin n, j ≤ i.val → ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) :
      Matrix (Fin n) (Fin n) k) i l = (g : Matrix (Fin n) (Fin n) k) i l := fun i l hi => by
    rw [peel_apply, if_neg (by omega), add_zero]
  refine ⟨fun i l hil => ?_, ?_⟩
  · rw [peel_apply]
    by_cases hl : l.val < j
    · rw [hg' i l (Or.inr hl), hrow l hl]; simp
    · by_cases hlj : l.val = j
      · have hl' : l = ⟨j, hj⟩ := Fin.ext hlj
        subst hl'
        by_cases hi : i.val < j
        · rw [if_pos hi, hjj, mul_one, add_neg_cancel, one_apply_ne]
          intro h; rw [h] at hi; simp at hi
        · rw [if_neg hi, add_zero]
          exact hg' i _ (Or.inl (by rw [Fin.le_iff_val_le_val]; simp; omega))
      · have hli : l ≤ i := hil.resolve_right (by omega)
        rw [if_neg (by rw [Fin.le_iff_val_le_val] at hli; omega), add_zero]
        exact hg' i l (Or.inl hli)
  · have key : ∀ i l : Fin n, (if l.val = i.val + 1 ∧ j ≤ l.val then (g : Matrix (Fin n) (Fin n) k) i l else 0) =
        (if l.val = i.val + 1 ∧ j + 1 ≤ l.val then ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) :
          Matrix (Fin n) (Fin n) k) i l else 0) +
        (if i = (⟨j - 1, by omega⟩ : Fin n) then (if l = (⟨j, hj⟩ : Fin n) then (g : Matrix (Fin n) (Fin n) k) i l else 0) else 0) := by
      intro i l
      by_cases h2 : l.val = i.val + 1 ∧ j + 1 ≤ l.val
      · rw [if_pos ⟨h2.1, by omega⟩, if_pos h2, hhi i l (by omega),
          if_neg (fun h => by rw [Fin.ext_iff] at h; simp at h; omega), add_zero]
      · rw [if_neg h2, zero_add]
        by_cases h1 : l.val = i.val + 1 ∧ j ≤ l.val
        · have e1 : i = ⟨j - 1, by omega⟩ := Fin.ext (by simp; omega)
          have e2 : l = ⟨j, hj⟩ := Fin.ext (by simp; omega)
          rw [if_pos h1, if_pos e1, if_pos e2]
        · rw [if_neg h1]
          by_cases e1 : i = ⟨j - 1, by omega⟩
          · by_cases e2 : l = ⟨j, hj⟩
            · exfalso; apply h1; rw [e1, e2]; simp; omega
            · rw [if_pos e1, if_neg e2]
          · rw [if_neg e1]
    rw [sdS, sdS]
    simp only [key, Finset.sum_add_distrib]
    congr 1
    simp

end DiscreteGroups.sglob.LConvGenM
