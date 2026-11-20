import Development.DiscreteGroups.GlobalIrreducibility.ExistsAvgNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LongElementConjUnipotentRadical

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

def colM (j : ℕ) (c : Fin n → k) : Matrix (Fin n) (Fin n) k :=
  Matrix.of fun i l => if i.val < j ∧ l.val = j then c i else 0

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem colM_apply (j : ℕ) (c : Fin n → k) (i l : Fin n) :
    colM j c i l = if i.val < j ∧ l.val = j then c i else 0 := rfl

/- English proof (translation)
Use extensionality with `i l`. Simplify using `only [mul_apply, colM_apply, Matrix.zero_apply]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : i.val < j ∧ a.val = j`. Distinguish the cases in `h2 : a.val < j ∧ l.val = j`.

Conclude with `absurd h2.1 (by omega)`. Simplify using `[h2]`. Simplify using `[h1]`.
-/
theorem colM_mul (j : ℕ) (c d : Fin n → k) : colM j c * colM j d = 0 := by
  ext i l
  simp only [mul_apply, colM_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases h1 : i.val < j ∧ a.val = j
  · by_cases h2 : a.val < j ∧ l.val = j
    · exact absurd h2.1 (by omega)
    · simp [h2]
  · simp [h1]

/- English proof (translation)
Use extensionality with `i l`. Simplify using `only [colM_apply, Matrix.add_apply, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem colM_add (j : ℕ) (c d : Fin n → k) : colM j (c + d) = colM j c + colM j d := by
  ext i l
  simp only [colM_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

def colU (j : ℕ) (c : Fin n → k) : GL (Fin n) k :=
  ⟨1 + colM j c, 1 - colM j c, by rw [add_mul, one_mul, mul_sub, mul_one, colM_mul]; abel,
    by rw [sub_mul, one_mul, mul_add, mul_one, colM_mul]; abel⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_colU (j : ℕ) (c : Fin n → k) : (colU j c : Matrix (Fin n) (Fin n) k) = 1 + colM j c := rfl

/- English proof (translation)
Use extensionality with `: 1`. Rewrite using `[Units.val_mul, val_colU, val_colU, val_colU, colM_add, add_mul, one_mul, mul_add, mul_one, colM_mul]`. Normalize the expressions using the abelian group laws.
-/
theorem colU_add (j : ℕ) (c d : Fin n → k) : colU j (c + d) = colU j c * colU j d := by
  ext : 1
  rw [Units.val_mul, val_colU, val_colU, val_colU, colM_add, add_mul, one_mul, mul_add, mul_one, colM_mul]
  abel

/- English proof (translation)
Use extensionality with `: 1`. Rewrite using `[val_colU, Units.val_one]`. Establish `: colM j (0 : Fin n → k) = 0` using `by ext i l; simp [colM_apply]`. Rewrite using `[this, add_zero]`.
-/
theorem colU_zero (j : ℕ) : colU j (0 : Fin n → k) = 1 := by
  ext : 1
  rw [val_colU, Units.val_one]
  have : colM j (0 : Fin n → k) = 0 := by ext i l; simp [colM_apply]
  rw [this, add_zero]

/- English proof (translation)
Use `(inv_eq_of_mul_eq_one_right ?_)` and prove the remaining obligations. Rewrite using `[← colU_add, add_neg_cancel, colU_zero]`.
-/
theorem colU_inv (j : ℕ) (c : Fin n → k) : (colU j c)⁻¹ = colU j (-c) := by
  refine (inv_eq_of_mul_eq_one_right ?_)
  rw [← colU_add, add_neg_cancel, colU_zero]

/- English proof (translation)
Rewrite using `[val_colU, add_mul, one_mul, Matrix.add_apply, mul_apply]`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single (⟨j, hj⟩ : Fin n)]`. Apply the tactic sequence `simp only [colM_apply, and_true] split_ifs <;> simp`. Introduce `a _ ha`.

Establish `: ¬ (a.val = j)` using `fun h => ha (Fin.ext h)`. Simplify using `[colM_apply, this]`. Simplify using the standard rewrite rules.
-/
theorem colU_mul_apply (j : ℕ) (hj : j < n) (c : Fin n → k) (M : Matrix (Fin n) (Fin n) k) (i l : Fin n) :
    ((colU j c : Matrix (Fin n) (Fin n) k) * M) i l = M i l + (if i.val < j then c i * M ⟨j, hj⟩ l else 0) := by
  rw [val_colU, add_mul, one_mul, Matrix.add_apply, mul_apply]
  congr 1
  rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin n)]
  · simp only [colM_apply, and_true]
    split_ifs <;> simp
  · intro a _ ha
    have : ¬ (a.val = j) := fun h => ha (Fin.ext h)
    simp [colM_apply, this]
  · simp

/- English proof (translation)
Use extensionality with `i l`. Rewrite using `[val_colU, GlobalTheory.RootUp.val_elem, Matrix.add_apply, Matrix.add_apply]`. Use `congr 1`. Rewrite using `[colM_apply, Matrix.single_apply]`. Distinguish the cases in `hi : i = r`.

Substitute `hi` using the available equality. Distinguish the cases in `hl : l.val = j`. Establish `: (⟨j, hj⟩ : Fin n) = l` using `Fin.ext hl.symm`. Simplify using `[hr, hl, this]`. Establish `: (⟨j, hj⟩ : Fin n) ≠ l` using `fun h => hl (by rw [← h])`.

Simplify using `[hl, this]`. Establish `: r ≠ i` using `Ne.symm hi`. Simplify using `[Pi.single_apply, hi, this]`.
-/
theorem colU_single_of_lt (j : ℕ) (hj : j < n) {r : Fin n} (hr : r.val < j) (a : k) :
    colU j (Pi.single r a) = GlobalTheory.RootUp.elem (i := r) (j := ⟨j, hj⟩) (fun h => by
      have := congrArg Fin.val h; simp at this; omega) a := by
  ext i l
  rw [val_colU, GlobalTheory.RootUp.val_elem, Matrix.add_apply, Matrix.add_apply]
  congr 1
  rw [colM_apply, Matrix.single_apply]
  by_cases hi : i = r
  · subst hi
    by_cases hl : l.val = j
    · have : (⟨j, hj⟩ : Fin n) = l := Fin.ext hl.symm
      simp [hr, hl, this]
    · have : (⟨j, hj⟩ : Fin n) ≠ l := fun h => hl (by rw [← h])
      simp [hl, this]
  · have : r ≠ i := Ne.symm hi
    simp [Pi.single_apply, hi, this]

/- English proof (translation)
Use extensionality with `i l`. Rewrite using `[val_colU, Units.val_one, Matrix.add_apply, colM_apply]`. Distinguish the cases in `hi : i = r`. Substitute `hi; simp [show ¬ i.val < j by omega]` using the available equality. Simplify using `[Pi.single_apply, hi]`.
-/
theorem colU_single_of_ge (j : ℕ) {r : Fin n} (hr : j ≤ r.val) (a : k) : colU j (Pi.single r a) = 1 := by
  ext i l
  rw [val_colU, Units.val_one, Matrix.add_apply, colM_apply]
  by_cases hi : i = r
  · subst hi; simp [show ¬ i.val < j by omega]
  · simp [Pi.single_apply, hi]

end DiscreteGroups.sglob.LConvGenM
