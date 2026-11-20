import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.LConvCut

noncomputable section
open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.LConvKir

variable {k : Type} [Field k] {m : ℕ}

def InH (j : ℕ) (g : GL (Fin (m + 1)) k) : Prop :=
  ∀ p q : Fin (m + 1), ¬ (p.val < j ∧ q.val < j) →
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) p q = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) p q

def colM (c : Fin (m + 1)) (x : Fin (m + 1) → k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  1 + Matrix.of fun p q => if q = c ∧ p < c then x p else 0

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem colM_zero (c : Fin (m + 1)) : colM c (0 : Fin (m + 1) → k) = 1 := by
  ext p q; simp [colM]

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem colM_mul (c : Fin (m + 1)) (x y : Fin (m + 1) → k) : colM c x * colM c y = colM c (x + y) := by
  have hAB : (Matrix.of fun p q => if q = c ∧ p < c then x p else 0) *
      (Matrix.of fun p q => if q = c ∧ p < c then y p else (0 : k)) = 0 := by
    ext p q
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : r = c
    · subst hr; simp
    · simp [hr]
  simp only [colM, add_mul, mul_add, one_mul, mul_one, hAB, add_zero]
  ext p q
  simp only [Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
  split_ifs <;> ring

def U (c : Fin (m + 1)) (x : Fin (m + 1) → k) : GL (Fin (m + 1)) k :=
  ⟨colM c x, colM c (-x), by rw [colM_mul, add_neg_cancel, colM_zero],
    by rw [colM_mul, neg_add_cancel, colM_zero]⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem U_add (c : Fin (m + 1)) (x y : Fin (m + 1) → k) : U c (x + y) = U c x * U c y :=
  Units.ext (colM_mul c x y).symm

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem U_mem (c : Fin (m + 1)) (x : Fin (m + 1) → k) : U c x ∈ unipB k (Fin (m + 1)) := by
  refine (mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩
  · show colM c x i j = 0
    simp only [colM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_ne (ne_of_gt hji)]
    rw [if_neg]
    · simp
    · rintro ⟨rfl, h⟩; exact absurd (h.trans hji) (lt_irrefl _)
  · show colM c x i i = 1
    simp only [colM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_eq]
    rw [if_neg]
    · simp
    · rintro ⟨rfl, h⟩; exact lt_irrefl _ h

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem superDiag_U (j : ℕ) (hj : j + 1 < m + 1) (x : Fin (m + 1) → k) :
    superDiag (U ⟨j + 1, hj⟩ x) = x ⟨j, by omega⟩ := by
  unfold superDiag
  rw [Finset.sum_eq_single (⟨j, by omega⟩ : Fin (m + 1))]
  · rw [Finset.sum_eq_single (⟨j + 1, hj⟩ : Fin (m + 1))]
    · show colM _ x _ _ = _
      simp [colM, Fin.ext_iff]
    · intro b hb hne
      exact absurd (Fin.ext (by simpa using (Finset.mem_filter.1 hb).2)) hne
    · intro h; exact absurd (by simp) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun q hq => ?_
    have hq' : q.val = b.val + 1 := (Finset.mem_filter.1 hq).2
    show colM _ x _ _ = 0
    simp only [colM, Matrix.add_apply, Matrix.of_apply]
    rw [Matrix.one_apply_ne (fun h => by rw [h] at hq'; omega), if_neg, add_zero]
    rintro ⟨rfl, -⟩
    exact hb (Fin.ext (by simp at hq' ⊢; omega))
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem InH_zero (g : GL (Fin (m + 1)) k) (hg : InH 0 g) : g = 1 :=
  Units.ext (Matrix.ext fun p q => hg p q (by simp))

end DiscreteGroups.sglob.LConvKir

/- English proof (translation)
A detailed English derivation is pending.
-/
example {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] : ContinuousInv₀ K := inferInstance
