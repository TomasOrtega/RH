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
Use extensionality with `p q`. Simplify using `[colM]`.
-/
theorem colM_zero (c : Fin (m + 1)) : colM c (0 : Fin (m + 1) → k) = 1 := by
  ext p q; simp [colM]

/- English proof (translation)
Establish `hAB : (Matrix.of fun p q => if q = c ∧ p < c then x p else 0) * (Matrix.of fun p q => if q = c ∧ p < c then y p else (0 : k)) = 0`. Use extensionality with `p q`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]`. Use `Finset.sum_eq_zero fun r _ => ?_` and prove the remaining obligations. Distinguish the cases in `hr : r = c`.

Substitute `hr` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hr]`. Simplify using `only [colM, add_mul, mul_add, one_mul, mul_one, hAB, add_zero]`. Use extensionality with `p q`.

Simplify using `only [Matrix.add_apply, Matrix.of_apply, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> ring`.
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
The claim follows from `Units.ext (colM_mul c x y).symm`.
-/
theorem U_add (c : Fin (m + 1)) (x y : Fin (m + 1) → k) : U c (x + y) = U c x * U c y :=
  Units.ext (colM_mul c x y).symm

/- English proof (translation)
Use `(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩` and prove the remaining obligations. Use `show colM c x i j = 0`. Simplify using `only [colM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_ne (ne_of_gt hji)]`. Rewrite using `[if_neg]`. Simplify using the standard rewrite rules.

Introduce and unpack `⟨rfl, h⟩`. Conclude with `absurd (h.trans hji) (lt_irrefl _)`. Use `show colM c x i i = 1`. Simplify using `only [colM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_eq]`. Rewrite using `[if_neg]`.

Simplify using the standard rewrite rules. Introduce and unpack `⟨rfl, h⟩`. Conclude with `lt_irrefl _ h`.
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
Unfold `superDiag`. Rewrite using `[Finset.sum_eq_single (⟨j, by omega⟩ : Fin (m + 1))]`. Rewrite using `[Finset.sum_eq_single (⟨j + 1, hj⟩ : Fin (m + 1))]`. Use `show colM _ x _ _ = _`. Simplify using `[colM, Fin.ext_iff]`.

Introduce `b hb hne`. Conclude with `absurd (Fin.ext (by simpa using (Finset.mem_filter.1 hb).2)) hne`. Introduce `h; exact absurd (by simp) h`. Introduce `b _ hb`. Use `Finset.sum_eq_zero fun q hq => ?_` and prove the remaining obligations.

Establish `hq' : q.val = b.val + 1` using `(Finset.mem_filter.1 hq).2`. Use `show colM _ x _ _ = 0`. Simplify using `only [colM, Matrix.add_apply, Matrix.of_apply]`. Rewrite using `[Matrix.one_apply_ne (fun h => by rw [h] at hq'; omega), if_neg, add_zero]`. Introduce and unpack `⟨rfl, -⟩`.

Conclude with `hb (Fin.ext (by simp at hq' ⊢; omega))`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
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
The claim follows from `Units.ext (Matrix.ext fun p q => hg p q (by simp))`.
-/
theorem InH_zero (g : GL (Fin (m + 1)) k) (hg : InH 0 g) : g = 1 :=
  Units.ext (Matrix.ext fun p q => hg p q (by simp))

end DiscreteGroups.sglob.LConvKir

/- English proof (translation)
The claim follows from `inferInstance`.
-/
example {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] : ContinuousInv₀ K := inferInstance
