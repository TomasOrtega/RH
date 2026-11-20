import Mathlib
import Formalism.FormalDegreeBessel.StatementG

open Matrix

noncomputable section

namespace GlobalTheory.LeadingMinorInv

open Formalism.QuantumDeterminants

def UpUni {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i j, j < i → U i j = 0) ∧ ∀ i, U i i = 1

/- English proof (translation)
Establish `hsub : (A * U).submatrix (Fin.castLE hl) (Fin.castLE hl) = A.submatrix (Fin.castLE hl) (Fin.castLE hl) * U.submatrix (Fin.castLE hl) (Fin.castLE hl)`. Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Use `symm`. Apply `Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl)` to reduce the goal to its premises.

Introduce `b hb`. Establish `hjb : Fin.castLE hl j < b`. Rewrite using `[Fin.lt_def]`. Use `show j.val < b.val`. Assume the negation of the conclusion as `hc`.

Use `j.isLt` as an intermediate fact. Conclude with `hb ⟨⟨b.val, by omega⟩, Fin.ext rfl⟩`. Rewrite using `[hU.1 b _ hjb, mul_zero]`. Introduce `a`. Both sides reduce to the same expression.

Establish `hdet : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1`. Rewrite using `[Matrix.det_of_isUpperTriangular]`. Simplify using `[Matrix.submatrix_apply, hU.2]`. Introduce `i j hij`. Simplify using `only [Matrix.submatrix_apply]`.

Apply `hU.1` to reduce the goal to its premises. Rewrite `hij`, the goal using `[Fin.lt_def]`. Conclude with `hij`. Rewrite using `[hsub, Matrix.det_mul, hdet, mul_one]`.
-/
lemma minor_mul {n l : ℕ} (hl : l ≤ n) (A U : Matrix (Fin n) (Fin n) ℂ) (hU : UpUni U) :
    ((A * U).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (A.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  have hsub : (A * U).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      A.submatrix (Fin.castLE hl) (Fin.castLE hl) * U.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    apply Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl)
    · intro b hb
      have hjb : Fin.castLE hl j < b := by
        rw [Fin.lt_def]
        show j.val < b.val
        by_contra hc
        have := j.isLt
        exact hb ⟨⟨b.val, by omega⟩, Fin.ext rfl⟩
      rw [hU.1 b _ hjb, mul_zero]
    · intro a
      rfl
  have hdet : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · simp [Matrix.submatrix_apply, hU.2]
    · intro i j hij
      simp only [Matrix.submatrix_apply]
      apply hU.1
      rw [Fin.lt_def] at hij ⊢
      exact hij
  rw [hsub, Matrix.det_mul, hdet, mul_one]

/- English proof (translation)
Establish `e : Uᴴ * A = (Aᴴ * U)ᴴ`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]`. Rewrite using `[e, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose, minor_mul hl _ _ hU, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose, star_star]`.
-/
lemma minor_mul_left {n l : ℕ} (hl : l ≤ n) (A U : Matrix (Fin n) (Fin n) ℂ) (hU : UpUni U) :
    ((Uᴴ * A).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (A.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  have e : Uᴴ * A = (Aᴴ * U)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [e, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose, minor_mul hl _ _ hU,
    ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose, star_star]

def flagMat (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ := Matrix.of fun i a => fvec k r z a i

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma mul_flagMat (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i) (b) :
    (g * flagMat k r z) i b = (g *ᵥ fvec k r z b) i := rfl

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Zhat, herm, Matrix.mul_apply, Matrix.conjTranspose_apply, flagMat, Matrix.of_apply, dotProduct, Matrix.mulVec, Pi.star_apply]`.
-/
lemma zhat_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Zhat k r z z' g = (flagMat k r z)ᴴ * (Hpk k r * (g * flagMat k r z')) := by
  ext a b
  simp only [Zhat, herm, Matrix.mul_apply, Matrix.conjTranspose_apply, flagMat, Matrix.of_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply]

/- English proof (translation)
Simplify using `only [Nset, Set.mem_setOf_eq] at hm`. Take `⟨-, hm2, hm3⟩` from `hm`. Establish `key : ∀ (a : Fin (r + 1)) (i : Fin (2 * r + k + 1)), (m *ᵥ fvec k r z a) i = fvec k r z a i + if i.val < a.val then (m *ᵥ fvec k r z a) i else 0`. Introduce `a i`. Establish `ha` using `a.isLt`.

Distinguish the cases in `hia : i.val < a.val`. Rewrite using `[if_pos hia]`. It suffices to establish `h0 : fvec k r z a i = 0 by rw [h0, zero_add]`. Distinguish the cases in `har : a.val < r`. Simplify using `only [fvec, dif_pos har, bvec]`.

Rewrite using `[Pi.single_apply, if_neg]`. Introduce `he`. Establish `h1` using `congrArg Fin.val he`. Simplify using `[eI] at h1`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [fvec, dif_neg har]`. Conclude with `hz i (Or.inl (by omega))`. Rewrite using `[if_neg hia, add_zero]`. Distinguish the cases in `har : a.val < r`. Simplify using `only [fvec, dif_pos har, bvec]`.

Simplify using `only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Conclude with `hm2 ⟨a.val, har⟩ i (by show a.val ≤ i.val; omega)`. Simplify using `only [fvec, dif_neg har]`. Establish `hterm : ∀ j, m i j * z j = if i = j then z j else 0`. Introduce `j`.

Distinguish the cases in `hj : r ≤ j.val ∧ j.val ≤ r + k`. Apply the tactic sequence `rw [hm3 i j hj.1 hj.2 (by omega)] split_ifs <;> simp`. Rewrite using `[hz j (by omega)]`. Simplify using the standard rewrite rules. Simplify using `only [Matrix.mulVec, dotProduct, hterm, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.

Use `⟨Matrix.of fun b a => (if b = a then 1 else 0) + (if hba : b.val < a.val then (m *ᵥ fvec k r z a) (eI k r ⟨b.val, by have := a.isLt; omega⟩) else 0), ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Establish `h1 : i ≠ j` using `hij.ne'`. Establish `h2 : ¬ i < j` using `by rw [Fin.lt_def] at hij ⊢; omega`. Simplify using `[h1, h2]`.

Introduce `i`. Simplify using the standard rewrite rules. Use extensionality with `i a`. Rewrite using `[mul_flagMat, Matrix.mul_apply]`. Simplify using `only [flagMat, Matrix.of_apply, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]`.

Rewrite using `[key a i]`. Use `congr 1`. Establish `ha` using `a.isLt`. Distinguish the cases in `hia : i.val < a.val`. Establish `hir : i.val < r` using `by omega`.

Rewrite using `[if_pos hia, Finset.sum_eq_single (⟨i.val, by omega⟩ : Fin (r + 1))]`. Establish `he : eI k r ⟨i.val, hir⟩ = i` using `Fin.ext rfl`. Simplify using `[fvec, hir, hia, he, bvec]`. Introduce `b _ hb split_ifs with hba`. Establish `hbr : b.val < r` using `by omega`.

Establish `hne : i ≠ eI k r ⟨b.val, hbr⟩`. Introduce `he`. Apply `hb` to reduce the goal to its premises. Use `ext`. Conclude with `(congrArg Fin.val he).symm`.

Simplify using `[fvec, hbr, bvec, Pi.single_apply, hne]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite using `[if_neg hia]`. Use `symm`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Use `split_ifs with hba`. Establish `hbr : b.val < r` using `by omega`. Establish `hne : i ≠ eI k r ⟨b.val, hbr⟩`.

Introduce `he`. Apply `hia` to reduce the goal to its premises. Rewrite using `[he]`. Conclude with `hba`. Simplify using `[fvec, hbr, bvec, Pi.single_apply, hne]`.

Simplify using the standard rewrite rules.
-/
lemma exists_N (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hm : m ∈ Nset k r) :
    ∃ U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, UpUni U ∧ m * flagMat k r z = flagMat k r z * U := by
  simp only [Nset, Set.mem_setOf_eq] at hm
  obtain ⟨-, hm2, hm3⟩ := hm
  have key : ∀ (a : Fin (r + 1)) (i : Fin (2 * r + k + 1)),
      (m *ᵥ fvec k r z a) i =
        fvec k r z a i + if i.val < a.val then (m *ᵥ fvec k r z a) i else 0 := by
    intro a i
    have ha := a.isLt
    by_cases hia : i.val < a.val
    · rw [if_pos hia]
      suffices h0 : fvec k r z a i = 0 by rw [h0, zero_add]
      by_cases har : a.val < r
      · simp only [fvec, dif_pos har, bvec]
        rw [Pi.single_apply, if_neg]
        intro he
        have h1 := congrArg Fin.val he
        simp [eI] at h1
        omega
      · simp only [fvec, dif_neg har]
        exact hz i (Or.inl (by omega))
    · rw [if_neg hia, add_zero]
      by_cases har : a.val < r
      · simp only [fvec, dif_pos har, bvec]
        simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
        exact hm2 ⟨a.val, har⟩ i (by show a.val ≤ i.val; omega)
      · simp only [fvec, dif_neg har]
        have hterm : ∀ j, m i j * z j = if i = j then z j else 0 := by
          intro j
          by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
          · rw [hm3 i j hj.1 hj.2 (by omega)]
            split_ifs <;> simp
          · rw [hz j (by omega)]
            simp
        simp only [Matrix.mulVec, dotProduct, hterm, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine ⟨Matrix.of fun b a => (if b = a then 1 else 0) +
      (if hba : b.val < a.val then
        (m *ᵥ fvec k r z a) (eI k r ⟨b.val, by have := a.isLt; omega⟩) else 0), ⟨?_, ?_⟩, ?_⟩
  · intro i j hij
    have h1 : i ≠ j := hij.ne'
    have h2 : ¬ i < j := by rw [Fin.lt_def] at hij ⊢; omega
    simp [h1, h2]
  · intro i
    simp
  · ext i a
    rw [mul_flagMat, Matrix.mul_apply]
    simp only [flagMat, Matrix.of_apply, mul_add, Finset.sum_add_distrib, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [key a i]
    congr 1
    have ha := a.isLt
    by_cases hia : i.val < a.val
    · have hir : i.val < r := by omega
      rw [if_pos hia, Finset.sum_eq_single (⟨i.val, by omega⟩ : Fin (r + 1))]
      · have he : eI k r ⟨i.val, hir⟩ = i := Fin.ext rfl
        simp [fvec, hir, hia, he, bvec]
      · intro b _ hb
        split_ifs with hba
        · have hbr : b.val < r := by omega
          have hne : i ≠ eI k r ⟨b.val, hbr⟩ := by
            intro he
            apply hb
            ext
            exact (congrArg Fin.val he).symm
          simp [fvec, hbr, bvec, Pi.single_apply, hne]
        · simp
      · simp
    · rw [if_neg hia]
      symm
      apply Finset.sum_eq_zero
      intro b _
      split_ifs with hba
      · have hbr : b.val < r := by omega
        have hne : i ≠ eI k r ⟨b.val, hbr⟩ := by
          intro he
          apply hia
          rw [he]
          exact hba
        simp [fvec, hbr, bvec, Pi.single_apply, hne]
      · simp

/- English proof (translation)
Simplify using `only [Sset, Set.mem_setOf_eq] at hs`. Take `⟨h, hh, m, hm, rfl⟩` from `hs`. Take `⟨U, hU, hmF⟩` from `exists_N k r z hz m hm`. Simplify using `only [UWset, Set.mem_setOf_eq] at hh`. Take `⟨hhU, hfix, hhz⟩` from `hh`.

Establish `hmU : mᴴ * Hpk k r * m = Hpk k r`. Simplify using `only [Nset, Set.mem_setOf_eq] at hm`. Conclude with `hm.1`. Establish `hhU' : hᴴ * Hpk k r * h = Hpk k r` using `hhU`. Use `⟨?_, U, hU, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Hpk k r := by rw [hhU', hmU]`. Establish `hF : h * flagMat k r z = flagMat k r z`. Use extensionality with `i b`.

Rewrite using `[mul_flagMat]`. Simplify using `only [flagMat, Matrix.of_apply]`. Distinguish the cases in `hb : b.val < r`. Simplify using `only [fvec, dif_pos hb]`. Rewrite using `[(hfix ⟨b.val, hb⟩).1]`.

Simplify using `only [fvec, dif_neg hb]`. Rewrite using `[hhz]`. Rewrite using `[Matrix.mul_assoc, hmF, ← Matrix.mul_assoc, hF]`.
-/
lemma exists_S (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hs : s ∈ Sset k r z) :
    sᴴ * Hpk k r * s = Hpk k r ∧ ∃ U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, UpUni U ∧ s * flagMat k r z = flagMat k r z * U := by
  simp only [Sset, Set.mem_setOf_eq] at hs
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  obtain ⟨U, hU, hmF⟩ := exists_N k r z hz m hm
  simp only [UWset, Set.mem_setOf_eq] at hh
  obtain ⟨hhU, hfix, hhz⟩ := hh
  have hmU : mᴴ * Hpk k r * m = Hpk k r := by
    simp only [Nset, Set.mem_setOf_eq] at hm
    exact hm.1
  have hhU' : hᴴ * Hpk k r * h = Hpk k r := hhU
  refine ⟨?_, U, hU, ?_⟩
  · calc (h * m)ᴴ * Hpk k r * (h * m) = mᴴ * (hᴴ * Hpk k r * h) * m := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [hhU', hmU]
  · have hF : h * flagMat k r z = flagMat k r z := by
      ext i b
      rw [mul_flagMat]
      simp only [flagMat, Matrix.of_apply]
      by_cases hb : b.val < r
      · simp only [fvec, dif_pos hb]
        rw [(hfix ⟨b.val, hb⟩).1]
      · simp only [fvec, dif_neg hb]
        rw [hhz]
    rw [Matrix.mul_assoc, hmF, ← Matrix.mul_assoc, hF]

end GlobalTheory.LeadingMinorInv

namespace GlobalTheory

open Formalism.QuantumDeterminants LeadingMinorInv

end GlobalTheory
