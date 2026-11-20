import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

namespace UpperTheory.RealTr.CartanExamples

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private def sg (key : ι → ℕ) (i : ι) (A : Finset ι) : ℂ :=
  (-1) ^ (A.filter fun j => key j < key i).card

private def tw (key : ι → ℕ) (i j : ι) : ℂ := if key j < key i then -1 else 1

/- English proof (translation)
Simplify using `[tw]`.
-/
private theorem tw_self (key : ι → ℕ) (i : ι) : tw key i i = 1 := by simp [tw]

/- English proof (translation)
Unfold `tw`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
private theorem tw_mul_self (key : ι → ℕ) (i j : ι) : tw key i j * tw key i j = 1 := by
  unfold tw
  split_ifs <;> norm_num

/- English proof (translation)
Establish `hne : key i ≠ key j` using `fun e => h (hk e)`. Apply the tactic sequence `rcases lt_or_gt_of_ne hne with h1 | h1 <;> simp [tw, h1, lt_asymm h1]`.
-/
private theorem tw_swap {key : ι → ℕ} (hk : Function.Injective key) {i j : ι} (h : i ≠ j) :
    tw key j i = -tw key i j := by
  have hne : key i ≠ key j := fun e => h (hk e)
  rcases lt_or_gt_of_ne hne with h1 | h1 <;> simp [tw, h1, lt_asymm h1]

/- English proof (translation)
Unfold `sg`. Rewrite using `[← mul_pow]`. Evaluate the numerical expressions.
-/
private theorem sg_mul_self (key : ι → ℕ) (i : ι) (A : Finset ι) :
    sg key i A * sg key i A = 1 := by
  unfold sg
  rw [← mul_pow]
  norm_num

/- English proof (translation)
Unfold `sg`. Simplify using the standard rewrite rules.
-/
private theorem star_sg (key : ι → ℕ) (i : ι) (A : Finset ι) :
    star (sg key i A) = sg key i A := by
  unfold sg
  simp

/- English proof (translation)
Unfold `sg tw`. Rewrite using `[Finset.filter_insert]`. Use `split_ifs with hk`. Rewrite using `[Finset.card_insert_of_notMem (fun hm => h (Finset.mem_filter.1 hm).1), pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules.
-/
private theorem sg_insert (key : ι → ℕ) (i : ι) {j : ι} {A : Finset ι} (h : j ∉ A) :
    sg key i (insert j A) = tw key i j * sg key i A := by
  unfold sg tw
  rw [Finset.filter_insert]
  split_ifs with hk
  · rw [Finset.card_insert_of_notMem (fun hm => h (Finset.mem_filter.1 hm).1), pow_succ]; ring
  · simp

/- English proof (translation)
Establish `h1` using `sg_insert key i (Finset.notMem_erase j A)`. Rewrite `h1` using `[Finset.insert_erase h]`. Rewrite using `[h1, ← mul_assoc, tw_mul_self, one_mul]`.
-/
private theorem sg_erase (key : ι → ℕ) (i : ι) {j : ι} {A : Finset ι} (h : j ∈ A) :
    sg key i (A.erase j) = tw key i j * sg key i A := by
  have h1 := sg_insert key i (Finset.notMem_erase j A)
  rw [Finset.insert_erase h] at h1
  rw [h1, ← mul_assoc, tw_mul_self, one_mul]

private def al (key : ι → ℕ) (i : ι) : Matrix (Finset ι) (Finset ι) ℂ :=
  Matrix.of fun A A' => if i ∉ A ∧ A' = insert i A then sg key i A else 0

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Simplify using `only [al, Matrix.of_apply]`. Use `split_ifs with hi`. Simplify using `[hi]`. Simplify using `[hi]`.
-/
private theorem al_mul (key : ι → ℕ) (i : ι) (M : Matrix (Finset ι) (Finset ι) ℂ) (A B : Finset ι) :
    (al key i * M) A B = if i ∈ A then 0 else sg key i A * M (insert i A) B := by
  rw [Matrix.mul_apply]
  simp only [al, Matrix.of_apply]
  split_ifs with hi
  · simp [hi]
  · simp [hi]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.conjTranspose_apply, al, Matrix.of_apply]`. Use `split_ifs with hi`. Rewrite using `[Finset.sum_eq_single (A.erase i)]`. Rewrite using `[if_pos ⟨Finset.notMem_erase i A, (Finset.insert_erase hi).symm⟩, star_sg, sg_erase key i hi, tw_self, one_mul]`.

Introduce `A' _ hA'`. Rewrite using `[if_neg, star_zero, zero_mul]`. Introduce and unpack `⟨h1, rfl⟩`. Conclude with `hA' (Finset.erase_insert h1).symm`. Introduce `hm`.

Conclude with `absurd (Finset.mem_univ _) hm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `A' _`. Rewrite using `[if_neg, star_zero, zero_mul]`. Introduce and unpack `⟨_, rfl⟩`.

Conclude with `hi (Finset.mem_insert_self i A')`.
-/
private theorem alH_mul (key : ι → ℕ) (i : ι) (M : Matrix (Finset ι) (Finset ι) ℂ)
    (A B : Finset ι) :
    ((al key i)ᴴ * M) A B = if i ∈ A then sg key i A * M (A.erase i) B else 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, al, Matrix.of_apply]
  split_ifs with hi
  · rw [Finset.sum_eq_single (A.erase i)]
    · rw [if_pos ⟨Finset.notMem_erase i A, (Finset.insert_erase hi).symm⟩, star_sg,
        sg_erase key i hi, tw_self, one_mul]
    · intro A' _ hA'
      rw [if_neg, star_zero, zero_mul]
      rintro ⟨h1, rfl⟩
      exact hA' (Finset.erase_insert h1).symm
    · intro hm
      exact absurd (Finset.mem_univ _) hm
  · apply Finset.sum_eq_zero
    intro A' _
    rw [if_neg, star_zero, zero_mul]
    rintro ⟨_, rfl⟩
    exact hi (Finset.mem_insert_self i A')

/- English proof (translation)
Use extensionality with `A B`. Simplify using `only [Matrix.add_apply, Matrix.zero_apply, al_mul]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Establish `hji : j ≠ i` using `fun e => hij e.symm`. Distinguish the cases in `hi : i ∈ A`. Simplify using `[hi]`. Distinguish the cases in `hj : j ∈ A`. Simplify using `[hj]`.

Simplify using `only [hi, hj, Finset.mem_insert, hij, hji, or_self, if_false]`. Rewrite using `[sg_insert key j hi, sg_insert key i hj, tw_swap hk hij, Finset.insert_comm j i]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem ann_ann {key : ι → ℕ} (hk : Function.Injective key) (i j : ι)
    (M : Matrix (Finset ι) (Finset ι) ℂ) :
    al key i * (al key j * M) + al key j * (al key i * M) = 0 := by
  ext A B
  simp only [Matrix.add_apply, Matrix.zero_apply, al_mul]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  · simp [hi]
  by_cases hj : j ∈ A
  · simp [hj]
  simp only [hi, hj, Finset.mem_insert, hij, hji, or_self, if_false]
  rw [sg_insert key j hi, sg_insert key i hj, tw_swap hk hij, Finset.insert_comm j i]
  ring

/- English proof (translation)
Use extensionality with `A B`. Simplify using `only [Matrix.add_apply, al_mul, alH_mul]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[if_pos rfl]`.

Distinguish the cases in `hi : i ∈ A`. Rewrite using `[if_pos hi, if_pos hi, if_neg (Finset.notMem_erase i A), Finset.insert_erase hi, sg_erase key i hi, tw_self, zero_add]`. Take the linear combination `M A B * sg_mul_self key i A`. Rewrite using `[if_neg hi, if_neg hi, if_pos (Finset.mem_insert_self i A), Finset.erase_insert hi, sg_insert key i hi, tw_self, add_zero]`. Take the linear combination `M A B * sg_mul_self key i A`.

Rewrite using `[if_neg hij, Matrix.zero_apply]`. Distinguish the cases in `hi : i ∈ A`. Rewrite using `[if_pos hi, zero_add, if_pos (Finset.mem_erase.2 ⟨hij, hi⟩)]`. Simplify using the standard rewrite rules. Distinguish the cases in `hj : j ∈ A`.

Rewrite using `[if_neg hi, if_pos (Finset.mem_insert_of_mem hj), if_pos hj, if_neg (fun hm => hi (Finset.mem_of_mem_erase hm)), sg_insert key j hi, sg_erase key i hj, tw_swap hk hij, Finset.erase_insert_of_ne hij]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : j ∉ insert i A` using `fun hm => (Finset.mem_insert.1 hm).elim (fun e => hij e.symm) hj`. Rewrite using `[if_neg hi, if_neg h1, if_neg hj]`. Simplify using the standard rewrite rules.
-/
private theorem ann_cre {key : ι → ℕ} (hk : Function.Injective key) (i j : ι)
    (M : Matrix (Finset ι) (Finset ι) ℂ) :
    al key i * ((al key j)ᴴ * M) + (al key j)ᴴ * (al key i * M) = if i = j then M else 0 := by
  ext A B
  simp only [Matrix.add_apply, al_mul, alH_mul]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    by_cases hi : i ∈ A
    · rw [if_pos hi, if_pos hi, if_neg (Finset.notMem_erase i A), Finset.insert_erase hi,
        sg_erase key i hi, tw_self, zero_add]
      linear_combination M A B * sg_mul_self key i A
    · rw [if_neg hi, if_neg hi, if_pos (Finset.mem_insert_self i A), Finset.erase_insert hi,
        sg_insert key i hi, tw_self, add_zero]
      linear_combination M A B * sg_mul_self key i A
  rw [if_neg hij, Matrix.zero_apply]
  by_cases hi : i ∈ A
  · rw [if_pos hi, zero_add, if_pos (Finset.mem_erase.2 ⟨hij, hi⟩)]
    simp
  by_cases hj : j ∈ A
  · rw [if_neg hi, if_pos (Finset.mem_insert_of_mem hj), if_pos hj,
      if_neg (fun hm => hi (Finset.mem_of_mem_erase hm)), sg_insert key j hi, sg_erase key i hj,
      tw_swap hk hij, Finset.erase_insert_of_ne hij]
    ring
  · have h1 : j ∉ insert i A := fun hm => (Finset.mem_insert.1 hm).elim (fun e => hij e.symm) hj
    rw [if_neg hi, if_neg h1, if_neg hj]
    simp

/- English proof (translation)
Use extensionality with `A B`. Rewrite using `[alH_mul, Matrix.diagonal_apply]`. Simplify using `only [al, Matrix.of_apply]`. Distinguish the cases in `hi : i ∈ A`. Rewrite using `[if_pos hi, if_pos hi, Finset.insert_erase hi, sg_erase key i hi, tw_self, one_mul]`.

Distinguish the cases in `hAB : A = B`. Substitute `hAB` using the available equality. Rewrite using `[if_pos ⟨Finset.notMem_erase i A, rfl⟩, if_pos rfl, sg_mul_self]`. Rewrite using `[if_neg (fun hc => hAB hc.2.symm), if_neg hAB, mul_zero]`. Rewrite using `[if_neg hi, if_neg hi]`.

Simplify using the standard rewrite rules.
-/
private theorem cre_ann (key : ι → ℕ) (i : ι) :
    (al key i)ᴴ * al key i = Matrix.diagonal fun A => if i ∈ A then 1 else 0 := by
  ext A B
  rw [alH_mul, Matrix.diagonal_apply]
  simp only [al, Matrix.of_apply]
  by_cases hi : i ∈ A
  · rw [if_pos hi, if_pos hi, Finset.insert_erase hi, sg_erase key i hi, tw_self, one_mul]
    by_cases hAB : A = B
    · subst hAB
      rw [if_pos ⟨Finset.notMem_erase i A, rfl⟩, if_pos rfl, sg_mul_self]
    · rw [if_neg (fun hc => hAB hc.2.symm), if_neg hAB, mul_zero]
  · rw [if_neg hi, if_neg hi]
    simp

end UpperTheory.RealTr.CartanExamples

open UpperTheory.RealTr.CartanExamples in
/- English proof (translation)
Introduce `ι _ _`. Set `key : ι → ℕ` to `fun i => (Fintype.equivFin ι i : ℕ)`. Establish `hk : Function.Injective key` using `fun a b h => (Fintype.equivFin ι).injective (Fin.ext h)`. Use `⟨al key, fun i j => ?_, fun i j => ?_, cre_ann key⟩` and prove the remaining obligations. Simplify using `using ann_ann hk i j 1`.

Simplify using `using ann_cre hk i j 1`.
-/
theorem UpperTheory.RealTr.carEx :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι], ∃ α : ι → Matrix (Finset ι) (Finset ι) ℂ, (∀ i j, α i * α j + α j * α i = 0) ∧
      (∀ i j, α i * (α j)ᴴ + (α j)ᴴ * α i = if i = j then 1 else 0) ∧ ∀ i, (α i)ᴴ * α i = Matrix.diagonal fun A => if i ∈ A then 1 else 0 := by
  intro ι _ _
  let key : ι → ℕ := fun i => (Fintype.equivFin ι i : ℕ)
  have hk : Function.Injective key := fun a b h => (Fintype.equivFin ι).injective (Fin.ext h)
  refine ⟨al key, fun i j => ?_, fun i j => ?_, cre_ann key⟩
  · simpa using ann_ann hk i j 1
  · simpa using ann_cre hk i j 1
