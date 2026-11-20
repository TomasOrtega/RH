import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.RowS

noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows.CornerBlockIndex

variable {ι : Type} {a m : ℕ}

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ p)]`. Simplify using `only [Matrix.updateRow_self]`. Use `congr 1`. Use `split_ifs with hj`. Substitute `hj` using the available equality.

Use `Finset.sum_eq_zero fun l hl => ?_` and prove the remaining obligations. Rewrite using `[Matrix.updateRow_ne (Finset.ne_of_mem_erase hl), Matrix.one_apply_ne (Finset.ne_of_mem_erase hl), mul_zero]`. Rewrite using `[Finset.sum_eq_single j]`. Rewrite using `[Matrix.updateRow_ne hj, Matrix.one_apply_eq, mul_one]`. Introduce `l hl hlj`.

Rewrite using `[Matrix.updateRow_ne (Finset.ne_of_mem_erase hl), Matrix.one_apply_ne hlj, mul_zero]`. Introduce `hj'`. Conclude with `absurd (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩) hj'`.
-/
theorem mul_upd {n R : Type} [Fintype n] [DecidableEq n] [CommRing R] (A : Matrix n n R) (p : n)
    (r : n → R) (i j : n) :
    (A * (1 : Matrix n n R).updateRow p r) i j = A i p * r j + if j = p then 0 else A i j := by
  rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
  simp only [Matrix.updateRow_self]
  congr 1
  split_ifs with hj
  · subst hj
    refine Finset.sum_eq_zero fun l hl => ?_
    rw [Matrix.updateRow_ne (Finset.ne_of_mem_erase hl),
      Matrix.one_apply_ne (Finset.ne_of_mem_erase hl), mul_zero]
  · rw [Finset.sum_eq_single j]
    · rw [Matrix.updateRow_ne hj, Matrix.one_apply_eq, mul_one]
    · intro l hl hlj
      rw [Matrix.updateRow_ne (Finset.ne_of_mem_erase hl), Matrix.one_apply_ne hlj, mul_zero]
    · intro hj'; exact absurd (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩) hj'

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem of_sM (hm : m + 1 < a) (x : V ι a m) :
    Matrix.of (sM hm x) = (1 : Matrix (Fin a) (Fin a) (ι → ℂ)).updateRow (mm hm) (rowS hm x) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem of_sI (hm : m + 1 < a) (x : V ι a m) :
    Matrix.of (sI hm x) = (1 : Matrix (Fin a) (Fin a) (ι → ℂ)).updateRow (mm hm) (rowT hm x) := rfl

/- English proof (translation)
Unfold `rowS`. Rewrite using `[dif_pos (by simp [mm])]`. Both sides reduce to the same expression.
-/
theorem rowS_mm (hm : m + 1 < a) (x : V ι a m) : rowS hm x (mm hm) = x (t0 hm) := by
  unfold rowS
  rw [dif_pos (by simp [mm])]
  rfl

/- English proof (translation)
Unfold `rowT`. Rewrite using `[dif_pos (by simp [mm]), if_pos (by simp [mm])]`.
-/
theorem rowT_mm (hm : m + 1 < a) (x : V ι a m) : rowT hm x (mm hm) = (x (t0 hm))⁻¹ := by
  unfold rowT
  rw [dif_pos (by simp [mm]), if_pos (by simp [mm])]

/- English proof (translation)
Establish `hj' : (j : ℕ) ≠ m` using `fun h => hj (Fin.ext h)`. Unfold `rowT rowS`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | rfl | simp`.
-/
theorem rowT_ne (hm : m + 1 < a) (x : V ι a m) {j : Fin a} (hj : j ≠ mm hm) :
    rowT hm x j = -(rowS hm x j * (x (t0 hm))⁻¹) := by
  have hj' : (j : ℕ) ≠ m := fun h => hj (Fin.ext h)
  unfold rowT rowS
  split_ifs <;> first | (exfalso; omega) | rfl | simp

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]`. Conclude with `mul_inv_cancel₀ (hx i)`.
-/
theorem mul_inv_cancel_at_t0_of_mem_O (hm : m + 1 < a) {x : V ι a m} (hx : x ∈ O ι hm) :
    x (t0 hm) * (x (t0 hm))⁻¹ = 1 := by
  funext i
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]
  exact mul_inv_cancel₀ (hx i)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Both sides reduce to the same expression. Introduce `h`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Prod.ext h` to reduce the goal to its premises. Apply `Fin.ext` to reduce the goal to its premises. Take `⟨-, h1, h2⟩` from `t.2`. Use `show (t.1.2 : ℕ) = m + 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem block_index_eq_corner_iff (hm : m + 1 < a) (t : UnipotentBlockColumnIndex a (m + 1) (m + 1)) : t = t0 hm ↔ t.1.1 = mm hm := by
  constructor
  · rintro rfl; rfl
  · intro h
    apply Subtype.ext
    apply Prod.ext h
    apply Fin.ext
    obtain ⟨-, h1, h2⟩ := t.2
    show (t.1.2 : ℕ) = m + 1
    omega

/- English proof (translation)
Unfold `rowS`. Use `split_ifs with hk`. Both sides reduce to the same expression. Rewrite using `[hh _ _ (Or.inr (by omega)), Matrix.one_apply_ne]`. Introduce `e`.

Apply `hk` to reduce the goal to its premises. Rewrite using `[← e]`. Simplify using `[mm]`.
-/
theorem rowS_xi (hm : m + 1 < a) {h : GL (Fin a) (ι → ℂ)} (hh : GlobalTheory (m + 1) h) (k : Fin a) :
    rowS hm (xi hm h) k = h.val (mm hm) k := by
  unfold rowS
  split_ifs with hk
  · rfl
  · rw [hh _ _ (Or.inr (by omega)), Matrix.one_apply_ne]
    intro e; apply hk; rw [← e]; simp [mm]

/- English proof (translation)
Establish `hi1` using `mul_inv_cancel_at_t0_of_mem_O hm hx`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Rewrite using `[of_sI, of_sM, mul_upd]`. Distinguish the cases in `hi : i = mm hm`. Substitute `hi` using the available equality.

Simplify using `only [Matrix.updateRow_self]`. Distinguish the cases in `hj : j = mm hm`. Substitute `hj` using the available equality. Rewrite using `[if_pos rfl, add_zero, rowT_mm, rowS_mm, Matrix.one_apply_eq, mul_comm, hi1]`. Rewrite using `[if_neg hj, rowT_mm, rowT_ne hm x hj, Matrix.one_apply_ne (Ne.symm hj)]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Matrix.updateRow_ne hi, Matrix.one_apply_ne hi, zero_mul, zero_add] split_ifs with hj`. Substitute `hj` using the available equality. Rewrite using `[Matrix.one_apply_ne hi]`. Both sides reduce to the same expression.
-/
theorem sI_mul_sM (hm : m + 1 < a) {x : V ι a m} (hx : x ∈ O ι hm) :
    Matrix.of (sI hm x) * Matrix.of (sM hm x) = 1 := by
  have hi1 := mul_inv_cancel_at_t0_of_mem_O hm hx
  refine Matrix.ext fun i j => ?_
  rw [of_sI, of_sM, mul_upd]
  by_cases hi : i = mm hm
  · subst hi
    simp only [Matrix.updateRow_self]
    by_cases hj : j = mm hm
    · subst hj
      rw [if_pos rfl, add_zero, rowT_mm, rowS_mm, Matrix.one_apply_eq, mul_comm, hi1]
    · rw [if_neg hj, rowT_mm, rowT_ne hm x hj, Matrix.one_apply_ne (Ne.symm hj)]
      ring
  · rw [Matrix.updateRow_ne hi, Matrix.one_apply_ne hi, zero_mul, zero_add]
    split_ifs with hj
    · subst hj; rw [Matrix.one_apply_ne hi]
    · rfl

/- English proof (translation)
Establish `hi1` using `mul_inv_cancel_at_t0_of_mem_O hm hx`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Rewrite using `[of_sI, of_sM, mul_upd]`. Distinguish the cases in `hi : i = mm hm`. Substitute `hi` using the available equality.

Simplify using `only [Matrix.updateRow_self]`. Distinguish the cases in `hj : j = mm hm`. Substitute `hj` using the available equality. Rewrite using `[if_pos rfl, add_zero, rowT_mm, rowS_mm, Matrix.one_apply_eq, hi1]`. Rewrite using `[if_neg hj, rowS_mm, rowT_ne hm x hj, Matrix.one_apply_ne (Ne.symm hj)]`.

Take the linear combination `(-(rowS hm x j)) * hi1`. Rewrite using `[Matrix.updateRow_ne hi, Matrix.one_apply_ne hi, zero_mul, zero_add] split_ifs with hj`. Substitute `hj` using the available equality. Rewrite using `[Matrix.one_apply_ne hi]`. Both sides reduce to the same expression.
-/
theorem sM_mul_sI (hm : m + 1 < a) {x : V ι a m} (hx : x ∈ O ι hm) :
    Matrix.of (sM hm x) * Matrix.of (sI hm x) = 1 := by
  have hi1 := mul_inv_cancel_at_t0_of_mem_O hm hx
  refine Matrix.ext fun i j => ?_
  rw [of_sI, of_sM, mul_upd]
  by_cases hi : i = mm hm
  · subst hi
    simp only [Matrix.updateRow_self]
    by_cases hj : j = mm hm
    · subst hj
      rw [if_pos rfl, add_zero, rowT_mm, rowS_mm, Matrix.one_apply_eq, hi1]
    · rw [if_neg hj, rowS_mm, rowT_ne hm x hj, Matrix.one_apply_ne (Ne.symm hj)]
      linear_combination (-(rowS hm x j)) * hi1
  · rw [Matrix.updateRow_ne hi, Matrix.one_apply_ne hi, zero_mul, zero_add]
    split_ifs with hj
    · subst hj; rw [Matrix.one_apply_ne hi]
    · rfl

open Classical in

def uM (hm : m + 1 < a) (x : V ι a m) : GL (Fin a) (ι → ℂ) :=
  if hx : x ∈ O ι hm then ⟨Matrix.of (sM hm x), Matrix.of (sI hm x), sM_mul_sI hm hx, sI_mul_sM hm hx⟩ else 1

/- English proof (translation)
Simplify using `[uM, hx]`.
-/
theorem uM_val (hm : m + 1 < a) {x : V ι a m} (hx : x ∈ O ι hm) : (uM hm x).val = Matrix.of (sM hm x) := by
  simp [uM, hx]

/- English proof (translation)
Simplify using `[uM, hx]`.
-/
theorem uM_inv_val (hm : m + 1 < a) {x : V ι a m} (hx : x ∈ O ι hm) :
    (uM hm x)⁻¹.val = Matrix.of (sI hm x) := by
  simp [uM, hx]

/- English proof (translation)
Introduce `i`. Simplify using `[e]`.
-/
theorem e_mem (hm : m + 1 < a) : e ι hm ∈ O ι hm := by
  intro i
  simp [e]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = mm hm`. Substitute `hj` using the available equality. Rewrite using `[rowS_mm]`. Simplify using `[e]`.

Establish `h0 : (1 : Matrix (Fin a) (Fin a) (ι → ℂ)) (mm hm) j = 0` using `Matrix.one_apply_ne (Ne.symm hj)`. Rewrite using `[h0]`. Unfold `rowS`. Use `split_ifs with h`. Simplify using `only [e]`.

Rewrite using `[Pi.single_eq_of_ne]`. Introduce `h'`. Conclude with `hj ((block_index_eq_corner_iff hm _).1 h')`. Both sides reduce to the same expression.
-/
theorem rowS_e (hm : m + 1 < a) :
    rowS hm (e ι hm) = (1 : Matrix (Fin a) (Fin a) (ι → ℂ)) (mm hm) := by
  funext j
  by_cases hj : j = mm hm
  · subst hj; rw [rowS_mm]; simp [e]
  · have h0 : (1 : Matrix (Fin a) (Fin a) (ι → ℂ)) (mm hm) j = 0 := Matrix.one_apply_ne (Ne.symm hj)
    rw [h0]
    unfold rowS
    split_ifs with h
    · simp only [e]
      rw [Pi.single_eq_of_ne]
      intro h'; exact hj ((block_index_eq_corner_iff hm _).1 h')
    · rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[uM_val hm (e_mem hm), of_sM, rowS_e, Matrix.updateRow_eq_self]`. Both sides reduce to the same expression.
-/
theorem uM_e (hm : m + 1 < a) : uM hm (e ι hm) = 1 := by
  apply Units.ext
  rw [uM_val hm (e_mem hm), of_sM, rowS_e, Matrix.updateRow_eq_self]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `only [xi, e, Units.val_one, Pi.single_apply, Matrix.one_apply, block_index_eq_corner_iff]`. Distinguish the cases in `h : t.1.1 = mm hm`. Simplify using `[h]`. Simplify using `[h, Ne.symm h]`.
-/
theorem xi_one (hm : m + 1 < a) : xi hm (1 : GL (Fin a) (ι → ℂ)) = e ι hm := by
  funext t
  simp only [xi, e, Units.val_one, Pi.single_apply, Matrix.one_apply, block_index_eq_corner_iff]
  by_cases h : t.1.1 = mm hm
  · simp [h]
  · simp [h, Ne.symm h]

/- English proof (translation)
Introduce `i j hij`. Distinguish the cases in `hx : x ∈ O ι hm`. Rewrite using `[uM_val hm hx, of_sM]`. Distinguish the cases in `hi : i = mm hm`. Substitute `hi` using the available equality.

Establish `hj : ¬ (j : ℕ) < m + 1` using `by simp [mm] at hij; omega`. Establish `hne : mm hm ≠ j` using `by intro h; subst h; simp [mm] at hj`. Rewrite using `[Matrix.updateRow_self, Matrix.one_apply_ne hne]`. Simplify using `[rowS, hj]`. Rewrite using `[Matrix.updateRow_ne hi]`.

Simplify using `[uM, hx]`.
-/
theorem blk_uM (hm : m + 1 < a) (x : V ι a m) : GlobalTheory (m + 1) (uM hm x) := by
  intro i j hij
  by_cases hx : x ∈ O ι hm
  · rw [uM_val hm hx, of_sM]
    by_cases hi : i = mm hm
    · subst hi
      have hj : ¬ (j : ℕ) < m + 1 := by simp [mm] at hij; omega
      have hne : mm hm ≠ j := by intro h; subst h; simp [mm] at hj
      rw [Matrix.updateRow_self, Matrix.one_apply_ne hne]
      simp [rowS, hj]
    · rw [Matrix.updateRow_ne hi]
  · simp [uM, hx]

/- English proof (translation)
Establish `hi1` using `mul_inv_cancel_at_t0_of_mem_O hm hx`. Establish `e0 : xi hm h (t0 hm) = h.val (mm hm) (mm hm)` using `rfl`. Rewrite `hi1` using `[e0]`. Introduce `i k hik`. Rewrite using `[Units.val_mul, uM_inv_val hm hx, of_sI, mul_upd]`.

Distinguish the cases in `hk : k = mm hm`. Substitute `hk` using the available equality. Rewrite using `[rowT_mm, if_pos rfl, add_zero, e0]`. Distinguish the cases in `hi : i = mm hm`. Substitute `hi` using the available equality.

Rewrite using `[hi1, Matrix.one_apply_eq]`. Establish `h2 : m + 1 ≤ (i : ℕ)`. Break down `hik with h1 | h1` into its components or cases. Establish `: (i : ℕ) ≠ m` using `fun e => hi (Fin.ext e)`. Use linear arithmetic over natural numbers and integers.

Simplify using `[mm] at h1`. Rewrite using `[hh i (mm hm) (Or.inl h2), Matrix.one_apply_ne hi, zero_mul]`. Rewrite using `[if_neg hk, rowT_ne hm _ hk, rowS_xi hm hh, e0]`. Distinguish the cases in `hi : i = mm hm`. Substitute `hi` using the available equality.

Rewrite using `[Matrix.one_apply_ne (Ne.symm hk)]`. Take the linear combination `(-(h.val (mm hm) k)) * hi1`. Break down `hik with h1 | h1` into its components or cases. Establish `h2 : m + 1 ≤ (i : ℕ)`. Establish `: (i : ℕ) ≠ m` using `fun e => hi (Fin.ext e)`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hh i (mm hm) (Or.inl h2), hh i k (Or.inl h2), Matrix.one_apply_ne hi]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : m + 1 ≤ (k : ℕ)` using `h1`. Rewrite using `[hh (mm hm) k (Or.inr h2), hh i k (Or.inr h2), Matrix.one_apply_ne (Ne.symm hk)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mir_mul (hm : m + 1 < a) {h : GL (Fin a) (ι → ℂ)} (hh : GlobalTheory (m + 1) h) (hx : xi hm h ∈ O ι hm) :
    Mir m (h * (uM hm (xi hm h))⁻¹) := by
  have hi1 := mul_inv_cancel_at_t0_of_mem_O hm hx
  have e0 : xi hm h (t0 hm) = h.val (mm hm) (mm hm) := rfl
  rw [e0] at hi1
  intro i k hik
  rw [Units.val_mul, uM_inv_val hm hx, of_sI, mul_upd]
  by_cases hk : k = mm hm
  · subst hk
    rw [rowT_mm, if_pos rfl, add_zero, e0]
    by_cases hi : i = mm hm
    · subst hi; rw [hi1, Matrix.one_apply_eq]
    · have h2 : m + 1 ≤ (i : ℕ) := by
        rcases hik with h1 | h1
        · have : (i : ℕ) ≠ m := fun e => hi (Fin.ext e)
          omega
        · simp [mm] at h1
      rw [hh i (mm hm) (Or.inl h2), Matrix.one_apply_ne hi, zero_mul]
  · rw [if_neg hk, rowT_ne hm _ hk, rowS_xi hm hh, e0]
    by_cases hi : i = mm hm
    · subst hi
      rw [Matrix.one_apply_ne (Ne.symm hk)]
      linear_combination (-(h.val (mm hm) k)) * hi1
    · rcases hik with h1 | h1
      · have h2 : m + 1 ≤ (i : ℕ) := by
          have : (i : ℕ) ≠ m := fun e => hi (Fin.ext e)
          omega
        rw [hh i (mm hm) (Or.inl h2), hh i k (Or.inl h2), Matrix.one_apply_ne hi]
        ring
      · have h2 : m + 1 ≤ (k : ℕ) := h1
        rw [hh (mm hm) k (Or.inr h2), hh i k (Or.inr h2), Matrix.one_apply_ne (Ne.symm hk)]
        ring

/- English proof (translation)
Establish `hu : IsUnit (Matrix.of (sI hm x))` using `⟨(uM hm x)⁻¹, uM_inv_val hm hx⟩`. Rewrite using `[orb, dif_pos hu, show hu.unit = (uM hm x)⁻¹ from Units.ext (by rw [IsUnit.unit_spec, uM_inv_val hm hx])]`.
-/
theorem orb_sI [Fintype ι] {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] (hm : m + 1 < a)
    (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (v : X) {x : V ι a m} (hx : x ∈ O ι hm) :
    orb ρ v (sI hm x) = ρ (uM hm x)⁻¹ v := by
  have hu : IsUnit (Matrix.of (sI hm x)) := ⟨(uM hm x)⁻¹, uM_inv_val hm hx⟩
  rw [orb, dif_pos hu, show hu.unit = (uM hm x)⁻¹ from Units.ext (by rw [IsUnit.unit_spec, uM_inv_val hm hx])]

end PositivityTheory.jumpWindows.CornerBlockIndex

end
