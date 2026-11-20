import Mathlib
import Formalism.PeriodIntegrals.WeylForU

noncomputable section

namespace PI.WeylForUWork

open Finset PI.UpqRep Formalism.BasicNotions

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `h1 : ∀ i ∈ range n, ∏ j ∈ Ico (i + 1) (n + 1), ((j : ℝ) - (i : ℝ)) = (∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ))) * ((n : ℝ) - (i : ℝ))`. Introduce `i hi`.

Conclude with `Finset.prod_Ico_succ_top (Nat.succ_le_of_lt (Finset.mem_range.mp hi)) _`. Establish `h2 : ∀ k : ℕ, ∏ i ∈ range k, ((k : ℝ) - (i : ℝ)) = ((k.factorial : ℕ) : ℝ)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ihk`. Establish `e : ∀ i ∈ range k, (((k + 1 : ℕ) : ℝ) - ((i + 1 : ℕ) : ℝ)) = (k : ℝ) - (i : ℝ)`. Introduce `i _`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Finset.prod_range_succ', Finset.prod_congr rfl e, ihk, Nat.factorial_succ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.prod_range_succ, Finset.prod_range_succ, Finset.Ico_self, Finset.prod_empty, mul_one, Finset.prod_congr rfl h1, Finset.prod_mul_distrib, ih, h2 n]`.
-/
theorem denom_range (n : ℕ) :
    ∏ i ∈ range n, ∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ)) =
      ∏ i ∈ range n, ((i.factorial : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∀ i ∈ range n, ∏ j ∈ Ico (i + 1) (n + 1), ((j : ℝ) - (i : ℝ)) =
        (∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ))) * ((n : ℝ) - (i : ℝ)) := by
      intro i hi
      exact Finset.prod_Ico_succ_top (Nat.succ_le_of_lt (Finset.mem_range.mp hi)) _
    have h2 : ∀ k : ℕ, ∏ i ∈ range k, ((k : ℝ) - (i : ℝ)) = ((k.factorial : ℕ) : ℝ) := by
      intro k
      induction k with
      | zero => simp
      | succ k ihk =>
        have e : ∀ i ∈ range k, (((k + 1 : ℕ) : ℝ) - ((i + 1 : ℕ) : ℝ)) = (k : ℝ) - (i : ℝ) := by
          intro i _
          push_cast
          ring
        rw [Finset.prod_range_succ', Finset.prod_congr rfl e, ihk, Nat.factorial_succ]
        push_cast
        ring
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.Ico_self, Finset.prod_empty, mul_one,
      Finset.prod_congr rfl h1, Finset.prod_mul_distrib, ih, h2 n]

/- English proof (translation)
Use `Finset.prod_nbij (fun b : Fin n => (b : ℕ)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `b hb`. Rewrite `hb` using `[Finset.mem_filter]`. Rewrite using `[Finset.mem_Ico]`. Conclude with `⟨hb.2, b.isLt⟩`.

Introduce `x _ y _ h`. Conclude with `Fin.ext h`. Introduce `j hj`. Rewrite `hj` using `[Finset.mem_coe, Finset.mem_Ico]`. Use `⟨⟨j, hj.2⟩, ?_, rfl⟩` and prove the remaining obligations.

Rewrite using `[Finset.mem_coe, Finset.mem_filter]`. Conclude with `⟨Finset.mem_univ _, hj.1⟩`. Introduce `b _`. Both sides reduce to the same expression.
-/
theorem row_fin (n : ℕ) (a : Fin n) :
    ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ j ∈ Ico ((a : ℕ) + 1) n, ((j : ℝ) - ((a : ℕ) : ℝ)) := by
  refine Finset.prod_nbij (fun b : Fin n => (b : ℕ)) ?_ ?_ ?_ ?_
  · intro b hb
    rw [Finset.mem_filter] at hb
    rw [Finset.mem_Ico]
    exact ⟨hb.2, b.isLt⟩
  · intro x _ y _ h
    exact Fin.ext h
  · intro j hj
    rw [Finset.mem_coe, Finset.mem_Ico] at hj
    refine ⟨⟨j, hj.2⟩, ?_, rfl⟩
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hj.1⟩
  · intro b _
    rfl

/- English proof (translation)
Use `(Finset.prod_congr rfl (fun a _ => row_fin n a)).trans ?_` and prove the remaining obligations. Conclude with `(Fin.prod_univ_eq_prod_range (fun i : ℕ => ∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ))) n).trans (denom_range n)`.
-/
theorem denom_fin (n : ℕ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ i ∈ range n, ((i.factorial : ℕ) : ℝ) := by
  refine (Finset.prod_congr rfl (fun a _ => row_fin n a)).trans ?_
  exact (Fin.prod_univ_eq_prod_range (fun i : ℕ => ∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ))) n).trans
    (denom_range n)

/- English proof (translation)
Introduce `i j hij`. Unfold `Formalism.BasicNotions.DomWeight.natW`. Conclude with `Int.toNat_le_toNat (sub_le_sub_right (lam.2 hij) _)`.
-/
theorem natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  unfold Formalism.BasicNotions.DomWeight.natW
  exact Int.toNat_le_toNat (sub_le_sub_right (lam.2 hij) _)

/- English proof (translation)
Establish `hN0 : 0 < N` using `Fin.pos i`. Establish `hle : lam.w ⟨N - 1, by omega⟩ ≤ lam.w i` using `lam.anti (Fin.le_iff_val_le_val.mpr (by simp only; omega))`. Unfold `DomWeight.natW DomWeight.detShift`. Rewrite using `[dif_pos hN0]`. Conclude with `Int.toNat_of_nonneg (by omega)`.
-/
theorem natW_cast {N : ℕ} (lam : DomWeight N) (i : Fin N) :
    ((lam.natW i : ℕ) : ℤ) = lam.w i - lam.detShift := by
  have hN0 : 0 < N := Fin.pos i
  have hle : lam.w ⟨N - 1, by omega⟩ ≤ lam.w i :=
    lam.anti (Fin.le_iff_val_le_val.mpr (by simp only; omega))
  unfold DomWeight.natW DomWeight.detShift
  rw [dif_pos hN0]
  exact Int.toNat_of_nonneg (by omega)

/- English proof (translation)
Conclude with `natW_cast lam i` after adjusting the coercions.
-/
theorem natW_cast_real {N : ℕ} (lam : DomWeight N) (i : Fin N) :
    ((lam.natW i : ℕ) : ℝ) = ((lam.w i : ℤ) : ℝ) - ((lam.detShift : ℤ) : ℝ) := by
  exact_mod_cast natW_cast lam i

/- English proof (translation)
Introduce `hM hN N Λ H _ _ σ S hU hK`. Take `⟨lam, hΛ, hdim⟩` from `hM N Λ H σ S hU hK`. Rewrite using `[hdim]`. Establish `h2 : ((Module.finrank ℂ ↥(nablaSq ℂ N lam) : ℕ) : ℚ) = (∏ i : Fin N, ∏ j ∈ univ.filter (fun j : Fin N => i < j), (((lam.natW i : ℕ) : ℚ) - ((lam.natW j : ℕ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))) / ∏ i : Fin N, ∏ j ∈ univ.filter (fun j : Fin N => i < j), (((j : ℕ) : ℚ) - ((i : ℕ) …`. Rewrite using `[← Finset.prod_div_distrib]`.

Use `(hN N lam.natW (natW_anti lam)).trans (Finset.prod_congr rfl (fun i _ => ?_))` and prove the remaining obligations. Rewrite using `[← Finset.prod_div_distrib, Finset.prod_filter]`. Establish `h3` using `congrArg (fun q : ℚ => (q : ℝ)) h2`. Move the coercions through the operations in `at h3`. Rewrite using `[h3, denom_fin]`.

Use `congr 1`. Use `Finset.prod_congr rfl (fun a _ => Finset.prod_congr rfl (fun b _ => ?_))` and prove the remaining obligations. Rewrite using `[natW_cast_real, natW_cast_real, hΛ a, hΛ b]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weylForU_of : PI.ModelIso → PI.NablaDim → PI.WeylForU := by
  intro hM hN N Λ H _ _ σ S hU hK
  obtain ⟨lam, hΛ, hdim⟩ := hM N Λ H σ S hU hK
  rw [hdim]
  have h2 : ((Module.finrank ℂ ↥(nablaSq ℂ N lam) : ℕ) : ℚ) =
      (∏ i : Fin N, ∏ j ∈ univ.filter (fun j : Fin N => i < j), (((lam.natW i : ℕ) : ℚ) -
        ((lam.natW j : ℕ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))) /
      ∏ i : Fin N, ∏ j ∈ univ.filter (fun j : Fin N => i < j), (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) := by
    rw [← Finset.prod_div_distrib]
    refine (hN N lam.natW (natW_anti lam)).trans (Finset.prod_congr rfl (fun i _ => ?_))
    rw [← Finset.prod_div_distrib, Finset.prod_filter]
  have h3 := congrArg (fun q : ℚ => (q : ℝ)) h2
  push_cast at h3
  rw [h3, denom_fin]
  congr 1
  refine Finset.prod_congr rfl (fun a _ => Finset.prod_congr rfl (fun b _ => ?_))
  rw [natW_cast_real, natW_cast_real, hΛ a, hΛ b]
  ring

end PI.WeylForUWork
