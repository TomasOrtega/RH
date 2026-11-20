import Mathlib
import Formalism.IncomingBounds.LevelTail

noncomputable section
open scoped BigOperators
open Finset fwdDiff

namespace Formalism.IncomingBounds

/- English proof (translation)
Establish `h` using `fwdDiff_iter_eq_sum_shift (1 : ℕ) (fun x ↦ (x.choose s : ℤ)) (D + 1) y`. Establish `hz : (fwdDiff (1 : ℕ))^[D + 1] (fun x ↦ (x.choose s : ℤ) : ℕ → ℤ) y = 0`. Take `⟨k, hk⟩ : ∃ k, D + 1 = (k + 1) + s` from `⟨D - s, by omega⟩`. Rewrite using `[hk, Function.iterate_add_apply]`. Establish `h0` using `fwdDiff_iter_choose 0 s`.

Simplify using `only [add_zero] at h0`. Rewrite using `[h0]`. Simplify using `only [Nat.choose_zero_right, Nat.cast_one, Function.iterate_succ_apply, fwdDiff_const]`. Rewrite using `[fwdDiff_iter_eq_sum_shift]`. Simplify using the standard rewrite rules.

Rewrite `h` using `[hz]`. Simplify `h.symm` using `[smul_eq_mul]`.
-/
theorem altChoose_sum_eq_zero (D s y : ℕ) (hs : s ≤ D) :
    ∑ k ∈ range (D + 1 + 1), ((-1 : ℤ) ^ (D + 1 - k) * ((D + 1).choose k : ℤ)) *
      (((y + k).choose s : ℕ) : ℤ) = 0 := by
  have h := fwdDiff_iter_eq_sum_shift (1 : ℕ) (fun x ↦ (x.choose s : ℤ)) (D + 1) y
  have hz : (fwdDiff (1 : ℕ))^[D + 1] (fun x ↦ (x.choose s : ℤ) : ℕ → ℤ) y = 0 := by
    obtain ⟨k, hk⟩ : ∃ k, D + 1 = (k + 1) + s := ⟨D - s, by omega⟩
    rw [hk, Function.iterate_add_apply]
    have h0 := fwdDiff_iter_choose 0 s
    simp only [add_zero] at h0
    rw [h0]
    simp only [Nat.choose_zero_right, Nat.cast_one, Function.iterate_succ_apply, fwdDiff_const]
    rw [fwdDiff_iter_eq_sum_shift]
    simp
  rw [hz] at h
  simpa [smul_eq_mul] using h.symm

/- English proof (translation)
Introduce `l hl A cap J hA hcap hJ`. Use `set T := (Finset.range J).filter Odd with hT`. Establish `hl1 : (1 : ℝ) ≤ l` using `by exact_mod_cast (by omega : 1 ≤ l)`. Establish `hlpos : (0 : ℝ) < l` using `by linarith`. Establish `hpow : ∀ n : ℕ, (0 : ℝ) < (l : ℝ) ^ n` using `fun n => pow_pos hlpos n`.

Establish `hle1 : ∀ j k : ℕ, max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹) 0 ≤ 1`. Introduce `j k`. Apply `max_le _ zero_le_one` to reduce the goal to its premises. Establish `: 0 ≤ (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Set `S` to `T.filter (fun j => A / (l : ℝ) ^ j ≤ cap j)`. Distinguish the cases in `hS : S.Nonempty`. Take `⟨k, hkS, hkmin⟩ : ∃ k ∈ S, ∀ j ∈ S, k ≤ j` from `⟨S.min' hS, S.min'_mem hS, fun j hj => S.min'_le j hj⟩`. Establish `hkT : k ∈ T` using `(Finset.mem_filter.mp hkS).1`. Establish `hkJ : k < J` using `Finset.mem_range.mp (Finset.mem_filter.mp hkT).1`.

Establish `hkcap : A / (l : ℝ) ^ k ≤ cap k` using `(Finset.mem_filter.mp hkS).2`. Use `⟨((l : ℝ) ^ k)⁻¹, ?_, ?_⟩` and prove the remaining obligations. Conclude with `inv_anti₀ (hpow k) (pow_le_pow_right₀ hl1 hkJ.le)`. Establish `hterm : ∀ j ∈ T, cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹) 0 + (if j = k then A * ((l : ℝ) ^ k)⁻¹ else 0) ≤ min (cap j) (A / (l : ℝ) ^ j)`. Introduce `j hj`.

Break down `lt_trichotomy j k with hjk | hjk | hjk` into its components or cases. Establish `hjS : j ∉ S` using `fun h => absurd (hkmin j h) (by omega)`. Establish `hlt : cap j < A / (l : ℝ) ^ j`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Conclude with `hjS (Finset.mem_filter.mpr ⟨hj, hc⟩)`. Rewrite using `[if_neg (by omega), add_zero, min_eq_left hlt.le]`. Combine the equalities or inequalities in the displayed calculation. Substitute `hjk` using the available equality. Rewrite using `[if_pos rfl, mul_inv_cancel₀ (hpow j).ne', sub_self, max_self, mul_zero, zero_add, min_eq_right hkcap, div_eq_mul_inv]`.

Establish `h1 : 1 ≤ (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹`. Rewrite using `[← div_eq_mul_inv, le_div_iff₀ (hpow k), one_mul]`. Conclude with `pow_le_pow_right₀ hl1 hjk.le`. Rewrite using `[if_neg (by omega), add_zero, max_eq_right (by linarith), mul_zero]`. Conclude with `le_min (hcap j) (div_nonneg hA (hpow j).le)`.

Establish `hsum` using `Finset.sum_le_sum hterm`. Rewrite `hsum` using `[Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hkT]`. Establish `: 0 ≤ A / (l : ℝ) ^ J` using `div_nonneg hA (hpow J).le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hS' : ∀ j ∈ T, cap j < A / (l : ℝ) ^ j`.

Introduce `j hj`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hS ⟨j, Finset.mem_filter.mpr ⟨hj, hc⟩⟩`. Use `⟨((l : ℝ) ^ J)⁻¹, le_rfl, ?_⟩` and prove the remaining obligations.

Establish `hterm : ∀ j ∈ T, cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ J)⁻¹) 0 ≤ min (cap j) (A / (l : ℝ) ^ j)`. Introduce `j hj`. Rewrite using `[min_eq_left (hS' j hj).le]`. Combine the equalities or inequalities in the displayed calculation. Establish `hsum` using `Finset.sum_le_sum hterm`.

Rewrite using `[div_eq_mul_inv A]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem top_radius_holds : TopRadius := by
  intro l hl A cap J hA hcap hJ
  set T := (Finset.range J).filter Odd with hT
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  have hlpos : (0 : ℝ) < l := by linarith
  have hpow : ∀ n : ℕ, (0 : ℝ) < (l : ℝ) ^ n := fun n => pow_pos hlpos n
  have hle1 : ∀ j k : ℕ, max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹) 0 ≤ 1 := by
    intro j k
    apply max_le _ zero_le_one
    have : 0 ≤ (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹ := by positivity
    linarith
  let S := T.filter (fun j => A / (l : ℝ) ^ j ≤ cap j)
  by_cases hS : S.Nonempty
  · obtain ⟨k, hkS, hkmin⟩ : ∃ k ∈ S, ∀ j ∈ S, k ≤ j :=
      ⟨S.min' hS, S.min'_mem hS, fun j hj => S.min'_le j hj⟩
    have hkT : k ∈ T := (Finset.mem_filter.mp hkS).1
    have hkJ : k < J := Finset.mem_range.mp (Finset.mem_filter.mp hkT).1
    have hkcap : A / (l : ℝ) ^ k ≤ cap k := (Finset.mem_filter.mp hkS).2
    refine ⟨((l : ℝ) ^ k)⁻¹, ?_, ?_⟩
    · exact inv_anti₀ (hpow k) (pow_le_pow_right₀ hl1 hkJ.le)
    · have hterm : ∀ j ∈ T, cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹) 0 +
          (if j = k then A * ((l : ℝ) ^ k)⁻¹ else 0) ≤ min (cap j) (A / (l : ℝ) ^ j) := by
        intro j hj
        rcases lt_trichotomy j k with hjk | hjk | hjk
        · have hjS : j ∉ S := fun h => absurd (hkmin j h) (by omega)
          have hlt : cap j < A / (l : ℝ) ^ j := by
            by_contra hc
            push Not at hc
            exact hjS (Finset.mem_filter.mpr ⟨hj, hc⟩)
          rw [if_neg (by omega), add_zero, min_eq_left hlt.le]
          calc cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹) 0 ≤ cap j * 1 :=
                mul_le_mul_of_nonneg_left (hle1 j k) (hcap j)
            _ = cap j := mul_one _
        · subst hjk
          rw [if_pos rfl, mul_inv_cancel₀ (hpow j).ne', sub_self, max_self, mul_zero, zero_add,
            min_eq_right hkcap, div_eq_mul_inv]
        · have h1 : 1 ≤ (l : ℝ) ^ j * ((l : ℝ) ^ k)⁻¹ := by
            rw [← div_eq_mul_inv, le_div_iff₀ (hpow k), one_mul]
            exact pow_le_pow_right₀ hl1 hjk.le
          rw [if_neg (by omega), add_zero, max_eq_right (by linarith), mul_zero]
          exact le_min (hcap j) (div_nonneg hA (hpow j).le)
      have hsum := Finset.sum_le_sum hterm
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hkT] at hsum
      have : 0 ≤ A / (l : ℝ) ^ J := div_nonneg hA (hpow J).le
      linarith
  · have hS' : ∀ j ∈ T, cap j < A / (l : ℝ) ^ j := by
      intro j hj
      by_contra hc
      push Not at hc
      exact hS ⟨j, Finset.mem_filter.mpr ⟨hj, hc⟩⟩
    refine ⟨((l : ℝ) ^ J)⁻¹, le_rfl, ?_⟩
    have hterm : ∀ j ∈ T, cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ J)⁻¹) 0 ≤
        min (cap j) (A / (l : ℝ) ^ j) := by
      intro j hj
      rw [min_eq_left (hS' j hj).le]
      calc cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ J)⁻¹) 0 ≤ cap j * 1 :=
            mul_le_mul_of_nonneg_left (hle1 j J) (hcap j)
        _ = cap j := mul_one _
    have hsum := Finset.sum_le_sum hterm
    rw [div_eq_mul_inv A]
    linarith

/- English proof (translation)
Introduce `R _ I D a y0 hwin`. Set `f : ℕ → R` to `fun y => ∑ s ∈ range (D + 1), a s * ((Nat.choose y s : ℕ) : R)`. Set `c : ℕ → ℤ` to `fun k => (-1 : ℤ) ^ (D + 1 - k) * (((D + 1).choose k : ℕ) : ℤ)`. Establish `hsm : ∀ (z : ℤ) (x : R), x ∈ I → (z : R) * x ∈ I`. Introduce `z x hx`.

Rewrite using `[← zsmul_eq_mul]`. Conclude with `I.zsmul_mem hx z`. Establish `hZ : ∀ y s, s ≤ D → ∑ k ∈ range (D + 1 + 1), (c k : R) * (((y + k).choose s : ℕ) : R) = 0`. Introduce `y s hs`. Use `congrArg (Int.cast : ℤ → R) (altChoose_sum_eq_zero D s y hs)` as an intermediate fact.

Move the coercions through the operations in `at this`. Simplify `this` using `[c]`. Establish `hE : ∀ y, ∑ k ∈ range (D + 1 + 1), (c k : R) * f (y + k) = 0`. Introduce `y`. Establish `hk : ∀ k, (c k : R) * f (y + k) = ∑ s ∈ range (D + 1), a s * ((c k : R) * (((y + k).choose s : ℕ) : R))`.

Introduce `k`. Simplify using `only [f, Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `s _`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[hk]`. Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `s hs`. Rewrite using `[← Finset.mul_sum, hZ y s (by simp at hs; omega), mul_zero]`.

Establish `hup : ∀ t, f (y0 + t) ∈ I`. Introduce `t`. Proceed by induction on `t using Nat.strong_induction_on with`. Consider the case `_ t ih`. Distinguish the cases in `ht : t ≤ D`.

Conclude with `hwin t ht`. Take `⟨u, rfl⟩ : ∃ u, t = u + (D + 1)` from `⟨t - (D + 1), by omega⟩`. Establish `h` using `hE (y0 + u)`. Rewrite `h` using `[Finset.sum_range_succ]`. Establish `hc : (c (D + 1) : R) = 1` using `by simp [c]`.

Rewrite `h` using `[hc, one_mul]`. Establish `hmem : ∑ k ∈ range (D + 1), (c k : R) * f (y0 + u + k) ∈ I`. Apply `AddSubgroup.sum_mem` to reduce the goal to its premises. Introduce `k hk`. Apply `hsm` to reduce the goal to its premises.

Use `ih (u + k) (by simp at hk; omega)` as an intermediate fact. Rewrite `this` using `[← add_assoc]`. Then use the resulting hypothesis. Establish `: f (y0 + (u + (D + 1))) = -(∑ k ∈ range (D + 1), (c k : R) * f (y0 + u + k))`. Rewrite using `[← add_assoc]`. Take the linear combination `h`.

Rewrite using `[this]`. Conclude with `I.neg_mem hmem`. Establish `hc0i : c 0 * c 0 = 1`. Simplify using `only [c, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero, ← mul_pow]`. Simplify using the standard rewrite rules.

Establish `hc0 : (c 0 : R) * (c 0 : R) = 1`. Rewrite using `[← Int.cast_mul, hc0i, Int.cast_one]`. Establish `hdown : ∀ m y, y0 ≤ y + m → f y ∈ I`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero`. Introduce `y hy`. Take `⟨t, rfl⟩ : ∃ t, y = y0 + t` from `⟨y - y0, by omega⟩`. Conclude with `hup t`. Consider the case `succ m ih`.

Introduce `y hy`. Establish `h` using `hE y`. Rewrite `h` using `[Finset.sum_range_succ']`. Simplify using `only [add_zero] at h`. Establish `hmem : ∑ k ∈ range (D + 1), (c (k + 1) : R) * f (y + (k + 1)) ∈ I`.

Apply `AddSubgroup.sum_mem` to reduce the goal to its premises. Introduce `k _`. Apply `hsm` to reduce the goal to its premises. Apply `ih` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers.

Establish `: f y = (c 0 : R) * (-(∑ k ∈ range (D + 1), (c (k + 1) : R) * f (y + (k + 1))))`. Take the linear combination `(c 0 : R) * h - (f y) * hc0`. Rewrite using `[this]`. Conclude with `hsm _ _ (I.neg_mem hmem)`. Introduce `y`.

Conclude with `hdown y0 y (by omega)`.
-/
theorem newton_window_holds : NewtonWindow := by
  intro R _ I D a y0 hwin
  let f : ℕ → R := fun y => ∑ s ∈ range (D + 1), a s * ((Nat.choose y s : ℕ) : R)
  let c : ℕ → ℤ := fun k => (-1 : ℤ) ^ (D + 1 - k) * (((D + 1).choose k : ℕ) : ℤ)
  have hsm : ∀ (z : ℤ) (x : R), x ∈ I → (z : R) * x ∈ I := by
    intro z x hx
    rw [← zsmul_eq_mul]
    exact I.zsmul_mem hx z
  have hZ : ∀ y s, s ≤ D →
      ∑ k ∈ range (D + 1 + 1), (c k : R) * (((y + k).choose s : ℕ) : R) = 0 := by
    intro y s hs
    have := congrArg (Int.cast : ℤ → R) (altChoose_sum_eq_zero D s y hs)
    push_cast at this
    simpa [c] using this
  have hE : ∀ y, ∑ k ∈ range (D + 1 + 1), (c k : R) * f (y + k) = 0 := by
    intro y
    have hk : ∀ k, (c k : R) * f (y + k) =
        ∑ s ∈ range (D + 1), a s * ((c k : R) * (((y + k).choose s : ℕ) : R)) := by
      intro k
      simp only [f, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    simp_rw [hk]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro s hs
    rw [← Finset.mul_sum, hZ y s (by simp at hs; omega), mul_zero]
  have hup : ∀ t, f (y0 + t) ∈ I := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      by_cases ht : t ≤ D
      · exact hwin t ht
      · obtain ⟨u, rfl⟩ : ∃ u, t = u + (D + 1) := ⟨t - (D + 1), by omega⟩
        have h := hE (y0 + u)
        rw [Finset.sum_range_succ] at h
        have hc : (c (D + 1) : R) = 1 := by simp [c]
        rw [hc, one_mul] at h
        have hmem : ∑ k ∈ range (D + 1), (c k : R) * f (y0 + u + k) ∈ I := by
          apply AddSubgroup.sum_mem
          intro k hk
          apply hsm
          have := ih (u + k) (by simp at hk; omega)
          rwa [← add_assoc] at this
        have : f (y0 + (u + (D + 1))) = -(∑ k ∈ range (D + 1), (c k : R) * f (y0 + u + k)) := by
          rw [← add_assoc]
          linear_combination h
        rw [this]
        exact I.neg_mem hmem
  have hc0i : c 0 * c 0 = 1 := by
    simp only [c, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero, ← mul_pow]
    simp
  have hc0 : (c 0 : R) * (c 0 : R) = 1 := by
    rw [← Int.cast_mul, hc0i, Int.cast_one]
  have hdown : ∀ m y, y0 ≤ y + m → f y ∈ I := by
    intro m
    induction m with
    | zero =>
      intro y hy
      obtain ⟨t, rfl⟩ : ∃ t, y = y0 + t := ⟨y - y0, by omega⟩
      exact hup t
    | succ m ih =>
      intro y hy
      have h := hE y
      rw [Finset.sum_range_succ'] at h
      simp only [add_zero] at h
      have hmem : ∑ k ∈ range (D + 1), (c (k + 1) : R) * f (y + (k + 1)) ∈ I := by
        apply AddSubgroup.sum_mem
        intro k _
        apply hsm
        apply ih
        omega
      have : f y = (c 0 : R) * (-(∑ k ∈ range (D + 1), (c (k + 1) : R) * f (y + (k + 1)))) := by
        linear_combination (c 0 : R) * h - (f y) * hc0
      rw [this]
      exact hsm _ _ (I.neg_mem hmem)
  intro y
  exact hdown y0 y (by omega)

end Formalism.IncomingBounds
