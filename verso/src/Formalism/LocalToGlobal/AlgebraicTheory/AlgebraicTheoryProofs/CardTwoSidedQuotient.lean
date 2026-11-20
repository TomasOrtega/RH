import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.KernelIndexForm
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.XiConn
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.DvdOfNormIntCastLt

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField IsDedekindDomain

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.H (IsReps Sesq altE dualLat semicharacterBasic)
open Formalism.L2.Col (Fields Sp HomE IsSdLat)
open Formalism.L2.Ker (Amb VCx LamC BC AC HV alV repsOf brk SplitHyp)

namespace KerA

/- English proof (translation)
Simplify using `only [altE, map_add, LinearMap.add_apply, Complex.add_im]`.
-/
private theorem skew_form_add_left {V : Type*} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (x y z : V) :
    altE H (x + y) z = altE H x z + altE H y z := by
  simp only [altE, map_add, LinearMap.add_apply, Complex.add_im]

/- English proof (translation)
Simplify using `only [altE, map_add, Complex.add_im]`.
-/
private theorem skew_form_add_right {V : Type*} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (x y z : V) :
    altE H x (y + z) = altE H x y + altE H x z := by
  simp only [altE, map_add, Complex.add_im]

/- English proof (translation)
Take `⟨m, rfl⟩` from `h`. Rewrite using `[show (2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) = (m : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]`. Conclude with `Complex.exp_int_mul_two_pi_mul_I m`.
-/
private theorem exp_two_pi_I_int_eq_one (t : ℝ) (h : ∃ m : ℤ, t = m) :
    Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) = 1 := by
  obtain ⟨m, rfl⟩ := h
  rw [show (2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) = (m : ℂ) * (2 * Real.pi * Complex.I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I m

/- English proof (translation)
Take `⟨n, hn⟩` from `Complex.exp_eq_one_iff.mp h`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0`. Simplify using `[Real.pi_ne_zero, Complex.I_ne_zero]`. Establish `h3 : (t : ℂ) = (n : ℂ)`.

Apply `mul_left_cancel₀ h2` to reduce the goal to its premises. Rewrite using `[hn]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `h3` after adjusting the coercions.
-/
private theorem exists_int_eq_of_exp_two_pi_I_eq_one (t : ℝ) (h : Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) = 1) :
    ∃ m : ℤ, t = m := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨n, ?_⟩
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h3 : (t : ℂ) = (n : ℂ) := by
    apply mul_left_cancel₀ h2
    rw [hn]
    ring
  exact_mod_cast h3

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Establish `key : ∀ x : V, ∃ y : V, x ∈ L₂ → y ∈ S ∧ x - y ∈ L₁`. Introduce `x`. Distinguish the cases in `hx : x ∈ L₂`. Take `⟨y, hy, hxy⟩` from `h3 x hx`.

Conclude with `⟨y, fun _ => ⟨hy, hxy⟩⟩`. Conclude with `⟨x, fun h => absurd h hx⟩`. Use `choose ρ hρ using key`. Establish `hst : ∀ s ∈ S, s + t ∈ L₂` using `fun s hs => L₂.add_mem (h1 s hs) ht`. Establish `hinj : Set.InjOn (fun s => ρ (s + t)) (S : Set V)`.

Introduce `s hs s' hs' hss`. Establish `hs1 : s ∈ S` using `Finset.mem_coe.mp hs`. Establish `hs2 : s' ∈ S` using `Finset.mem_coe.mp hs'`. Apply `h2 s hs1 s' hs2` to reduce the goal to its premises. Establish `e1` using `(hρ (s + t) (hst s hs1)).2`.

Establish `e2` using `(hρ (s' + t) (hst s' hs2)).2`. Establish `hss' : ρ (s + t) = ρ (s' + t)` using `hss`. Establish `hrw : s - s' = (s + t - ρ (s + t)) - (s' + t - ρ (s' + t))`. Rewrite using `[hss']`. Normalize the expressions using the abelian group laws.

Rewrite using `[hrw]`. Conclude with `L₁.sub_mem e1 e2`. Establish `himg : S.image (fun s => ρ (s + t)) = S`. Apply `Finset.eq_of_subset_of_card_le` to reduce the goal to its premises. Introduce `x hx`.

Take `⟨s, hs, rfl⟩` from `Finset.mem_image.mp hx`. Conclude with `(hρ (s + t) (hst s hs)).1`. Conclude with `(Finset.card_image_of_injOn hinj).ge`. Establish `hsum : ∑ s ∈ S, f s = c * ∑ s ∈ S, f s`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Rewrite using `[← hmul s (h1 s hs)]`. Conclude with `(hinv (s + t) (hst s hs) _ (h1 _ (hρ (s + t) (hst s hs)).1) (hρ (s + t) (hst s hs)).2).symm`. Use `_ = c * ∑ s ∈ S, f s := by rw [Finset.mul_sum]`. Establish `h0 : (1 - c) * ∑ s ∈ S, f s = 0` using `by linear_combination hsum`.

Break down `mul_eq_zero.mp h0 with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.mp h).symm hc`. Conclude with `h`.
-/
private theorem sum_reps_eq_zero_of_shift_mul {V : Type*} [AddCommGroup V] [Module ℂ V] (L₁ L₂ : AddSubgroup V)
    (S : Finset V) (h : IsReps L₁ L₂ S) (f : V → ℂ) (t : V) (ht : t ∈ L₂) (c : ℂ) (hc : c ≠ 1)
    (hinv : ∀ x ∈ L₂, ∀ y ∈ L₂, x - y ∈ L₁ → f x = f y)
    (hmul : ∀ x ∈ L₂, f (x + t) = c * f x) : ∑ s ∈ S, f s = 0 := by
  classical
  obtain ⟨h1, h2, h3⟩ := h
  have key : ∀ x : V, ∃ y : V, x ∈ L₂ → y ∈ S ∧ x - y ∈ L₁ := by
    intro x
    by_cases hx : x ∈ L₂
    · obtain ⟨y, hy, hxy⟩ := h3 x hx
      exact ⟨y, fun _ => ⟨hy, hxy⟩⟩
    · exact ⟨x, fun h => absurd h hx⟩
  choose ρ hρ using key
  have hst : ∀ s ∈ S, s + t ∈ L₂ := fun s hs => L₂.add_mem (h1 s hs) ht
  have hinj : Set.InjOn (fun s => ρ (s + t)) (S : Set V) := by
    intro s hs s' hs' hss
    have hs1 : s ∈ S := Finset.mem_coe.mp hs
    have hs2 : s' ∈ S := Finset.mem_coe.mp hs'
    apply h2 s hs1 s' hs2
    have e1 := (hρ (s + t) (hst s hs1)).2
    have e2 := (hρ (s' + t) (hst s' hs2)).2
    have hss' : ρ (s + t) = ρ (s' + t) := hss
    have hrw : s - s' = (s + t - ρ (s + t)) - (s' + t - ρ (s' + t)) := by
      rw [hss']
      abel
    rw [hrw]
    exact L₁.sub_mem e1 e2
  have himg : S.image (fun s => ρ (s + t)) = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
      exact (hρ (s + t) (hst s hs)).1
    · exact (Finset.card_image_of_injOn hinj).ge
  have hsum : ∑ s ∈ S, f s = c * ∑ s ∈ S, f s := by
    calc ∑ s ∈ S, f s = ∑ x ∈ S.image (fun s => ρ (s + t)), f x := by rw [himg]
      _ = ∑ s ∈ S, f (ρ (s + t)) := Finset.sum_image hinj
      _ = ∑ s ∈ S, c * f s := by
          refine Finset.sum_congr rfl fun s hs => ?_
          rw [← hmul s (h1 s hs)]
          exact (hinv (s + t) (hst s hs) _ (h1 _ (hρ (s + t) (hst s hs)).1)
            (hρ (s + t) (hst s hs)).2).symm
      _ = c * ∑ s ∈ S, f s := by rw [Finset.mul_sum]
  have h0 : (1 - c) * ∑ s ∈ S, f s = 0 := by linear_combination hsum
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hc
  · exact h

/- English proof (translation)
Take `⟨hH, -, -, -, hB, hG⟩` from `hyp`. Take `⟨hΛ, -, -, -, h5⟩` from `hG`. Take `⟨hA1, hA2, hA3⟩` from `hSA`. Take `⟨hB1, hB2, hB3⟩` from `hSB`. Establish `hB' : dualLat H B = B` using `hB`.

Take `⟨E, hE⟩ : ∃ E : V → V → ℂ, ∀ x y, E x y = Complex.exp (2 * Real.pi * Complex.I * (altE H x y : ℂ))` from `⟨_, fun _ _ => rfl⟩`. Establish `EaddL : ∀ x y z, E (x + y) z = E x z * E y z`. Introduce `x y z`. Rewrite using `[hE, hE, hE, skew_form_add_left, Complex.ofReal_add, mul_add, Complex.exp_add]`. Establish `EaddR : ∀ x y z, E x (y + z) = E x y * E x z`.

Introduce `x y z`. Rewrite using `[hE, hE, hE, skew_form_add_right, Complex.ofReal_add, mul_add, Complex.exp_add]`. Establish `Eint : ∀ x y, (∃ m : ℤ, altE H x y = m) → E x y = 1` using `fun x y h => by`. Rewrite using `[hE]`. Conclude with `exp_two_pi_I_int_eq_one _ h`.

Establish `Eone : ∀ x y, E x y = 1 → ∃ m : ℤ, altE H x y = m` using `fun x y h => by`. Rewrite `h` using `[hE]`. Conclude with `exists_int_eq_of_exp_two_pi_I_eq_one _ h`. Establish `F2 : ∀ x ∈ B, ∀ y ∈ B, E x y = 1`. Introduce `x hx y hy`.

Apply `Eint` to reduce the goal to its premises. Establish `hx' : x ∈ dualLat H B` using `by rw [hB']; exact hx`. Conclude with `(show ∀ y ∈ B, ∃ m : ℤ, altE H x y = (m : ℝ) from hx') y hy`. Establish `hskew : ∀ x y, altE H y x = -altE H x y`. Introduce `x y`.

Establish `h : H y x = (starRingEnd ℂ) (H x y)` using `hH x y`. Simplify using `only [altE]`. Rewrite using `[h, Complex.conj_im]`. Establish `F3 : ∀ x ∈ Λ, ∀ y ∈ Λ, E x y = 1`. Introduce `x hx y hy`.

Establish `e1` using `hΛ.2 x hx y hy`. Establish `e2` using `hΛ.2 y hy x hx`. Rewrite `e2` using `[add_comm y x, hskew x y]`. Establish `hx0 : α x ≠ 0`. Apply the tactic sequence `rcases hΛ.1 x hx with h | h <;> rw [h] <;> norm_num`.

Establish `hy0 : α y ≠ 0`. Apply the tactic sequence `rcases hΛ.1 y hy with h | h <;> rw [h] <;> norm_num`. Establish `key : Complex.exp (Real.pi * Complex.I * (altE H x y : ℂ)) = Complex.exp (Real.pi * Complex.I * ((-altE H x y : ℝ) : ℂ))`. Establish `h3 : α x * α y * Complex.exp (Real.pi * Complex.I * (altE H x y : ℂ)) = α x * α y * Complex.exp (Real.pi * Complex.I * ((-altE H x y : ℝ) : ℂ))`. Rewrite using `[← e1, e2]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `mul_left_cancel₀ (mul_ne_zero hx0 hy0) h3`. Rewrite using `[hE]`. Establish `h4 : (2 * Real.pi * Complex.I * (altE H x y : ℂ)) = Real.pi * Complex.I * (altE H x y : ℂ) + Real.pi * Complex.I * (altE H x y : ℂ)` using `by ring`. Rewrite using `[h4, Complex.exp_add]`.

Use `nth_rewrite 2 [key]`. Rewrite using `[← Complex.exp_add, show (Real.pi * Complex.I * (altE H x y : ℂ) + Real.pi * Complex.I * ((-altE H x y : ℝ) : ℂ)) = 0 by push_cast; ring, Complex.exp_zero]`. Establish `F4 : ∀ x, x ∉ B → ∃ y ∈ B, E x y ≠ 1`. Introduce `x hx`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Apply `hx` to reduce the goal to its premises. Rewrite using `[← hB']`. Use `show ∀ y ∈ B, ∃ m : ℤ, altE H x y = (m : ℝ)`. Introduce `y hy`.

Conclude with `Eone x y (hcon y hy)`. Establish `F5 : ∀ y ∈ B, y ∉ Λ → ∃ x ∈ Λ ⊓ A, E x y ≠ 1`. Introduce `y hy hyΛ`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Apply `hyΛ` to reduce the goal to its premises. Apply `h5 y hy` to reduce the goal to its premises. Introduce `x hxA hxΛ`. Conclude with `Eone x y (hcon x (AddSubgroup.mem_inf.mpr ⟨hxΛ, hxA⟩))`. Establish `inner1 : ∀ x ∈ SA, ∑ y ∈ SB, E x y = if x ∈ B then (SB.card : ℂ) else 0`.

Introduce `x hx`. Establish `hxΛ : x ∈ Λ` using `(AddSubgroup.mem_inf.mp (hA1 x hx)).1`. Use `split_ifs with hxB`. Rewrite using `[Finset.sum_congr rfl fun y hy => F2 x hxB y (hB1 y hy)]`. Simplify using the standard rewrite rules.

Take `⟨t, ht, hEt⟩` from `F4 x hxB`. Use `sum_reps_eq_zero_of_shift_mul Λ B SB ⟨hB1, hB2, hB3⟩ (fun y => E x y) t ht (E x t) hEt ?_ ?_` and prove the remaining obligations. Introduce `u hu v hv huv show E x u = E x v`. Establish `hu' : u = v + (u - v)` using `by abel`. Rewrite using `[hu', EaddR, F3 x hxΛ _ huv, mul_one]`.

Introduce `u hu show E x (u + t) = E x t * E x u`. Rewrite using `[EaddR, mul_comm]`. Establish `count1 : (SA.filter (fun x => x ∈ B)).card = 1`. Take `⟨x0, hx0, h0⟩` from `hA3 0 (Λ ⊓ A).zero_mem`. Establish `hx0B : x0 ∈ B` using `by simpa using B.neg_mem h0`.

Rewrite using `[Finset.card_eq_one]`. Use `⟨x0, Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hx0, hx0B⟩, ?_⟩⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨hxS, hxB⟩` from `Finset.mem_filter.mp hx`. Conclude with `hA2 x hxS x0 hx0 (B.sub_mem hxB hx0B)`.

Establish `S1 : ∑ x ∈ SA, ∑ y ∈ SB, E x y = SB.card`. Rewrite using `[Finset.sum_congr rfl inner1, ← Finset.sum_filter, Finset.sum_const, count1, one_smul]`. Establish `inner2 : ∀ y ∈ SB, ∑ x ∈ SA, E x y = if y ∈ Λ then (SA.card : ℂ) else 0`. Introduce `y hy`. Establish `hyB : y ∈ B` using `hB1 y hy`.

Use `split_ifs with hyΛ`. Rewrite using `[Finset.sum_congr rfl fun x hx => F3 x (AddSubgroup.mem_inf.mp (hA1 x hx)).1 y hyΛ]`. Simplify using the standard rewrite rules. Take `⟨t, ht, hEt⟩` from `F5 y hyB hyΛ`. Use `sum_reps_eq_zero_of_shift_mul B (Λ ⊓ A) SA ⟨hA1, hA2, hA3⟩ (fun x => E x y) t ht (E t y) hEt ?_ ?_` and prove the remaining obligations.

Introduce `u hu v hv huv show E u y = E v y`. Establish `hu' : u = v + (u - v)` using `by abel`. Rewrite using `[hu', EaddL, F2 _ huv y hyB, mul_one]`. Introduce `u hu show E (u + t) y = E t y * E u y`. Rewrite using `[EaddL, mul_comm]`.

Establish `count2 : (SB.filter (fun y => y ∈ Λ)).card = 1`. Take `⟨y0, hy0, h0⟩` from `hB3 0 B.zero_mem`. Establish `hy0Λ : y0 ∈ Λ` using `by simpa using Λ.neg_mem h0`. Rewrite using `[Finset.card_eq_one]`. Use `⟨y0, Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hy0, hy0Λ⟩, ?_⟩⟩` and prove the remaining obligations.

Introduce `y hy`. Take `⟨hyS, hyΛ⟩` from `Finset.mem_filter.mp hy`. Conclude with `hB2 y hyS y0 hy0 (Λ.sub_mem hyΛ hy0Λ)`. Establish `S2 : ∑ y ∈ SB, ∑ x ∈ SA, E x y = SA.card`. Rewrite using `[Finset.sum_congr rfl inner2, ← Finset.sum_filter, Finset.sum_const, count2, one_smul]`.

Establish `hfin : (SA.card : ℂ) = SB.card`. Rewrite using `[← S1, ← S2, Finset.sum_comm]`. Conclude with `hfin` after adjusting the coercions.
-/
theorem card_SA_SB {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V)
    (hyp : SplitHyp H α A B Λ) (SA SB : Finset V) (hSA : IsReps B (Λ ⊓ A) SA) (hSB : IsReps Λ B SB) :
    SA.card = SB.card := by
  classical
  obtain ⟨hH, -, -, -, hB, hG⟩ := hyp
  obtain ⟨hΛ, -, -, -, h5⟩ := hG
  obtain ⟨hA1, hA2, hA3⟩ := hSA
  obtain ⟨hB1, hB2, hB3⟩ := hSB
  have hB' : dualLat H B = B := hB
  obtain ⟨E, hE⟩ : ∃ E : V → V → ℂ,
      ∀ x y, E x y = Complex.exp (2 * Real.pi * Complex.I * (altE H x y : ℂ)) := ⟨_, fun _ _ => rfl⟩
  have EaddL : ∀ x y z, E (x + y) z = E x z * E y z := by
    intro x y z
    rw [hE, hE, hE, skew_form_add_left, Complex.ofReal_add, mul_add, Complex.exp_add]
  have EaddR : ∀ x y z, E x (y + z) = E x y * E x z := by
    intro x y z
    rw [hE, hE, hE, skew_form_add_right, Complex.ofReal_add, mul_add, Complex.exp_add]
  have Eint : ∀ x y, (∃ m : ℤ, altE H x y = m) → E x y = 1 := fun x y h => by
    rw [hE]
    exact exp_two_pi_I_int_eq_one _ h
  have Eone : ∀ x y, E x y = 1 → ∃ m : ℤ, altE H x y = m := fun x y h => by
    rw [hE] at h
    exact exists_int_eq_of_exp_two_pi_I_eq_one _ h
  have F2 : ∀ x ∈ B, ∀ y ∈ B, E x y = 1 := by
    intro x hx y hy
    apply Eint
    have hx' : x ∈ dualLat H B := by rw [hB']; exact hx
    exact (show ∀ y ∈ B, ∃ m : ℤ, altE H x y = (m : ℝ) from hx') y hy
  have hskew : ∀ x y, altE H y x = -altE H x y := by
    intro x y
    have h : H y x = (starRingEnd ℂ) (H x y) := hH x y
    simp only [altE]
    rw [h, Complex.conj_im]
  have F3 : ∀ x ∈ Λ, ∀ y ∈ Λ, E x y = 1 := by
    intro x hx y hy
    have e1 := hΛ.2 x hx y hy
    have e2 := hΛ.2 y hy x hx
    rw [add_comm y x, hskew x y] at e2
    have hx0 : α x ≠ 0 := by
      rcases hΛ.1 x hx with h | h <;> rw [h] <;> norm_num
    have hy0 : α y ≠ 0 := by
      rcases hΛ.1 y hy with h | h <;> rw [h] <;> norm_num
    have key : Complex.exp (Real.pi * Complex.I * (altE H x y : ℂ)) =
        Complex.exp (Real.pi * Complex.I * ((-altE H x y : ℝ) : ℂ)) := by
      have h3 : α x * α y * Complex.exp (Real.pi * Complex.I * (altE H x y : ℂ)) =
          α x * α y * Complex.exp (Real.pi * Complex.I * ((-altE H x y : ℝ) : ℂ)) := by
        rw [← e1, e2]
        ring
      exact mul_left_cancel₀ (mul_ne_zero hx0 hy0) h3
    rw [hE]
    have h4 : (2 * Real.pi * Complex.I * (altE H x y : ℂ)) =
        Real.pi * Complex.I * (altE H x y : ℂ) + Real.pi * Complex.I * (altE H x y : ℂ) := by ring
    rw [h4, Complex.exp_add]
    nth_rewrite 2 [key]
    rw [← Complex.exp_add, show (Real.pi * Complex.I * (altE H x y : ℂ) +
      Real.pi * Complex.I * ((-altE H x y : ℝ) : ℂ)) = 0 by push_cast; ring, Complex.exp_zero]
  have F4 : ∀ x, x ∉ B → ∃ y ∈ B, E x y ≠ 1 := by
    intro x hx
    by_contra hcon
    push_neg at hcon
    apply hx
    rw [← hB']
    show ∀ y ∈ B, ∃ m : ℤ, altE H x y = (m : ℝ)
    intro y hy
    exact Eone x y (hcon y hy)
  have F5 : ∀ y ∈ B, y ∉ Λ → ∃ x ∈ Λ ⊓ A, E x y ≠ 1 := by
    intro y hy hyΛ
    by_contra hcon
    push_neg at hcon
    apply hyΛ
    apply h5 y hy
    intro x hxA hxΛ
    exact Eone x y (hcon x (AddSubgroup.mem_inf.mpr ⟨hxΛ, hxA⟩))
  have inner1 : ∀ x ∈ SA, ∑ y ∈ SB, E x y = if x ∈ B then (SB.card : ℂ) else 0 := by
    intro x hx
    have hxΛ : x ∈ Λ := (AddSubgroup.mem_inf.mp (hA1 x hx)).1
    split_ifs with hxB
    · rw [Finset.sum_congr rfl fun y hy => F2 x hxB y (hB1 y hy)]
      simp
    · obtain ⟨t, ht, hEt⟩ := F4 x hxB
      refine sum_reps_eq_zero_of_shift_mul Λ B SB ⟨hB1, hB2, hB3⟩ (fun y => E x y) t ht (E x t) hEt ?_ ?_
      · intro u hu v hv huv
        show E x u = E x v
        have hu' : u = v + (u - v) := by abel
        rw [hu', EaddR, F3 x hxΛ _ huv, mul_one]
      · intro u hu
        show E x (u + t) = E x t * E x u
        rw [EaddR, mul_comm]
  have count1 : (SA.filter (fun x => x ∈ B)).card = 1 := by
    obtain ⟨x0, hx0, h0⟩ := hA3 0 (Λ ⊓ A).zero_mem
    have hx0B : x0 ∈ B := by simpa using B.neg_mem h0
    rw [Finset.card_eq_one]
    refine ⟨x0, Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hx0, hx0B⟩, ?_⟩⟩
    intro x hx
    obtain ⟨hxS, hxB⟩ := Finset.mem_filter.mp hx
    exact hA2 x hxS x0 hx0 (B.sub_mem hxB hx0B)
  have S1 : ∑ x ∈ SA, ∑ y ∈ SB, E x y = SB.card := by
    rw [Finset.sum_congr rfl inner1, ← Finset.sum_filter, Finset.sum_const, count1, one_smul]
  have inner2 : ∀ y ∈ SB, ∑ x ∈ SA, E x y = if y ∈ Λ then (SA.card : ℂ) else 0 := by
    intro y hy
    have hyB : y ∈ B := hB1 y hy
    split_ifs with hyΛ
    · rw [Finset.sum_congr rfl fun x hx => F3 x (AddSubgroup.mem_inf.mp (hA1 x hx)).1 y hyΛ]
      simp
    · obtain ⟨t, ht, hEt⟩ := F5 y hyB hyΛ
      refine sum_reps_eq_zero_of_shift_mul B (Λ ⊓ A) SA ⟨hA1, hA2, hA3⟩ (fun x => E x y) t ht (E t y) hEt ?_ ?_
      · intro u hu v hv huv
        show E u y = E v y
        have hu' : u = v + (u - v) := by abel
        rw [hu', EaddL, F2 _ huv y hyB, mul_one]
      · intro u hu
        show E (u + t) y = E t y * E u y
        rw [EaddL, mul_comm]
  have count2 : (SB.filter (fun y => y ∈ Λ)).card = 1 := by
    obtain ⟨y0, hy0, h0⟩ := hB3 0 B.zero_mem
    have hy0Λ : y0 ∈ Λ := by simpa using Λ.neg_mem h0
    rw [Finset.card_eq_one]
    refine ⟨y0, Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hy0, hy0Λ⟩, ?_⟩⟩
    intro y hy
    obtain ⟨hyS, hyΛ⟩ := Finset.mem_filter.mp hy
    exact hB2 y hyS y0 hy0 (Λ.sub_mem hyΛ hy0Λ)
  have S2 : ∑ y ∈ SB, ∑ x ∈ SA, E x y = SA.card := by
    rw [Finset.sum_congr rfl inner2, ← Finset.sum_filter, Finset.sum_const, count2, one_smul]
  have hfin : (SA.card : ℂ) = SB.card := by
    rw [← S1, ← S2, Finset.sum_comm]
  exact_mod_cast hfin

end KerA

/- English proof (translation)
Introduce `X A a b S N N' c hN hN' hLa hc`. Take `⟨-, -, -, -, hall⟩` from `Formalism.L2.Ker.heisHyp_of A a b S hLa`. Take `⟨-, hcc⟩` from `hall N N' hN hN'`. Take `⟨hsplit, hi1, hi2, -⟩` from `hcc c hc`. Conclude with `KerA.card_SA_SB _ _ _ _ _ hsplit _ _ (Formalism.L2.Ker.repsOf_spec _ _ hi1) (Formalism.L2.Ker.repsOf_spec _ _ hi2)`.
-/
theorem card_two_sided_quotient : CardSAB := by
  intro X A a b S N N' c hN hN' hLa hc
  obtain ⟨-, -, -, -, hall⟩ := Formalism.L2.Ker.heisHyp_of A a b S hLa
  obtain ⟨-, hcc⟩ := hall N N' hN hN'
  obtain ⟨hsplit, hi1, hi2, -⟩ := hcc c hc
  exact KerA.card_SA_SB _ _ _ _ _ hsplit _ _ (Formalism.L2.Ker.repsOf_spec _ _ hi1) (Formalism.L2.Ker.repsOf_spec _ _ hi2)

namespace KerB

open Formalism.L2.Th1.H (matH Sesq altE IsHerm IsPosDef IsLat IsReps IsSelfDual opU sumU alphaQ qOf taylorMv Th)
open Formalism.L2.Ker (VCx DVar HV alV desc derivAt0 jetC)

variable {T : Type} [Fintype T] [DecidableEq T] {a b : ℕ}

/- English proof (translation)
Unfold `desc`. Use `split_ifs with h`. Conclude with `Or.inl h.choose_spec`. Conclude with `Or.inr (map_zero σ)`.
-/
theorem desc_cases {K : Type} [Field K] (σ : K →+* ℂ) (z : ℂ) : σ (desc σ z) = z ∨ σ (desc σ z) = 0 := by
  unfold desc
  split_ifs with h
  · exact Or.inl h.choose_spec
  · exact Or.inr (map_zero σ)

/- English proof (translation)
Simplify using `only [matH, hSc, LinearMap.mk₂'ₛₗ_apply, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem matH_hSc (sc : ℝ) (z w : DVar T a b → ℂ) :
    matH (hSc T a b sc) z w = (sc : ℂ) * ∑ i, z i * conj (w i) := by
  simp only [matH, hSc, LinearMap.mk₂'ₛₗ_apply, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Rewrite using `[matH_hSc]`. Express the relevant statement in the definitionally equal form `(sc : ℂ) * ∑ τ, ∑ i, ∑ j, z (τ, i, j) * (starRingEnd ℂ) (w (τ, i, j)) = _`. Simplify using `only [Fintype.sum_prod_type]`.
-/
theorem HV_flat (sc : ℝ) (z w : DVar T a b → ℂ) :
    HV sc (flat T a b z) (flat T a b w) = matH (hSc T a b sc) z w := by
  rw [matH_hSc]
  change (sc : ℂ) * ∑ τ, ∑ i, ∑ j, z (τ, i, j) * (starRingEnd ℂ) (w (τ, i, j)) = _
  simp only [Fintype.sum_prod_type]

/- English proof (translation)
Simplify using `only [opU]`. Rewrite using `[← HV_flat, ← HV_flat, map_add, LinearEquiv.apply_symm_apply]`.
-/
theorem opU_flat (sc : ℝ) (u : VCx T a b) (F : VCx T a b → ℂ) (w : DVar T a b → ℂ) :
    opU (HV sc) u F (flat T a b w) = opU (matH (hSc T a b sc)) ((flat T a b).symm u) (fun v => F (flat T a b v)) w := by
  simp only [opU]
  rw [← HV_flat, ← HV_flat, map_add, LinearEquiv.apply_symm_apply]

/- English proof (translation)
Simplify using `only [alV, alphaQ, qOf, HV_flat]`.
-/
theorem alV_flat (d : ℕ) (sc : ℝ) (z : DVar T a b → ℂ) :
    alV d sc (flat T a b z) = alphaQ (Real.sqrt d / 2) (matH (hSc T a b sc)) z := by
  simp only [alV, alphaQ, qOf, HV_flat]

/- English proof (translation)
Introduce `x y`. Rewrite using `[matH_hSc, matH_hSc, map_mul, map_sum, Complex.conj_ofReal]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, Complex.conj_conj, mul_comm]`.
-/
theorem herm_hSc (sc : ℝ) : IsHerm (matH (hSc T a b sc)) := by
  intro x y
  rw [matH_hSc, matH_hSc, map_mul, map_sum, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

/- English proof (translation)
Introduce `x hx`. Rewrite using `[matH_hSc]`. Establish `hsum : (∑ i, x i * conj (x i)) = ((∑ i, Complex.normSq (x i) : ℝ) : ℂ)`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Complex.mul_conj]`. Rewrite using `[hsum, ← Complex.ofReal_mul, Complex.ofReal_re]`. Apply `mul_pos hsc` to reduce the goal to its premises. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, x i ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hx (funext h)`. Conclude with `Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩`.
-/
theorem posDef_hSc (sc : ℝ) (hsc : 0 < sc) : IsPosDef (matH (hSc T a b sc)) := by
  intro x hx
  rw [matH_hSc]
  have hsum : (∑ i, x i * conj (x i)) = ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.mul_conj]
  rw [hsum, ← Complex.ofReal_mul, Complex.ofReal_re]
  apply mul_pos hsc
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [cLat, Formalism.L2.Th1.H.imgLat, AddSubgroup.mem_map, AddSubgroup.mem_comap]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hyx⟩`. Use `⟨g y, by simpa using hy, ?_⟩` and prove the remaining obligations.

Establish `hyx' : c • y = x` using `by simpa using hyx`. Simplify using `[← hyx', map_smul]`. Introduce and unpack `⟨z, hz, hzx⟩`. Establish `hzx' : c • z = g x` using `by simpa using hzx`. Use `⟨g.symm z, by simpa using hz, ?_⟩` and prove the remaining obligations.

Establish `hcz : c • g.symm z = x`. Combine the equalities or inequalities in the displayed calculation. Simplify using `using hcz`.
-/
theorem cLat_comap {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (g : V ≃ₗ[ℂ] W) (c : ℂ)
    (L : AddSubgroup W) :
    cLat c (L.comap g.toLinearMap.toAddMonoidHom) = (cLat c L).comap g.toLinearMap.toAddMonoidHom := by
  ext x
  simp only [cLat, Formalism.L2.Th1.H.imgLat, AddSubgroup.mem_map, AddSubgroup.mem_comap]
  constructor
  · rintro ⟨y, hy, hyx⟩
    refine ⟨g y, by simpa using hy, ?_⟩
    have hyx' : c • y = x := by simpa using hyx
    simp [← hyx', map_smul]
  · rintro ⟨z, hz, hzx⟩
    have hzx' : c • z = g x := by simpa using hzx
    refine ⟨g.symm z, by simpa using hz, ?_⟩
    have hcz : c • g.symm z = x := by
      calc c • g.symm z = g.symm (c • z) := (LinearEquiv.map_smul g.symm c z).symm
        _ = g.symm (g x) := by rw [hzx']
        _ = x := g.symm_apply_apply x
    simpa using hcz

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨s, hs, rfl⟩` from `Finset.mem_image.mp hx`. Use `show g (g.symm s) ∈ L₂`.

Rewrite using `[LinearEquiv.apply_symm_apply]`. Conclude with `h1 s hs`. Introduce `x hx y hy hxy`. Take `⟨s, hs, rfl⟩` from `Finset.mem_image.mp hx`. Take `⟨t, ht, rfl⟩` from `Finset.mem_image.mp hy`.

Establish `hg : g (g.symm s - g.symm t) ∈ L₁` using `hxy`. Rewrite `hg` using `[map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Rewrite using `[h2 s hs t ht hg]`. Introduce `y hy`. Take `⟨s, hs, hys⟩` from `h3 (g y) hy`.

Use `⟨g.symm s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show g (y - g.symm s) ∈ L₁`. Rewrite using `[map_sub, LinearEquiv.apply_symm_apply]`. Conclude with `hys`.
-/
theorem isReps_comap {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [DecidableEq V]
    (g : V ≃ₗ[ℂ] W) (L₁ L₂ : AddSubgroup W) (S : Finset W) (h : IsReps L₁ L₂ S) :
    IsReps (L₁.comap g.toLinearMap.toAddMonoidHom) (L₂.comap g.toLinearMap.toAddMonoidHom) (S.image g.symm) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    show g (g.symm s) ∈ L₂
    rw [LinearEquiv.apply_symm_apply]
    exact h1 s hs
  · intro x hx y hy hxy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
    have hg : g (g.symm s - g.symm t) ∈ L₁ := hxy
    rw [map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hg
    rw [h2 s hs t ht hg]
  · intro y hy
    obtain ⟨s, hs, hys⟩ := h3 (g y) hy
    refine ⟨g.symm s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
    show g (y - g.symm s) ∈ L₁
    rw [map_sub, LinearEquiv.apply_symm_apply]
    exact hys

/- English proof (translation)
Establish `hH : (H ((k : ℂ) • x) ((k : ℂ) • x)).re = (k : ℝ) ^ 2 * (H x x).re`. Simplify using `[Complex.mul_re]`. Expand and normalize the polynomial expressions, which then agree. Unfold `alphaQ qOf`. Rewrite using `[← Complex.exp_nat_mul, hH]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem alphaQ_natSmul {V : Type*} [AddCommGroup V] [Module ℂ V] (c : ℝ) (H : Sesq V) (x : V) (k : ℕ) :
    alphaQ c H ((k : ℂ) • x) = alphaQ c H x ^ (k ^ 2) := by
  have hH : (H ((k : ℂ) • x) ((k : ℂ) • x)).re = (k : ℝ) ^ 2 * (H x x).re := by
    simp [Complex.mul_re]
    ring
  unfold alphaQ qOf
  rw [← Complex.exp_nat_mul, hH]
  congr 1
  push_cast
  ring

/- English proof (translation)
Simplify using `only [Finsupp.prod, Finset.prod_pow_eq_pow_sum]`. Both sides reduce to the same expression.
-/
theorem prod_const_pow {K : Type*} [CommMonoid K] {ι : Type*} (m : ι →₀ ℕ) (c : K) :
    (m.prod fun _ e => c ^ e) = c ^ m.degree := by
  simp only [Finsupp.prod, Finset.prod_pow_eq_pow_sum]
  rfl

end KerB

open Formalism.L2.Th1.H (matH altE IsReps opU sumU alphaQ taylorMv relIdx)
open Formalism.L2.Ker (VCx DVar LamC BC AC HV alV embH volC repsOf desc derivAt0 jetC)
open Formalism.L2.Th1.GD (frameM)
open Formalism.DworkPowerSeriesWeights (JetsIntegral mfact)

/- English proof (translation)
Introduce `X A a b S N N' a₀ b₀ c₀ ha hd lam hlam p _ ι hp2 hpd hK hN hN' hLa π pE hπ hππ hS c' x hc' hpc' hx m`. Establish `hp : p.Prime` using `Fact.out`. Take `⟨hOK, hsc, hLat, hSD, hSt, hθ, hInt, hLoc, ⟨J, hJ, v, M, hv, hM, hfr⟩, hchi⟩` from `hK`. It suffices to establish `hmain : ‖ι (jetC A.cD (A.thInd S N N' (p * c') x) m)‖ * ‖ι (conj π)‖ ^ m.degree * ‖(p : ℂ_[p])‖ ^ (Fintype.card X.Tau * b * a) ≤ 1 by`. Establish `hjk : A.jetK S N N' (p * c') x m = desc A.σ₀ ((A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' (p * c') x) m)` using `rfl`.

Rewrite using `[hjk]`. Break down `KerB.desc_cases A.σ₀ ((A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' (p * c') x) m) with h | h` into its components or cases. Rewrite using `[h, map_mul, norm_mul, map_inv₀, norm_inv, hchi, inv_one, one_mul]`. Conclude with `hmain`. Rewrite using `[h, map_zero, norm_zero, zero_mul, zero_mul]`.

Conclude with `zero_le_one`. Distinguish the cases in `hvol : 0 < volC A.AA S N N'`. Use `swap`. Establish `h0 : A.thInd S N N' (p * c') x = fun _ => 0`. Use function extensionality and compare the values at `z`.

Establish `: Real.sqrt (volC A.AA S N N') = 0` using `Real.sqrt_eq_zero'.2 (not_lt.1 hvol)`. Use `show ((Real.sqrt (volC A.AA S N N') : ℝ) : ℂ)⁻¹ * _ = 0`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Establish `hj0 : jetC A.cD (A.thInd S N N' (p * c') x) m = 0`.

Rewrite using `[h0]`. Unfold `jetC derivAt0`. Simplify using the standard rewrite rules. Rewrite using `[hj0]`. Simplify using the standard rewrite rules.

Establish `hp0 : (p : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hp.ne_zero`. Establish `hπ0 : π ≠ 0` using `by rintro rfl; rw [zero_mul] at hππ; exact hp0 hππ.symm`. Establish `hπ'0 : conj π ≠ 0` using `by rwa [ne_eq, map_eq_zero]`. Establish `hcq : IsQInt A.d (conj π)` using `XiTorsion.qint_conj A.d π hπ`. Establish `hΛq : ∀ β : ℂ, IsQInt A.d β → ∀ y ∈ lamF A N N', β • y ∈ lamF A N N'` using `TensorIntegralTorsion.qint_smul_mem (lamF A N N') b₀ A.d (TensorIntegralTorsion.odd_b hOK) hSt`.

Take `⟨-, -, -, -, -, hall⟩` from `id hLa`. Take `⟨hfix, hSDV, hSCV⟩` from `hall N N' hN hN'`. Take `⟨-, -, -, -, hallH⟩` from `Formalism.L2.Ker.heisHyp_of A a b S hLa`. Take `⟨-, hcc⟩` from `hallH N N' hN hN'`. Establish `hcpos : 0 < p * c'` using `Nat.mul_pos hp.pos hc'`.

Take `⟨-, hi1, hi2, -⟩` from `hcc (p * c') hcpos`. Use `set Λ := LamC (X.embC A.σ₀) A.δ A.AA N N' with hΛdef`. Use `set B := BC (X.embC A.σ₀) A.δ A.AA S N N' (p * c') with hBdef`. Establish `hrel1 : relIdx Λ (killIn (c' : ℂ) B Λ) ≠ 0` using `fun h0 => hi2 (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h0)`. Establish `hrel2 : relIdx Λ (killIn (p : ℂ) B Λ) ≠ 0` using `fun h0 => hi2 (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h0)`.

Use `set S₁ := repsOf Λ (killIn (c' : ℂ) B Λ) with hS₁def`. Use `set S₂ := repsOf Λ (killIn (p : ℂ) B Λ) with hS₂def`. Establish `hS₁ : IsReps Λ (killIn (c' : ℂ) B Λ) S₁` using `Formalism.L2.Ker.repsOf_spec _ _ hrel1`. Establish `hS₂ : IsReps Λ (killIn (p : ℂ) B Λ) S₂` using `Formalism.L2.Ker.repsOf_spec _ _ hrel2`. Establish `hcop : Nat.Coprime c' p` using `Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hpc')`.

Establish `hkill : ∀ y ∈ B, (((c' * p : ℕ) : ℂ)) • y ∈ Λ`. Introduce `y hy`. Rewrite using `[mul_comm c' p]`. Conclude with `f3 X A a b S N N' (p * c') hN hN' hLa hcpos y hy`. Establish `hF1` using `f1 X A a b S N N' (p * c') x hN hN' hLa hcpos hvol c' p hcop hkill S₁ S₂ hS₁ hS₂`.

Use `set SA := repsOf B (Λ ⊓ AC (X.embC A.σ₀) A.δ A.AA S N N' (p * c')) with hSAdef`. Establish `hSAB` using `f6 X A a b S N N' (p * c') hN hN' hLa hcpos`. Establish `hSBspec : IsReps Λ B (repsOf Λ B)` using `Formalism.L2.Ker.repsOf_spec Λ B hi2`. Take `⟨hsplitc, hprime⟩` from `f2 (VCx X.Tau a b) B Λ c' p hcop hkill _ S₁ S₂ hSBspec hS₁ hS₂`. Establish `hS1p : ¬ p ∣ S₁.card` using `fun h => hpc' (hprime p hp h)`.

Establish `hS₂P` using `f5 X A a b S N N' p hp hp2 hpd hN hN' hLa π pE hπ hππ hS c' hc' hpc' S₂ hS₂`. Use `set Sa := S₂.image (flat X.Tau a b).symm with hSadef`. Establish `hSa : IsReps (cLat (conj π) (lamF A N N')) (cLat (conj π / π) (lamF A N N')) Sa`. Establish `h` using `KerB.isReps_comap (flat X.Tau a b) _ _ _ hS₂P`. Rewrite `h` using `[← KerB.cLat_comap, ← KerB.cLat_comap]`.

Conclude with `h`. Establish `hcardSa` using `f7 (DVar X.Tau a b) (lamF A N N') hLat p hp π hππ (hΛq π hπ) (hΛq _ hcq) Sa hSa`. Establish `hcardS2 : S₂.card = p ^ Fintype.card (DVar X.Tau a b)`. Rewrite using `[← hcardSa, hSadef, Finset.card_image_of_injective _ (flat X.Tau a b).symm.injective]`. Establish `hSAcard : (SA.card : ℂ) = (S₁.card : ℂ) * (p : ℂ) ^ Fintype.card (DVar X.Tau a b)`.

Rewrite using `[hSAB, hsplitc, hcardS2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hrelSb : relIdx (cLat (conj π) (lamF A N N')) (lamF A N N') ≠ 0`. Establish `h1` using `SC.relIdx_cLat (lamF A N N') hLat (conj π) hπ'0 (hΛq _ hcq)`.

Introduce `h0`. Rewrite `h1` using `[h0, Nat.cast_zero]`. Establish `: Complex.normSq (conj π) ≠ 0` using `by rw [Complex.normSq_conj]; exact (Complex.normSq_pos.2 hπ0).ne'`. Conclude with `(pow_ne_zero _ this) h1.symm`. Use `set Sb := repsOf (cLat (conj π) (lamF A N N')) (lamF A N N') with hSbdef`.

Establish `hSb : IsReps (cLat (conj π) (lamF A N N')) (lamF A N N') Sb` using `Formalism.L2.Ker.repsOf_spec _ _ hrelSb`. Use `set Ψ : (DVar X.Tau a b → ℂ) → ℂ := fun y => if y ∈ cLat (conj π) (lamF A N N') then ((S₁.card : ℂ))⁻¹ else 0 with hΨdef`. Establish `hΨ : ∀ y ∈ Sb, ‖ι (Ψ y)‖ ≤ 1`. Introduce `y _`. Simplify using `only [hΨdef]`.

Use `split_ifs`. Rewrite using `[map_inv₀, map_natCast, norm_inv, LocalJetRescaling.norm_natCast p hS1p, inv_one]`. Simplify using the standard rewrite rules. Use `set s := embH (X.embC A.σ₀) A.δ (A.liftW S N N' (p * c') x) with hsdef`. Establish `hsΛ : (c' : ℂ) • s ∈ Λ` using `f4 X A a b S N N' (p * c') c' x hN hN' hLa hcpos hc' (Dvd.intro_left p rfl) hx`.

Use `set r : ↥S₁ → ℂ := fun k => alV A.d A.sc s * alV A.d A.sc k.1 * Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE (HV A.sc) (-s) k.1 : ℂ)) with hrdef`. Use `set t : ↥S₁ → DVar X.Tau a b → ℂ := fun k => (flat X.Tau a b).symm (-s + k.1) with htdef`. Establish `hyΛ : ∀ k : ↥S₁, (c' : ℂ) • k.1 ∈ Λ` using `fun k => (KerA.mem_killIn.1 (hS₁.1 k.1 k.2)).2`. Establish `hα1 : ∀ y : VCx X.Tau a b, (c' : ℂ) • y ∈ Λ → ‖ι (alV A.d A.sc y)‖ = 1`. Introduce `y hy`.

Apply `XiTorsion.norm_root ι _ (2 * c' ^ 2) (by positivity)` to reduce the goal to its premises. Establish `h1` using `hSCV.1 _ hy`. Establish `h2 : alV A.d A.sc ((c' : ℂ) • y) = alV A.d A.sc y ^ (c' ^ 2)` using `KerB.alphaQ_natSmul _ _ y c'`. Rewrite using `[pow_mul', ← h2]`. Apply the tactic sequence `rcases h1 with h1 | h1 <;> rw [h1] <;> norm_num`.

Establish `hr : ∀ k, ‖ι (r k)‖ ≤ 1`. Introduce `k`. Simplify using `only [hrdef, map_mul, norm_mul, hα1 s hsΛ, hα1 k.1 (hyΛ k), one_mul]`. Establish `hs' : (c' : ℂ) • (-s) ∈ Λ` using `by rw [smul_neg]; exact Λ.neg_mem hsΛ`. Take `⟨q, hq⟩` from `XiTorsion.altE_int hSDV hs' (hyΛ k)`.

Rewrite `hq` using `[XiTorsion.altE_smul_left, XiTorsion.altE_smul_right]`. Rewrite using `[XiConnection.norm_phase ι _ (c' * c') (Nat.mul_pos hc' hc') q (by push_cast; linarith)]`. Establish `ht : ∀ k, (c' : ℂ) • t k ∈ lamF A N N'`. Introduce `k`. Use `show flat X.Tau a b ((c' : ℂ) • (flat X.Tau a b).symm (-s + k.1)) ∈ Λ`.

Rewrite using `[map_smul, LinearEquiv.apply_symm_apply, smul_add, smul_neg]`. Conclude with `Λ.add_mem (Λ.neg_mem hsΛ) (hyΛ k)`. Use `set Afr : J → DVar X.Tau a b → ℂ_[p] := fun j k => ι (conj π) * M j k with hAfrdef`. Establish `hAfr : ∀ j k, ‖Afr j k‖ ≤ ‖ι (conj π)‖`. Introduce `j k`.

Simplify using `only [hAfrdef, norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (hM j k)`. Establish `hJI` using `hC a₀ b₀ c₀ A.d ha hd lam hlam hOK (DVar X.Tau a b) (hSc X.Tau a b A.sc) (lamF A N N') (KerB.herm_hSc A.sc) (KerB.posDef_hSc A.sc hsc) hLat hSD hSt (thF A N N') hθ p hp2 hpd ι hInt hLoc π hπ hππ Sa Sb hSa hSb Ψ hΨ (↥S₁) r t c' hr hc' hpc' ht J v hv (DVar X.Tau a b) Afr hAfr`. Establish `hxh : ∀ a' ∈ Sa, xiHat (matH (hSc X.Tau a b A.sc)) (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sb a' = ((SA.card : ℂ))⁻¹`. Introduce `a' ha'`.

Take `⟨μ, hμ, hμa⟩` from `XiTorsion.mem_cLat (hSa.1 a' ha')`. Unfold `xiHat`. Take `⟨b0, _, hb0, hsum⟩` from `Formalism.L2.Th1.H.Inv.sum_reps hSb (fun y => Ψ y * Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE (matH (hSc X.Tau a b A.sc)) y a' : ℂ))) (fun y _ hy => by simp [hΨdef, hy])`. Rewrite using `[hsum]`. Take `⟨l, hl, hlb⟩` from `XiTorsion.mem_cLat hb0`.

Establish `hint : ∃ q : ℤ, altE (matH (hSc X.Tau a b A.sc)) b0 a' = q`. Establish `e : altE (matH (hSc X.Tau a b A.sc)) b0 a' = altE (matH (hSc X.Tau a b A.sc)) (π • l) μ`. Rewrite using `[hlb, hμa]`. Unfold `altE`. Use `congr 1`.

Rewrite using `[LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, LinearMap.map_smul, LinearMap.smul_apply]`. Simplify using `only [smul_eq_mul, map_div₀, Complex.conj_conj]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `XiTorsion.altE_int hSD (hΛq π hπ l hl) hμ`.

Take `⟨q, hq⟩` from `hint`. Simplify using `only [hΨdef, if_pos hb0, hq]`. Establish `hex : Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ((q : ℝ) : ℂ)) = 1`. Rewrite using `[Complex.exp_eq_one_iff]; exact ⟨-q, by push_cast; ring⟩`. Rewrite using `[hex, mul_one, hSAcard]`.

Use `push_cast`. Rewrite using `[mul_inv, mul_comm]`. Establish `hxiG : ∀ v, xiG (matH (hSc X.Tau a b A.sc)) (alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.sc))) (thF A N N') (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sa Sb v = ((SA.card : ℂ))⁻¹ * sumU (HV A.sc) (alV A.d A.sc) S₂ (A.e a b N N') (flat X.Tau a b v)`. Introduce `v`. Unfold `xiG`.

Establish `e1 : ∀ a' ∈ Sa, xiHat (matH (hSc X.Tau a b A.sc)) (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sb a' * alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.sc)) a' * opU (matH (hSc X.Tau a b A.sc)) a' (thF A N N') v = ((SA.card : ℂ))⁻¹ * (alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.s …` using `fun a' ha' => by rw [hxh a' ha']; ring`. Rewrite using `[Finset.sum_congr rfl e1, ← Finset.mul_sum]`. Use `congr 1`. Rewrite using `[hSadef, Finset.sum_image (fun y _ y' _ h => (flat X.Tau a b).symm.injective h)]`. Use `show _ = ∑ y ∈ S₂, alV A.d A.sc y * opU (HV A.sc) y (A.e a b N N') (flat X.Tau a b v)`.

Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[KerB.opU_flat, ← KerB.alV_flat, LinearEquiv.apply_symm_apply]`. Both sides reduce to the same expression. Establish `hfun : (fun z => ∑ k : ↥S₁, r k * opU (matH (hSc X.Tau a b A.sc)) (t k) (xiG (matH (hSc X.Tau a b A.sc)) (alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.sc))) (thF A N N') (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sa Sb) z) = fun z => A.thInd S N N' (p * c') x (flat X.Tau a b z)`. Use function extensionality and compare the values at `z`.

Rewrite using `[hF1 (flat X.Tau a b z)]`. Establish `hx' : xiG (matH (hSc X.Tau a b A.sc)) (alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.sc))) (thF A N N') (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sa Sb = fun v => ((SA.card : ℂ))⁻¹ * sumU (HV A.sc) (alV A.d A.sc) S₂ (A.e a b N N') (flat X.Tau a b v)` using `funext hxiG`. Rewrite using `[hx', ← Finset.sum_coe_sort S₁, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [hrdef, htdef]`.

Rewrite using `[XiTorsion.opU_cmul, ← KerB.opU_flat, Formalism.L2.Th1.H.opUMul _ (HV A.sc) (Formalism.L2.Ker.herm_HV A.sc) (-s) k.1]`. Expand and normalize the polynomial expressions, which then agree. Establish `hxiAn : AnalyticOnNhd ℂ (xiG (matH (hSc X.Tau a b A.sc)) (alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.sc))) (thF A N N') (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sa Sb) Set.univ`. Establish `e : xiG (matH (hSc X.Tau a b A.sc)) (alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.sc))) (thF A N N') (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sa Sb = fun v => ∑ a' ∈ Sa, (xiHat (matH (hSc X.Tau a b A.sc)) (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sb a' * alphaQ (Real.sqrt A.d / 2) …`. Use function extensionality and compare the values at `v`.

Both sides reduce to the same expression. Rewrite using `[e]`. Establish `h` using `Finset.analyticOnNhd_sum (𝕜 := ℂ) (s := Set.univ) (f := fun a' v => (xiHat (matH (hSc X.Tau a b A.sc)) (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sb a' * alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.sc)) a') * opU (matH (hSc X.Tau a b A.sc)) a' (thF A N N') v) Sa (fun a' _ => ana …`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `v`.

Simplify using `[Finset.sum_apply]`. Establish `hΦ : AnalyticOnNhd ℂ (fun z => ∑ k : ↥S₁, r k * opU (matH (hSc X.Tau a b A.sc)) (t k) (xiG (matH (hSc X.Tau a b A.sc)) (alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.sc))) (thF A N N') (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sa Sb) z) Set.univ`. Establish `h` using `Finset.analyticOnNhd_sum (𝕜 := ℂ) (s := Set.univ) (f := fun k z => r k * opU (matH (hSc X.Tau a b A.sc)) (t k) (xiG (matH (hSc X.Tau a b A.sc)) (alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.sc))) (thF A N N') (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sa Sb) z) Finset.univ (fun k …`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z`.

Simplify using `[Finset.sum_apply]`. Establish `hAn : AnalyticOnNhd ℂ (A.thInd S N N' (p * c') x) Set.univ`. Establish `e : A.thInd S N N' (p * c') x = fun u => (fun z => ∑ k : ↥S₁, r k * opU (matH (hSc X.Tau a b A.sc)) (t k) (xiG (matH (hSc X.Tau a b A.sc)) (alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.sc))) (thF A N N') (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sa Sb) z) ((flat X.Tau a b).symm …`. Use function extensionality and compare the values at `u`. Rewrite using `[hfun]`.

Simplify using `only [LinearEquiv.apply_symm_apply]`. Rewrite using `[e]`. Introduce `u _`. Establish `hlin : AnalyticAt ℂ (fun u => (flat X.Tau a b).symm u) u` using `(LinearMap.toContinuousLinearMap ((flat X.Tau a b).symm : VCx X.Tau a b →ₗ[ℂ] (DVar X.Tau a b → ℂ))).analyticAt u`. Conclude with `(hΦ _ (Set.mem_univ _)).comp hlin`.

Establish `hT` using `f8 X.Tau a b (A.thInd S N N' (p * c') x) hAn m`. Establish `hco` using `hJI m`. Unfold `serLin at hco`. Rewrite `hco` using `[hfun]`. Establish `hfrd : frameM (ι : ℂ →+* ℂ_[p]) v Afr = fun i k => if i = k then ι (conj π) * ι (A.cD k.1) else 0`.

Use function extensionality and compare the values at `i k`. Establish `e : frameM (ι : ℂ →+* ℂ_[p]) v Afr i k = ι (conj π) * frameM (ι : ℂ →+* ℂ_[p]) v M i k`. Unfold `frameM`. Simplify using `only [hAfrdef]`. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring`.

Establish `h2 : frameM (ι : ℂ →+* ℂ_[p]) v M i k = if i = k then ι (A.cD k.1) else 0` using `hfr i k`. Rewrite using `[e, h2]`. Apply the tactic sequence `split_ifs <;> first | rfl | simp`. Rewrite `hco` using `[hfrd, MvPowerSeries.coeff_C_mul]`. Establish `e9` using `f9 ℂ_[p] (DVar X.Tau a b) (fun k => ι (conj π) * ι (A.cD k.1)) (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv fun z => A.thInd S N N' (p * c') x (flat X.Tau a b z))) m`.

Rewrite `hco` using `[e9, MvPowerSeries.coeff_map]`. Establish `hjet : ι (jetC A.cD (A.thInd S N N' (p * c') x) m) = (m.prod fun k e => ι (A.cD k.1) ^ e) * ((mfact m : ℂ_[p]) * (ι : ℂ →+* ℂ_[p]) (MvPowerSeries.coeff m (taylorMv fun z => A.thInd S N N' (p * c') x (flat X.Tau a b z))))`. Unfold `jetC`. Rewrite using `[← hT, map_mul, map_mul, map_natCast, map_finsuppProd]`. Simplify using `only [map_pow]`.

Both sides reduce to the same expression. Establish `hprod : (m.prod fun k e => (ι (conj π) * ι (A.cD k.1)) ^ e) = ι (conj π) ^ m.degree * (m.prod fun k e => ι (A.cD k.1) ^ e)`. Repeatedly rewrite using `[mul_pow]`. Rewrite using `[Finsupp.prod_mul, KerB.prod_const_pow]`. Establish `hcard : Fintype.card (DVar X.Tau a b) = Fintype.card X.Tau * b * a`.

Simplify using `[Fintype.card_prod, Fintype.card_fin, mul_assoc]`. Establish `hfin : (mfact m : ℂ_[p]) * ((p : ℂ_[p]) ^ Fintype.card (DVar X.Tau a b) * ((m.prod fun k e => (ι (conj π) * ι (A.cD k.1)) ^ e) * (ι : ℂ →+* ℂ_[p]) (MvPowerSeries.coeff m (taylorMv fun z => A.thInd S N N' (p * c') x (flat X.Tau a b z))))) = ι (jetC A.cD (A.thInd S N N' (p * c') x) …`. Rewrite using `[hjet, hprod, hcard]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hco` using `[hfin, norm_mul, norm_mul, norm_pow, norm_pow]`.

Conclude with `hco`.
-/
theorem jetAtSplit_of (hC : SelfDualLatticeThetaPadicIntegrality) (f1 : KerIndForm) (f2 : RepsSplit) (f3 : HalfKill) (f4 : LiftKill) (f5 : HalfP)
    (f6 : CardSAB) (f7 : IdxPi) (f8 : TaylorJet) (f9 : LinSubDiag) : JetAtSplit := by
  intro X A a b S N N' a₀ b₀ c₀ ha hd lam hlam p _ ι hp2 hpd hK hN hN' hLa π pE hπ hππ hS c' x hc' hpc' hx m
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨hOK, hsc, hLat, hSD, hSt, hθ, hInt, hLoc, ⟨J, hJ, v, M, hv, hM, hfr⟩, hchi⟩ := hK

  suffices hmain : ‖ι (jetC A.cD (A.thInd S N N' (p * c') x) m)‖ * ‖ι (conj π)‖ ^ m.degree *
      ‖(p : ℂ_[p])‖ ^ (Fintype.card X.Tau * b * a) ≤ 1 by
    have hjk : A.jetK S N N' (p * c') x m =
        desc A.σ₀ ((A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' (p * c') x) m) := rfl
    rw [hjk]
    rcases KerB.desc_cases A.σ₀ ((A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' (p * c') x) m) with h | h
    · rw [h, map_mul, norm_mul, map_inv₀, norm_inv, hchi, inv_one, one_mul]; exact hmain
    · rw [h, map_zero, norm_zero, zero_mul, zero_mul]; exact zero_le_one
  by_cases hvol : 0 < volC A.AA S N N'
  swap
  · have h0 : A.thInd S N N' (p * c') x = fun _ => 0 := by
      funext z
      have : Real.sqrt (volC A.AA S N N') = 0 := Real.sqrt_eq_zero'.2 (not_lt.1 hvol)
      show ((Real.sqrt (volC A.AA S N N') : ℝ) : ℂ)⁻¹ * _ = 0
      rw [this]; simp
    have hj0 : jetC A.cD (A.thInd S N N' (p * c') x) m = 0 := by
      rw [h0]; unfold jetC derivAt0; simp
    rw [hj0]; simp

  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hπ0 : π ≠ 0 := by rintro rfl; rw [zero_mul] at hππ; exact hp0 hππ.symm
  have hπ'0 : conj π ≠ 0 := by rwa [ne_eq, map_eq_zero]
  have hcq : IsQInt A.d (conj π) := XiTorsion.qint_conj A.d π hπ
  have hΛq : ∀ β : ℂ, IsQInt A.d β → ∀ y ∈ lamF A N N', β • y ∈ lamF A N N' :=
    TensorIntegralTorsion.qint_smul_mem (lamF A N N') b₀ A.d (TensorIntegralTorsion.odd_b hOK) hSt
  obtain ⟨-, -, -, -, -, hall⟩ := id hLa
  obtain ⟨hfix, hSDV, hSCV⟩ := hall N N' hN hN'
  obtain ⟨-, -, -, -, hallH⟩ := Formalism.L2.Ker.heisHyp_of A a b S hLa
  obtain ⟨-, hcc⟩ := hallH N N' hN hN'
  have hcpos : 0 < p * c' := Nat.mul_pos hp.pos hc'
  obtain ⟨-, hi1, hi2, -⟩ := hcc (p * c') hcpos
  set Λ := LamC (X.embC A.σ₀) A.δ A.AA N N' with hΛdef
  set B := BC (X.embC A.σ₀) A.δ A.AA S N N' (p * c') with hBdef
  have hrel1 : relIdx Λ (killIn (c' : ℂ) B Λ) ≠ 0 := fun h0 =>
    hi2 (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h0)
  have hrel2 : relIdx Λ (killIn (p : ℂ) B Λ) ≠ 0 := fun h0 =>
    hi2 (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h0)
  set S₁ := repsOf Λ (killIn (c' : ℂ) B Λ) with hS₁def
  set S₂ := repsOf Λ (killIn (p : ℂ) B Λ) with hS₂def
  have hS₁ : IsReps Λ (killIn (c' : ℂ) B Λ) S₁ := Formalism.L2.Ker.repsOf_spec _ _ hrel1
  have hS₂ : IsReps Λ (killIn (p : ℂ) B Λ) S₂ := Formalism.L2.Ker.repsOf_spec _ _ hrel2
  have hcop : Nat.Coprime c' p := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hpc')
  have hkill : ∀ y ∈ B, (((c' * p : ℕ) : ℂ)) • y ∈ Λ := by
    intro y hy; rw [mul_comm c' p]; exact f3 X A a b S N N' (p * c') hN hN' hLa hcpos y hy
  have hF1 := f1 X A a b S N N' (p * c') x hN hN' hLa hcpos hvol c' p hcop hkill S₁ S₂ hS₁ hS₂

  set SA := repsOf B (Λ ⊓ AC (X.embC A.σ₀) A.δ A.AA S N N' (p * c')) with hSAdef
  have hSAB := f6 X A a b S N N' (p * c') hN hN' hLa hcpos
  have hSBspec : IsReps Λ B (repsOf Λ B) := Formalism.L2.Ker.repsOf_spec Λ B hi2
  obtain ⟨hsplitc, hprime⟩ := f2 (VCx X.Tau a b) B Λ c' p hcop hkill _ S₁ S₂ hSBspec hS₁ hS₂
  have hS1p : ¬ p ∣ S₁.card := fun h => hpc' (hprime p hp h)
  have hS₂P := f5 X A a b S N N' p hp hp2 hpd hN hN' hLa π pE hπ hππ hS c' hc' hpc' S₂ hS₂
  set Sa := S₂.image (flat X.Tau a b).symm with hSadef
  have hSa : IsReps (cLat (conj π) (lamF A N N')) (cLat (conj π / π) (lamF A N N')) Sa := by
    have h := KerB.isReps_comap (flat X.Tau a b) _ _ _ hS₂P
    rw [← KerB.cLat_comap, ← KerB.cLat_comap] at h
    exact h
  have hcardSa := f7 (DVar X.Tau a b) (lamF A N N') hLat p hp π hππ (hΛq π hπ) (hΛq _ hcq) Sa hSa
  have hcardS2 : S₂.card = p ^ Fintype.card (DVar X.Tau a b) := by
    rw [← hcardSa, hSadef, Finset.card_image_of_injective _ (flat X.Tau a b).symm.injective]
  have hSAcard : (SA.card : ℂ) = (S₁.card : ℂ) * (p : ℂ) ^ Fintype.card (DVar X.Tau a b) := by
    rw [hSAB, hsplitc, hcardS2]; push_cast; ring

  have hrelSb : relIdx (cLat (conj π) (lamF A N N')) (lamF A N N') ≠ 0 := by
    have h1 := SC.relIdx_cLat (lamF A N N') hLat (conj π) hπ'0 (hΛq _ hcq)
    intro h0
    rw [h0, Nat.cast_zero] at h1
    have : Complex.normSq (conj π) ≠ 0 := by rw [Complex.normSq_conj]; exact (Complex.normSq_pos.2 hπ0).ne'
    exact (pow_ne_zero _ this) h1.symm
  set Sb := repsOf (cLat (conj π) (lamF A N N')) (lamF A N N') with hSbdef
  have hSb : IsReps (cLat (conj π) (lamF A N N')) (lamF A N N') Sb := Formalism.L2.Ker.repsOf_spec _ _ hrelSb

  set Ψ : (DVar X.Tau a b → ℂ) → ℂ := fun y => if y ∈ cLat (conj π) (lamF A N N') then ((S₁.card : ℂ))⁻¹ else 0 with hΨdef
  have hΨ : ∀ y ∈ Sb, ‖ι (Ψ y)‖ ≤ 1 := by
    intro y _
    simp only [hΨdef]
    split_ifs
    · rw [map_inv₀, map_natCast, norm_inv, LocalJetRescaling.norm_natCast p hS1p, inv_one]
    · simp
  set s := embH (X.embC A.σ₀) A.δ (A.liftW S N N' (p * c') x) with hsdef
  have hsΛ : (c' : ℂ) • s ∈ Λ := f4 X A a b S N N' (p * c') c' x hN hN' hLa hcpos hc' (Dvd.intro_left p rfl) hx
  set r : ↥S₁ → ℂ := fun k => alV A.d A.sc s * alV A.d A.sc k.1 *
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE (HV A.sc) (-s) k.1 : ℂ)) with hrdef
  set t : ↥S₁ → DVar X.Tau a b → ℂ := fun k => (flat X.Tau a b).symm (-s + k.1) with htdef
  have hyΛ : ∀ k : ↥S₁, (c' : ℂ) • k.1 ∈ Λ := fun k => (KerA.mem_killIn.1 (hS₁.1 k.1 k.2)).2
  have hα1 : ∀ y : VCx X.Tau a b, (c' : ℂ) • y ∈ Λ → ‖ι (alV A.d A.sc y)‖ = 1 := by
    intro y hy
    apply XiTorsion.norm_root ι _ (2 * c' ^ 2) (by positivity)
    have h1 := hSCV.1 _ hy
    have h2 : alV A.d A.sc ((c' : ℂ) • y) = alV A.d A.sc y ^ (c' ^ 2) := KerB.alphaQ_natSmul _ _ y c'
    rw [pow_mul', ← h2]
    rcases h1 with h1 | h1 <;> rw [h1] <;> norm_num
  have hr : ∀ k, ‖ι (r k)‖ ≤ 1 := by
    intro k
    simp only [hrdef, map_mul, norm_mul, hα1 s hsΛ, hα1 k.1 (hyΛ k), one_mul]
    have hs' : (c' : ℂ) • (-s) ∈ Λ := by rw [smul_neg]; exact Λ.neg_mem hsΛ
    obtain ⟨q, hq⟩ := XiTorsion.altE_int hSDV hs' (hyΛ k)
    rw [XiTorsion.altE_smul_left, XiTorsion.altE_smul_right] at hq
    rw [XiConnection.norm_phase ι _ (c' * c') (Nat.mul_pos hc' hc') q (by push_cast; linarith)]
  have ht : ∀ k, (c' : ℂ) • t k ∈ lamF A N N' := by
    intro k
    show flat X.Tau a b ((c' : ℂ) • (flat X.Tau a b).symm (-s + k.1)) ∈ Λ
    rw [map_smul, LinearEquiv.apply_symm_apply, smul_add, smul_neg]
    exact Λ.add_mem (Λ.neg_mem hsΛ) (hyΛ k)
  set Afr : J → DVar X.Tau a b → ℂ_[p] := fun j k => ι (conj π) * M j k with hAfrdef
  have hAfr : ∀ j k, ‖Afr j k‖ ≤ ‖ι (conj π)‖ := by
    intro j k
    simp only [hAfrdef, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hM j k)
  have hJI := hC a₀ b₀ c₀ A.d ha hd lam hlam hOK (DVar X.Tau a b) (hSc X.Tau a b A.sc) (lamF A N N')
    (KerB.herm_hSc A.sc) (KerB.posDef_hSc A.sc hsc) hLat hSD hSt (thF A N N') hθ p hp2 hpd ι hInt hLoc π hπ hππ
    Sa Sb hSa hSb Ψ hΨ (↥S₁) r t c' hr hc' hpc' ht J v hv (DVar X.Tau a b) Afr hAfr

  have hxh : ∀ a' ∈ Sa, xiHat (matH (hSc X.Tau a b A.sc)) (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sb a' = ((SA.card : ℂ))⁻¹ := by
    intro a' ha'
    obtain ⟨μ, hμ, hμa⟩ := XiTorsion.mem_cLat (hSa.1 a' ha')
    unfold xiHat
    obtain ⟨b0, _, hb0, hsum⟩ := Formalism.L2.Th1.H.Inv.sum_reps hSb
      (fun y => Ψ y * Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE (matH (hSc X.Tau a b A.sc)) y a' : ℂ)))
      (fun y _ hy => by simp [hΨdef, hy])
    rw [hsum]
    obtain ⟨l, hl, hlb⟩ := XiTorsion.mem_cLat hb0
    have hint : ∃ q : ℤ, altE (matH (hSc X.Tau a b A.sc)) b0 a' = q := by
      have e : altE (matH (hSc X.Tau a b A.sc)) b0 a' = altE (matH (hSc X.Tau a b A.sc)) (π • l) μ := by
        rw [hlb, hμa]
        unfold altE
        congr 1
        rw [LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, LinearMap.map_smul, LinearMap.smul_apply]
        simp only [smul_eq_mul, map_div₀, Complex.conj_conj]
        field_simp
      rw [e]; exact XiTorsion.altE_int hSD (hΛq π hπ l hl) hμ
    obtain ⟨q, hq⟩ := hint
    simp only [hΨdef, if_pos hb0, hq]
    have hex : Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ((q : ℝ) : ℂ)) = 1 := by
      rw [Complex.exp_eq_one_iff]; exact ⟨-q, by push_cast; ring⟩
    rw [hex, mul_one, hSAcard]
    push_cast
    rw [mul_inv, mul_comm]
  have hxiG : ∀ v, xiG (matH (hSc X.Tau a b A.sc)) (alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.sc))) (thF A N N')
      (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sa Sb v =
      ((SA.card : ℂ))⁻¹ * sumU (HV A.sc) (alV A.d A.sc) S₂ (A.e a b N N') (flat X.Tau a b v) := by
    intro v
    unfold xiG
    have e1 : ∀ a' ∈ Sa, xiHat (matH (hSc X.Tau a b A.sc)) (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sb a' *
        alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.sc)) a' * opU (matH (hSc X.Tau a b A.sc)) a' (thF A N N') v =
        ((SA.card : ℂ))⁻¹ * (alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.sc)) a' *
          opU (matH (hSc X.Tau a b A.sc)) a' (thF A N N') v) := fun a' ha' => by rw [hxh a' ha']; ring
    rw [Finset.sum_congr rfl e1, ← Finset.mul_sum]
    congr 1
    rw [hSadef, Finset.sum_image (fun y _ y' _ h => (flat X.Tau a b).symm.injective h)]
    show _ = ∑ y ∈ S₂, alV A.d A.sc y * opU (HV A.sc) y (A.e a b N N') (flat X.Tau a b v)
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [KerB.opU_flat, ← KerB.alV_flat, LinearEquiv.apply_symm_apply]
    rfl

  have hfun : (fun z => ∑ k : ↥S₁, r k * opU (matH (hSc X.Tau a b A.sc)) (t k)
      (xiG (matH (hSc X.Tau a b A.sc)) (alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.sc))) (thF A N N')
        (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sa Sb) z) = fun z => A.thInd S N N' (p * c') x (flat X.Tau a b z) := by
    funext z
    rw [hF1 (flat X.Tau a b z)]
    have hx' : xiG (matH (hSc X.Tau a b A.sc)) (alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.sc))) (thF A N N')
        (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sa Sb =
        fun v => ((SA.card : ℂ))⁻¹ * sumU (HV A.sc) (alV A.d A.sc) S₂ (A.e a b N N') (flat X.Tau a b v) := funext hxiG
    rw [hx', ← Finset.sum_coe_sort S₁, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hrdef, htdef]
    rw [XiTorsion.opU_cmul, ← KerB.opU_flat,
      Formalism.L2.Th1.H.opUMul _ (HV A.sc) (Formalism.L2.Ker.herm_HV A.sc) (-s) k.1]
    ring

  have hxiAn : AnalyticOnNhd ℂ (xiG (matH (hSc X.Tau a b A.sc)) (alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.sc)))
      (thF A N N') (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sa Sb) Set.univ := by
    have e : xiG (matH (hSc X.Tau a b A.sc)) (alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.sc)))
        (thF A N N') (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sa Sb = fun v => ∑ a' ∈ Sa,
          (xiHat (matH (hSc X.Tau a b A.sc)) (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sb a' *
            alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.sc)) a') * opU (matH (hSc X.Tau a b A.sc)) a' (thF A N N') v := by
      funext v; rfl
    rw [e]
    have h := Finset.analyticOnNhd_sum (𝕜 := ℂ) (s := Set.univ) (f := fun a' v =>
      (xiHat (matH (hSc X.Tau a b A.sc)) (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sb a' *
        alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.sc)) a') * opU (matH (hSc X.Tau a b A.sc)) a' (thF A N N') v) Sa
      (fun a' _ => analyticOnNhd_const.mul (Formalism.L2.Th1.H.opUAnalytic _ (matH (hSc X.Tau a b A.sc)) a' _ hθ.1))
    convert h using 1
    funext v
    simp [Finset.sum_apply]
  have hΦ : AnalyticOnNhd ℂ (fun z => ∑ k : ↥S₁, r k * opU (matH (hSc X.Tau a b A.sc)) (t k)
      (xiG (matH (hSc X.Tau a b A.sc)) (alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.sc))) (thF A N N')
        (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sa Sb) z) Set.univ :=
    by
      have h := Finset.analyticOnNhd_sum (𝕜 := ℂ) (s := Set.univ) (f := fun k z => r k * opU (matH (hSc X.Tau a b A.sc)) (t k)
        (xiG (matH (hSc X.Tau a b A.sc)) (alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.sc))) (thF A N N')
          (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sa Sb) z) Finset.univ
        (fun k _ => analyticOnNhd_const.mul (Formalism.L2.Th1.H.opUAnalytic _ (matH (hSc X.Tau a b A.sc)) (t k) _ hxiAn))
      convert h using 1
      funext z
      simp [Finset.sum_apply]
  have hAn : AnalyticOnNhd ℂ (A.thInd S N N' (p * c') x) Set.univ := by
    have e : A.thInd S N N' (p * c') x = fun u => (fun z => ∑ k : ↥S₁, r k * opU (matH (hSc X.Tau a b A.sc)) (t k)
        (xiG (matH (hSc X.Tau a b A.sc)) (alphaQ (Real.sqrt A.d / 2) (matH (hSc X.Tau a b A.sc))) (thF A N N')
          (p ^ Fintype.card (DVar X.Tau a b)) Ψ Sa Sb) z) ((flat X.Tau a b).symm u) := by
      funext u
      rw [hfun]
      simp only [LinearEquiv.apply_symm_apply]
    rw [e]
    intro u _
    have hlin : AnalyticAt ℂ (fun u => (flat X.Tau a b).symm u) u :=
      (LinearMap.toContinuousLinearMap ((flat X.Tau a b).symm : VCx X.Tau a b →ₗ[ℂ] (DVar X.Tau a b → ℂ))).analyticAt u
    exact (hΦ _ (Set.mem_univ _)).comp hlin

  have hT := f8 X.Tau a b (A.thInd S N N' (p * c') x) hAn m
  have hco := hJI m
  unfold serLin at hco
  rw [hfun] at hco
  have hfrd : frameM (ι : ℂ →+* ℂ_[p]) v Afr = fun i k => if i = k then ι (conj π) * ι (A.cD k.1) else 0 := by
    funext i k
    have e : frameM (ι : ℂ →+* ℂ_[p]) v Afr i k = ι (conj π) * frameM (ι : ℂ →+* ℂ_[p]) v M i k := by
      unfold frameM
      simp only [hAfrdef]
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    have h2 : frameM (ι : ℂ →+* ℂ_[p]) v M i k = if i = k then ι (A.cD k.1) else 0 := hfr i k
    rw [e, h2]
    split_ifs <;> first | rfl | simp
  rw [hfrd, MvPowerSeries.coeff_C_mul] at hco
  have e9 := f9 ℂ_[p] (DVar X.Tau a b) (fun k => ι (conj π) * ι (A.cD k.1))
    (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv fun z => A.thInd S N N' (p * c') x (flat X.Tau a b z))) m
  rw [e9, MvPowerSeries.coeff_map] at hco
  have hjet : ι (jetC A.cD (A.thInd S N N' (p * c') x) m) =
      (m.prod fun k e => ι (A.cD k.1) ^ e) * ((mfact m : ℂ_[p]) *
        (ι : ℂ →+* ℂ_[p]) (MvPowerSeries.coeff m (taylorMv fun z => A.thInd S N N' (p * c') x (flat X.Tau a b z)))) := by
    unfold jetC
    rw [← hT, map_mul, map_mul, map_natCast, map_finsuppProd]
    simp only [map_pow]
    rfl
  have hprod : (m.prod fun k e => (ι (conj π) * ι (A.cD k.1)) ^ e) =
      ι (conj π) ^ m.degree * (m.prod fun k e => ι (A.cD k.1) ^ e) := by
    simp_rw [mul_pow]
    rw [Finsupp.prod_mul, KerB.prod_const_pow]
  have hcard : Fintype.card (DVar X.Tau a b) = Fintype.card X.Tau * b * a := by
    simp [Fintype.card_prod, Fintype.card_fin, mul_assoc]
  have hfin : (mfact m : ℂ_[p]) * ((p : ℂ_[p]) ^ Fintype.card (DVar X.Tau a b) *
      ((m.prod fun k e => (ι (conj π) * ι (A.cD k.1)) ^ e) *
        (ι : ℂ →+* ℂ_[p]) (MvPowerSeries.coeff m (taylorMv fun z => A.thInd S N N' (p * c') x (flat X.Tau a b z))))) =
      ι (jetC A.cD (A.thInd S N N' (p * c') x) m) * ι (conj π) ^ m.degree * (p : ℂ_[p]) ^ (Fintype.card X.Tau * b * a) := by
    rw [hjet, hprod, hcard]; ring
  rw [hfin, norm_mul, norm_mul, norm_pow, norm_pow] at hco
  exact hco

end Formalism.L2.AlgTh
