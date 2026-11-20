import Mathlib
import Formalism.HermitianCurvature.StatementQ

open Matrix Finset

namespace Formalism.FourierDecayAlt.Q.Adapted

open Formalism.REAL

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `h1` using `congrFun (congrFun h i) k`. Rewrite `h1` using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [Matrix.mulVec, dotProduct, h1, Pi.single_apply]`.
-/
theorem mulVec_col {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) (h : Q * P = 1) (k : Fin n) :
    (Q *ᵥ fun p => P p k) = Pi.single k 1 := by
  funext i
  have h1 := congrFun (congrFun h i) k
  rw [Matrix.mul_apply, Matrix.one_apply] at h1
  simp only [Matrix.mulVec, dotProduct, h1, Pi.single_apply]

/- English proof (translation)
Unfold `chatA`. Rewrite using `[Finset.sum_eq_single l (fun i _ hi => ?_) (fun h => absurd (Finset.mem_univ l) h)]`. Rewrite using `[Finset.sum_eq_single l (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ l) h)]`. Use `congr 1`. Rewrite using `[Pi.single_eq_same, mul_one, ← two_mul, pow_mul]`.

Evaluate the numerical expressions. Simplify using `[Pi.single_apply, hj]`. Conclude with `Finset.sum_eq_zero fun j _ => by simp [hγ i hi]`.
-/
theorem chatA_single {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (u : ℂ)
    (l : Fin m) (γ : Fin m → ℂ) (hγ : ∀ j, j ≠ l → γ j = 0) :
    chatA E u (Pi.single l 1) γ = γ l • qminor E (skip1 l) (skip1 l) u := by
  unfold chatA
  rw [Finset.sum_eq_single l (fun i _ hi => ?_) (fun h => absurd (Finset.mem_univ l) h)]
  · rw [Finset.sum_eq_single l (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ l) h)]
    · congr 1
      rw [Pi.single_eq_same, mul_one, ← two_mul, pow_mul]
      norm_num
    · simp [Pi.single_apply, hj]
  · exact Finset.sum_eq_zero fun j _ => by simp [hγ i hi]

/- English proof (translation)
Establish `hC : j' ≠ 0`. Introduce and unpack `rfl`. Simplify using `[Fin.lt_def] at h`. Apply the tactic sequence `by_cases hA : j = 0 <;> by_cases hB : j' = 1 <;> simp [Pi.single_apply, hA, hB, hC]`.
-/
theorem coefA {n : ℕ} (j j' : Fin (n + 2)) (h : j < j') :
    (Pi.single 0 1 : Fin (n + 2) → ℂ) j * (Pi.single 1 1 : Fin (n + 2) → ℂ) j' -
      (Pi.single 0 1 : Fin (n + 2) → ℂ) j' * (Pi.single 1 1 : Fin (n + 2) → ℂ) j =
      if j = 0 ∧ j' = 1 then 1 else 0 := by
  have hC : j' ≠ 0 := by
    rintro rfl
    simp [Fin.lt_def] at h
  by_cases hA : j = 0 <;> by_cases hB : j' = 1 <;> simp [Pi.single_apply, hA, hB, hC]

/- English proof (translation)
Establish `hi' : 2 ≤ i'.val`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Apply `hne` to reduce the goal to its premises. Establish `h1 : i.val < i'.val` using `h`.

Apply the tactic sequence `refine ⟨Fin.ext ?_, Fin.ext ?_⟩ <;> simp only [Fin.val_zero, Fin.val_one] <;> omega`. Rewrite using `[(hγ i' hi').1, (hγ i' hi').2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coefB {n : ℕ} (γ γ' : Fin (n + 2) → ℂ) (hγ : ∀ j : Fin (n + 2), 2 ≤ j.val → γ j = 0 ∧ γ' j = 0)
    (i i' : Fin (n + 2)) (h : i < i') (hne : ¬ (i = 0 ∧ i' = 1)) :
    γ i * γ' i' - γ i' * γ' i = 0 := by
  have hi' : 2 ≤ i'.val := by
    by_contra hlt
    push_neg at hlt
    apply hne
    have h1 : i.val < i'.val := h
    refine ⟨Fin.ext ?_, Fin.ext ?_⟩ <;> simp only [Fin.val_zero, Fin.val_one] <;> omega
  rw [(hγ i' hi').1, (hγ i' hi').2]
  ring

/- English proof (translation)
Unfold `chat2A`. Establish `key : ∀ i i' j j' : Fin (n + 2), (if i < i' ∧ j < j' then ((-1) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ)) * (γ i * γ' i' - γ i' * γ' i) * ((Pi.single 0 1 : Fin (n + 2) → ℂ) j * (Pi.single 1 1 : Fin (n + 2) → ℂ) j' - (Pi.single 0 1 : Fin (n + 2) → ℂ) j' * (Pi.single 1 1 : Fin (n …`. Introduce `i i' j j'`. Distinguish the cases in `h : i < i' ∧ j < j'`. Rewrite using `[if_pos h, coefA j j' h.2]`.

Distinguish the cases in `hii : i = 0 ∧ i' = 1`. Distinguish the cases in `hjj : j = 0 ∧ j' = 1`. Take `⟨rfl, rfl⟩` from `hii`. Take `⟨rfl, rfl⟩` from `hjj`. Evaluate the numerical expressions.

Rewrite using `[if_neg hjj, if_neg (show ¬(j' = 1 ∧ j = 0 ∧ i' = 1 ∧ i = 0) from fun h' => hjj ⟨h'.2.1, h'.1⟩), mul_zero, zero_smul]`. Rewrite using `[coefB γ γ' hγ i i' h.1 hii, if_neg (show ¬(j' = 1 ∧ j = 0 ∧ i' = 1 ∧ i = 0) from fun h' => hii ⟨h'.2.2.2, h'.2.2.1⟩), mul_zero, zero_mul, zero_smul]`. Rewrite using `[if_neg h, if_neg]`. Introduce and unpack `⟨rfl, rfl, rfl, rfl⟩`. Conclude with `h ⟨by simp [Fin.lt_def], by simp [Fin.lt_def]⟩`.

Simplify using `only [key]`. Simplify using `only [ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem second_capelli_minor_standard_basis {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin (n + 2) → Fin (n + 2) → A)
    (u : ℂ) (γ γ' : Fin (n + 2) → ℂ) (hγ : ∀ j : Fin (n + 2), 2 ≤ j.val → γ j = 0 ∧ γ' j = 0) :
    chat2A E u (Pi.single 0 1) (Pi.single 1 1) γ γ' =
      (γ 0 * γ' 1 - γ 1 * γ' 0) • qminor E (skip2 0 1) (skip2 0 1) u := by
  unfold chat2A
  have key : ∀ i i' j j' : Fin (n + 2),
      (if i < i' ∧ j < j' then
        ((-1) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ)) * (γ i * γ' i' - γ i' * γ' i) *
          ((Pi.single 0 1 : Fin (n + 2) → ℂ) j * (Pi.single 1 1 : Fin (n + 2) → ℂ) j' -
            (Pi.single 0 1 : Fin (n + 2) → ℂ) j' * (Pi.single 1 1 : Fin (n + 2) → ℂ) j)) •
          qminor E (skip2 i i') (skip2 j j') u
      else 0) =
      if j' = 1 ∧ j = 0 ∧ i' = 1 ∧ i = 0 then (γ 0 * γ' 1 - γ 1 * γ' 0) • qminor E (skip2 0 1) (skip2 0 1) u else 0 := by
    intro i i' j j'
    by_cases h : i < i' ∧ j < j'
    · rw [if_pos h, coefA j j' h.2]
      by_cases hii : i = 0 ∧ i' = 1
      · by_cases hjj : j = 0 ∧ j' = 1
        · obtain ⟨rfl, rfl⟩ := hii
          obtain ⟨rfl, rfl⟩ := hjj
          norm_num
        · rw [if_neg hjj, if_neg (show ¬(j' = 1 ∧ j = 0 ∧ i' = 1 ∧ i = 0) from fun h' => hjj ⟨h'.2.1, h'.1⟩),
            mul_zero, zero_smul]
      · rw [coefB γ γ' hγ i i' h.1 hii,
          if_neg (show ¬(j' = 1 ∧ j = 0 ∧ i' = 1 ∧ i = 0) from fun h' => hii ⟨h'.2.2.2, h'.2.2.1⟩),
          mul_zero, zero_mul, zero_smul]
    · rw [if_neg h, if_neg]
      rintro ⟨rfl, rfl, rfl, rfl⟩
      exact h ⟨by simp [Fin.lt_def], by simp [Fin.lt_def]⟩
  simp only [key]
  simp only [ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Introduce `A _ _ n E P Q hE hQP hPQ u β hβ`. Establish `h` using `(hcov A (n + 1) E P Q hE hQP hPQ u (fun p => P p (Fin.last n)) 0 β 0).2.1`. Rewrite using `[← h, mulVec_col P Q hQP (Fin.last n)]`. Conclude with `chatA_single _ u (Fin.last n) (β ᵥ* P) hβ`.
-/
theorem chatAdapted_of (hcov : ContractionsCovariant) : ChatAdapted := by
  intro A _ _ n E P Q hE hQP hPQ u β hβ
  have h := (hcov A (n + 1) E P Q hE hQP hPQ u (fun p => P p (Fin.last n)) 0 β 0).2.1
  rw [← h, mulVec_col P Q hQP (Fin.last n)]
  exact chatA_single _ u (Fin.last n) (β ᵥ* P) hβ

/- English proof (translation)
Introduce `A _ _ n E P Q hE hQP hPQ u β β' hβ`. Establish `h` using `(hcov A (n + 2) E P Q hE hQP hPQ u (fun p => P p 0) (fun p => P p 1) β β').2.2`. Rewrite using `[← h, mulVec_col P Q hQP 0, mulVec_col P Q hQP 1]`. Conclude with `second_capelli_minor_standard_basis _ u (β ᵥ* P) (β' ᵥ* P) hβ`.
-/
theorem chat2Adapted_of (hcov : ContractionsCovariant) : Chat2Adapted := by
  intro A _ _ n E P Q hE hQP hPQ u β β' hβ
  have h := (hcov A (n + 2) E P Q hE hQP hPQ u (fun p => P p 0) (fun p => P p 1) β β').2.2
  rw [← h, mulVec_col P Q hQP 0, mulVec_col P Q hQP 1]
  exact second_capelli_minor_standard_basis _ u (β ᵥ* P) (β' ᵥ* P) hβ

/- English proof (translation)
Introduce `h` and use `⟨chatAdapted_of h, chat2Adapted_of h⟩`.
-/
theorem main : ContractionsCovariant → ChatAdapted ∧ Chat2Adapted := fun h => ⟨chatAdapted_of h, chat2Adapted_of h⟩

end Formalism.FourierDecayAlt.Q.Adapted
