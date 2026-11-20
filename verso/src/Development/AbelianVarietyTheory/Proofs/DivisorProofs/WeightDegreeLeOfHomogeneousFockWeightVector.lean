import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PderivEqZeroOfColOp

noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg

open GlobalTheory.JointHarm in

/- English proof (translation)
Take `⟨m, hm⟩` from `support_nonempty.2 hP0`. Take `⟨h1, h2⟩` from `(h.mem_wtSub μ P).1 hP`. Establish `e1 : m.degree = d`. Rewrite using `[Finsupp.degree_eq_weight_one]`. Conclude with `hd (mem_support_iff.1 hm)`.

Rewrite using `[← e1, degree_eq_blocks he, degW, Fintype.sum_sum_type, Nat.cast_add, Nat.cast_sum, Nat.cast_sum]`. Use `add_le_add (Finset.sum_le_sum fun t _ => ?_) (Finset.sum_le_sum fun t _ => ?_)` and prove the remaining obligations. Rewrite using `[mixed_weight _ _ (h1 t) hm, Nat.cast_add]`. Conclude with `(abs_sub _ _).trans (by simp only [Nat.abs_cast, le_refl])`. Rewrite using `[mixed_weight _ _ (h2 t) hm, Nat.cast_add]`.

Conclude with `(abs_sub _ _).trans (by simp only [Nat.abs_cast, le_refl])`.
-/
theorem degW_le_of_isSide {σ : Type} {p q r s : ℕ} {e : Ln p q r s → σ}
    {act : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)} [Fintype σ]
    (he : Function.Bijective e) (h : IsSide e act) {d : ℕ}
    {μ : Ix p q → ℚ} {P : MvPolynomial σ ℂ} (hd : P ∈ homog σ d) (hP0 : P ≠ 0)
    (hP : P ∈ wtSub act μ) : degW (cPair r s) μ ≤ d := by
  obtain ⟨m, hm⟩ := support_nonempty.2 hP0
  obtain ⟨h1, h2⟩ := (h.mem_wtSub μ P).1 hP
  have e1 : m.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hd (mem_support_iff.1 hm)
  rw [← e1, degree_eq_blocks he, degW, Fintype.sum_sum_type, Nat.cast_add, Nat.cast_sum,
    Nat.cast_sum]
  refine add_le_add (Finset.sum_le_sum fun t _ => ?_) (Finset.sum_le_sum fun t _ => ?_)
  · rw [mixed_weight _ _ (h1 t) hm, Nat.cast_add]
    exact (abs_sub _ _).trans (by simp only [Nat.abs_cast, le_refl])
  · rw [mixed_weight _ _ (h2 t) hm, Nat.cast_add]
    exact (abs_sub _ _).trans (by simp only [Nat.abs_cast, le_refl])

/- English proof (translation)
Introduce `_ _ _ _` and use `⟨fun _ _ _ hd h0 hP => degW_le_of_isSide Function.bijective_id GlobalTheory.JointHarm.isSide_one hd h0 hP, fun _ _ _ hd h0 hP => degW_le_of_isSide Prod.swap_bijective GlobalTheory.JointHarm.isSide_two hd h0 hP⟩`.
-/
theorem degW_le_of_homog_wtSub : ∀ (p q r s : ℕ),
    (∀ (d : ℕ) (μ : Ix p q → ℚ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → P ≠ 0 →
      P ∈ wtSub (fockAct1 p q r s) μ → degW (cPair r s) μ ≤ d) ∧
    (∀ (d : ℕ) (μ : Ix r s → ℚ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → P ≠ 0 →
      P ∈ wtSub (fockAct2 p q r s) μ → degW (cPair p q) μ ≤ d) := fun _ _ _ _ =>
  ⟨fun _ _ _ hd h0 hP =>
      degW_le_of_isSide Function.bijective_id GlobalTheory.JointHarm.isSide_one hd h0 hP,
    fun _ _ _ hd h0 hP =>
      degW_le_of_isSide Prod.swap_bijective GlobalTheory.JointHarm.isSide_two hd h0 hP⟩

end GlobalTheory.FockAlg
