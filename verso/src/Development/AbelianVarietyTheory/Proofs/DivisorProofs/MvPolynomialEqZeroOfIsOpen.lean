import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial

namespace GlobalTheory.Mean4

/- English proof (translation)
Take `⟨x, hx⟩` from `hne`. Take `⟨ε, hε, hb⟩` from `Metric.isOpen_iff.1 hU x hx`. Use `MvPolynomial.funext_set (fun i => Set.Ioo (x i - ε) (x i + ε)) (fun i => Set.Ioo_infinite (by linarith)) (fun y hy => ?_)` and prove the remaining obligations. Rewrite using `[map_zero]`. Use `h y (hb ?_)` and prove the remaining obligations.

Rewrite using `[ball_pi x hε]`. Introduce `i hi`. Simplify using `only [Real.ball_eq_Ioo]`. Conclude with `hy i hi`.
-/
theorem mvPolynomial_eq_zero_of_isOpen {σ : Type} [Fintype σ] {U : Set (σ → ℝ)} (hU : IsOpen U)
    (hne : U.Nonempty) (P : MvPolynomial σ ℝ) (h : ∀ x ∈ U, eval x P = 0) : P = 0 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 hU x hx
  refine MvPolynomial.funext_set (fun i => Set.Ioo (x i - ε) (x i + ε))
    (fun i => Set.Ioo_infinite (by linarith)) (fun y hy => ?_)
  rw [map_zero]
  refine h y (hb ?_)
  rw [ball_pi x hε]
  intro i hi
  simp only [Real.ball_eq_Ioo]
  exact hy i hi

/- English proof (translation)
Set `V` to `restrictTotalDegree σ ℝ d`. Set `ev : (σ → ℝ) → (V →ₗ[ℝ] ℝ)` to `fun x => (aeval x).toLinearMap ∘ₗ V.subtype`. Establish `hev : ∀ x (P : V), ev x P = eval x (P : MvPolynomial σ ℝ)` using `fun x P => by`. Simplify using `[ev]`. Establish `hspan : Submodule.span ℝ (ev '' U) = ⊤`.

Use `Submodule.span_eq_top_of_ne_zero (fun z hz => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Use `hz (Subtype.ext (mvPolynomial_eq_zero_of_isOpen hU hne _ fun x hx => ?_))` and prove the remaining obligations. Rewrite using `[← hev]`.

Conclude with `hc _ ⟨x, hx, rfl⟩`. Establish `key : ∀ φ : V →ₗ[ℝ] ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : V) (e : ℝ), (∀ x ∈ U, |eval x (P : MvPolynomial σ ℝ)| ≤ e) → |φ P| ≤ C * e`. Introduce `φ`. Establish `hφ : φ ∈ Submodule.span ℝ (ev '' U)` using `hspan ▸ Submodule.mem_top`. Proceed by induction on `hφ using Submodule.span_induction with`.

Consider the case `mem φ h`. Take `⟨x, hx, rfl⟩` from `h`. Conclude with `⟨1, zero_le_one, fun P e he => by rw [hev, one_mul]; exact he x hx⟩`. Consider the case `zero => exact ⟨0, le_rfl, fun P e _ => by simp⟩`. Consider the case `add φ ψ _ _ h1 h2`.

Take `⟨C, hC, h1⟩` from `h1`. Take `⟨D, hD, h2⟩` from `h2`. Use `⟨C + D, add_nonneg hC hD, fun P e he => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.add_apply, add_mul]`. Conclude with `(abs_add_le _ _).trans (add_le_add (h1 P e he) (h2 P e he))`.

Consider the case `smul a φ _ h1`. Take `⟨C, hC, h1⟩` from `h1`. Use `⟨|a| * C, mul_nonneg (abs_nonneg a) hC, fun P e he => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, smul_eq_mul, abs_mul, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (h1 P e he) (abs_nonneg a)`.

Use `choose c hc0 hc using fun m : σ →₀ ℕ => key (lcoeff ℝ m ∘ₗ V.subtype)`. Set `S : Finset (σ →₀ ℕ)` to `Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => d)`. Use `⟨∑ m ∈ S, c m, Finset.sum_nonneg fun m _ => hc0 m, fun P e hd he m => ?_⟩` and prove the remaining obligations. Establish `he0 : 0 ≤ e`. Take `⟨x, hx⟩` from `hne`.

Conclude with `(abs_nonneg _).trans (he x hx)`. Distinguish the cases in `hm : m ∈ P.support`. Establish `hmS : m ∈ S`. Use `Finset.mem_Iic.2 fun i => ?_` and prove the remaining obligations. Conclude with `(monomial_le_degreeOf i hm).trans ((degreeOf_le_totalDegree P i).trans hd)`.

Use `hc m ⟨P, (mem_restrictTotalDegree σ d P).2 hd⟩ e he` as an intermediate fact. Use `this.trans (mul_le_mul_of_nonneg_right ?_ he0)` and prove the remaining obligations. Conclude with `Finset.single_le_sum (fun m _ => hc0 m) hmS`. Rewrite using `[notMem_support_iff.1 hm, abs_zero]`. Conclude with `mul_nonneg (Finset.sum_nonneg fun m _ => hc0 m) he0`.
-/
theorem coeff_le_of_eval_le (σ : Type) [Fintype σ] [DecidableEq σ] (d : ℕ) (U : Set (σ → ℝ))
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : MvPolynomial σ ℝ) (e : ℝ), P.totalDegree ≤ d →
      (∀ x ∈ U, |eval x P| ≤ e) → ∀ m, |P.coeff m| ≤ C * e := by
  let V := restrictTotalDegree σ ℝ d
  let ev : (σ → ℝ) → (V →ₗ[ℝ] ℝ) := fun x => (aeval x).toLinearMap ∘ₗ V.subtype
  have hev : ∀ x (P : V), ev x P = eval x (P : MvPolynomial σ ℝ) := fun x P => by
    simp [ev]
  have hspan : Submodule.span ℝ (ev '' U) = ⊤ := by
    refine Submodule.span_eq_top_of_ne_zero (fun z hz => ?_)
    by_contra hc
    push Not at hc
    refine hz (Subtype.ext (mvPolynomial_eq_zero_of_isOpen hU hne _ fun x hx => ?_))
    rw [← hev]
    exact hc _ ⟨x, hx, rfl⟩
  have key : ∀ φ : V →ₗ[ℝ] ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : V) (e : ℝ),
      (∀ x ∈ U, |eval x (P : MvPolynomial σ ℝ)| ≤ e) → |φ P| ≤ C * e := by
    intro φ
    have hφ : φ ∈ Submodule.span ℝ (ev '' U) := hspan ▸ Submodule.mem_top
    induction hφ using Submodule.span_induction with
    | mem φ h =>
      obtain ⟨x, hx, rfl⟩ := h
      exact ⟨1, zero_le_one, fun P e he => by rw [hev, one_mul]; exact he x hx⟩
    | zero => exact ⟨0, le_rfl, fun P e _ => by simp⟩
    | add φ ψ _ _ h1 h2 =>
      obtain ⟨C, hC, h1⟩ := h1
      obtain ⟨D, hD, h2⟩ := h2
      refine ⟨C + D, add_nonneg hC hD, fun P e he => ?_⟩
      rw [LinearMap.add_apply, add_mul]
      exact (abs_add_le _ _).trans (add_le_add (h1 P e he) (h2 P e he))
    | smul a φ _ h1 =>
      obtain ⟨C, hC, h1⟩ := h1
      refine ⟨|a| * C, mul_nonneg (abs_nonneg a) hC, fun P e he => ?_⟩
      rw [LinearMap.smul_apply, smul_eq_mul, abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (h1 P e he) (abs_nonneg a)
  choose c hc0 hc using fun m : σ →₀ ℕ => key (lcoeff ℝ m ∘ₗ V.subtype)
  let S : Finset (σ →₀ ℕ) := Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => d)
  refine ⟨∑ m ∈ S, c m, Finset.sum_nonneg fun m _ => hc0 m, fun P e hd he m => ?_⟩
  have he0 : 0 ≤ e := by
    obtain ⟨x, hx⟩ := hne
    exact (abs_nonneg _).trans (he x hx)
  by_cases hm : m ∈ P.support
  · have hmS : m ∈ S := by
      refine Finset.mem_Iic.2 fun i => ?_
      exact (monomial_le_degreeOf i hm).trans ((degreeOf_le_totalDegree P i).trans hd)
    have := hc m ⟨P, (mem_restrictTotalDegree σ d P).2 hd⟩ e he
    refine this.trans (mul_le_mul_of_nonneg_right ?_ he0)
    exact Finset.single_le_sum (fun m _ => hc0 m) hmS
  · rw [notMem_support_iff.1 hm, abs_zero]
    exact mul_nonneg (Finset.sum_nonneg fun m _ => hc0 m) he0

end GlobalTheory.Mean4
