import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableAtOneParameter

open Filter Topology

namespace GlobalTheory.OneParamMatrix

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
Establish `hd` using `GlobalTheory.LocWeil.DerComm.differentiableAt_oneParameter N hc h0 hm`. Use `set Y := deriv N 0 with hY`. Establish `hN : ∀ t, HasDerivAt N (N t * Y) t`. Introduce `t`. Establish `h1 : HasDerivAt (fun s => N t * N (s - t)) (N t * Y) t`.

Establish `h2 : HasDerivAt (fun s => N (s - t)) Y t`. Establish `hd' : HasDerivAt N Y (t - t)` using `by rw [sub_self]; exact hd.hasDerivAt`. Conclude with `hd'.comp_sub_const t t`. Conclude with `h2.const_mul (N t)`. Use `h1.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[← hm]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `⟨Y, fun t => ?_⟩` and prove the remaining obligations.

Use `set f : ℝ → Matrix n n ℂ := fun s => N s * NormedSpace.exp ((-s) • Y) with hf`. Establish `hfd : ∀ s, HasDerivAt f 0 s`. Introduce `s`. Establish `he : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • (-Y))) (NormedSpace.exp (s • (-Y)) * (-Y)) s` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) (-Y) s`. Establish `he' : HasDerivAt (fun u : ℝ => NormedSpace.exp ((-u) • Y)) (NormedSpace.exp ((-s) • Y) * (-Y)) s`.

Simplify `he` using `[smul_neg, neg_smul]`. Use `(hN s).mul he'` as an intermediate fact. Use `this.congr_deriv ?_` and prove the remaining obligations. Establish `hcomm : Y * NormedSpace.exp ((-s) • Y) = NormedSpace.exp ((-s) • Y) * Y` using `((Commute.refl Y).smul_right (-s)).exp_right.eq`. Rewrite using `[mul_assoc, hcomm]`.

Simplify using `[mul_neg]`. Establish `hconst` using `is_const_of_deriv_eq_zero (fun s => (hfd s).differentiableAt) (fun s => (hfd s).deriv) t 0`. Establish `hf0 : f 0 = 1` using `by simp [hf, h0]`. Rewrite `hconst` using `[hf0]`. Establish `hinv : NormedSpace.exp ((-t) • Y) * NormedSpace.exp (t • Y) = 1`.

Rewrite using `[← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _)]`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eq_exp_of_continuous_oneParameter {n : Type} [Fintype n] [DecidableEq n]
    (N : ℝ → Matrix n n ℂ) (hc : Continuous N) (h0 : N 0 = 1)
    (hm : ∀ s t, N (s + t) = N s * N t) :
    ∃ Y : Matrix n n ℂ, ∀ t : ℝ, N t = NormedSpace.exp (t • Y) := by
  have hd := GlobalTheory.LocWeil.DerComm.differentiableAt_oneParameter N hc h0 hm
  set Y := deriv N 0 with hY
  have hN : ∀ t, HasDerivAt N (N t * Y) t := by
    intro t
    have h1 : HasDerivAt (fun s => N t * N (s - t)) (N t * Y) t := by
      have h2 : HasDerivAt (fun s => N (s - t)) Y t := by
        have hd' : HasDerivAt N Y (t - t) := by rw [sub_self]; exact hd.hasDerivAt
        exact hd'.comp_sub_const t t
      exact h2.const_mul (N t)
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only
    rw [← hm]; congr 1; ring
  refine ⟨Y, fun t => ?_⟩
  set f : ℝ → Matrix n n ℂ := fun s => N s * NormedSpace.exp ((-s) • Y) with hf
  have hfd : ∀ s, HasDerivAt f 0 s := by
    intro s
    have he : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • (-Y))) (NormedSpace.exp (s • (-Y)) * (-Y)) s :=
      hasDerivAt_exp_smul_const (𝕂 := ℝ) (-Y) s
    have he' : HasDerivAt (fun u : ℝ => NormedSpace.exp ((-u) • Y))
        (NormedSpace.exp ((-s) • Y) * (-Y)) s := by
      simpa [smul_neg, neg_smul] using he
    have := (hN s).mul he'
    refine this.congr_deriv ?_
    have hcomm : Y * NormedSpace.exp ((-s) • Y) = NormedSpace.exp ((-s) • Y) * Y :=
      ((Commute.refl Y).smul_right (-s)).exp_right.eq
    rw [mul_assoc, hcomm]
    simp [mul_neg]
  have hconst := is_const_of_deriv_eq_zero (fun s => (hfd s).differentiableAt)
    (fun s => (hfd s).deriv) t 0
  have hf0 : f 0 = 1 := by simp [hf, h0]
  rw [hf0] at hconst
  have hinv : NormedSpace.exp ((-t) • Y) * NormedSpace.exp (t • Y) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _)]
    simp
  calc N t = N t * (NormedSpace.exp ((-t) • Y) * NormedSpace.exp (t • Y)) := by rw [hinv, mul_one]
    _ = f t * NormedSpace.exp (t • Y) := by simp only [hf, mul_assoc]
    _ = NormedSpace.exp (t • Y) := by rw [hconst, one_mul]

end GlobalTheory.OneParamMatrix
