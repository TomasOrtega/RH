import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.SkewSolve

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open Formalism.MainNotions.S Matrix

/- English proof (translation)
Introduce `E _ _ r β x Q v l hind hβQ hβv hQβ hskew`. Establish `hS : βᴴ * x + xᴴ * β = 0`. Use extensionality with `a b`. Simplify using `only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.zero_apply, ← Finset.sum_add_distrib]`. Conclude with `hskew a b`.

Establish `h1 : x * Q + (x * Q)ᴴ = 0`. Establish `h0` using `congrArg (fun M => Qᴴ * M * Q) hS`. Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_zero, Matrix.zero_mul] at h0`. Establish `e1 : Qᴴ * (βᴴ * x) * Q = x * Q`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hβQ, Matrix.conjTranspose_one, Matrix.one_mul]`.

Establish `e2 : Qᴴ * (xᴴ * β) * Q = (x * Q)ᴴ`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_assoc, hβQ, Matrix.mul_one]`. Rewrite `h0` using `[e1, e2]`. Conclude with `h0`. Establish `hβv' : β *ᵥ v = 0`.

Use function extensionality and compare the values at `c`. Conclude with `hβv c`. Establish `hw : βᴴ *ᵥ (x *ᵥ v) = 0`. Establish `h0` using `congrArg (fun M => M *ᵥ v) hS`. Simplify using `only [Matrix.add_mulVec, Matrix.zero_mulVec, ← Matrix.mulVec_mulVec, hβv', Matrix.mulVec_zero, add_zero] at h0`.

Conclude with `h0`. Establish `hxv : x *ᵥ v = 0`. Establish `hu` using `hind (fun c => star ((x *ᵥ v) c)) (fun b => by`. Establish `hb` using `congrFun hw b`. Establish `h2 : ∑ c, star ((x *ᵥ v) c) * β c b = star ((βᴴ *ᵥ (x *ᵥ v)) b)` using `by show _ = star (∑ c, βᴴ b c * (x *ᵥ v) c)`.

Simplify using `only [Matrix.conjTranspose_apply, star_sum, star_mul', star_star]`. Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Rewrite using `[h2, hb]`. Use the proof step `simp)`. Use function extensionality and compare the values at `c`.

Establish `hc` using `congrFun hu c`. Simplify using `using hc`. Use `⟨fun c d => ?_, ?_⟩` and prove the remaining obligations. Establish `hcd` using `congrFun (congrFun h1 c) d`. Simplify `hcd` using `only [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.zero_apply]`.

Rewrite using `[Matrix.mul_assoc]`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [hQβ, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Establish `hi` using `congrFun hxv i`.

Establish `h' : ∑ k, x i k * (v k * l j) = (x *ᵥ v) i * l j` using `by show _ = (∑ k, x i k * v k) * l j`. Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`. Rewrite using `[h', hi]`. Simplify using the standard rewrite rules.
-/
theorem skewSolve_holds : SkewSolve := by
  intro E _ _ r β x Q v l hind hβQ hβv hQβ hskew
  have hS : βᴴ * x + xᴴ * β = 0 := by
    ext a b
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.zero_apply,
      ← Finset.sum_add_distrib]
    exact hskew a b
  have h1 : x * Q + (x * Q)ᴴ = 0 := by
    have h0 := congrArg (fun M => Qᴴ * M * Q) hS
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_zero, Matrix.zero_mul] at h0
    have e1 : Qᴴ * (βᴴ * x) * Q = x * Q := by
      rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hβQ, Matrix.conjTranspose_one, Matrix.one_mul]
    have e2 : Qᴴ * (xᴴ * β) * Q = (x * Q)ᴴ := by
      rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_assoc, hβQ, Matrix.mul_one]
    rw [e1, e2] at h0
    exact h0
  have hβv' : β *ᵥ v = 0 := by
    funext c
    exact hβv c
  have hw : βᴴ *ᵥ (x *ᵥ v) = 0 := by
    have h0 := congrArg (fun M => M *ᵥ v) hS
    simp only [Matrix.add_mulVec, Matrix.zero_mulVec, ← Matrix.mulVec_mulVec, hβv', Matrix.mulVec_zero,
      add_zero] at h0
    exact h0
  have hxv : x *ᵥ v = 0 := by
    have hu := hind (fun c => star ((x *ᵥ v) c)) (fun b => by
      have hb := congrFun hw b
      have h2 : ∑ c, star ((x *ᵥ v) c) * β c b = star ((βᴴ *ᵥ (x *ᵥ v)) b) := by
        show _ = star (∑ c, βᴴ b c * (x *ᵥ v) c)
        simp only [Matrix.conjTranspose_apply, star_sum, star_mul', star_star]
        exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
      rw [h2, hb]
      simp)
    funext c
    have hc := congrFun hu c
    simpa using hc
  refine ⟨fun c d => ?_, ?_⟩
  · have hcd := congrFun (congrFun h1 c) d
    simpa only [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.zero_apply] using hcd
  · rw [Matrix.mul_assoc]
    ext i j
    rw [Matrix.mul_apply]
    simp only [hQβ, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    have hi := congrFun hxv i
    have h' : ∑ k, x i k * (v k * l j) = (x *ᵥ v) i * l j := by
      show _ = (∑ k, x i k * v k) * l j
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [h', hi]
    simp

end PI.TermsAtPtFiniteW
