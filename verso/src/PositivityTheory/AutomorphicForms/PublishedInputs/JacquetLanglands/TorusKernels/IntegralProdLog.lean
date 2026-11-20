import Mathlib

noncomputable section
open MeasureTheory

namespace UpperTheory.Esk.UnipotentIntegrandLemmas

/- English proof (translation)
Use `set ψ : I → I → ℝ → ℂ := fun w v t => (if v = w then (Real.log (1 + t ^ 2) : ℂ) else 1) * φ v t with hψ`. Establish `hψprod : ∀ (w : I) (x : I → ℝ), ∏ v, ψ w v (x v) = (Real.log (1 + x w ^ 2) : ℂ) * ∏ v, φ v (x v)`. Introduce `w x`. Simplify using `only [hψ, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]`. Establish `hψint : ∀ w v, Integrable (ψ w v)`.

Introduce `w v`. Distinguish the cases in `hv : v = w`. Simplify `(h w).2.1` using `[hψ, hv]`. Simplify `(h v).1` using `[hψ, hv]`. Establish `hP : Integrable (fun x : I → ℝ => ∏ v, φ v (x v))`.

Rewrite using `[volume_pi]`. Conclude with `Integrable.fintype_prod (fun v => (h v).1)`. Establish `hψP : ∀ w, Integrable (fun x : I → ℝ => ∏ v, ψ w v (x v))`. Introduce `w`. Rewrite using `[volume_pi]`.

Conclude with `Integrable.fintype_prod (fun v => hψint w v)`. Establish `hφzero : ∫ x : I → ℝ, ∏ v, φ v (x v) = 0`. Take `⟨v, -, -⟩` from `exists_pair_ne I`. Rewrite using `[integral_fintype_prod_volume_eq_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ v) (h v).2.2`.

Establish `hψzero : ∀ w, ∫ x : I → ℝ, ∏ v, ψ w v (x v) = 0`. Introduce `w`. Take `⟨v, hv⟩` from `exists_ne w`. Rewrite using `[integral_fintype_prod_volume_eq_prod]`. Use `Finset.prod_eq_zero (Finset.mem_univ v) ?_` and prove the remaining obligations.

Simplify `(h v).2.2` using `[hψ, hv]`. Establish `key : ∀ x : I → ℝ, (∏ v, φ v (x v)) * ((R * (C + ∑ v, Real.log (1 + x v ^ 2)) : ℝ) : ℂ) = (R * C : ℂ) * ∏ v, φ v (x v) + ∑ w, (R : ℂ) * ∏ v, ψ w v (x v)`. Introduce `x`. Simplify using `only [hψprod]`. Rewrite using `[← Finset.mul_sum, ← Finset.sum_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[key]`. Rewrite using `[integral_add (hP.const_mul _) (integrable_finset_sum _ fun w _ => (hψP w).const_mul _), integral_const_mul, hφzero, integral_finset_sum _ fun w _ => (hψP w).const_mul _]`. Simplify using `[integral_const_mul, hψzero]`.
-/
theorem integral_prod_log {I : Type} [Fintype I] [Nontrivial I] (φ : I → ℝ → ℂ)
    (h : ∀ v, Integrable (φ v) ∧ Integrable (fun x => (Real.log (1 + x ^ 2) : ℂ) * φ v x) ∧ ∫ x, φ v x = 0)
    (R C : ℝ) :
    ∫ x : I → ℝ, (∏ v, φ v (x v)) * ((R * (C + ∑ v, Real.log (1 + x v ^ 2)) : ℝ) : ℂ) = 0 := by
  classical
  set ψ : I → I → ℝ → ℂ := fun w v t =>
    (if v = w then (Real.log (1 + t ^ 2) : ℂ) else 1) * φ v t with hψ
  have hψprod : ∀ (w : I) (x : I → ℝ),
      ∏ v, ψ w v (x v) = (Real.log (1 + x w ^ 2) : ℂ) * ∏ v, φ v (x v) := by
    intro w x
    simp only [hψ, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  have hψint : ∀ w v, Integrable (ψ w v) := by
    intro w v
    by_cases hv : v = w
    · simpa [hψ, hv] using (h w).2.1
    · simpa [hψ, hv] using (h v).1
  have hP : Integrable (fun x : I → ℝ => ∏ v, φ v (x v)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (fun v => (h v).1)
  have hψP : ∀ w, Integrable (fun x : I → ℝ => ∏ v, ψ w v (x v)) := by
    intro w
    rw [volume_pi]
    exact Integrable.fintype_prod (fun v => hψint w v)
  have hφzero : ∫ x : I → ℝ, ∏ v, φ v (x v) = 0 := by
    obtain ⟨v, -, -⟩ := exists_pair_ne I
    rw [integral_fintype_prod_volume_eq_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ v) (h v).2.2
  have hψzero : ∀ w, ∫ x : I → ℝ, ∏ v, ψ w v (x v) = 0 := by
    intro w
    obtain ⟨v, hv⟩ := exists_ne w
    rw [integral_fintype_prod_volume_eq_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
    simpa [hψ, hv] using (h v).2.2
  have key : ∀ x : I → ℝ,
      (∏ v, φ v (x v)) * ((R * (C + ∑ v, Real.log (1 + x v ^ 2)) : ℝ) : ℂ)
        = (R * C : ℂ) * ∏ v, φ v (x v) + ∑ w, (R : ℂ) * ∏ v, ψ w v (x v) := by
    intro x
    simp only [hψprod]
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    push_cast
    ring
  simp_rw [key]
  rw [integral_add (hP.const_mul _) (integrable_finset_sum _ fun w _ => (hψP w).const_mul _),
    integral_const_mul, hφzero,
    integral_finset_sum _ fun w _ => (hψP w).const_mul _]
  simp [integral_const_mul, hψzero]

end UpperTheory.Esk.UnipotentIntegrandLemmas
