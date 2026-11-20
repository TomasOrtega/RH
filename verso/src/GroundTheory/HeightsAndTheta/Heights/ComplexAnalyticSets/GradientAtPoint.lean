import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace GradientAtPoint

variable {σ : Type*} (w : σ → ℂ)

def grad : MvPolynomial σ ℂ →ₗ[ℂ] (σ → ℂ) :=
  LinearMap.pi fun i => (aeval w).toLinearMap ∘ₗ (pderiv i : Derivation ℂ (MvPolynomial σ ℂ) _).toLinearMap

/- English proof (translation)
Simplify using `[grad]`.
-/
theorem grad_apply (p : MvPolynomial σ ℂ) (i : σ) : grad w p i = eval w (pderiv i p) := by
  simp [grad]

/- English proof (translation)
Use extensionality with `i`. Simplify using `only [grad_apply, Derivation.leibniz, smul_eq_mul, map_add, map_mul, Pi.add_apply, Pi.smul_apply]`.
-/
theorem grad_mul (a b : MvPolynomial σ ℂ) :
    grad w (a * b) = eval w a • grad w b + eval w b • grad w a := by
  ext i
  simp only [grad_apply, Derivation.leibniz, smul_eq_mul, map_add, map_mul, Pi.add_apply, Pi.smul_apply]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[grad_apply]`.
-/
theorem grad_C (c : ℂ) : grad w (C c : MvPolynomial σ ℂ) = 0 := by
  ext i
  simp [grad_apply]

/- English proof (translation)
Use extensionality with `i`. Rewrite using `[grad_apply, map_sub, pderiv_C, sub_zero, pderiv_X]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h, Ne.symm h]`.
-/
theorem grad_X_sub_C [DecidableEq σ] (j : σ) : grad w (X j - C (w j)) = Pi.single j 1 := by
  ext i
  rw [grad_apply, map_sub, pderiv_C, sub_zero, pderiv_X]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

/- English proof (translation)
Rewrite using `[grad_mul, hp, zero_smul, add_zero]`.
-/
theorem grad_mul_of_eval_eq_zero (r p : MvPolynomial σ ℂ) (hp : eval w p = 0) :
    grad w (r * p) = eval w r • grad w p := by
  rw [grad_mul, hp, zero_smul, add_zero]

def linPart [Fintype σ] (c : σ → ℂ) : MvPolynomial σ ℂ :=
  ∑ i, C (c i) * (X i - C (w i))

/- English proof (translation)
Simplify using `[linPart]`.
-/
theorem eval_linPart [Fintype σ] (c : σ → ℂ) : eval w (linPart w c) = 0 := by
  simp [linPart]

/- English proof (translation)
Use extensionality with `i`. Rewrite using `[linPart, map_sum, Finset.sum_apply]`. Simplify using `[grad_mul, grad_C, grad_X_sub_C, Pi.single_apply]`.
-/
theorem grad_linPart [Fintype σ] (c : σ → ℂ) : grad w (linPart w c) = c := by
  classical
  ext i
  rw [linPart, map_sum, Finset.sum_apply]
  simp [grad_mul, grad_C, grad_X_sub_C, Pi.single_apply]

/- English proof (translation)
Rewrite using `[linPart, Finset.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules.
-/
theorem linPart_single [Fintype σ] [DecidableEq σ] (j : σ) : linPart w (Pi.single j 1) = X j - C (w j) := by
  rw [linPart, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq`. Rewrite using `[map_add, map_add, show p + q - (C (eval w p) + C (eval w q)) = (p - C (eval w p)) + (q - C (eval w q)) by ring]`. Conclude with `Ideal.add_mem _ hp hq`.

Consider the case `mul_X p i hp`. Rewrite using `[map_mul, eval_X, map_mul, show p * X i - C (eval w p) * C (w i) = (p - C (eval w p)) * X i + C (eval w p) * (X i - C (w i)) by ring]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))`.
-/
theorem sub_C_eval_mem_span (p : MvPolynomial σ ℂ) :
    p - C (eval w p) ∈ Ideal.span (Set.range fun i => (X i - C (w i) : MvPolynomial σ ℂ)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add, map_add, show p + q - (C (eval w p) + C (eval w q)) = (p - C (eval w p)) + (q - C (eval w q)) by
      ring]
    exact Ideal.add_mem _ hp hq
  | mul_X p i hp =>
    rw [map_mul, eval_X, map_mul,
      show p * X i - C (eval w p) * C (w i) = (p - C (eval w p)) * X i + C (eval w p) * (X i - C (w i)) by ring]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp)
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `p hp`. Establish `h` using `sub_C_eval_mem_span w p`. Rewrite `h` using `[RingHom.mem_ker.1 hp, map_zero, sub_zero]`. Then use the resulting hypothesis. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Simplify using `[RingHom.mem_ker]`.
-/
theorem ker_eval_eq_span :
    RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) =
      Ideal.span (Set.range fun i => (X i - C (w i) : MvPolynomial σ ℂ)) := by
  apply le_antisymm
  · intro p hp
    have h := sub_C_eval_mem_span w p
    rwa [RingHom.mem_ker.1 hp, map_zero, sub_zero] at h
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker]

/- English proof (translation)
Rewrite `hp` using `[pow_two]`. Use `Submodule.mul_induction_on hp (fun a ha b hb => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations. Rewrite using `[grad_mul, RingHom.mem_ker.1 ha, RingHom.mem_ker.1 hb, zero_smul, zero_smul, add_zero]`. Rewrite using `[map_add, hx, hy, add_zero]`.
-/
theorem grad_eq_zero_of_mem_sq {p : MvPolynomial σ ℂ}
    (hp : p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) ^ 2) : grad w p = 0 := by
  rw [pow_two] at hp
  refine Submodule.mul_induction_on hp (fun a ha b hb => ?_) (fun x y hx hy => ?_)
  · rw [grad_mul, RingHom.mem_ker.1 ha, RingHom.mem_ker.1 hb, zero_smul, zero_smul, add_zero]
  · rw [map_add, hx, hy, add_zero]

/- English proof (translation)
Rewrite `hp` using `[ker_eval_eq_span]`. Take `⟨a, rfl⟩` from `(Ideal.mem_span_range_iff_exists_fun).1 hp`. Establish `hg : grad w (∑ i, a i * (X i - C (w i))) = fun i => eval w (a i)`. Rewrite using `[map_sum]`. Repeatedly rewrite using `[grad_mul, grad_X_sub_C, map_sub, eval_X, eval_C, sub_self, zero_smul, add_zero]`.

Use extensionality with `i`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[hg, linPart, ← Finset.sum_sub_distrib]`. Use `Ideal.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← sub_mul, pow_two]`.

Use `Ideal.mul_mem_mul ?_ ?_` and prove the remaining obligations. Simplify using `[RingHom.mem_ker]`. Simplify using `[RingHom.mem_ker]`.
-/
theorem sub_linPart_mem_sq [Fintype σ] {p : MvPolynomial σ ℂ}
    (hp : p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) :
    p - linPart w (grad w p) ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) ^ 2 := by
  classical
  rw [ker_eval_eq_span] at hp
  obtain ⟨a, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hp
  have hg : grad w (∑ i, a i * (X i - C (w i))) = fun i => eval w (a i) := by
    rw [map_sum]
    simp_rw [grad_mul, grad_X_sub_C, map_sub, eval_X, eval_C, sub_self, zero_smul, add_zero]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hg, linPart, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [← sub_mul, pow_two]
  refine Ideal.mul_mem_mul ?_ ?_
  · simp [RingHom.mem_ker]
  · simp [RingHom.mem_ker]

/- English proof (translation)
Establish `h` using `sub_linPart_mem_sq w hp`. Rewrite `h` using `[hg, linPart, Finset.sum_eq_zero (fun i _ => by simp), sub_zero]`. Then use the resulting hypothesis.
-/
theorem mem_sq_of_grad_eq_zero [Fintype σ] {p : MvPolynomial σ ℂ}
    (hp : p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) (hg : grad w p = 0) :
    p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) ^ 2 := by
  have h := sub_linPart_mem_sq w hp
  rwa [hg, linPart, Finset.sum_eq_zero (fun i _ => by simp), sub_zero] at h

end GradientAtPoint

end

end GroundTheory.Heights₂.Heights
