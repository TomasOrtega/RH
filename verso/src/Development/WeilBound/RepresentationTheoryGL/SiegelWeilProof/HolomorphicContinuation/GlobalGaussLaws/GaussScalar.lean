import Mathlib

noncomputable section

open Complex MeasureTheory

namespace PositivityTheory.Rg.Sw.Glob.VacS

/- English proof (translation)
Establish `h` using `GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := ℂ) hb (I * ((2 * s : ℝ) : ℂ)) w`. Establish `hf : (Module.finrank ℝ ℂ : ℂ) / 2 = 1`. Rewrite using `[Complex.finrank_real_complex]`. Evaluate the numerical expressions. Rewrite `h` using `[hf, cpow_one]`.

Establish `e1 : ∀ y : ℂ, cexp (-b * ((‖y‖ ^ 2 : ℝ) : ℂ)) * cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ w) * y).re : ℂ)) = cexp (-b * (‖y‖ : ℂ) ^ 2 + I * ((2 * s : ℝ) : ℂ) * ((inner ℝ w y : ℝ) : ℂ))`. Introduce `y`. Rewrite using `[← Complex.exp_add, Complex.inner, mul_comm (starRingEnd ℂ w) y]`. Use `push_cast`. Put the polynomial expressions in normal form.

Repeatedly rewrite using `[e1]`. Rewrite using `[h]`. Use `congr 1`. Use `congr 1`. Use `push_cast`.

Establish `hb0 : b ≠ 0`. Introduce `h0`. Rewrite `hb` using `[h0]`. Simplify using `at hb`. Clear the denominators using the available nonvanishing facts.

Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gauss_scalar (b : ℂ) (hb : 0 < b.re) (s : ℝ) (w : ℂ) :
    ∫ y : ℂ, cexp (-b * ((‖y‖ ^ 2 : ℝ) : ℂ)) * cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ w) * y).re : ℂ)) =
      ((Real.pi : ℂ) / b) * cexp (-((s : ℂ) ^ 2) * ((‖w‖ ^ 2 : ℝ) : ℂ) / b) := by
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := ℂ) hb (I * ((2 * s : ℝ) : ℂ)) w
  have hf : (Module.finrank ℝ ℂ : ℂ) / 2 = 1 := by
    rw [Complex.finrank_real_complex]; norm_num
  rw [hf, cpow_one] at h
  have e1 : ∀ y : ℂ, cexp (-b * ((‖y‖ ^ 2 : ℝ) : ℂ)) * cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ w) * y).re : ℂ)) =
      cexp (-b * (‖y‖ : ℂ) ^ 2 + I * ((2 * s : ℝ) : ℂ) * ((inner ℝ w y : ℝ) : ℂ)) := by
    intro y
    rw [← Complex.exp_add, Complex.inner, mul_comm (starRingEnd ℂ w) y]
    push_cast
    ring_nf
  simp_rw [e1]
  rw [h]
  congr 1
  congr 1
  push_cast
  have hb0 : b ≠ 0 := by
    intro h0; rw [h0] at hb; simp at hb
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

def DG {m n : ℕ} (K : ℂ) (γ : Fin m → Fin n → ℂ) (v : Fin m → Fin n → ℂ) : ℂ :=
  K * ∏ a, ∏ j, cexp (-γ a j * ((‖v a j‖ ^ 2 : ℝ) : ℂ))

def ftG {m n : ℕ} (σ : Fin m → ℝ) (s : ℝ) (f : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  ∫ y : Fin m → Fin n → ℂ, f y *
    cexp (I * ((2 * s : ℝ) : ℂ) * ((∑ a, ∑ j, σ a * ((starRingEnd ℂ (u a j)) * y a j).re : ℝ) : ℂ))

/- English proof (translation)
Establish `hk : ∀ y : Fin m → Fin n → ℂ, DG K γ y * cexp (I * ((2 * s : ℝ) : ℂ) * ((∑ a, ∑ j, σ a * ((starRingEnd ℂ (u a j)) * y a j).re : ℝ) : ℂ)) = K * ∏ a, ∏ j, (cexp (-γ a j * ((‖y a j‖ ^ 2 : ℝ) : ℂ)) * cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * y a j).re : ℂ) …`. Introduce `y`. Unfold `DG`. Establish `e : cexp (I * ((2 * s : ℝ) : ℂ) * ((∑ a, ∑ j, σ a * ((starRingEnd ℂ (u a j)) * y a j).re : ℝ) : ℂ)) = ∏ a, ∏ j, cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * y a j).re : ℂ))`. Rewrite using `[Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]`.

Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `congr 2`. Rewrite using `[map_mul, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]`.

Apply the tactic sequence `all_goals (push_cast; try ring)`. Rewrite using `[e, mul_assoc, ← Finset.prod_mul_distrib]`. Use `congr 1`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib]`.

Unfold `ftG`. Repeatedly rewrite using `[hk]`. Rewrite using `[integral_const_mul]`. Establish `hI : ∫ y : Fin m → Fin n → ℂ, ∏ a, ∏ j, (cexp (-γ a j * ((‖y a j‖ ^ 2 : ℝ) : ℂ)) * cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * y a j).re : ℂ))) = ∏ a, ∏ j, (((Real.pi : ℂ) / γ a j) * cexp (-((s : ℂ) ^ 2) * ((‖(σ a : ℂ) * u a j‖ ^ 2 : ℝ) : ℂ) / γ a j))`. Rewrite using `[integral_fintype_prod_volume_eq_prod (f := fun a (x : Fin n → ℂ) => ∏ j, (cexp (-γ a j * ((‖x j‖ ^ 2 : ℝ) : ℂ)) * cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * x j).re : ℂ))))]`.

Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[integral_fintype_prod_volume_eq_prod (f := fun j (z : ℂ) => (cexp (-γ a j * ((‖z‖ ^ 2 : ℝ) : ℂ)) * cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * z).re : ℂ))))]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Conclude with `gauss_scalar _ (hγ a j) s _`. Rewrite using `[hI]`.

Unfold `DG`. Rewrite using `[mul_assoc]`. Use `congr 1`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `congr 1`. Use `congr 1`. Rewrite using `[norm_mul, Complex.norm_real]`.

Use `push_cast`. Establish `hg : γ a j ≠ 0`. Introduce `h0`. Use `hγ a j` as an intermediate fact. Rewrite `this` using `[h0]`.

Simplify using `at this`. Clear the denominators using the available nonvanishing facts. Rewrite using `[Real.norm_eq_abs]`. Establish `hs : ((|σ a| : ℝ) : ℂ) ^ 2 = ((σ a : ℝ) : ℂ) ^ 2`. Rewrite using `[← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]`.

Use `push_cast`. Rewrite using `[hs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ftG_DG {m n : ℕ} (σ : Fin m → ℝ) (s : ℝ) (K : ℂ) (γ : Fin m → Fin n → ℂ) (hγ : ∀ a j, 0 < (γ a j).re)
    (u : Fin m → Fin n → ℂ) :
    ftG σ s (DG K γ) u = DG (K * ∏ a, ∏ j, ((Real.pi : ℂ) / γ a j))
      (fun a j => (s : ℂ) ^ 2 * ((σ a : ℂ) ^ 2) / γ a j) u := by
  have hk : ∀ y : Fin m → Fin n → ℂ, DG K γ y *
      cexp (I * ((2 * s : ℝ) : ℂ) * ((∑ a, ∑ j, σ a * ((starRingEnd ℂ (u a j)) * y a j).re : ℝ) : ℂ)) =
      K * ∏ a, ∏ j, (cexp (-γ a j * ((‖y a j‖ ^ 2 : ℝ) : ℂ)) *
        cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * y a j).re : ℂ))) := by
    intro y
    unfold DG
    have e : cexp (I * ((2 * s : ℝ) : ℂ) * ((∑ a, ∑ j, σ a * ((starRingEnd ℂ (u a j)) * y a j).re : ℝ) : ℂ)) =
        ∏ a, ∏ j, cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * y a j).re : ℂ)) := by
      rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
      refine Finset.prod_congr rfl fun j _ => ?_
      congr 2
      rw [map_mul, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]
      all_goals (push_cast; try ring)
    rw [e, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← Finset.prod_mul_distrib]
  unfold ftG
  simp_rw [hk]
  rw [integral_const_mul]
  have hI : ∫ y : Fin m → Fin n → ℂ, ∏ a, ∏ j, (cexp (-γ a j * ((‖y a j‖ ^ 2 : ℝ) : ℂ)) *
        cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * y a j).re : ℂ))) =
      ∏ a, ∏ j, (((Real.pi : ℂ) / γ a j) * cexp (-((s : ℂ) ^ 2) * ((‖(σ a : ℂ) * u a j‖ ^ 2 : ℝ) : ℂ) / γ a j)) := by
    rw [integral_fintype_prod_volume_eq_prod (f := fun a (x : Fin n → ℂ) => ∏ j, (cexp (-γ a j * ((‖x j‖ ^ 2 : ℝ) : ℂ)) *
        cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * x j).re : ℂ))))]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [integral_fintype_prod_volume_eq_prod (f := fun j (z : ℂ) => (cexp (-γ a j * ((‖z‖ ^ 2 : ℝ) : ℂ)) *
        cexp (I * ((2 * s : ℝ) : ℂ) * (((starRingEnd ℂ ((σ a : ℂ) * u a j)) * z).re : ℂ))))]
    refine Finset.prod_congr rfl fun j _ => ?_
    exact gauss_scalar _ (hγ a j) s _
  rw [hI]
  unfold DG
  rw [mul_assoc]
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  congr 1
  rw [norm_mul, Complex.norm_real]
  push_cast
  have hg : γ a j ≠ 0 := by
    intro h0; have := hγ a j; rw [h0] at this; simp at this
  field_simp
  rw [Real.norm_eq_abs]
  have hs : ((|σ a| : ℝ) : ℂ) ^ 2 = ((σ a : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]
  push_cast
  rw [hs]
  ring

end PositivityTheory.Rg.Sw.Glob.VacS
