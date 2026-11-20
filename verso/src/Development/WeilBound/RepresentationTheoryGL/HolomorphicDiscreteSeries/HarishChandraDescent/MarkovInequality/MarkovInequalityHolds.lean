import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Descent

noncomputable section

open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

/- English proof (translation)
Introduce `M _ _ u Z R hu hR hZ hpos x hx`. Establish `e : ∀ (r : ℝ) (y : M), r • y = (r : ℂ) • y` using `fun r y => (RCLike.real_smul_eq_coe_smul (K := ℂ) r y)`. Establish `hv : u x ∈ Z` using `hZ x hx`. Establish `hw : u (u x) ∈ Z` using `hZ _ hv`. Establish `h1` using `hpos (x - (R⁻¹ : ℂ) • u x) (Z.sub_mem hx (Z.smul_mem _ hv))`.

Establish `h2` using `hpos (u x - (R⁻¹ : ℂ) • u (u x)) (Z.sub_mem hv (Z.smul_mem _ hw))`. Simplify using `only [e, map_add, map_sub, map_smul, add_sub_cancel_left, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_ …`. Rewrite `*` using `[hu (u x) x, hu (u (u x)) x, ← hu (u x) (u x)]`. Rewrite `h2` using `[hu (u (u x)) (u x)]`. Generalize the expression as in `(⟪u x, x⟫_ℂ).re = p at *`.

Generalize the expression as in `(⟪u x, u x⟫_ℂ).re = a at *`. Generalize the expression as in `(⟪u (u x), u x⟫_ℂ).re = q at *`. Generalize the expression as in `(⟪u (u x), u (u x)⟫_ℂ).re = b at *`. Generalize the expression as in `(⟪u (u (u x)), u (u x)⟫_ℂ).re = r at *`. Establish `hR0 : R ≠ 0` using `hR.ne'`.

Rewrite using `[le_div_iff₀ (by positivity)]`. Establish `hs : R⁻¹ * R = 1` using `inv_mul_cancel₀ hR0`. Establish `hc : (R ^ 2)⁻¹ = R⁻¹ ^ 2` using `(inv_pow R 2).symm`. Rewrite using `[hc]`. Establish `key : p + R⁻¹ ^ 2 * q + R⁻¹ ^ 2 * (q + R⁻¹ ^ 2 * r) - (R⁻¹ ^ 2 * a + R⁻¹ ^ 2 * (R⁻¹ ^ 2 * b)) * (2 * R) = (p - R⁻¹ * a - R⁻¹ * (a - R⁻¹ * q)) + R⁻¹ ^ 2 * (q - R⁻¹ * b - R⁻¹ * (b - R⁻¹ * r))`.

Take the linear combination `(-(2 * R⁻¹ * a + 2 * R⁻¹ ^ 3 * b)) * hs`. Use polynomial arithmetic with `[mul_nonneg (sq_nonneg R⁻¹) h2]`.
-/
theorem markov_inequality_holds : Markov := by
  intro M _ _ u Z R hu hR hZ hpos x hx
  have e : ∀ (r : ℝ) (y : M), r • y = (r : ℂ) • y := fun r y =>
    (RCLike.real_smul_eq_coe_smul (K := ℂ) r y)
  have hv : u x ∈ Z := hZ x hx
  have hw : u (u x) ∈ Z := hZ _ hv
  have h1 := hpos (x - (R⁻¹ : ℂ) • u x) (Z.sub_mem hx (Z.smul_mem _ hv))
  have h2 := hpos (u x - (R⁻¹ : ℂ) • u (u x)) (Z.sub_mem hv (Z.smul_mem _ hw))
  simp only [e, map_add, map_sub, map_smul, add_sub_cancel_left, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, ← Complex.ofReal_inv] at h1 h2 ⊢
  rw [hu (u x) x, hu (u (u x)) x, ← hu (u x) (u x)] at *
  rw [hu (u (u x)) (u x)] at h2
  generalize (⟪u x, x⟫_ℂ).re = p at *
  generalize (⟪u x, u x⟫_ℂ).re = a at *
  generalize (⟪u (u x), u x⟫_ℂ).re = q at *
  generalize (⟪u (u x), u (u x)⟫_ℂ).re = b at *
  generalize (⟪u (u (u x)), u (u x)⟫_ℂ).re = r at *
  have hR0 : R ≠ 0 := hR.ne'
  rw [le_div_iff₀ (by positivity)]
  have hs : R⁻¹ * R = 1 := inv_mul_cancel₀ hR0
  have hc : (R ^ 2)⁻¹ = R⁻¹ ^ 2 := (inv_pow R 2).symm
  rw [hc]
  have key : p + R⁻¹ ^ 2 * q + R⁻¹ ^ 2 * (q + R⁻¹ ^ 2 * r)
      - (R⁻¹ ^ 2 * a + R⁻¹ ^ 2 * (R⁻¹ ^ 2 * b)) * (2 * R)
      = (p - R⁻¹ * a - R⁻¹ * (a - R⁻¹ * q))
        + R⁻¹ ^ 2 * (q - R⁻¹ * b - R⁻¹ * (b - R⁻¹ * r)) := by
    linear_combination (-(2 * R⁻¹ * a + 2 * R⁻¹ ^ 3 * b)) * hs
  nlinarith [mul_nonneg (sq_nonneg R⁻¹) h2]

end PositivityTheory.RgHe3
