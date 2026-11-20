import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

/- English proof (translation)
Introduce `Ω _ ε h N n₀ a z v hN ha h0`. Use `set g : ℕ → ℚ := fun k => (((n₀ + k : ℤ) : ℚ) / N) with hg`. Establish `hNq : (N : ℚ) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hinj : Function.Injective g`. Introduce `k l hkl`.

Simplify using `only [hg] at hkl`. Use `(div_left_inj' hNq).mp hkl` as an intermediate fact. Establish `h2 : ((n₀ + k : ℤ)) = n₀ + l` using `by exact_mod_cast this`. Use linear arithmetic over natural numbers and integers. Use `set f : ℚ → ℂ := fun r => ε (h.coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z) with hf`.

Establish `hzero : ∀ r, r ∉ Set.range g → f r = 0`. Introduce `r hr`. Establish `: ∀ k : ℕ, r ≠ ((n₀ + k : ℤ) : ℚ) / N`. Introduce `k hk`. Conclude with `hr ⟨k, hk.symm⟩`.

Simplify using `[hf, h0 r this]`. Use `set c : ℂ := Complex.exp (2 * Real.pi * Complex.I * n₀ * z / N) with hc`. Establish `hc0 : c ≠ 0` using `Complex.exp_ne_zero _`. Establish `hcomp : f ∘ g = fun k : ℕ => (ε (a k) * Complex.exp (2 * Real.pi * Complex.I * z / N) ^ k) * c`. Use function extensionality and compare the values at `k`.

Simplify using `only [Function.comp, hf, hg, ha k, hc]`. Rewrite using `[← Complex.exp_nat_mul, mul_assoc (ε (a k)), ← Complex.exp_add]`. Use `congr 2`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hinj.hasSum_iff hzero, hcomp]`. Establish `hv : v = (v * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N))) * c`. Rewrite using `[hc, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]`. Use `conv_lhs => rw [hv]`.

Conclude with `hasSum_mul_right_iff hc0`.
-/
theorem fn_hasSum_reindex_nat : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (h : HahnSeries ℚ Ω) (N : ℕ) (n₀ : ℤ) (a : ℕ → Ω) (z v : ℂ), 0 < N → (∀ k : ℕ, h.coeff (((n₀ + k : ℤ) : ℚ) / N) = a k) → (∀ r : ℚ, (∀ k : ℕ, r ≠ ((n₀ + k : ℤ) : ℚ) / N) → h.coeff r = 0) → (HasSum (fun r : ℚ => ε (h.coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) v ↔ HasSum (fun k : ℕ => ε (a k) * Complex.exp (2 * Real.pi * Complex.I * z / N) ^ k) (v * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N)))) := by
  intro Ω _ ε h N n₀ a z v hN ha h0
  set g : ℕ → ℚ := fun k => (((n₀ + k : ℤ) : ℚ) / N) with hg
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hinj : Function.Injective g := by
    intro k l hkl
    simp only [hg] at hkl
    have := (div_left_inj' hNq).mp hkl
    have h2 : ((n₀ + k : ℤ)) = n₀ + l := by exact_mod_cast this
    omega
  set f : ℚ → ℂ := fun r => ε (h.coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z) with hf
  have hzero : ∀ r, r ∉ Set.range g → f r = 0 := by
    intro r hr
    have : ∀ k : ℕ, r ≠ ((n₀ + k : ℤ) : ℚ) / N := by
      intro k hk; exact hr ⟨k, hk.symm⟩
    simp [hf, h0 r this]
  set c : ℂ := Complex.exp (2 * Real.pi * Complex.I * n₀ * z / N) with hc
  have hc0 : c ≠ 0 := Complex.exp_ne_zero _
  have hcomp : f ∘ g = fun k : ℕ => (ε (a k) * Complex.exp (2 * Real.pi * Complex.I * z / N) ^ k) * c := by
    funext k
    simp only [Function.comp, hf, hg, ha k, hc]
    rw [← Complex.exp_nat_mul, mul_assoc (ε (a k)), ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  rw [← hinj.hasSum_iff hzero, hcomp]
  have hv : v = (v * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N))) * c := by
    rw [hc, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  conv_lhs => rw [hv]
  exact hasSum_mul_right_iff hc0

end GlobalTheory
