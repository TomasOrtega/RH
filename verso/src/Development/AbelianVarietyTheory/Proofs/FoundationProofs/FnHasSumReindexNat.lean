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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
