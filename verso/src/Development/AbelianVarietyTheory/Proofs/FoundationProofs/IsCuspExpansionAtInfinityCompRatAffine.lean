import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem isExp_comp_affine : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f f' : ℍ → ℂ) (l m : ℚ) (h h' : HahnSeries ℚ Ω), 0 < l →
    (∀ z ∈ Hs, up f' z = up f ((l : ℂ) * z + m)) →
    (∀ r : ℚ, ε (h'.coeff (r * l)) = Complex.exp (2 * Real.pi * Complex.I * ((r * m : ℚ) : ℂ)) * ε (h.coeff r)) →
    IsExp ε f h → IsExp ε f' h' := by
  intro Ω _ ε f f' l m h h' hl hf hc hexp
  obtain ⟨⟨N, hN, hden⟩, C, hC⟩ := hexp
  have hl0 : l ≠ 0 := hl.ne'
  refine ⟨⟨N * l.den, Nat.mul_pos hN l.den_pos, ?_⟩, max (C / l) 0, ?_⟩
  · intro s hs
    have hr : h.coeff (s / l) ≠ 0 := by
      intro h0
      apply hs
      have := hc (s / l)
      rw [div_mul_cancel₀ _ hl0, h0, map_zero, mul_zero] at this
      exact (map_eq_zero ε).1 this
    obtain ⟨n, hn⟩ := hden _ hr
    refine ⟨n * l.num, ?_⟩
    have hs' : s = s / l * l := by field_simp
    have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    have hd0 : (l.den : ℚ) ≠ 0 := by exact_mod_cast l.den_pos.ne'
    rw [hs', hn]
    push_cast
    rw [← Rat.mul_den_eq_num l]
    field_simp
  · intro z hz
    have hz0 : 0 < z.im := lt_of_le_of_lt (le_max_right _ _) hz
    have hlz : C < ((l : ℂ) * z + (m : ℂ)).im := by
      have h1 : C / l < z.im := lt_of_le_of_lt (le_max_left _ _) hz
      have h2 : C < z.im * l := (div_lt_iff₀ (by exact_mod_cast hl)).1 h1
      simpa [mul_comm] using h2
    rw [hf z hz0]
    have key := hC _ hlz
    rw [← (Equiv.mulRight₀ l hl0).hasSum_iff]
    convert key using 1
    funext r
    have he : (Equiv.mulRight₀ l hl0) r = r * l := rfl
    simp only [Function.comp, he, hc r]
    rw [mul_comm (Complex.exp _) (ε (h.coeff r)), mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring

end GlobalTheory.FN
