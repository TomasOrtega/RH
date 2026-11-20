import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspExpansionDiscriminantIntegerLeadingOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHahnSeriesOfHasQStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

/- English proof (translation)
Introduce `Ω _ ε f hf`. Take `⟨N, w, hN, -, hq⟩` from `hf`. Take `⟨a, ha, hmem⟩` from `hq 1`. Use `choose b hb using fun n => (hmem n : a n ∈ ε.range)`. Establish `hg : HasQ N (fun τ => DD τ ^ w * f τ) (fun n => ε (b n))`.

Introduce `τ`. Use `ha τ` as an intermediate fact. Simplify using `only [one_smul] at this`. Simplify `this` using `only [hb]`. Take `⟨hg', hexg, -, -⟩` from `GlobalTheory.T.exists_hahnSeries_isExp_of_hasQ Ω ε N _ b hN hg`.

Take `⟨hD, hexD, hD0, -, -⟩` from `GlobalTheory.T.exists_cuspExpansion_discriminant_integer_leading_one Ω ε`. Take `⟨hring, -, hconst, -, hinv⟩` from `GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε`. Establish `hDi` using `hinv DD hD hD0 hexD`. Establish `hpow : ∀ k : ℕ, IsExp ε (DD⁻¹ ^ k) (hD⁻¹ ^ k)`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero`. Use `hconst 1` as an intermediate fact. Simplify using `only [map_one, HahnSeries.C_one] at this`. Rewrite using `[pow_zero, pow_zero]`.

Conclude with `this`. Consider the case `succ k ih`. Simplify `(hring _ _ _ _ ih hDi).2.2` using `[pow_succ]`. Establish `hprod` using `(hring _ _ _ _ hexg (hpow w)).2.2`. Use `⟨hg' * hD⁻¹ ^ w, ?_⟩` and prove the remaining obligations.

Use `hprod using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `τ`. Use `ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ` as an intermediate fact. Simplify using `only [Pi.mul_apply, Pi.pow_apply, Pi.inv_apply]`. Rewrite using `[inv_pow, mul_comm (DD τ ^ w), mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ this), mul_one]`.
-/
theorem exists_isExp : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f : ℍ → ℂ), InR ε.range f →
    ∃ h : HahnSeries ℚ Ω, IsExp ε f h := by
  intro Ω _ ε f hf
  obtain ⟨N, w, hN, -, hq⟩ := hf
  obtain ⟨a, ha, hmem⟩ := hq 1
  choose b hb using fun n => (hmem n : a n ∈ ε.range)
  have hg : HasQ N (fun τ => DD τ ^ w * f τ) (fun n => ε (b n)) := by
    intro τ
    have := ha τ
    simp only [one_smul] at this
    simpa only [hb] using this
  obtain ⟨hg', hexg, -, -⟩ := GlobalTheory.T.exists_hahnSeries_isExp_of_hasQ Ω ε N _ b hN hg
  obtain ⟨hD, hexD, hD0, -, -⟩ := GlobalTheory.T.exists_cuspExpansion_discriminant_integer_leading_one Ω ε
  obtain ⟨hring, -, hconst, -, hinv⟩ := GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε
  have hDi := hinv DD hD hD0 hexD
  have hpow : ∀ k : ℕ, IsExp ε (DD⁻¹ ^ k) (hD⁻¹ ^ k) := by
    intro k
    induction k with
    | zero =>
      have := hconst 1
      simp only [map_one, HahnSeries.C_one] at this
      rw [pow_zero, pow_zero]
      exact this
    | succ k ih =>
      simpa [pow_succ] using (hring _ _ _ _ ih hDi).2.2
  have hprod := (hring _ _ _ _ hexg (hpow w)).2.2
  refine ⟨hg' * hD⁻¹ ^ w, ?_⟩
  convert hprod using 1
  funext τ
  have := ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.inv_apply]
  rw [inv_pow, mul_comm (DD τ ^ w), mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ this), mul_one]

end GlobalTheory.FN
