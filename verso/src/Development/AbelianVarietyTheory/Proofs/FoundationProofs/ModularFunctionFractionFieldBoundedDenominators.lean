import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspExpansionCoeffMemFinitelyGeneratedSubringStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicSubringClosureCommonDenominatorStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesSubringCoeffMulInvMemStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOverStatement

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

/- English proof (translation)
Introduce `Ω _ _ _ ε T f`. Take `⟨a, b, hb, hab⟩` from `T.io_surj f`. Establish `hexpS : ∀ c : ring ε.range, ∃ S : Finset Ω, ∀ r, (T.exp (T.io c)).coeff r ∈ Subring.closure (S : Set Ω)`. Introduce `c`. Establish `hc : InR ε.range (c : ℍ → ℂ)` using `((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 c).1 c.2`.

Conclude with `GlobalTheory.T.cuspExpansion_coeff_mem_finitelyGenerated_subring Ω ε c _ hc (T.exp_io c)`. Take `⟨Sa, hSa⟩` from `hexpS a`. Take `⟨Sb, hSb⟩` from `hexpS b`. Establish `hiob : T.io b ≠ 0`. Introduce `h`.

Apply `hb` to reduce the goal to its premises. Apply `T.io_inj` to reduce the goal to its premises. Rewrite using `[h, map_zero]`. Establish `hexpb : T.exp (T.io b) ≠ 0`. Introduce `h`.

Apply `hiob` to reduce the goal to its premises. Conclude with `(injective_iff_map_eq_zero (T.exp : T.K →+* HahnSeries ℚ Ω)).1 (T.exp : T.K →+* HahnSeries ℚ Ω).injective _ h`. Establish `hf : T.exp f = T.exp (T.io a) * (T.exp (T.io b))⁻¹`. Rewrite using `[← hab, map_mul, mul_assoc, mul_inv_cancel₀ hexpb, mul_one]`. Set `S : Finset Ω` to `Sa ∪ Sb ∪ {(T.exp (T.io b)).leadingCoeff⁻¹}`.

Set `A : Subring Ω` to `Subring.closure (S : Set Ω)`. Establish `hA_a : ∀ r, (T.exp (T.io a)).coeff r ∈ A` using `fun r => Subring.closure_mono (by intro x hx; simp [S, hx]) (hSa r)`. Establish `hA_b : ∀ r, (T.exp (T.io b)).coeff r ∈ A` using `fun r => Subring.closure_mono (by intro x hx; simp [S, hx]) (hSb r)`. Establish `hA_l : (T.exp (T.io b)).leadingCoeff⁻¹ ∈ A` using `Subring.subset_closure (by simp [S])`. Establish `hP` using `GlobalTheory.T.hahnSeries_subring_coeff_mul_inv_mem Ω A`.

Establish `hA_inv` using `hP.2 _ hA_b hA_l`. Establish `hA_f : ∀ r, (T.exp f).coeff r ∈ A`. Introduce `r`. Rewrite using `[hf]`. Conclude with `hP.1 _ _ hA_a hA_inv r`.

Use `haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic`. Take `⟨D, hD, hDk⟩` from `GlobalTheory.T.algebraic_subring_closure_common_denominator Ω S`. Conclude with `⟨D, hD, fun r => hDk _ (hA_f r)⟩`.
-/
theorem frac_bdd_den : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K),
    ∃ D : ℕ, 0 < D ∧ ∀ r : ℚ, ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * (T.exp f).coeff r) := by
  intro Ω _ _ _ ε T f
  obtain ⟨a, b, hb, hab⟩ := T.io_surj f
  have hexpS : ∀ c : ring ε.range, ∃ S : Finset Ω, ∀ r, (T.exp (T.io c)).coeff r ∈ Subring.closure (S : Set Ω) := by
    intro c
    have hc : InR ε.range (c : ℍ → ℂ) := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 c).1 c.2
    exact GlobalTheory.T.cuspExpansion_coeff_mem_finitelyGenerated_subring Ω ε c _ hc (T.exp_io c)
  obtain ⟨Sa, hSa⟩ := hexpS a
  obtain ⟨Sb, hSb⟩ := hexpS b
  have hiob : T.io b ≠ 0 := by
    intro h
    apply hb
    apply T.io_inj
    rw [h, map_zero]
  have hexpb : T.exp (T.io b) ≠ 0 := by
    intro h
    apply hiob
    exact (injective_iff_map_eq_zero (T.exp : T.K →+* HahnSeries ℚ Ω)).1
      (T.exp : T.K →+* HahnSeries ℚ Ω).injective _ h
  have hf : T.exp f = T.exp (T.io a) * (T.exp (T.io b))⁻¹ := by
    rw [← hab, map_mul, mul_assoc, mul_inv_cancel₀ hexpb, mul_one]
  classical
  let S : Finset Ω := Sa ∪ Sb ∪ {(T.exp (T.io b)).leadingCoeff⁻¹}
  let A : Subring Ω := Subring.closure (S : Set Ω)
  have hA_a : ∀ r, (T.exp (T.io a)).coeff r ∈ A := fun r =>
    Subring.closure_mono (by intro x hx; simp [S, hx]) (hSa r)
  have hA_b : ∀ r, (T.exp (T.io b)).coeff r ∈ A := fun r =>
    Subring.closure_mono (by intro x hx; simp [S, hx]) (hSb r)
  have hA_l : (T.exp (T.io b)).leadingCoeff⁻¹ ∈ A := Subring.subset_closure (by simp [S])
  have hP := GlobalTheory.T.hahnSeries_subring_coeff_mul_inv_mem Ω A
  have hA_inv := hP.2 _ hA_b hA_l
  have hA_f : ∀ r, (T.exp f).coeff r ∈ A := by
    intro r
    rw [hf]
    exact hP.1 _ _ hA_a hA_inv r
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  obtain ⟨D, hD, hDk⟩ := GlobalTheory.T.algebraic_subring_closure_common_denominator Ω S
  exact ⟨D, hD, fun r => hDk _ (hA_f r)⟩

end GlobalTheory.FN
