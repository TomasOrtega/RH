import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicTraceGeWhittakerDimensionGLnStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotentsPropertiesPrimeFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTraceIdempotentAndIrreducibleDegree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIrrCharactersAndFinsumCentralIdempotentsEq
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.LowerWt

/- English proof (translation)
Unfold `eSerC`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]`. Simplify using `only [MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]`. Use `Finset.sum_congr rfl fun χ _ => ?_` and prove the remaining obligations. Conclude with `((GlobalTheory.GLq.trIdem (Gn g N) a χ).2.2)`.
-/
theorem coeff_mul_eSerC {g : ℕ} [Fact g.Prime] (L : LabelDatum g) {N : ℕ} (f : (ZMod g)[X])
    (a : MonoidAlgebra ℂ (Gn g N))
    (hfin : {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite) :
    (a * eSerC L N f).coeff 1 = ∑ χ ∈ hfin.toFinset, χ 1 / (Fintype.card (Gn g N) : ℂ) * tr a χ := by
  unfold eSerC
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun χ _ => ?_
  exact ((GlobalTheory.GLq.trIdem (Gn g N) a χ).2.2)

/- English proof (translation)
Rewrite using `[coeff_mul_eSerC L f a hfin, Complex.re_sum]`. Use `Finset.sum_congr rfl fun χ hχ => ?_` and prove the remaining obligations. Establish `hI : IsIrr χ` using `((Set.Finite.mem_toFinset hfin).1 hχ).1`. Take `⟨d, -, hd⟩` from `(GlobalTheory.GLq.trIdem (Gn g N) a χ).2.1 hI`. Rewrite using `[hd]`.

Establish `: (d : ℂ) / (Fintype.card (Gn g N) : ℂ) = (((d : ℝ) / (Fintype.card (Gn g N) : ℝ) : ℝ) : ℂ)` using `by push_cast; rfl`. Rewrite using `[this, Complex.re_ofReal_mul]`. Simplify using the standard rewrite rules.
-/
theorem re_coeff_mul_eSerC {g : ℕ} [Fact g.Prime] (L : LabelDatum g) {N : ℕ} (f : (ZMod g)[X])
    (a : MonoidAlgebra ℂ (Gn g N))
    (hfin : {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite) :
    ((a * eSerC L N f).coeff 1).re =
      ∑ χ ∈ hfin.toFinset, (χ 1).re / (Fintype.card (Gn g N) : ℝ) * (tr a χ).re := by
  rw [coeff_mul_eSerC L f a hfin, Complex.re_sum]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  have hI : IsIrr χ := ((Set.Finite.mem_toFinset hfin).1 hχ).1
  obtain ⟨d, -, hd⟩ := (GlobalTheory.GLq.trIdem (Gn g N) a χ).2.1 hI
  rw [hd]
  have : (d : ℂ) / (Fintype.card (Gn g N) : ℂ) = (((d : ℝ) / (Fintype.card (Gn g N) : ℝ) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [this, Complex.re_ofReal_mul]
  simp

/- English proof (translation)
Establish `hI : IsIrr χ` using `((Set.Finite.mem_toFinset hfin).1 hχ).1`. Take `⟨d, -, hd⟩` from `(GlobalTheory.GLq.trIdem (Gn g N) (1 : MonoidAlgebra ℂ (Gn g N)) χ).2.1 hI`. Rewrite using `[hd]`. Simplify using `only [Complex.natCast_re]`. Check the signs of the components of the expression.
-/
theorem weight_nonneg {g : ℕ} [Fact g.Prime] (L : LabelDatum g) {N : ℕ} (f : (ZMod g)[X])
    (hfin : {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite) (χ : Gn g N → ℂ) (hχ : χ ∈ hfin.toFinset) :
    0 ≤ (χ 1).re / (Fintype.card (Gn g N) : ℝ) := by
  have hI : IsIrr χ := ((Set.Finite.mem_toFinset hfin).1 hχ).1
  obtain ⟨d, -, hd⟩ := (GlobalTheory.GLq.trIdem (Gn g N) (1 : MonoidAlgebra ℂ (Gn g N)) χ).2.1 hI
  rw [hd]
  simp only [Complex.natCast_re]
  positivity

end GlobalTheory.GLq.LowerWt

/- English proof (translation)
Introduce `g _ L ψ hψ N k s hN hk f`. Establish `hL8` using `GlobalTheory.T.mirabolic_trace_ge_whittakerDimension_GLn g ψ hψ N k s hN hk`. Take `⟨-, hU1, hJ, -⟩` from `GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g N k s ψ`. Take `⟨-, hJ1⟩` from `hJ hN`. Establish `hfin : {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite` using `(irr_finite_and_finsum_zOf_eq_one (Gn g N)).1.subset fun χ h => h.1`.

Use `set T := hfin.toFinset`. Use `set c : (Gn g N → ℂ) → ℝ := fun χ => (χ 1).re / (Fintype.card (Gn g N) : ℝ) with hc`. Use `set A := ∑ χ ∈ T, c χ * (tr (eU g N ψ) χ).re with hA`. Use `set B := ∑ χ ∈ T, c χ * (tr (eJ g N k s ψ) χ).re with hB`. Establish `hAeq : ((eU g N ψ * eSerC L N f).coeff 1).re = A` using `LowerWt.re_coeff_mul_eSerC L f _ hfin`.

Establish `hBeq : ((eJ g N k s ψ * eSerC L N f).coeff 1).re = B` using `LowerWt.re_coeff_mul_eSerC L f _ hfin`. Establish `hG : (0 : ℝ) < g` using `by exact_mod_cast (Fact.out : g.Prime).pos`. Use `set M := N * (N - 1) / 2`. Establish `hU1r : ((eU g N ψ).coeff 1).re = ((g : ℝ) ^ M)⁻¹`. Rewrite using `[hU1]`.

Establish `: ((g : ℂ) ^ M)⁻¹ = ((((g : ℝ) ^ M)⁻¹ : ℝ) : ℂ)` using `by push_cast; rfl`. Rewrite using `[this, Complex.ofReal_re]`. Establish `hJ1r : ((eJ g N k s ψ).coeff 1).re = (g : ℝ) ^ k * ((g : ℝ) ^ M)⁻¹`. Rewrite using `[hJ1]`. Establish `: (g : ℂ) ^ k * ((g : ℂ) ^ M)⁻¹ = ((((g : ℝ) ^ k * ((g : ℝ) ^ M)⁻¹) : ℝ) : ℂ)` using `by push_cast; rfl`.

Rewrite using `[this, Complex.ofReal_re]`. Establish `hBA : ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * A ≤ B`. Rewrite using `[hA, hB, Finset.mul_sum]`. Use `Finset.sum_le_sum fun χ hχ => ?_` and prove the remaining obligations. Establish `h0 : 0 ≤ c χ` using `LowerWt.weight_nonneg L f hfin χ hχ`.

Establish `hI : IsIrr χ` using `((Set.Finite.mem_toFinset hfin).1 hχ).1`. Establish `hC : IsChar χ` using `by obtain ⟨V, -, hV⟩ := hI; exact ⟨V, hV⟩`. Establish `h8` using `hL8 χ hC`. Unfold `wh at h8`. Combine the equalities or inequalities in the displayed calculation.

Establish `hpow : (g : ℝ) ^ k - (g : ℝ) ^ (k - 1) = (g : ℝ) ^ k * (1 - 1 / (g : ℝ))`. Take `⟨j, rfl⟩ : ∃ j, k = j + 1` from `⟨k - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel, pow_succ]`. Clear the denominators using the available nonvanishing facts. Unfold `wtC`.

Rewrite using `[hAeq, hBeq, hU1r, hJ1r]`. Establish `hgk : (0 : ℝ) < (g : ℝ) ^ k` using `pow_pos hG k`. Establish `hgM : (0 : ℝ) < (g : ℝ) ^ M` using `pow_pos hG M`. Rewrite `hBA` using `[hpow]`. Rewrite using `[div_inv_eq_mul, le_div_iff₀ (mul_pos hgk (inv_pos.2 hgM))]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem GlobalTheory.GLq.lowerWtComparison : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 →
    ∀ (N k s : ℕ), N = k + 2 * s + 1 → 1 ≤ k →
      ∀ f, (1 - 1 / (g : ℝ)) * wtC L (eU g N ψ) f ≤ wtC L (eJ g N k s ψ) f := by
  intro g _ L ψ hψ N k s hN hk f
  have hL8 := GlobalTheory.T.mirabolic_trace_ge_whittakerDimension_GLn g ψ hψ N k s hN hk
  obtain ⟨-, hU1, hJ, -⟩ := GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g N k s ψ
  obtain ⟨-, hJ1⟩ := hJ hN
  have hfin : {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite :=
    (irr_finite_and_finsum_zOf_eq_one (Gn g N)).1.subset fun χ h => h.1
  set T := hfin.toFinset
  set c : (Gn g N → ℂ) → ℝ := fun χ => (χ 1).re / (Fintype.card (Gn g N) : ℝ) with hc
  set A := ∑ χ ∈ T, c χ * (tr (eU g N ψ) χ).re with hA
  set B := ∑ χ ∈ T, c χ * (tr (eJ g N k s ψ) χ).re with hB
  have hAeq : ((eU g N ψ * eSerC L N f).coeff 1).re = A := LowerWt.re_coeff_mul_eSerC L f _ hfin
  have hBeq : ((eJ g N k s ψ * eSerC L N f).coeff 1).re = B := LowerWt.re_coeff_mul_eSerC L f _ hfin
  have hG : (0 : ℝ) < g := by exact_mod_cast (Fact.out : g.Prime).pos
  set M := N * (N - 1) / 2
  have hU1r : ((eU g N ψ).coeff 1).re = ((g : ℝ) ^ M)⁻¹ := by
    rw [hU1]
    have : ((g : ℂ) ^ M)⁻¹ = ((((g : ℝ) ^ M)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.ofReal_re]
  have hJ1r : ((eJ g N k s ψ).coeff 1).re = (g : ℝ) ^ k * ((g : ℝ) ^ M)⁻¹ := by
    rw [hJ1]
    have : (g : ℂ) ^ k * ((g : ℂ) ^ M)⁻¹ = ((((g : ℝ) ^ k * ((g : ℝ) ^ M)⁻¹) : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.ofReal_re]
  have hBA : ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * A ≤ B := by
    rw [hA, hB, Finset.mul_sum]
    refine Finset.sum_le_sum fun χ hχ => ?_
    have h0 : 0 ≤ c χ := LowerWt.weight_nonneg L f hfin χ hχ
    have hI : IsIrr χ := ((Set.Finite.mem_toFinset hfin).1 hχ).1
    have hC : IsChar χ := by obtain ⟨V, -, hV⟩ := hI; exact ⟨V, hV⟩
    have h8 := hL8 χ hC
    unfold wh at h8
    calc ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * (c χ * (tr (eU g N ψ) χ).re)
        = c χ * (((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * (tr (eU g N ψ) χ).re) := by ring
      _ ≤ c χ * (tr (eJ g N k s ψ) χ).re := mul_le_mul_of_nonneg_left h8 h0
  have hpow : (g : ℝ) ^ k - (g : ℝ) ^ (k - 1) = (g : ℝ) ^ k * (1 - 1 / (g : ℝ)) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    field_simp
  unfold wtC
  rw [hAeq, hBeq, hU1r, hJ1r]
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := pow_pos hG k
  have hgM : (0 : ℝ) < (g : ℝ) ^ M := pow_pos hG M
  rw [hpow] at hBA
  rw [div_inv_eq_mul, le_div_iff₀ (mul_pos hgk (inv_pos.2 hgM))]
  calc (1 - 1 / (g : ℝ)) * (A * (g : ℝ) ^ M) * ((g : ℝ) ^ k * ((g : ℝ) ^ M)⁻¹)
      = (g : ℝ) ^ k * (1 - 1 / (g : ℝ)) * A * ((g : ℝ) ^ M * ((g : ℝ) ^ M)⁻¹) := by ring
    _ = (g : ℝ) ^ k * (1 - 1 / (g : ℝ)) * A := by rw [mul_inv_cancel₀ hgM.ne', mul_one]
    _ ≤ B := hBA
