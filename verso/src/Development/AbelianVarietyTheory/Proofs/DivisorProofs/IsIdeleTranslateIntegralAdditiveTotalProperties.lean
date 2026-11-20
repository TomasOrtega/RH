import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.WpFam.TrAdd

open IsDedekindDomain GlobalTheory.Idele
open scoped nonZeroDivisors

/- English proof (translation)
Rewrite using `[mem_adelicIdeal_one_iff]`. Both sides reduce to the same expression.
-/
theorem tr_iff {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (x x' : K) :
    Tr t x x' ↔ (t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x ∈
      adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [mem_adelicIdeal_one_iff]; rfl

/- English proof (translation)
Introduce `K _ _ t`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x x' y y' hx hy`. Rewrite `*` using `[tr_iff]`. Use `sub_mem hx hy` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_sub]`. Expand and normalize the polynomial expressions, which then agree. Introduce `a x x' ha hx`. Rewrite `*` using `[tr_iff]`.

Set `b : 𝓞 K` to `⟨a, ha⟩`. Use `Submodule.smul_mem _ b hx` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `v`. Rewrite using `[adele_smul_apply]`.

Establish `: algebraMap (𝓞 K) K b = a` using `rfl`. Rewrite using `[this]`. Simplify using `only [adele_sub_apply, adele_mul_apply, adele_algebraMap_apply, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Introduce `x`.

Establish `hI : ((t⁻¹ : (Af K)ˣ) • (1 : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0` using `GlobalTheory.Idele.smul_ne_zero _ one_ne_zero`. Take `⟨x', hx'⟩` from `exists_sub_mem_adelicIdeal hI (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) x)`. Use `⟨x', ?_⟩` and prove the remaining obligations. Rewrite using `[tr_iff]`. Establish `e : ((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) x - algebraMap K (Af K) x' = ((t⁻¹ : (Af K)ˣ) : Af K) * -((t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x)`.

Rewrite using `[mul_neg, mul_sub, Units.inv_mul_cancel_left]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hx'` using `[e, mul_mem_adelicIdeal_smul]`. Simplify using `using neg_mem hx'`. Introduce `x'`.

Take `⟨x, hx⟩` from `exists_sub_mem_adelicIdeal (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K)) ((t : Af K) * algebraMap K (Af K) x')`. Conclude with `⟨x, (tr_iff t x x').2 hx⟩`.
-/
theorem main : ∀ (K : Type) [Field K] [NumberField K] (t : (Af K)ˣ), (∀ x x' y y' : K, Tr t x x' → Tr t y y' → Tr t (x - y) (x' - y')) ∧ (∀ (a x x' : K), IsIntegral ℤ a → Tr t x x' → Tr t (a * x) (a * x')) ∧ (∀ x : K, ∃ x', Tr t x x') ∧ (∀ x' : K, ∃ x, Tr t x x') := by
  intro K _ _ t
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x x' y y' hx hy
    rw [tr_iff] at *
    have := sub_mem hx hy
    convert this using 1
    simp only [map_sub]
    ring
  · intro a x x' ha hx
    rw [tr_iff] at *
    let b : 𝓞 K := ⟨a, ha⟩
    have := Submodule.smul_mem _ b hx
    convert this using 1
    ext v
    rw [adele_smul_apply]
    have : algebraMap (𝓞 K) K b = a := rfl
    rw [this]
    simp only [adele_sub_apply, adele_mul_apply, adele_algebraMap_apply, map_mul]
    ring
  · intro x
    have hI : ((t⁻¹ : (Af K)ˣ) • (1 : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 :=
      GlobalTheory.Idele.smul_ne_zero _ one_ne_zero
    obtain ⟨x', hx'⟩ := exists_sub_mem_adelicIdeal hI (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) x)
    refine ⟨x', ?_⟩
    rw [tr_iff]
    have e : ((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) x - algebraMap K (Af K) x' =
        ((t⁻¹ : (Af K)ˣ) : Af K) * -((t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x) := by
      rw [mul_neg, mul_sub, Units.inv_mul_cancel_left]
      ring
    rw [e, mul_mem_adelicIdeal_smul] at hx'
    simpa using neg_mem hx'
  · intro x'
    obtain ⟨x, hx⟩ := exists_sub_mem_adelicIdeal (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K))
      ((t : Af K) * algebraMap K (Af K) x')
    exact ⟨x, (tr_iff t x x').2 hx⟩

end GlobalTheory.WpFam.TrAdd
