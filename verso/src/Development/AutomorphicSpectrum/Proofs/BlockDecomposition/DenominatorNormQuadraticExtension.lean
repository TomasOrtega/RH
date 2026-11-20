import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix nonZeroDivisors

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem mem_den_iff {K : Type} [Field K] [NumberField K] (x : K) (a : 𝓞 K) :
    a ∈ HS.den K x ↔ ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = algebraMap (𝓞 K) K a * x := by
  rw [HS.den, Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  show (∀ i : Fin 1, ∃ o, algebraMap (𝓞 K) K o = (a • fun _ : Fin 1 => x) i) ↔ _
  simp only [Pi.smul_apply, Algebra.smul_def]
  exact ⟨fun h => h 0, fun h _ => h⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem exists_bezout {K : Type} [Field K] [NumberField K] (x : K) :
    ∃ a ∈ HS.den K x, ∃ c ∈ HS.den K x,
      algebraMap (𝓞 K) K a + algebraMap (𝓞 K) K c * x = 1 := by
  classical
  obtain ⟨S, hSdef⟩ : ∃ S : FractionalIdeal (𝓞 K)⁰ K,
      S = FractionalIdeal.spanSingleton (𝓞 K)⁰ (1 : K) ⊔ FractionalIdeal.spanSingleton (𝓞 K)⁰ x :=
    ⟨_, rfl⟩
  have h1S : (1 : K) ∈ S := by
    rw [hSdef]; exact (le_sup_left : FractionalIdeal.spanSingleton (𝓞 K)⁰ (1 : K) ≤ _)
      (FractionalIdeal.mem_spanSingleton_self _ _)
  have hxS : x ∈ S := by
    rw [hSdef]; exact (le_sup_right : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≤ _)
      (FractionalIdeal.mem_spanSingleton_self _ _)
  have hS : S ≠ 0 := by
    intro h
    rw [h] at h1S
    exact one_ne_zero ((FractionalIdeal.mem_zero_iff _).1 h1S)
  have hden : ∀ t ∈ S⁻¹, ∃ a ∈ HS.den K x, algebraMap (𝓞 K) K a = t := by
    intro t ht
    rw [FractionalIdeal.mem_inv_iff hS] at ht
    have ht1 : t ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
      have := ht 1 h1S
      rwa [mul_one] at this
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).1 ht1
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).1 (ht x hxS)
    exact ⟨a, (mem_den_iff x a).2 ⟨o, by rw [ho, ha]⟩, ha⟩
  have hsplit : ∀ T : FractionalIdeal (𝓞 K)⁰ K, S * T = FractionalIdeal.spanSingleton (𝓞 K)⁰ (1 : K) * T ⊔
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x * T := by
    intro T
    rw [hSdef, FractionalIdeal.sup_eq_add, FractionalIdeal.sup_eq_add, add_mul]
  have h1 : (1 : K) ∈ S * S⁻¹ := by
    rw [mul_inv_cancel₀ hS]; exact FractionalIdeal.one_mem_one _
  rw [hsplit S⁻¹, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_sup, Submodule.mem_sup] at h1
  obtain ⟨u, hu, v, hv, huv⟩ := h1
  rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul] at hu hv
  obtain ⟨u', hu', rfl⟩ := hu
  obtain ⟨v', hv', rfl⟩ := hv
  obtain ⟨a, ha, ha'⟩ := hden u' hu'
  obtain ⟨c, hc, hc'⟩ := hden v' hv'
  refine ⟨a, ha, c, hc, ?_⟩
  rw [ha', hc', ← huv]
  ring

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem den_algebraMap (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (x : F) :
    HS.den E (algebraMap F E x) = Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (HS.den F x) := by
  have tower : ∀ o : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) o) =
      algebraMap F E (algebraMap (𝓞 F) F o) := by
    intro o
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  apply le_antisymm
  · intro b hb
    obtain ⟨a, ha, c, hc, hac⟩ := exists_bezout x
    obtain ⟨o, ho⟩ := (mem_den_iff _ b).1 hb
    have key : b = algebraMap (𝓞 F) (𝓞 E) a * b + algebraMap (𝓞 F) (𝓞 E) c * o := by
      apply FaithfulSMul.algebraMap_injective (𝓞 E) E
      have hac' := congrArg (algebraMap F E) hac
      simp only [map_add, map_mul, map_one] at hac'
      simp only [map_add, map_mul, tower, ho]
      linear_combination (-(algebraMap (𝓞 E) E b)) * hac'
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha))
      (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc))
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_den_iff]
    obtain ⟨o, ho⟩ := (mem_den_iff x a).1 ha
    exact ⟨algebraMap (𝓞 F) (𝓞 E) o, by rw [tower, tower, ho, map_mul]⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem absNorm_den_algebraMap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E], Module.finrank F E = 2 → ∀ x : F,
      Ideal.absNorm (HS.den E (algebraMap F E x)) = Ideal.absNorm (HS.den F x) ^ 2 := by
  intro F E _ _ _ _ _ h2 x
  rw [den_algebraMap, Ideal.absNorm_algebraMap]
  congr 1
  rw [← h2]
  exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap
