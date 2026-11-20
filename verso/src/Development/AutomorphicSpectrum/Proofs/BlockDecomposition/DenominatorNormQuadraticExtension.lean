import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix nonZeroDivisors

/- English proof (translation)
Rewrite using `[HS.den, Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Use `show (∀ i : Fin 1, ∃ o, algebraMap (𝓞 K) K o = (a • fun _ : Fin 1 => x) i) ↔ _`. Simplify using `only [Pi.smul_apply, Algebra.smul_def]`. Conclude with `⟨fun h => h 0, fun h _ => h⟩`.
-/
theorem mem_den_iff {K : Type} [Field K] [NumberField K] (x : K) (a : 𝓞 K) :
    a ∈ HS.den K x ↔ ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = algebraMap (𝓞 K) K a * x := by
  rw [HS.den, Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  show (∀ i : Fin 1, ∃ o, algebraMap (𝓞 K) K o = (a • fun _ : Fin 1 => x) i) ↔ _
  simp only [Pi.smul_apply, Algebra.smul_def]
  exact ⟨fun h => h 0, fun h _ => h⟩

/- English proof (translation)
Take `⟨S, hSdef⟩ : ∃ S : FractionalIdeal (𝓞 K)⁰ K, S = FractionalIdeal.spanSingleton (𝓞 K)⁰ (1 : K) ⊔ FractionalIdeal.spanSingleton (𝓞 K)⁰ x` from `⟨_, rfl⟩`. Establish `h1S : (1 : K) ∈ S`. Rewrite using `[hSdef]`. Conclude with `(le_sup_left : FractionalIdeal.spanSingleton (𝓞 K)⁰ (1 : K) ≤ _) (FractionalIdeal.mem_spanSingleton_self _ _)`. Establish `hxS : x ∈ S`.

Rewrite using `[hSdef]`. Conclude with `(le_sup_right : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≤ _) (FractionalIdeal.mem_spanSingleton_self _ _)`. Establish `hS : S ≠ 0`. Introduce `h`. Rewrite `h1S` using `[h]`.

Conclude with `one_ne_zero ((FractionalIdeal.mem_zero_iff _).1 h1S)`. Establish `hden : ∀ t ∈ S⁻¹, ∃ a ∈ HS.den K x, algebraMap (𝓞 K) K a = t`. Introduce `t ht`. Rewrite `ht` using `[FractionalIdeal.mem_inv_iff hS]`. Establish `ht1 : t ∈ (1 : FractionalIdeal (𝓞 K)⁰ K)`.

Use `ht 1 h1S` as an intermediate fact. Rewrite `this` using `[mul_one]`. Then use the resulting hypothesis. Take `⟨a, ha⟩` from `(FractionalIdeal.mem_one_iff (𝓞 K)⁰).1 ht1`. Take `⟨o, ho⟩` from `(FractionalIdeal.mem_one_iff (𝓞 K)⁰).1 (ht x hxS)`. Conclude with `⟨a, (mem_den_iff x a).2 ⟨o, by rw [ho, ha]⟩, ha⟩`.

Establish `hsplit : ∀ T : FractionalIdeal (𝓞 K)⁰ K, S * T = FractionalIdeal.spanSingleton (𝓞 K)⁰ (1 : K) * T ⊔ FractionalIdeal.spanSingleton (𝓞 K)⁰ x * T`. Introduce `T`. Rewrite using `[hSdef, FractionalIdeal.sup_eq_add, FractionalIdeal.sup_eq_add, add_mul]`. Establish `h1 : (1 : K) ∈ S * S⁻¹`. Rewrite using `[mul_inv_cancel₀ hS]`.

Conclude with `FractionalIdeal.one_mem_one _`. Rewrite `h1` using `[hsplit S⁻¹, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_sup, Submodule.mem_sup]`. Take `⟨u, hu, v, hv, huv⟩` from `h1`. Rewrite `hu`, `hv` using `[FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul]`. Take `⟨u', hu', rfl⟩` from `hu`.

Take `⟨v', hv', rfl⟩` from `hv`. Take `⟨a, ha, ha'⟩` from `hden u' hu'`. Take `⟨c, hc, hc'⟩` from `hden v' hv'`. Use `⟨a, ha, c, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[ha', hc', ← huv]`.

Expand and normalize the polynomial expressions, which then agree.
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
Establish `tower : ∀ o : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) o) = algebraMap F E (algebraMap (𝓞 F) F o)`. Introduce `o`. Rewrite using `[← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `b hb`.

Take `⟨a, ha, c, hc, hac⟩` from `exists_bezout x`. Take `⟨o, ho⟩` from `(mem_den_iff _ b).1 hb`. Establish `key : b = algebraMap (𝓞 F) (𝓞 E) a * b + algebraMap (𝓞 F) (𝓞 E) c * o`. Apply `FaithfulSMul.algebraMap_injective (𝓞 E) E` to reduce the goal to its premises. Establish `hac'` using `congrArg (algebraMap F E) hac`.

Simplify using `only [map_add, map_mul, map_one] at hac'`. Simplify using `only [map_add, map_mul, tower, ho]`. Take the linear combination `(-(algebraMap (𝓞 E) E b)) * hac'`. Rewrite using `[key]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)) (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc))`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Rewrite using `[Ideal.mem_comap, mem_den_iff]`. Take `⟨o, ho⟩` from `(mem_den_iff x a).1 ha`. Conclude with `⟨algebraMap (𝓞 F) (𝓞 E) o, by rw [tower, tower, ho, map_mul]⟩`.
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
Introduce `F E _ _ _ _ _ h2 x`. Rewrite using `[den_algebraMap, Ideal.absNorm_algebraMap]`. Use `congr 1`. Rewrite using `[← h2]`. Conclude with `(IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm`.
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
