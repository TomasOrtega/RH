import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.BCT

/- English proof (translation)
Introduce `E _ _ _ w u h`. Use `set σ : E ≃+* E := (IsCMField.complexConj E).toRingEquiv with hσ`. Use `set e : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv σ with he`. Establish `hc : ∀ x : 𝓞 E, ((e x : 𝓞 E) : E) = IsCMField.complexConj E (x : E)` using `fun x => rfl`. Establish `hmem : ∀ x ∈ w.asIdeal, x ∈ u.asIdeal ∨ e x ∈ u.asIdeal`.

Introduce `x hx`. Establish `hfix : IsCMField.complexConj E (((x * e x : 𝓞 E)) : E) = ((x * e x : 𝓞 E) : E)`. Establish `h1 : ((x * e x : 𝓞 E) : E) = (x : E) * IsCMField.complexConj E (x : E)`. Rewrite using `[← hc]`. Both sides reduce to the same expression.

Rewrite using `[h1, map_mul, IsCMField.complexConj_apply_apply, mul_comm]`. Establish `hF : ((x * e x : 𝓞 E) : E) ∈ maximalRealSubfield E` using `(IsCMField.complexConj_eq_self_iff E _).1 hfix`. Establish `hint : IsIntegral ℤ (⟨_, hF⟩ : maximalRealSubfield E)`. Use `(x * e x).isIntegral_coe` as an intermediate fact. Conclude with `(isIntegral_algebraMap_iff (algebraMap (maximalRealSubfield E) E).injective).1 this`.

Establish `hz : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) ⟨_, hint⟩ = x * e x` using `RingOfIntegers.ext rfl`. Establish `h1 : (⟨_, hint⟩ : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) _ ∈ w.asIdeal`. Rewrite using `[hz]`. Conclude with `Ideal.mul_mem_right _ _ hx`.

Rewrite `h1` using `[← h]`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) _ ∈ u.asIdeal at h1`. Rewrite `h1` using `[hz]`. Conclude with `u.isPrime.mem_or_mem h1`. Establish `hsub : (w.asIdeal : Set (𝓞 E)) ⊆ (u.asIdeal : Set (𝓞 E)) ∪ (u.comap (e : 𝓞 E →+* 𝓞 E) e.surjective).asIdeal` using `fun x hx => hmem x hx`.

Break down `Ideal.subset_union.1 hsub with h2 | h2` into its components or cases. Use `left`. Establish `: w = u` using `HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top h2)`. Substitute `this` using the available equality. Introduce `y`.

Both sides reduce to the same expression. Use `right`. Introduce `y`. Conclude with `GlobalTheory.QNorm.valuation_of_eq_comap σ u w (w.isMaximal.eq_of_le (u.comap (e : 𝓞 E →+* 𝓞 E) e.surjective).isPrime.ne_top h2) y`.
-/
theorem valuation_eq_or_eq_conj_of_under_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w u : Pl E), u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → (∀ y : E, w.valuation E y = u.valuation E y) ∨ (∀ y : E, w.valuation E y = u.valuation E (IsCMField.complexConj E y)) := by
  intro E _ _ _ w u h
  set σ : E ≃+* E := (IsCMField.complexConj E).toRingEquiv with hσ
  set e : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv σ with he
  have hc : ∀ x : 𝓞 E, ((e x : 𝓞 E) : E) = IsCMField.complexConj E (x : E) := fun x => rfl
  have hmem : ∀ x ∈ w.asIdeal, x ∈ u.asIdeal ∨ e x ∈ u.asIdeal := by
    intro x hx
    have hfix : IsCMField.complexConj E (((x * e x : 𝓞 E)) : E) = ((x * e x : 𝓞 E) : E) := by
      have h1 : ((x * e x : 𝓞 E) : E) = (x : E) * IsCMField.complexConj E (x : E) := by
        rw [← hc]; rfl
      rw [h1, map_mul, IsCMField.complexConj_apply_apply, mul_comm]
    have hF : ((x * e x : 𝓞 E) : E) ∈ maximalRealSubfield E :=
      (IsCMField.complexConj_eq_self_iff E _).1 hfix
    have hint : IsIntegral ℤ (⟨_, hF⟩ : maximalRealSubfield E) := by
      have := (x * e x).isIntegral_coe
      exact (isIntegral_algebraMap_iff (algebraMap (maximalRealSubfield E) E).injective).1 this
    have hz : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) ⟨_, hint⟩ = x * e x :=
      RingOfIntegers.ext rfl
    have h1 : (⟨_, hint⟩ : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      change algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) _ ∈ w.asIdeal
      rw [hz]
      exact Ideal.mul_mem_right _ _ hx
    rw [← h] at h1
    change algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) _ ∈ u.asIdeal at h1
    rw [hz] at h1
    exact u.isPrime.mem_or_mem h1
  have hsub : (w.asIdeal : Set (𝓞 E)) ⊆ (u.asIdeal : Set (𝓞 E)) ∪
      (u.comap (e : 𝓞 E →+* 𝓞 E) e.surjective).asIdeal := fun x hx => hmem x hx
  rcases Ideal.subset_union.1 hsub with h2 | h2
  · left
    have : w = u := HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top h2)
    subst this
    intro y; rfl
  · right
    intro y
    exact GlobalTheory.QNorm.valuation_of_eq_comap σ u w
      (w.isMaximal.eq_of_le (u.comap (e : 𝓞 E →+* 𝓞 E) e.surjective).isPrime.ne_top h2) y

end GlobalTheory.BCT
