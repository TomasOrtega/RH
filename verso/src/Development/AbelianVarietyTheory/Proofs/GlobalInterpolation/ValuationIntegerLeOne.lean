import Mathlib

universe u_1 u_2

namespace GlobalTheory.UnitDenominatorValuation

open NumberField
open scoped nonZeroDivisors

/- English proof (translation)
Establish `hZ : IsIntegral ℤ (ι (a : E))` using `(NumberField.RingOfIntegers.isIntegral_coe a).map ι.toIntAlgHom`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.mp (hZ.tower_top (A := A))`. Rewrite using `[← hy]`. Conclude with `A.valuation_le_one y`.
-/
theorem valuation_integer_le_one {E : Type u_1} {Ω : Type u_2} [Field E] [NumberField E]
    [Field Ω] (ι : E →+* Ω) (A : ValuationSubring Ω) (a : 𝓞 E) :
    A.valuation (ι (a : E)) ≤ 1 := by

  have hZ : IsIntegral ℤ (ι (a : E)) := (NumberField.RingOfIntegers.isIntegral_coe a).map ι.toIntAlgHom
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hZ.tower_top (A := A))
  rw [← hy]
  exact A.valuation_le_one y

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Set `P : Submodule (𝓞 E) E` to `{ carrier := {u | A.valuation (ι u) < 1} add_mem' := fun {u v} hu hv => by`. Simplify using `only [Set.mem_ofPred_eq, map_add] at hu hv ⊢`. Conclude with `lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hu hv)`.

Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := fun r u hu => by`. Simplify using `only [Set.mem_ofPred_eq, Algebra.smul_def, map_mul] at hu ⊢`. Combine the equalities or inequalities in the displayed calculation. Set `J : FractionalIdeal (𝓞 E)⁰ E` to `1 ⊔ FractionalIdeal.spanSingleton _ x`.

Establish `h1J : (1 : E) ∈ J` using `(le_sup_left : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ J) (FractionalIdeal.one_mem_one _)`. Establish `hxJ : x ∈ J` using `(le_sup_right : FractionalIdeal.spanSingleton _ x ≤ J) (FractionalIdeal.mem_spanSingleton_self _ x)`. Establish `hJ : J ≠ 0`. Introduce `h`. Rewrite `h1J` using `[h, FractionalIdeal.mem_zero_iff]`.

Conclude with `one_ne_zero h1J`. Establish `hJle : ∀ z ∈ (J : Submodule (𝓞 E) E), A.valuation (ι z) ≤ 1`. Introduce `z hz`. Rewrite `hz` using `[FractionalIdeal.coe_sup, Submodule.mem_sup]`. Take `⟨a, ha, b, hb, rfl⟩` from `hz`.

Take `⟨a', rfl⟩` from `(FractionalIdeal.mem_one_iff _).mp ha`. Take `⟨b', rfl⟩` from `(FractionalIdeal.mem_spanSingleton _).mp hb`. Rewrite using `[map_add]`. Use `le_trans (Valuation.map_add _ _ _) (max_le (valuation_integer_le_one ι A a') ?_)` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul, map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hinv : ∀ y ∈ ((J⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E), A.valuation (ι y) < 1`. Introduce `y hy`. Establish `hy1` using `(FractionalIdeal.mem_inv_iff hJ).mp hy 1 h1J`. Establish `hyx` using `(FractionalIdeal.mem_inv_iff hJ).mp hy x hxJ`.

Rewrite `hy1` using `[mul_one]`. Take `⟨s, rfl⟩` from `(FractionalIdeal.mem_one_iff _).mp hy1`. Take `⟨t, ht⟩` from `(FractionalIdeal.mem_one_iff _).mp hyx`. Use `lt_of_le_of_ne (valuation_integer_le_one ι A s) fun h => hne s t h ?_` and prove the remaining obligations. Conclude with `ht.symm`.

Establish `hle : ((J * J⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) ≤ P`. Rewrite using `[FractionalIdeal.coe_mul]`. Use `Submodule.mul_le.mpr fun z hz y hy => ?_` and prove the remaining obligations. Use `show A.valuation (ι (z * y)) < 1`. Rewrite using `[map_mul, map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite `hle` using `[mul_inv_cancel₀ hJ]`. Establish `h1 : A.valuation (ι 1) < 1` using `hle (FractionalIdeal.one_mem_one _)`. Simplify using `at h1`.
-/
theorem exists_unit_denominator {E : Type u_1} {Ω : Type u_2} [inst : Field E] [NumberField E]
    [inst_2 : Field Ω] (ι : E →+* Ω) (A : ValuationSubring Ω) {x : E}
    (hx : A.valuation (ι x) ≤ 1) :
    ∃ (s : 𝓞 E) (t : 𝓞 E), A.valuation (ι (s : E)) = 1 ∧ (s : E) * x = (t : E) := by
  classical
  by_contra hne
  push Not at hne

  let P : Submodule (𝓞 E) E :=
    { carrier := {u | A.valuation (ι u) < 1}
      add_mem' := fun {u v} hu hv => by
        simp only [Set.mem_ofPred_eq, map_add] at hu hv ⊢
        exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hu hv)
      zero_mem' := by simp
      smul_mem' := fun r u hu => by
        simp only [Set.mem_ofPred_eq, Algebra.smul_def, map_mul] at hu ⊢
        calc A.valuation (ι (algebraMap (𝓞 E) E r)) * A.valuation (ι u)
            ≤ 1 * A.valuation (ι u) := mul_le_mul' (valuation_integer_le_one ι A r) le_rfl
          _ < 1 := by rwa [one_mul] }

  let J : FractionalIdeal (𝓞 E)⁰ E := 1 ⊔ FractionalIdeal.spanSingleton _ x
  have h1J : (1 : E) ∈ J := (le_sup_left : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ J)
    (FractionalIdeal.one_mem_one _)
  have hxJ : x ∈ J := (le_sup_right : FractionalIdeal.spanSingleton _ x ≤ J)
    (FractionalIdeal.mem_spanSingleton_self _ x)
  have hJ : J ≠ 0 := by
    intro h
    rw [h, FractionalIdeal.mem_zero_iff] at h1J
    exact one_ne_zero h1J

  have hJle : ∀ z ∈ (J : Submodule (𝓞 E) E), A.valuation (ι z) ≤ 1 := by
    intro z hz
    rw [FractionalIdeal.coe_sup, Submodule.mem_sup] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    obtain ⟨a', rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨b', rfl⟩ := (FractionalIdeal.mem_spanSingleton _).mp hb
    rw [map_add]
    refine le_trans (Valuation.map_add _ _ _) (max_le (valuation_integer_le_one ι A a') ?_)
    rw [Algebra.smul_def, map_mul, map_mul]
    calc A.valuation (ι (algebraMap (𝓞 E) E b')) * A.valuation (ι x) ≤ 1 * 1 :=
          mul_le_mul' (valuation_integer_le_one ι A b') hx
      _ = 1 := one_mul 1

  have hinv : ∀ y ∈ ((J⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E),
      A.valuation (ι y) < 1 := by
    intro y hy
    have hy1 := (FractionalIdeal.mem_inv_iff hJ).mp hy 1 h1J
    have hyx := (FractionalIdeal.mem_inv_iff hJ).mp hy x hxJ
    rw [mul_one] at hy1
    obtain ⟨s, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hy1
    obtain ⟨t, ht⟩ := (FractionalIdeal.mem_one_iff _).mp hyx
    refine lt_of_le_of_ne (valuation_integer_le_one ι A s) fun h => hne s t h ?_
    exact ht.symm
  have hle : ((J * J⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) ≤ P := by
    rw [FractionalIdeal.coe_mul]
    refine Submodule.mul_le.mpr fun z hz y hy => ?_
    show A.valuation (ι (z * y)) < 1
    rw [map_mul, map_mul]
    calc A.valuation (ι z) * A.valuation (ι y) ≤ 1 * A.valuation (ι y) :=
          mul_le_mul' (hJle z hz) le_rfl
      _ < 1 := by rw [one_mul]; exact hinv y hy
  rw [mul_inv_cancel₀ hJ] at hle
  have h1 : A.valuation (ι 1) < 1 := hle (FractionalIdeal.one_mem_one _)
  simp at h1

end GlobalTheory.UnitDenominatorValuation
