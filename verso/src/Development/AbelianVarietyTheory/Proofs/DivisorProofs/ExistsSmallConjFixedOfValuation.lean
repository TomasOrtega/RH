import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
open Polynomial

namespace GlobalTheory.UnitLemma

noncomputable def UQ.cInt (K : UQ) : K.O ≃+* K.O :=
  let f := algebraMap K.O K.E
  have hf : Function.Injective f := IsFractionRing.injective K.O K.E
  let d : K.O → K.O := fun x => Classical.choose (K.c_int x)
  have hd : ∀ x, f (d x) = K.c (f x) := fun x => (Classical.choose_spec (K.c_int x)).symm
  have hdd : ∀ x, d (d x) = x := fun x => hf (by rw [hd, hd, K.c_c])
  { toFun := d
    invFun := d
    left_inv := hdd
    right_inv := hdd
    map_mul' := fun a b => hf (by rw [hd, map_mul, map_mul, map_mul, hd, hd])
    map_add' := fun a b => hf (by rw [hd, map_add, map_add, map_add, hd, hd]) }

/- English proof (translation)
The claim follows from `(Classical.choose_spec (K.c_int x)).symm`.
-/
theorem UQ.cInt_spec (K : UQ) (x : K.O) :
    algebraMap K.O K.E (K.cInt x) = K.c (algebraMap K.O K.E x) :=
  (Classical.choose_spec (K.c_int x)).symm

/- English proof (translation)
Establish `h1 : (IsDiscreteValuationRing.maximalIdeal O).intValuation s = WithZero.exp (-1 : ℤ)` using `IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ hs.ne_zero ((IsDiscreteValuationRing.irreducible_iff_uniformizer s).mp hs)`. Unfold `val`. Rewrite using `[map_pow, map_pow, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, h1]`. Simplify using the standard rewrite rules.
-/
theorem val_algebraMap_irreducible_pow (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type} [Field E]
    [Algebra O E] [IsFractionRing O E] {s : O} (hs : Irreducible s) (n : ℕ) :
    val O (algebraMap O E (s ^ n)) = n := by
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).intValuation s = WithZero.exp (-1 : ℤ) :=
    IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ hs.ne_zero
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer s).mp hs)
  unfold val
  rw [map_pow, map_pow, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, h1]
  simp

/- English proof (translation)
Establish `hm : ∀ a : K.O, a ∈ IsLocalRing.maximalIdeal K.O ↔ ¬ IsUnit a` using `fun a => IsLocalRing.mem_maximalIdeal a`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible K.O`. Establish `hcϖ : Irreducible (K.cInt ϖ)` using `(MulEquiv.irreducible_iff (K.cInt : K.O ≃* K.O)).mpr hϖ`. Take `⟨ε, hε⟩` from `IsDiscreteValuationRing.associated_of_irreducible K.O hϖ hcϖ`. Take `⟨x, y, hxy, hunit⟩` from `K.c_res`.

Establish `hcx : K.cInt x = y` using `IsFractionRing.injective K.O K.E (by rw [K.cInt_spec, hxy])`. Establish `hcc : ∀ a, K.cInt (K.cInt a) = a` using `fun a => K.cInt.symm_apply_apply a`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs, hsc⟩ : ∃ s : K.O, Irreducible s ∧ K.cInt s = s := by`. Distinguish the cases in `h1 : IsUnit (1 + (ε : K.O))`. Use `⟨ϖ + K.cInt ϖ, ?_, ?_⟩` and prove the remaining obligations.

Establish `: ϖ + K.cInt ϖ = ϖ * h1.unit` using `by rw [← hε]; simp [mul_add]`. Rewrite using `[this]`. Conclude with `(associated_mul_unit_right ϖ _ h1.unit.isUnit).irreducible hϖ`. Rewrite using `[map_add, hcc, add_comm]`. Distinguish the cases in `h2 : IsUnit (x + y * (ε : K.O))`.

Use `⟨x * ϖ + K.cInt (x * ϖ), ?_, ?_⟩` and prove the remaining obligations. Establish `: x * ϖ + K.cInt (x * ϖ) = ϖ * h2.unit`. Rewrite using `[map_mul, hcx, ← hε]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `(associated_mul_unit_right ϖ _ h2.unit.isUnit).irreducible hϖ`. Rewrite using `[map_add, hcc, add_comm]`. Apply `absurd _ hunit` to reduce the goal to its premises. Establish `e : x - y = (x + y * (ε : K.O)) - y * (1 + (ε : K.O))` using `by ring`.

Rewrite using `[e]`. Conclude with `Ideal.sub_mem _ ((hm _).mpr h2) (Ideal.mul_mem_left _ _ ((hm _).mpr h1))`. Use `⟨s ^ k, ⟨pow_ne_zero _ hs.ne_zero, ?_, ?_⟩, val_algebraMap_irreducible_pow K.O hs k⟩` and prove the remaining obligations. Conclude with `Ideal.pow_mem_of_mem _ ((hm s).mpr hs.not_isUnit) k hk`. Rewrite using `[← K.cInt_spec, map_pow, hsc]`.
-/
theorem exists_small_val (K : UQ) (k : ℕ) (hk : 1 ≤ k) :
    ∃ t : K.O, K.Small t ∧ val K.O (algebraMap K.O K.E t) = k := by
  have hm : ∀ a : K.O, a ∈ IsLocalRing.maximalIdeal K.O ↔ ¬ IsUnit a := fun a =>
    IsLocalRing.mem_maximalIdeal a
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hcϖ : Irreducible (K.cInt ϖ) := (MulEquiv.irreducible_iff (K.cInt : K.O ≃* K.O)).mpr hϖ
  obtain ⟨ε, hε⟩ := IsDiscreteValuationRing.associated_of_irreducible K.O hϖ hcϖ
  obtain ⟨x, y, hxy, hunit⟩ := K.c_res
  have hcx : K.cInt x = y :=
    IsFractionRing.injective K.O K.E (by rw [K.cInt_spec, hxy])
  have hcc : ∀ a, K.cInt (K.cInt a) = a := fun a => K.cInt.symm_apply_apply a

  obtain ⟨s, hs, hsc⟩ : ∃ s : K.O, Irreducible s ∧ K.cInt s = s := by
    by_cases h1 : IsUnit (1 + (ε : K.O))
    · refine ⟨ϖ + K.cInt ϖ, ?_, ?_⟩
      · have : ϖ + K.cInt ϖ = ϖ * h1.unit := by rw [← hε]; simp [mul_add]
        rw [this]
        exact (associated_mul_unit_right ϖ _ h1.unit.isUnit).irreducible hϖ
      · rw [map_add, hcc, add_comm]
    · by_cases h2 : IsUnit (x + y * (ε : K.O))
      · refine ⟨x * ϖ + K.cInt (x * ϖ), ?_, ?_⟩
        · have : x * ϖ + K.cInt (x * ϖ) = ϖ * h2.unit := by
            rw [map_mul, hcx, ← hε]; simp; ring
          rw [this]
          exact (associated_mul_unit_right ϖ _ h2.unit.isUnit).irreducible hϖ
        · rw [map_add, hcc, add_comm]
      · apply absurd _ hunit
        have e : x - y = (x + y * (ε : K.O)) - y * (1 + (ε : K.O)) := by ring
        rw [e]
        exact Ideal.sub_mem _ ((hm _).mpr h2) (Ideal.mul_mem_left _ _ ((hm _).mpr h1))
  refine ⟨s ^ k, ⟨pow_ne_zero _ hs.ne_zero, ?_, ?_⟩, val_algebraMap_irreducible_pow K.O hs k⟩
  · exact Ideal.pow_mem_of_mem _ ((hm s).mpr hs.not_isUnit) k hk
  · rw [← K.cInt_spec, map_pow, hsc]

end GlobalTheory.UnitLemma
