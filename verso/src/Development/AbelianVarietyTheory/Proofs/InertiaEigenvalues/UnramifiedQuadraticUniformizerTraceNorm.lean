import Mathlib
import GroundTheory.LocalFields.UnramifiedNormSurj
import GroundTheory.LocalFields.UnramifiedGalois
open ValuativeRel

namespace GlobalTheory

open GroundTheory.LocalField IsLocalRing in

/- English proof (translation)
Introduce `K L _ _ _ _ _ _ _ _ _ _ _ he h2`. Use `haveI : IsUnramified K L := ⟨he⟩`. Establish `memK : ∀ x : K, x ∈ 𝒪[K] ↔ x ≤ᵥ 1` using `fun x ↦ by`. Rewrite using `[Valuation.mem_integer_iff, ← map_one (ValuativeRel.valuation K), ← Valuation.vle_iff_le]`. Establish `memL : ∀ x : L, x ∈ 𝒪[L] ↔ x ≤ᵥ 1` using `fun x ↦ by`.

Rewrite using `[Valuation.mem_integer_iff, ← map_one (ValuativeRel.valuation L), ← Valuation.vle_iff_le]`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Establish `hϖ0 : (ϖ : K) ≠ 0` using `by exact_mod_cast hϖ.ne_zero`. Use `⟨(ϖ : K), hϖ0, (memK _).1 ϖ.2, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h1`.

Establish `hv : ValuativeRel.valuation K (ϖ : K) = 1` using `le_antisymm ((Valuation.vle_iff_le _).1 ((memK _).1 ϖ.2) |>.trans_eq (map_one _)) ((map_one (ValuativeRel.valuation K)).symm.trans_le ((Valuation.vle_iff_le _).1 h1))`. Conclude with `hϖ.not_isUnit ((Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 hv)`. Introduce and unpack `⟨y, hy⟩`. Establish `h` using `ord_norm (K := K) y`. Rewrite `h` using `[hy, ord_uniformizer hϖ, IsUnramified.residueDegree_eq_finrank K L, h2]`.

Use linear arithmetic over natural numbers and integers. Introduce `y hy`. Establish `hπ` using `irreducible_algebraMap_of_isUnramified (L := L) hϖ`. Use `set y' : 𝒪[L] := ⟨y, (memL y).2 hy⟩`. Distinguish the cases in `hu : IsUnit y'`.

Use `right`. Use `⟨((hu.unit⁻¹ : 𝒪[L]ˣ) : 𝒪[L]), (memL _).1 (hu.unit⁻¹ : 𝒪[L]ˣ).1.2, ?_⟩` and prove the remaining obligations. Establish `h` using `hu.unit.mul_inv`. Rewrite `h` using `[IsUnit.unit_spec]`. Use `congrArg (fun u : 𝒪[L] ↦ (u : L)) h` as an intermediate fact.

Simplify using `only [MulMemClass.coe_mul, OneMemClass.coe_one] at this`. Conclude with `this`. Use `left`. Establish `hm : y' ∈ maximalIdeal 𝒪[L]` using `(mem_maximalIdeal y').2 hu`. Rewrite `hm` using `[hπ.maximalIdeal_eq, Ideal.mem_span_singleton]`.

Take `⟨c, hc⟩` from `hm`. Use `⟨(c : L), (memL _).1 c.2, ?_⟩` and prove the remaining obligations. Use `congrArg (fun u : 𝒪[L] ↦ (u : L)) hc` as an intermediate fact. Simplify using `only [y', MulMemClass.coe_mul, coe_algebraMap_integer] at this`. Conclude with `this`.

Introduce `s hs`. Take `⟨a, ha⟩` from `trace_integer_surjective (K := K) (L := L) ⟨s, (memK s).2 hs⟩`. Use `⟨(a : L), (memL _).1 a.2, ?_⟩` and prove the remaining obligations. Rewrite using `[← coe_trace_integer, ha]`. Introduce `s hs1 hs2`.

Use `set s' : 𝒪[K] := ⟨s, (memK s).2 hs1⟩`. Establish `hv : ValuativeRel.valuation K s = 1` using `le_antisymm ((Valuation.vle_iff_le _).1 hs1 |>.trans_eq (map_one _)) ((map_one (ValuativeRel.valuation K)).symm.trans_le ((Valuation.vle_iff_le _).1 hs2))`. Establish `hu : IsUnit s'` using `(Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 hv`. Take `⟨w, hw⟩` from `normIntegerUnits_surjective (K := K) (L := L) hu.unit`. Use `⟨((w : 𝒪[L]) : L), (memL _).1 (w : 𝒪[L]).2, ?_⟩` and prove the remaining obligations.

Use `congrArg (fun u : 𝒪[K]ˣ ↦ ((u : 𝒪[K]) : K)) hw` as an intermediate fact. Simplify using `only [coe_normIntegerUnits_eq, IsUnit.unit_spec] at this`. Rewrite using `[← coe_norm_integer]`. Conclude with `this`.
-/
theorem unramified_quadratic_uniformizer_trace_norm : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L], GroundTheory.LocalField.ramificationIndex K L = 1 → Module.finrank K L = 2 → ∃ ϖ : K, ϖ ≠ 0 ∧ ϖ ≤ᵥ 1 ∧ ¬ (1 : K) ≤ᵥ ϖ ∧ (¬ ∃ y : L, Algebra.norm K y = ϖ) ∧ (∀ y : L, y ≤ᵥ 1 → (∃ z : L, z ≤ᵥ 1 ∧ y = algebraMap K L ϖ * z) ∨ ∃ z : L, z ≤ᵥ 1 ∧ y * z = 1) ∧ (∀ s : K, s ≤ᵥ 1 → ∃ z : L, z ≤ᵥ 1 ∧ Algebra.trace K L z = s) ∧ ∀ s : K, s ≤ᵥ 1 → 1 ≤ᵥ s → ∃ w : L, w ≤ᵥ 1 ∧ Algebra.norm K w = s := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ he h2
  haveI : IsUnramified K L := ⟨he⟩
  have memK : ∀ x : K, x ∈ 𝒪[K] ↔ x ≤ᵥ 1 := fun x ↦ by
    rw [Valuation.mem_integer_iff, ← map_one (ValuativeRel.valuation K), ← Valuation.vle_iff_le]
  have memL : ∀ x : L, x ∈ 𝒪[L] ↔ x ≤ᵥ 1 := fun x ↦ by
    rw [Valuation.mem_integer_iff, ← map_one (ValuativeRel.valuation L), ← Valuation.vle_iff_le]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  refine ⟨(ϖ : K), hϖ0, (memK _).1 ϖ.2, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro h1
    have hv : ValuativeRel.valuation K (ϖ : K) = 1 :=
      le_antisymm ((Valuation.vle_iff_le _).1 ((memK _).1 ϖ.2) |>.trans_eq (map_one _))
        ((map_one (ValuativeRel.valuation K)).symm.trans_le ((Valuation.vle_iff_le _).1 h1))
    exact hϖ.not_isUnit ((Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 hv)
  ·
    rintro ⟨y, hy⟩
    have h := ord_norm (K := K) y
    rw [hy, ord_uniformizer hϖ, IsUnramified.residueDegree_eq_finrank K L, h2] at h
    omega
  ·
    intro y hy
    have hπ := irreducible_algebraMap_of_isUnramified (L := L) hϖ
    set y' : 𝒪[L] := ⟨y, (memL y).2 hy⟩
    by_cases hu : IsUnit y'
    · right
      refine ⟨((hu.unit⁻¹ : 𝒪[L]ˣ) : 𝒪[L]), (memL _).1 (hu.unit⁻¹ : 𝒪[L]ˣ).1.2, ?_⟩
      have h := hu.unit.mul_inv
      rw [IsUnit.unit_spec] at h
      have := congrArg (fun u : 𝒪[L] ↦ (u : L)) h
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
      exact this
    · left
      have hm : y' ∈ maximalIdeal 𝒪[L] := (mem_maximalIdeal y').2 hu
      rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
      obtain ⟨c, hc⟩ := hm
      refine ⟨(c : L), (memL _).1 c.2, ?_⟩
      have := congrArg (fun u : 𝒪[L] ↦ (u : L)) hc
      simp only [y', MulMemClass.coe_mul, coe_algebraMap_integer] at this
      exact this
  ·
    intro s hs
    obtain ⟨a, ha⟩ := trace_integer_surjective (K := K) (L := L) ⟨s, (memK s).2 hs⟩
    refine ⟨(a : L), (memL _).1 a.2, ?_⟩
    rw [← coe_trace_integer, ha]
  ·
    intro s hs1 hs2
    set s' : 𝒪[K] := ⟨s, (memK s).2 hs1⟩
    have hv : ValuativeRel.valuation K s = 1 :=
      le_antisymm ((Valuation.vle_iff_le _).1 hs1 |>.trans_eq (map_one _))
        ((map_one (ValuativeRel.valuation K)).symm.trans_le ((Valuation.vle_iff_le _).1 hs2))
    have hu : IsUnit s' := (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 hv
    obtain ⟨w, hw⟩ := normIntegerUnits_surjective (K := K) (L := L) hu.unit
    refine ⟨((w : 𝒪[L]) : L), (memL _).1 (w : 𝒪[L]).2, ?_⟩
    have := congrArg (fun u : 𝒪[K]ˣ ↦ ((u : 𝒪[K]) : K)) hw
    simp only [coe_normIntegerUnits_eq, IsUnit.unit_spec] at this
    rw [← coe_norm_integer]
    exact this

end GlobalTheory
