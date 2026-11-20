import Mathlib
import GroundTheory.LocalFields.HerbrandLocalBase
import GroundTheory.LocalFields.CompleteTrivialLocal

namespace GroundTheory.LocalField

open ValuativeRel GroundTheory.GroupCoh GroundTheory.Global

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra K L]
  [ValuativeExtension K L] [FiniteDimensional K L] in

/- English proof (translation)
Establish `: Finite (𝒪[L]ˣ ⧸ V)` using `Subgroup.quotient_finite_of_isOpen V h`. Conclude with `Subgroup.finiteIndex_of_finite_quotient`.
-/
theorem finiteIndex_of_isOpen_integerUnits {V : Subgroup 𝒪[L]ˣ} (h : IsOpen (V : Set 𝒪[L]ˣ)) :
    V.FiniteIndex := by
  have : Finite (𝒪[L]ˣ ⧸ V) := Subgroup.quotient_finite_of_isOpen V h
  exact Subgroup.finiteIndex_of_finite_quotient

variable [IsGalois K L] {σ : L ≃ₐ[K] L}

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, V, hV, -, hopen, hT⟩` from `exists_openSubgroup_units_tateTrivial (K := K) (L := L)`. Set `` to `stableUnitsAction V hV`. Use `finiteIndex_of_isOpen_integerUnits hopen` as an intermediate fact. Use `hT.1` as an intermediate fact. Use `hT.2` as an intermediate fact.

Conclude with `cycHerbrand_integerUnits_eq_one_of_subgroup hσ V fun g v => Units.ext (Subtype.ext (unitVal_smul V hV g v))`.
-/
theorem cycHerbrand_integerUnits_eq_one (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ = 1 := by
  obtain ⟨-, -, -, -, -, -, -, V, hV, -, hopen, hT⟩ :=
    exists_openSubgroup_units_tateTrivial (K := K) (L := L)
  let := stableUnitsAction V hV
  have := finiteIndex_of_isOpen_integerUnits hopen
  have := hT.1
  have := hT.2
  exact cycHerbrand_integerUnits_eq_one_of_subgroup hσ V
    fun g v => Units.ext (Subtype.ext (unitVal_smul V hV g v))

/- English proof (translation)
Take `⟨hA, h1⟩` from `cycHerbrand_integerUnits_eq_one hσ`. Take `⟨hB, h2⟩` from `cycHerbrand_units_eq_mul hσ hA`. Use `⟨hB, ?_⟩` and prove the remaining obligations. Rewrite using `[h2, h1, one_mul, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]`.
-/
theorem cycHerbrand_units_eq_finrank (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ =
        Module.finrank K L := by
  obtain ⟨hA, h1⟩ := cycHerbrand_integerUnits_eq_one hσ
  obtain ⟨hB, h2⟩ := cycHerbrand_units_eq_mul hσ hA
  refine ⟨hB, ?_⟩
  rw [h2, h1, one_mul, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]

variable [IsCyclic (L ≃ₐ[K] L)]

/- English proof (translation)
Take `⟨τ, hτ⟩` from `IsCyclic.exists_generator (α := L ≃ₐ[K] L)`. Take `⟨hA, h1⟩` from `cycHerbrand_integerUnits_eq_one hτ`. Take `⟨f0, f1⟩` from `(hasHerbrandQuotient_iff hτ).mp hA`. Use `⟨f0, f1, ?_⟩` and prove the remaining obligations. Rewrite `h1` using `[cycHerbrand_ofMulDistribMulAction hτ]`.

Establish `h0 : (Nat.card (TateNegOne (L ≃ₐ[K] L) 𝒪[L]ˣ) : ℚ) ≠ 0`. Conclude with `Nat.card_pos.ne'` after adjusting the coercions. Conclude with `(div_eq_one_iff_eq h0).mp h1` after adjusting the coercions.
-/
theorem natCard_tateZero_integerUnits_eq :
    Finite (TateZero (L ≃ₐ[K] L) 𝒪[L]ˣ) ∧ Finite (TateNegOne (L ≃ₐ[K] L) 𝒪[L]ˣ) ∧
      Nat.card (TateZero (L ≃ₐ[K] L) 𝒪[L]ˣ) = Nat.card (TateNegOne (L ≃ₐ[K] L) 𝒪[L]ˣ) := by
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  obtain ⟨hA, h1⟩ := cycHerbrand_integerUnits_eq_one hτ
  obtain ⟨f0, f1⟩ := (hasHerbrandQuotient_iff hτ).mp hA
  refine ⟨f0, f1, ?_⟩
  rw [cycHerbrand_ofMulDistribMulAction hτ] at h1
  have h0 : (Nat.card (TateNegOne (L ≃ₐ[K] L) 𝒪[L]ˣ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  exact_mod_cast (div_eq_one_iff_eq h0).mp h1

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [IsGalois K L] in

/- English proof (translation)
Use `subsingleton_tateNegOne_units (K := K) (L := L)` as an intermediate fact. Conclude with `Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩`.
-/
theorem natCard_tateNegOne_units : Nat.card (TateNegOne (L ≃ₐ[K] L) Lˣ) = 1 := by
  have := subsingleton_tateNegOne_units (K := K) (L := L)
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

/- English proof (translation)
Take `⟨τ, hτ⟩` from `IsCyclic.exists_generator (α := L ≃ₐ[K] L)`. Establish `h` using `(cycHerbrand_units_eq_finrank hτ).2`. Rewrite `h` using `[cycHerbrand_ofMulDistribMulAction hτ, natCard_tateNegOne_units, Nat.cast_one, div_one]`. Conclude with `h` after adjusting the coercions.
-/
theorem natCard_tateZero_units :
    Nat.card (TateZero (L ≃ₐ[K] L) Lˣ) = Module.finrank K L := by
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  have h := (cycHerbrand_units_eq_finrank hτ).2
  rw [cycHerbrand_ofMulDistribMulAction hτ, natCard_tateNegOne_units, Nat.cast_one, div_one] at h
  exact_mod_cast h

/- English proof (translation)
Rewrite using `[← natCard_tateZero_units_eq]`. Conclude with `natCard_tateZero_units`.
-/
theorem natCard_units_quotient_range_normUnits :
    Nat.card (Kˣ ⧸ (normUnits K L).range) = Module.finrank K L := by
  rw [← natCard_tateZero_units_eq]
  exact natCard_tateZero_units

end GroundTheory.LocalField
