import Mathlib
import GroundTheory.LocalFields.UnramifiedNormSurj
import GroundTheory.LocalFields.UnitsGalois
import GroundTheory.LocalFields.CompleteTrivial
import GroundTheory.LocalFields.HilbertCyclic

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

/- English proof (translation)
Rewrite using `[Algebra.norm_eq_prod_automorphisms, tateNorm_apply, Units.coe_prod]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem coe_tateNorm_integerUnits [IsGalois K L] (u : 𝒪[L]ˣ) :
    (((tateNorm (L ≃ₐ[K] L) 𝒪[L]ˣ u : 𝒪[L]ˣ) : 𝒪[L]) : L) =
      algebraMap K L (Algebra.norm K ((u : 𝒪[L]) : L)) := by
  rw [Algebra.norm_eq_prod_automorphisms, tateNorm_apply, Units.coe_prod]
  push_cast
  rfl

/- English proof (translation)
Establish `hfix : ((x : 𝒪[L]) : L) ∈ (⊥ : IntermediateField K L)` using `(IsGalois.mem_bot_iff_fixed _).2 fun σ ↦ by`. Use `congrArg (fun u : 𝒪[L]ˣ ↦ ((u : 𝒪[L]) : L)) (hx σ)` as an intermediate fact. Simplify using `using this`. Take `⟨c, hc⟩` from `IntermediateField.mem_bot.1 hfix`. Establish `hc0 : c ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hc` using `[map_zero]`. Conclude with `(Units.ne_zero x) (by exact_mod_cast hc.symm)`. Establish `h1 : c ∈ 𝒪[K]` using `(algebraMap_mem_integer_iff K L c).1 (hc ▸ (x : 𝒪[L]).2)`. Establish `h2 : c⁻¹ ∈ 𝒪[K]`.

Use `(algebraMap_mem_integer_iff K L c⁻¹).1 ?_` and prove the remaining obligations. Establish `e : algebraMap K L c⁻¹ = (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L)`. Rewrite using `[map_inv₀, hc, eq_comm, ← mul_eq_one_iff_eq_inv₀ (by exact_mod_cast (Units.ne_zero x))]`. Conclude with `congrArg (fun u : 𝒪[L] ↦ (u : L)) x.inv_mul` after adjusting the coercions. Rewrite using `[e]`.

Conclude with `(((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L])).2`. Use `⟨⟨⟨c, h1⟩, ⟨c⁻¹, h2⟩, ?_, ?_⟩, hc⟩` and prove the remaining obligations. Use `ext`. Simplify using `[hc0]`. Use `ext`.

Simplify using `[hc0]`.
-/
theorem exists_eq_of_forall_smul_eq [IsGalois K L] {x : 𝒪[L]ˣ}
    (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x) :
    ∃ w : 𝒪[K]ˣ, algebraMap K L ((w : 𝒪[K]) : K) = ((x : 𝒪[L]) : L) := by
  have hfix : ((x : 𝒪[L]) : L) ∈ (⊥ : IntermediateField K L) :=
    (IsGalois.mem_bot_iff_fixed _).2 fun σ ↦ by
      have := congrArg (fun u : 𝒪[L]ˣ ↦ ((u : 𝒪[L]) : L)) (hx σ)
      simpa using this
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hfix
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact (Units.ne_zero x) (by exact_mod_cast hc.symm)
  have h1 : c ∈ 𝒪[K] := (algebraMap_mem_integer_iff K L c).1 (hc ▸ (x : 𝒪[L]).2)
  have h2 : c⁻¹ ∈ 𝒪[K] := by
    refine (algebraMap_mem_integer_iff K L c⁻¹).1 ?_
    have e : algebraMap K L c⁻¹ = (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) := by
      rw [map_inv₀, hc, eq_comm, ← mul_eq_one_iff_eq_inv₀ (by exact_mod_cast (Units.ne_zero x))]
      exact_mod_cast congrArg (fun u : 𝒪[L] ↦ (u : L)) x.inv_mul
    rw [e]
    exact (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L])).2
  refine ⟨⟨⟨c, h1⟩, ⟨c⁻¹, h2⟩, ?_, ?_⟩, hc⟩
  · ext
    simp [hc0]
  · ext
    simp [hc0]

/- English proof (translation)
Rewrite using `[subsingleton_tateZero_iff]`. Introduce `x hx`. Take `⟨w, hw⟩` from `exists_eq_of_forall_smul_eq hx`. Take `⟨v, rfl⟩` from `normIntegerUnits_surjective (K := K) (L := L) w`. Use `⟨v, Units.ext (Subtype.ext ?_)⟩` and prove the remaining obligations.

Rewrite using `[coe_tateNorm_integerUnits, ← hw, ← coe_norm_integer, coe_normIntegerUnits_eq]`.
-/
theorem subsingleton_tateZero_integerUnits [IsGalois K L] [IsUnramified K L] :
    Subsingleton (TateZero (L ≃ₐ[K] L) 𝒪[L]ˣ) := by
  rw [subsingleton_tateZero_iff]
  intro x hx
  obtain ⟨w, hw⟩ := exists_eq_of_forall_smul_eq hx
  obtain ⟨v, rfl⟩ := normIntegerUnits_surjective (K := K) (L := L) w
  refine ⟨v, Units.ext (Subtype.ext ?_)⟩
  rw [coe_tateNorm_integerUnits, ← hw, ← coe_norm_integer, coe_normIntegerUnits_eq]

/- English proof (translation)
Rewrite using `[subsingleton_tateNegOne_iff]`. Introduce `x hx`. Take `⟨g, hg⟩` from `IsCyclic.exists_generator (α := L ≃ₐ[K] L)`. Establish `hxL : tateNorm (L ≃ₐ[K] L) Lˣ (unitsIncl L x) = 1`. Rewrite using `[tateNorm_apply]`.

Repeatedly rewrite using `[← unitsIncl_smul]`. Rewrite using `[← map_prod, ← tateNorm_apply, hx, map_one]`. Take `⟨y, hy⟩` from `exists_smul_div_eq_of_tateNorm_eq_one hg hxL`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Establish `hϖL` using `irreducible_algebraMap_of_isUnramified (L := L) hϖ`.

Take `⟨⟨m, v⟩, rfl⟩` from `(unitsOfIntProd_bijective hϖL).2 y`. Establish `hπ : g • uniformizerUnit hϖL = uniformizerUnit hϖL`. Use `ext`. Express the relevant statement in the definitionally equal form `g ((uniformizerUnit hϖL : Lˣ) : L) = _`. Rewrite using `[coe_uniformizerUnit, coe_algebraMap_integer, AlgEquiv.commutes]`.

Establish `hx' : x = g • v / v`. Apply `unitsIncl_injective (K := L)` to reduce the goal to its premises. Rewrite using `[← hy, unitsOfIntProd_eq, _root_.map_div, unitsIncl_smul, smul_mul', smul_zpow', hπ, mul_div_mul_left_eq_div]`. Rewrite using `[hx']`. Conclude with `Subgroup.subset_closure ⟨g, v, rfl⟩`.
-/
theorem subsingleton_tateNegOne_integerUnits [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    [IsUnramified K L] :
    Subsingleton (TateNegOne (L ≃ₐ[K] L) 𝒪[L]ˣ) := by
  rw [subsingleton_tateNegOne_iff]
  intro x hx
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  have hxL : tateNorm (L ≃ₐ[K] L) Lˣ (unitsIncl L x) = 1 := by
    rw [tateNorm_apply]
    simp_rw [← unitsIncl_smul]
    rw [← map_prod, ← tateNorm_apply, hx, map_one]
  obtain ⟨y, hy⟩ := exists_smul_div_eq_of_tateNorm_eq_one hg hxL
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖL := irreducible_algebraMap_of_isUnramified (L := L) hϖ
  obtain ⟨⟨m, v⟩, rfl⟩ := (unitsOfIntProd_bijective hϖL).2 y
  have hπ : g • uniformizerUnit hϖL = uniformizerUnit hϖL := by
    ext
    change g ((uniformizerUnit hϖL : Lˣ) : L) = _
    rw [coe_uniformizerUnit, coe_algebraMap_integer, AlgEquiv.commutes]
  have hx' : x = g • v / v := by
    apply unitsIncl_injective (K := L)
    rw [← hy, unitsOfIntProd_eq, _root_.map_div, unitsIncl_smul, smul_mul', smul_zpow', hπ,
      mul_div_mul_left_eq_div]
  rw [hx']
  exact Subgroup.subset_closure ⟨g, v, rfl⟩

end GroundTheory.LocalField
