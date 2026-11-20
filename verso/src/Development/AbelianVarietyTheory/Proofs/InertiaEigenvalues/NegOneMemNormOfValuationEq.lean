import Mathlib
import GroundTheory.LocalFields.UnramifiedNormSurj
open ValuativeRel

namespace GlobalTheory

open GroundTheory.LocalField in

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ _ _ _ _ hval`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[E]`. Take `⟨x, h1, h2⟩` from `hval (ϖ : E)`. Establish `hv : valuation E (ϖ : E) = valuation E (algebraMap F E x)` using `le_antisymm ((Valuation.Compatible.vle_iff_le _ _).1 h1) ((Valuation.Compatible.vle_iff_le _ _).1 h2)`. Establish `hord : ord (ϖ : E) = ord (algebraMap F E x)`.

Simplify using `only [ord]`. Rewrite using `[(normalizedValuation_eq_iff (K := E)).2 hv]`. Rewrite `hord` using `[ord_uniformizer hϖ, ord_algebraMap]`. Establish `he : ramificationIndex F E = 1`. Establish `hd : ((ramificationIndex F E : ℕ) : ℤ) ∣ 1` using `⟨ord x, hord⟩`.

Conclude with `Int.eq_one_of_dvd_one (by positivity) hd` after adjusting the coercions. Use `haveI : IsUnramified F E := (isUnramified_iff F E).2 he`. Take `⟨w, hw⟩` from `normIntegerUnits_surjective (K := F) (L := E) (-1)`. Use `⟨((w : 𝒪[E]) : E), ?_⟩` and prove the remaining obligations. Use `congrArg (fun u : 𝒪[F]ˣ => ((u : 𝒪[F]) : F)) hw` as an intermediate fact.

Simplify using `only [coe_normIntegerUnits_eq] at this`. Rewrite using `[← coe_norm_integer]`. Simplify using `using this`.
-/
theorem neg_one_mem_norm_of_valuation_eq : ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E], (∀ y : E, ∃ x : F, y ≤ᵥ algebraMap F E x ∧ algebraMap F E x ≤ᵥ y) → ∃ z : E, Algebra.norm F z = -1 := by
  intro F E _ _ _ _ _ _ _ _ _ _ _ hval
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  obtain ⟨x, h1, h2⟩ := hval (ϖ : E)
  have hv : valuation E (ϖ : E) = valuation E (algebraMap F E x) :=
    le_antisymm ((Valuation.Compatible.vle_iff_le _ _).1 h1) ((Valuation.Compatible.vle_iff_le _ _).1 h2)
  have hord : ord (ϖ : E) = ord (algebraMap F E x) := by
    simp only [ord]
    rw [(normalizedValuation_eq_iff (K := E)).2 hv]
  rw [ord_uniformizer hϖ, ord_algebraMap] at hord
  have he : ramificationIndex F E = 1 := by
    have hd : ((ramificationIndex F E : ℕ) : ℤ) ∣ 1 := ⟨ord x, hord⟩
    exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hd
  haveI : IsUnramified F E := (isUnramified_iff F E).2 he
  obtain ⟨w, hw⟩ := normIntegerUnits_surjective (K := F) (L := E) (-1)
  refine ⟨((w : 𝒪[E]) : E), ?_⟩
  have := congrArg (fun u : 𝒪[F]ˣ => ((u : 𝒪[F]) : F)) hw
  simp only [coe_normIntegerUnits_eq] at this
  rw [← coe_norm_integer]
  simpa using this

end GlobalTheory
