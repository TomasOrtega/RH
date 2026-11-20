import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

/- English proof (translation)
Use `(mem_standardOpenSubgroup F).2 fun v ↦ ?_` and prove the remaining obligations. Establish `h1 : ((infiniteEmbedding w a : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1`. Rewrite using `[coe_infiniteEmbedding]`. Both sides reduce to the same expression. Establish `h2 : (((infiniteEmbedding w a)⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1`.

Rewrite using `[← map_inv, coe_infiniteEmbedding]`. Both sides reduce to the same expression. Rewrite using `[h1, h2]`. Conclude with `⟨one_mem _, one_mem _⟩`.
-/
theorem infiniteEmbedding_mem_standardOpenSubgroup {F : Type*} [Field F] [NumberField F]
    (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    infiniteEmbedding w a ∈ standardOpenSubgroup F := by
  refine (mem_standardOpenSubgroup F).2 fun v ↦ ?_
  have h1 : ((infiniteEmbedding w a : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
    rw [coe_infiniteEmbedding]
    rfl
  have h2 : (((infiniteEmbedding w a)⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
    rw [← map_inv, coe_infiniteEmbedding]
    rfl
  rw [h1, h2]
  exact ⟨one_mem _, one_mem _⟩

/- English proof (translation)
Use `(χ.infiniteParams_unique w (p := (0, 0)) (fun _ ↦ ⟨le_rfl, by norm_num⟩) fun a ↦ ?_).symm` and prove the remaining obligations. Establish `h : χ.toIdele (infiniteEmbedding w a) = 1` using `hχ (infiniteEmbedding_mem_standardOpenSubgroup w a)`. Simplify using `[HeckeCharacter.infiniteComponent_apply, h]`.
-/
theorem infiniteParams_eq_zero {F : Type*} [Field F] [NumberField F] (χ : HeckeCharacter F)
    (hχ : standardOpenSubgroup F ≤ χ.toIdele.ker) (w : InfinitePlace F) :
    χ.infiniteParams w = (0, 0) := by
  refine (χ.infiniteParams_unique w (p := (0, 0)) (fun _ ↦ ⟨le_rfl, by norm_num⟩) fun a ↦ ?_).symm
  have h : χ.toIdele (infiniteEmbedding w a) = 1 :=
    hχ (infiniteEmbedding_mem_standardOpenSubgroup w a)
  simp [HeckeCharacter.infiniteComponent_apply, h]

/- English proof (translation)
Introduce `F _ _ _ χ hχ s`. Establish `hw : ∀ w : InfinitePlace F, χ.infiniteGamma w s = Complex.Gammaℝ s` using `fun w ↦ by`. Establish `hr : w.IsReal` using `IsTotallyReal.isReal w`. Establish `hp` using `infiniteParams_eq_zero χ hχ w`. Simplify using `[HeckeCharacter.infiniteGamma, hr, HeckeCharacter.infiniteTau, HeckeCharacter.infiniteWeight, hp]`.

Establish `hcard : Fintype.card (InfinitePlace F) = Module.finrank ℚ F`. Establish `h1` using `InfinitePlace.card_add_two_mul_card_eq_rank F`. Establish `h2` using `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F`. Establish `h3` using `IsTotallyReal.nrComplexPlaces_eq_zero F`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[HeckeCharacter.gammaFactor, Finset.prod_congr rfl fun w _ ↦ hw w, Finset.prod_const, Finset.card_univ, hcard]`.
-/
theorem gammaFactor_eq_of_unramified : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (χ : HeckeCharacter F), standardOpenSubgroup F ≤ χ.toIdele.ker →
    ∀ s : ℂ, χ.gammaFactor s = Complex.Gammaℝ s ^ Module.finrank ℚ F := by
  intro F _ _ _ χ hχ s
  have hw : ∀ w : InfinitePlace F, χ.infiniteGamma w s = Complex.Gammaℝ s := fun w ↦ by
    have hr : w.IsReal := IsTotallyReal.isReal w
    have hp := infiniteParams_eq_zero χ hχ w
    simp [HeckeCharacter.infiniteGamma, hr, HeckeCharacter.infiniteTau,
      HeckeCharacter.infiniteWeight, hp]
  have hcard : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
    have h3 := IsTotallyReal.nrComplexPlaces_eq_zero F
    omega
  rw [HeckeCharacter.gammaFactor, Finset.prod_congr rfl fun w _ ↦ hw w, Finset.prod_const,
    Finset.card_univ, hcard]

end GlobalTheory.CompanionTheory.PartialZeta
