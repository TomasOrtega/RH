import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTracePairingBilinearNondegenerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiFinRat

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical
open GlobalTheory.BoxLattice GlobalTheory.EvAdm

namespace GlobalTheory.BoxLattice

/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Substitute `ha haveI : Subsingleton (boxLat F κ 0) := by` using the available equality. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, bx, rfl⟩ ⟨y, by', rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Simplify using `[ratInf]`. Use `infer_instance`. Establish `hmem : ∀ x : boxLat F κ a, ∀ i : κ, mixedEmbedding F a⁻¹ * (x : κ → mixedEmbedding.mixedSpace F) i ∈ mixedEmbedding.integerLattice F`. Introduce and unpack `⟨x, b, rfl⟩ i`.

Establish `: mixedEmbedding F a⁻¹ * ratInf F κ (fun i => a * (b i : F)) i = mixedEmbedding F ((b i : 𝓞 F) : F)`. Simplify using `only [ratInf, ← map_mul, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]`. Rewrite using `[this]`. Conclude with `⟨b i, rfl⟩`. Use `DiscreteTopology.of_continuous_injective (f := fun x : boxLat F κ a => fun i : κ => (⟨mixedEmbedding F a⁻¹ * (x : κ → mixedEmbedding.mixedSpace F) i, hmem x i⟩ : mixedEmbedding.integerLattice F)) ?_ ?_` and prove the remaining obligations.

Use `continuous_pi fun i => ?_` and prove the remaining obligations. Use `Continuous.subtype_mk ?_ _` and prove the remaining obligations. Conclude with `continuous_const.mul ((continuous_apply i).comp continuous_subtype_val)`. Introduce `x y hxy`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Establish `h1` using `congrArg Subtype.val (congrFun hxy i)`. Simplify using `only at h1`. Establish `h2` using `congrArg (fun z => mixedEmbedding F a * z) h1`. Simplify using `only [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul] at h2`.

Conclude with `h2`.
-/
theorem boxLat_discrete (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F) :
    DiscreteTopology (boxLat F κ a) := by
  by_cases ha : a = 0
  · subst ha
    haveI : Subsingleton (boxLat F κ 0) := by
      constructor
      rintro ⟨x, bx, rfl⟩ ⟨y, by', rfl⟩
      apply Subtype.ext
      funext i
      simp [ratInf]
    infer_instance
  · have hmem : ∀ x : boxLat F κ a, ∀ i : κ,
        mixedEmbedding F a⁻¹ * (x : κ → mixedEmbedding.mixedSpace F) i ∈
          mixedEmbedding.integerLattice F := by
      rintro ⟨x, b, rfl⟩ i
      have : mixedEmbedding F a⁻¹ * ratInf F κ (fun i => a * (b i : F)) i =
          mixedEmbedding F ((b i : 𝓞 F) : F) := by
        simp only [ratInf, ← map_mul, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
      rw [this]
      exact ⟨b i, rfl⟩
    refine DiscreteTopology.of_continuous_injective
      (f := fun x : boxLat F κ a => fun i : κ =>
        (⟨mixedEmbedding F a⁻¹ * (x : κ → mixedEmbedding.mixedSpace F) i, hmem x i⟩ :
          mixedEmbedding.integerLattice F)) ?_ ?_
    · refine continuous_pi fun i => ?_
      refine Continuous.subtype_mk ?_ _
      exact continuous_const.mul ((continuous_apply i).comp continuous_subtype_val)
    · intro x y hxy
      apply Subtype.ext
      funext i
      have h1 := congrArg Subtype.val (congrFun hxy i)
      simp only at h1
      have h2 := congrArg (fun z => mixedEmbedding F a * z) h1
      simp only [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul] at h2
      exact h2

end GlobalTheory.BoxLattice
