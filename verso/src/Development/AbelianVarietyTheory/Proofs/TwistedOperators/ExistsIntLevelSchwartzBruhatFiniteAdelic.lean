import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupsIntegers

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.SBLevel

/- English proof (translation)
Introduce `F _ _ κ _ g hg`. Take `⟨N, hN, hNg⟩` from `GlobalTheory.SBBox.exists_nhds_zero_add_eq hg.1 hg.2`. Rewrite `hN` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, -, t, ht, hIt⟩` from `hN`. Establish `hW : (⋂ i, t i) ∈ nhds (0 : FiniteAdeleRing (𝓞 F) F)` using `Filter.iInter_mem.2 ht`.

Take `⟨d, hd0, hd⟩` from `GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW`. Use `⟨d, hd0, fun x u hu => hNg x u (hIt fun i _ => ?_)⟩` and prove the remaining obligations. Establish `hdK : (algebraMap (𝓞 F) F d) ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]` and apply the resulting hypothesis. Establish `hmem` using `hd (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) (hu i)`.

Establish `he : algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F d) * (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) = u i`. Rewrite using `[← mul_assoc, ← map_mul]`. Establish `: algebraMap (𝓞 F) F d * (d : F)⁻¹ = 1` using `mul_inv_cancel₀ hdK`. Rewrite using `[this, map_one, one_mul]`. Rewrite `hmem` using `[he]`.

Conclude with `Set.mem_iInter.1 hmem i`.
-/
theorem exists_int_level : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ x u : κ → FiniteAdeleRing (𝓞 F) F,
      (∀ i, ∀ v : HeightOneSpectrum (𝓞 F),
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) v ∈ v.adicCompletionIntegers F) →
      g (x + u) = g x := by
  intro F _ _ κ _ g hg
  classical
  obtain ⟨N, hN, hNg⟩ := GlobalTheory.SBBox.exists_nhds_zero_add_eq hg.1 hg.2
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, -, t, ht, hIt⟩ := hN
  have hW : (⋂ i, t i) ∈ nhds (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.2 ht
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  refine ⟨d, hd0, fun x u hu => hNg x u (hIt fun i _ => ?_)⟩
  have hdK : (algebraMap (𝓞 F) F d) ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  have hmem := hd (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) (hu i)
  have he : algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F d) *
      (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) = u i := by
    rw [← mul_assoc, ← map_mul]
    have : algebraMap (𝓞 F) F d * (d : F)⁻¹ = 1 := mul_inv_cancel₀ hdK
    rw [this, map_one, one_mul]
  rw [he] at hmem
  exact Set.mem_iInter.1 hmem i

end GlobalTheory.SBLevel
