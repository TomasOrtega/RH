import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU Filter Topology

namespace GlobalTheory.UnitarySmallSub

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ d J N hN`. Set `e` to `GlobalTheory.ThK.SquareIntegrability.toGAd hσ J (one_ne_zero : (1 : E) ≠ 0)`. Establish `he : Continuous e` using `continuous_subtype_val.subtype_mk _`. Establish `he' : Continuous e.symm` using `continuous_subtype_val.subtype_mk _`. Use `haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GFin σ ((1 : E) • J.map σ)`.

Establish `hc` using `continuous_ofFin σ ((1 : E) • J.map σ)`. Establish `hN' : {y | e.symm (ofFin σ _ y) ∈ N} ∈ 𝓝 (1 : GFin σ ((1 : E) • J.map σ))`. Use `(he'.comp hc).continuousAt.preimage_mem_nhds ?_` and prove the remaining obligations. Rewrite using `[Function.comp_apply, map_one, map_one]`. Conclude with `hN`.

Take `⟨W, hW⟩` from `NonarchimedeanGroup.is_nonarchimedean _ hN'`. Use `⟨W.toSubgroup.comap ((projFin σ _).comp e.toMonoidHom), W.isOpen.preimage ((continuous_projFin σ _).comp he), ?_⟩` and prove the remaining obligations. Introduce `k hk hkm`. Establish `hfin : e k ∈ finPts σ ((1 : E) • J.map σ)`. Use `Units.ext ?_` and prove the remaining obligations.

Conclude with `hkm`. Establish `h` using `ofInf_projInf_mul_ofFin_projFin σ _ (e k)`. Rewrite `h` using `[mem_finPts.1 hfin, map_one, one_mul]`. Use `hW hk` as an intermediate fact. Simplify using `only [Set.mem_setOf_eq, MonoidHom.coe_comp, Function.comp_apply] at this`.

Express the relevant statement in the definitionally equal form `e.symm (ofFin σ _ (projFin σ _ (e k))) ∈ N at this`. Rewrite `this` using `[h, MulEquiv.symm_apply_apply]`. Conclude with `this`.
-/
theorem exists_open_subgroup_finite_subset : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ x, σ (σ x) = x) → ∀ {d : ℕ} (J : Matrix (Fin d) (Fin d) E), ∀ N ∈ 𝓝 (1 : UA σ J),
      ∃ U : Subgroup (UA σ J), IsOpen (U : Set (UA σ J)) ∧
        ∀ k ∈ U, (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 → k ∈ N := by
  intro F E _ _ _ _ _ σ hσ d J N hN
  let e := GlobalTheory.ThK.SquareIntegrability.toGAd hσ J (one_ne_zero : (1 : E) ≠ 0)
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GFin σ ((1 : E) • J.map σ)
  have hc := continuous_ofFin σ ((1 : E) • J.map σ)
  have hN' : {y | e.symm (ofFin σ _ y) ∈ N} ∈ 𝓝 (1 : GFin σ ((1 : E) • J.map σ)) := by
    refine (he'.comp hc).continuousAt.preimage_mem_nhds ?_
    rw [Function.comp_apply, map_one, map_one]
    exact hN
  obtain ⟨W, hW⟩ := NonarchimedeanGroup.is_nonarchimedean _ hN'
  refine ⟨W.toSubgroup.comap ((projFin σ _).comp e.toMonoidHom),
    W.isOpen.preimage ((continuous_projFin σ _).comp he), ?_⟩
  intro k hk hkm
  have hfin : e k ∈ finPts σ ((1 : E) • J.map σ) := by
    refine Units.ext ?_
    exact hkm
  have h := ofInf_projInf_mul_ofFin_projFin σ _ (e k)
  rw [mem_finPts.1 hfin, map_one, one_mul] at h
  have := hW hk
  simp only [Set.mem_setOf_eq, MonoidHom.coe_comp, Function.comp_apply] at this
  change e.symm (ofFin σ _ (projFin σ _ (e k))) ∈ N at this
  rw [h, MulEquiv.symm_apply_apply] at this
  exact this

end GlobalTheory.UnitarySmallSub
