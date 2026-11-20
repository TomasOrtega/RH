import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NuInRange
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Formalism.LocalRingCardinality.Lemmas
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem

/- English proof (translation)
Establish `hV : OrthogonalFamily ℂ (fun i => p i) (fun i => (p i).subtypeₗᵢ)` using `OrthogonalFamily.of_pairwise (fun i j h => horth i j h)`. Establish `hint : DirectSum.IsInternal p` using `(DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top p).2 ⟨hV.independent, htop⟩`. Set `v : ∀ i, OrthonormalBasis (Fin (Module.finrank ℂ (p i))) ℂ (p i)` to `fun i => stdOrthonormalBasis ℂ (p i)`. Set `c` to `hint.collectedOrthonormalBasis hV v`. Establish `hc : ∀ a : (Σ i, Fin (Module.finrank ℂ (p i))), c a = (v a.1 a.2 : E)`.

Introduce `a`. Simplify using `[c, DirectSum.IsInternal.collectedOrthonormalBasis, DirectSum.IsInternal.collectedBasis_coe]`. Establish `hcard : Fintype.card (Σ i, Fin (Module.finrank ℂ (p i))) = Module.finrank ℂ E` using `(Module.finrank_eq_card_basis c.toBasis).symm`. Set `e : (Σ i, Fin (Module.finrank ℂ (p i))) ≃ Fin (Module.finrank ℂ E)` to `Fintype.equivFinOfCardEq hcard`. Use `⟨c.reindex e, fun σ => (e.symm σ).1, fun i => ?_⟩` and prove the remaining obligations.

Establish `himg : (c.reindex e) '' {σ | (e.symm σ).1 = i} = (p i).subtype '' Set.range (v i).toBasis`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨σ, hσ, rfl⟩`. Rewrite using `[OrthonormalBasis.reindex_apply, hc]`.

Simplify using `only [Set.mem_ofPred_eq] at hσ`. Generalize the expression as in `e.symm σ = a at hσ`. Take `⟨j, k⟩` from `a`. Substitute `hσ` using the available equality. Conclude with `⟨v j k, ⟨k, by simp⟩, rfl⟩`.

Introduce and unpack `⟨_, ⟨k, rfl⟩, rfl⟩`. Use `⟨e ⟨i, k⟩, by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply, hc]`. Simplify using the standard rewrite rules. Rewrite using `[himg, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]`.
-/
theorem exists_orthonormalBasis_adapted (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (I : Type) [Fintype I] [DecidableEq I] (p : I → Submodule ℂ E)
    (htop : (⨆ i, p i) = ⊤) (horth : ∀ i j, i ≠ j → p i ⟂ p j) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E) (ty : Fin (Module.finrank ℂ E) → I),
      ∀ i, Submodule.span ℂ (b '' {σ | ty σ = i}) = p i := by
  classical
  have hV : OrthogonalFamily ℂ (fun i => p i) (fun i => (p i).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise (fun i j h => horth i j h)
  have hint : DirectSum.IsInternal p :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top p).2 ⟨hV.independent, htop⟩
  let v : ∀ i, OrthonormalBasis (Fin (Module.finrank ℂ (p i))) ℂ (p i) :=
    fun i => stdOrthonormalBasis ℂ (p i)
  let c := hint.collectedOrthonormalBasis hV v
  have hc : ∀ a : (Σ i, Fin (Module.finrank ℂ (p i))), c a = (v a.1 a.2 : E) := by
    intro a
    simp [c, DirectSum.IsInternal.collectedOrthonormalBasis, DirectSum.IsInternal.collectedBasis_coe]
  have hcard : Fintype.card (Σ i, Fin (Module.finrank ℂ (p i))) = Module.finrank ℂ E :=
    (Module.finrank_eq_card_basis c.toBasis).symm
  let e : (Σ i, Fin (Module.finrank ℂ (p i))) ≃ Fin (Module.finrank ℂ E) :=
    Fintype.equivFinOfCardEq hcard
  refine ⟨c.reindex e, fun σ => (e.symm σ).1, fun i => ?_⟩
  have himg : (c.reindex e) '' {σ | (e.symm σ).1 = i}
      = (p i).subtype '' Set.range (v i).toBasis := by
    ext x
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      rw [OrthonormalBasis.reindex_apply, hc]
      simp only [Set.mem_ofPred_eq] at hσ
      generalize e.symm σ = a at hσ
      obtain ⟨j, k⟩ := a
      subst hσ
      exact ⟨v j k, ⟨k, by simp⟩, rfl⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      refine ⟨e ⟨i, k⟩, by simp, ?_⟩
      rw [OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply, hc]
      simp
  rw [himg, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

end GlobalTheory.Mem
