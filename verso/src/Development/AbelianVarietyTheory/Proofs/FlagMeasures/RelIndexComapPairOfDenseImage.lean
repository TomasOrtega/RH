import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexComapEqOfCosetsHit
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit`. Consider the case `exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit`. Consider the case `(apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit ..)`.
-/
theorem index_comap_of_dense_image {A B : Type} [Group A] [Group B] (f : A →* B) (H : Subgroup B)
    (hf : ∀ b, ∃ a, (f a)⁻¹ * b ∈ H) : (H.comap f).index = H.index := by
  first
  | exact @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit
  | exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit
  | (apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)
  | (intros; apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit ..)

/- English proof (translation)
Set `f : U.comap φ →* U` to `φ.subgroupComap U`. Establish `hc : (K.comap φ).subgroupOf (U.comap φ) = (K.subgroupOf U).comap f`. Use extensionality with `x`. Conclude with `Iff.rfl`. Establish `key` using `index_comap_of_dense_image f (K.subgroupOf U) (by`.

Introduce and unpack `⟨b, hb⟩`. Take `⟨γ, hγK, hγU⟩` from `h b hb`. Establish `hγ : φ γ ∈ U`. Use `U.mul_mem hb (U.inv_mem hγU)` as an intermediate fact. Simplify using `using this`.

Use `⟨⟨γ, hγ⟩, ?_⟩` and prove the remaining obligations. Conclude with `hγK)`. Simplify using `only [Subgroup.relIndex]`. Rewrite using `[hc, key]`.
-/
theorem relIndex_comap_of_dense_image {Γ G : Type} [Group Γ] [Group G] (φ : Γ →* G)
    (K U : Subgroup G) (h : ∀ g ∈ U, ∃ γ, (φ γ)⁻¹ * g ∈ K ⊓ U) :
    (K.comap φ).relIndex (U.comap φ) = K.relIndex U := by
  let f : U.comap φ →* U := φ.subgroupComap U
  have hc : (K.comap φ).subgroupOf (U.comap φ) = (K.subgroupOf U).comap f := by
    ext x
    exact Iff.rfl
  have key := index_comap_of_dense_image f (K.subgroupOf U) (by
    rintro ⟨b, hb⟩
    obtain ⟨γ, hγK, hγU⟩ := h b hb
    have hγ : φ γ ∈ U := by
      have := U.mul_mem hb (U.inv_mem hγU)
      simpa using this
    refine ⟨⟨γ, hγ⟩, ?_⟩
    exact hγK)
  simp only [Subgroup.relIndex]
  rw [hc, key]

/- English proof (translation)
Introduce `Γ G _ _ φ K U h`. Use `⟨relIndex_comap_of_dense_image φ K U fun g hg => h g (Or.inr hg), ?_⟩` and prove the remaining obligations. Use `relIndex_comap_of_dense_image φ U K fun g hg => ?_` and prove the remaining obligations. Take `⟨γ, hγ⟩` from `h g (Or.inl hg)`. Conclude with `⟨γ, by rwa [inf_comm]⟩`.
-/
theorem relIndex_pair_comap_of_dense_image : ∀ {Γ G : Type} [Group Γ] [Group G] (φ : Γ →* G) (K U : Subgroup G), (∀ g, g ∈ K ∨ g ∈ U → ∃ γ, (φ γ)⁻¹ * g ∈ K ⊓ U) → (K.comap φ).relIndex (U.comap φ) = K.relIndex U ∧ (U.comap φ).relIndex (K.comap φ) = U.relIndex K := by
  intro Γ G _ _ φ K U h
  refine ⟨relIndex_comap_of_dense_image φ K U fun g hg => h g (Or.inr hg), ?_⟩
  refine relIndex_comap_of_dense_image φ U K fun g hg => ?_
  obtain ⟨γ, hγ⟩ := h g (Or.inl hg)
  exact ⟨γ, by rwa [inf_comm]⟩

end GlobalTheory.HL
