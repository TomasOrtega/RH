import Development.EtaleCohomology.EtaleSheaves.LeafCompPf
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Topology TopologicalSpace

namespace LateralTheory.E.E4.GeomPf

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun x => IsEmpty.elim (inferInstance : IsEmpty (∅ : Scheme.{0})) ((Sigma.desc (fun j : Fin 0 => j.elim0) : (∐ Z) ⟶ (∅ : Scheme.{0})) x)⟩`.
-/
lemma sigma_empty_isEmpty (Z : Fin 0 → Scheme.{0}) : IsEmpty (∐ Z : Scheme.{0}) :=
  ⟨fun x => IsEmpty.elim (inferInstance : IsEmpty (∅ : Scheme.{0}))
    ((Sigma.desc (fun j : Fin 0 => j.elim0) : (∐ Z) ⟶ (∅ : Scheme.{0})) x)⟩

def splitIso {n : ℕ} (Z : Fin (n + 1) → Scheme.{0}) :
    (∐ Z : Scheme.{0}) ≅ (Z 0 ⨿ ∐ fun i : Fin n => Z i.succ) :=
  (colimit.isColimit _).coconePointUniqueUpToIso
      (extendCofanIsColimit Z (colimit.isColimit (Discrete.functor fun i : Fin n => Z i.succ))
        (coprodIsCoprod _ _))

/- English proof (translation)
Apply `Sigma.hom_ext` to reduce the goal to its premises. Introduce `j`. Use `Fin.cases ?_ ?_ j` and prove the remaining obligations. Rewrite using `[Sigma.ι_desc, splitIso] erw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc]`. Simplify using `only [extendCofan_ι_app]`.

Use `erw [Fin.cases_zero]`. Conclude with `(coprod.inl_desc _ _).symm`. Introduce `i`. Rewrite using `[Sigma.ι_desc, splitIso]`. Use `erw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc]`.

Simplify using `only [extendCofan_ι_app]`. Use `erw [Fin.cases_succ, Category.assoc, coprod.inr_desc]`. Use `erw [colimit.ι_desc]`. Both sides reduce to the same expression.
-/
lemma desc_split {n : ℕ} (Z : Fin (n + 1) → Scheme.{0}) {X : Scheme.{0}} (ι : ∀ j, Z j ⟶ X) :
    Sigma.desc ι = (splitIso Z).hom ≫ coprod.desc (ι 0) (Sigma.desc fun i => ι i.succ) := by
  apply Sigma.hom_ext
  intro j
  refine Fin.cases ?_ ?_ j
  · rw [Sigma.ι_desc, splitIso]
    erw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc]
    simp only [extendCofan_ι_app]
    erw [Fin.cases_zero]
    exact (coprod.inl_desc _ _).symm
  · intro i
    rw [Sigma.ι_desc, splitIso]
    erw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc]
    simp only [extendCofan_ι_app]
    erw [Fin.cases_succ, Category.assoc, coprod.inr_desc]
    erw [colimit.ι_desc]
    rfl

/- English proof (translation)
The claim follows from `| 0, Z, X, ι, _ => by have := sigma_empty_isEmpty Z infer_instance | n + 1, Z, X, ι, h => by have := isFinite_sigmaDesc n (fun i => Z i.succ) (fun i => ι i.succ) (fun i => h _) have := h 0 rw [desc_split] infer_instance`.
-/
theorem isFinite_sigmaDesc : ∀ (n : ℕ) (Z : Fin n → Scheme.{0}) {X : Scheme.{0}} (ι : ∀ j, Z j ⟶ X),
    (∀ j, IsFinite (ι j)) → IsFinite (Sigma.desc ι)
  | 0, Z, X, ι, _ => by
    have := sigma_empty_isEmpty Z
    infer_instance
  | n + 1, Z, X, ι, h => by
    have := isFinite_sigmaDesc n (fun i => Z i.succ) (fun i => ι i.succ) (fun i => h _)
    have := h 0
    rw [desc_split]
    infer_instance

end LateralTheory.E.E4.GeomPf

namespace LateralTheory.E.E4
open Topology TopologicalSpace

/- English proof (translation)
Introduce `k _ X p _`. Establish `: IsLocallyNoetherian X` using `LocallyOfFiniteType.isLocallyNoetherian p`. Establish `: CompactSpace X` using `QuasiCompact.compactSpace_of_compactSpace p`. Establish `: IsNoetherian X` using `{}`. Establish `hfin` using `finite_irreducibleComponents_of_isNoetherian (X := X)`.

Set `S` to `hfin.toFinset`. Set `e : Fin S.card ≃ S` to `S.equivFin.symm`. Establish `hmem : ∀ j, ((e j : Set X)) ∈ irreducibleComponents X` using `fun j => hfin.mem_toFinset.mp (e j).2`. Set `C : Fin S.card → Closeds X` to `fun j => ⟨e j, isClosed_of_mem_irreducibleComponents _ (hmem j)⟩`. Use `⟨S.card, fun j => (Scheme.IdealSheafData.vanishingIdeal (C j)).subscheme, fun j => (Scheme.IdealSheafData.vanishingIdeal (C j)).subschemeι, fun j => ⟨inferInstance, GlobalTheory.isIntegral_red (hmem j).1⟩, ?_, ?_⟩` and prove the remaining obligations.

Use `GeomPf.isFinite_sigmaDesc S.card (fun j => (Scheme.IdealSheafData.vanishingIdeal (C j)).subscheme) (fun j => (Scheme.IdealSheafData.vanishingIdeal (C j)).subschemeι) (fun j => inferInstance) infer_instance` as an intermediate fact. Apply `Surjective.sigmaDesc_of_union_range_eq_univ` to reduce the goal to its premises. Rewrite using `[Set.eq_univ_iff_forall]`. Introduce `x`. Take `⟨Y, hY, hx⟩` from `exists_mem_irreducibleComponents_subset_of_isIrreducible {x} isIrreducible_singleton`.

Establish `hYS : Y ∈ S` using `hfin.mem_toFinset.mpr hY`. Rewrite using `[Set.mem_iUnion]`. Use `⟨e.symm ⟨Y, hYS⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]`. Simplify using `[C, hx rfl]`.
-/
theorem leafCompGeom : LeafCompGeom := by
  intro k _ X p _
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian X := {}
  have hfin := finite_irreducibleComponents_of_isNoetherian (X := X)
  let S := hfin.toFinset
  let e : Fin S.card ≃ S := S.equivFin.symm
  have hmem : ∀ j, ((e j : Set X)) ∈ irreducibleComponents X := fun j => hfin.mem_toFinset.mp (e j).2
  let C : Fin S.card → Closeds X := fun j => ⟨e j, isClosed_of_mem_irreducibleComponents _ (hmem j)⟩
  refine ⟨S.card, fun j => (Scheme.IdealSheafData.vanishingIdeal (C j)).subscheme,
    fun j => (Scheme.IdealSheafData.vanishingIdeal (C j)).subschemeι,
    fun j => ⟨inferInstance, GlobalTheory.isIntegral_red (hmem j).1⟩, ?_, ?_⟩
  · have := GeomPf.isFinite_sigmaDesc S.card (fun j => (Scheme.IdealSheafData.vanishingIdeal (C j)).subscheme)
      (fun j => (Scheme.IdealSheafData.vanishingIdeal (C j)).subschemeι) (fun j => inferInstance)
    infer_instance
  · apply Surjective.sigmaDesc_of_union_range_eq_univ
    rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨Y, hY, hx⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x} isIrreducible_singleton
    have hYS : Y ∈ S := hfin.mem_toFinset.mpr hY
    rw [Set.mem_iUnion]
    refine ⟨e.symm ⟨Y, hYS⟩, ?_⟩
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    simp [C, hx rfl]

end LateralTheory.E.E4
