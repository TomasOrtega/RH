import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

namespace GlobalTheory.CompanionTheory.CptDiag

/- English proof (translation)
Establish `hK : IsCompact (φ '' closure (Subgroup.zpowers t : Set G))` using `ht.image hφ`. Use `hK.of_isClosed_subset isClosed_closure ?_` and prove the remaining obligations. Use `closure_minimal ?_ hK.isClosed` and prove the remaining obligations. Introduce `x hx`. Take `⟨k, rfl⟩` from `Subgroup.mem_zpowers_iff.mp hx`.

Conclude with `⟨t ^ k, subset_closure (Subgroup.zpow_mem_zpowers t k), map_zpow φ t k⟩`.
-/
theorem isCompact_closure_zpowers_image {G G' : Type} [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G']
    [T2Space G'] (φ : G →* G') (hφ : Continuous φ) (t : G)
    (ht : IsCompact (closure (Subgroup.zpowers t : Set G))) :
    IsCompact (closure (Subgroup.zpowers (φ t) : Set G')) := by
  have hK : IsCompact (φ '' closure (Subgroup.zpowers t : Set G)) := ht.image hφ
  refine hK.of_isClosed_subset isClosed_closure ?_
  refine closure_minimal ?_ hK.isClosed
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact ⟨t ^ k, subset_closure (Subgroup.zpow_mem_zpowers t k), map_zpow φ t k⟩

/- English proof (translation)
Introduce `H _ _ _ _ Z`. Unfold `cptPart`. Rewrite using `[MonoidHom.map_closure]`. Use `congr 1`. Use extensionality with `u`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hu, hc⟩`. Take `⟨t, ht, rfl⟩` from `Subgroup.mem_map.mp hu`. Use `⟨t, ⟨ht, ?_⟩, rfl⟩` and prove the remaining obligations. Use `isCompact_closure_zpowers_image (MonoidHom.fst H H) continuous_fst _ hc` as an intermediate fact.

Simplify using `using this`. Introduce and unpack `⟨t, ⟨ht, hc⟩, rfl⟩`. Establish `hcont : Continuous ((MonoidHom.id H).prod (MonoidHom.id H))` using `by show Continuous fun x : H => (x, x)`. Conclude with `continuous_id.prodMk continuous_id`. Conclude with `⟨Subgroup.mem_map_of_mem _ ht, isCompact_closure_zpowers_image _ hcont t hc⟩`.
-/
theorem cptPart_diag : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (Z : Subgroup H), cptPart (Z.map ((MonoidHom.id H).prod (MonoidHom.id H))) = (cptPart Z).map ((MonoidHom.id H).prod (MonoidHom.id H)) := by
  intro H _ _ _ _ Z
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  ext u
  constructor
  · rintro ⟨hu, hc⟩
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hu
    refine ⟨t, ⟨ht, ?_⟩, rfl⟩
    have := isCompact_closure_zpowers_image (MonoidHom.fst H H) continuous_fst _ hc
    simpa using this
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    have hcont : Continuous ((MonoidHom.id H).prod (MonoidHom.id H)) := by
      show Continuous fun x : H => (x, x)
      exact continuous_id.prodMk continuous_id
    exact ⟨Subgroup.mem_map_of_mem _ ht, isCompact_closure_zpowers_image _ hcont t hc⟩

end GlobalTheory.CompanionTheory.CptDiag
