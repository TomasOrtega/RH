import Development.EtaleCohomology.EtaleSheaves.ChowGraphCut

open CategoryTheory AlgebraicGeometry

namespace LateralTheory.E.CoverExistence

/- English proof (translation)
Introduce `A _ X p _ _`. Establish `: CompactSpace X` using `QuasiCompact.compactSpace_of_compactSpace p`. Establish `h : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V`. Introduce `x`. Take `⟨V, hV, hxV, -⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)`.

Conclude with `⟨V, hV, hxV⟩`. Use `choose V hV hxV using h`. Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover (fun x => (V x : Set X)) (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)`. Use `⟨t.card, fun j => V (t.equivFin.symm j), fun j => hV _, fun j => ⟨_, hxV _⟩, fun x => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, hxy⟩` from `Set.mem_iUnion₂.mp (ht (Set.mem_univ x))`.

Conclude with `⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩`.
-/
theorem Cover_of : LateralTheory.E.ChowGraphCut.Cover := by
  intro A _ X p _ _
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have h : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := by
    intro x
    obtain ⟨V, hV, hxV, -⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨V, hV, hxV⟩
  choose V hV hxV using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  refine ⟨t.card, fun j => V (t.equivFin.symm j), fun j => hV _, fun j => ⟨_, hxV _⟩, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact ⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩

end LateralTheory.E.CoverExistence
