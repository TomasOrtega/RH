import Mathlib

universe u

namespace AlgebraicGeometry.Scheme

/- English proof (translation)
Take `⟨U, hU, hxU, -⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X) (show x ∈ (⊤ : X.Opens) from trivial)`. Conclude with `⟨U, hxU, hU⟩`.
-/
theorem exists_isAffineOpen_mem {X : Scheme.{u}} (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U := by
  obtain ⟨U, hU, hxU, -⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)
      (show x ∈ (⊤ : X.Opens) from trivial)
  exact ⟨U, hxU, hU⟩

/- English proof (translation)
Establish `hx : x ∈ (⨆ U : X.affineOpens, (U : X.Opens))`. Rewrite using `[AlgebraicGeometry.iSup_affineOpens_eq_top X]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨U, hU⟩` from `TopologicalSpace.Opens.mem_iSup.mp hx`. Conclude with `⟨U, hU⟩`.
-/
theorem exists_affineOpens_mem {X : Scheme.{u}} (x : X) : ∃ U : X.affineOpens, x ∈ U.1 := by
  have hx : x ∈ (⨆ U : X.affineOpens, (U : X.Opens)) := by
    rw [AlgebraicGeometry.iSup_affineOpens_eq_top X]
    trivial
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨U, hU⟩

/- English proof (translation)
Take `⟨V, hV, hxV, hsub⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen`. Take `⟨W, hW, rfl⟩` from `hV`. Conclude with `⟨⟨W, hW⟩, hxV, hsub⟩`.
-/
theorem exists_affineOpens_mem_le {X : Scheme.{u}} {x : X} {U : X.Opens} (hx : x ∈ U) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ U := by
  obtain ⟨V, hV, hxV, hsub⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  obtain ⟨W, hW, rfl⟩ := hV
  exact ⟨⟨W, hW⟩, hxV, hsub⟩

end AlgebraicGeometry.Scheme
