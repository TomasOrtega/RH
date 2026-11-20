import Development.EtaleCohomology.CohomologicalPurity.LeafFlqPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.Flq

/- English proof (translation)
Proceed by induction on `ha using AddSubgroup.closure_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `zero => exact ⟨0, map_zero _, map_zero _⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨b, hb0, hb⟩` from `hx`.

Take `⟨c, hc0, hc⟩` from `hy`. Use `⟨b + c, ?_, ?_⟩` and prove the remaining obligations. Use `show ((K.X (n-1)).obj.map U'.ι.op).hom (b + c) = 0`. Rewrite using `[map_add, show ((K.X (n-1)).obj.map U'.ι.op).hom b = 0 from hb0, show ((K.X (n-1)).obj.map U'.ι.op).hom c = 0 from hc0, add_zero]`. Use `show ((K.d (n - 1) n).hom.app (op Y)).hom (b + c) = x + y`.

Rewrite using `[map_add]`. Rewrite using `[← hb, ← hc]`. Consider the case `neg x _ hx`. Take `⟨b, hb0, hb⟩` from `hx`. Use `⟨-b, ?_, ?_⟩` and prove the remaining obligations.

Use `show ((K.X (n-1)).obj.map U'.ι.op).hom (-b) = 0`. Rewrite using `[map_neg]`. Rewrite using `[show ((K.X (n-1)).obj.map U'.ι.op).hom b = 0 from hb0, neg_zero]`. Use `show ((K.d (n - 1) n).hom.app (op Y)).hom (-b) = -x`. Rewrite using `[map_neg]`.

Rewrite using `[← hb]`.
-/
theorem etale_section_boundary_of_mem_addSubgroup_closure {R : Type} [CommRing R] (K : Cx R) {Y : Scheme.{0}} (U' : Y.Opens) (n : ℤ)
    (a : Sec (K.X n) Y) (ha : a ∈ AddSubgroup.closure {a | Bd K U' n a}) : Bd K U' n a := by
  induction ha using AddSubgroup.closure_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, map_zero _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb0, hb⟩ := hx
    obtain ⟨c, hc0, hc⟩ := hy
    refine ⟨b + c, ?_, ?_⟩
    · show ((K.X (n-1)).obj.map U'.ι.op).hom (b + c) = 0
      rw [map_add, show ((K.X (n-1)).obj.map U'.ι.op).hom b = 0 from hb0, show ((K.X (n-1)).obj.map U'.ι.op).hom c = 0 from hc0, add_zero]
    · show ((K.d (n - 1) n).hom.app (op Y)).hom (b + c) = x + y
      rw [map_add]; rw [← hb, ← hc]
  | neg x _ hx =>
    obtain ⟨b, hb0, hb⟩ := hx
    refine ⟨-b, ?_, ?_⟩
    · show ((K.X (n-1)).obj.map U'.ι.op).hom (-b) = 0
      rw [map_neg]; rw [show ((K.X (n-1)).obj.map U'.ι.op).hom b = 0 from hb0, neg_zero]
    · show ((K.d (n - 1) n).hom.app (op Y)).hom (-b) = -x
      rw [map_neg]; rw [← hb]

/- English proof (translation)
Introduce `R _ K X U n W a ha`. Conclude with `etale_section_boundary_of_mem_addSubgroup_closure K _ n a ha`.
-/
theorem LeafBdAdd_of : LeafBdAdd := by
  intro R _ K X U n W a ha
  exact etale_section_boundary_of_mem_addSubgroup_closure K _ n a ha

end LateralTheory.CohomologicalPurity.Cl.Flq
