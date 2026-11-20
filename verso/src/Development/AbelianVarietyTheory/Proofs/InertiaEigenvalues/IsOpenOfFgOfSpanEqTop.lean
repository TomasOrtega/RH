import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.Cyc

/- English proof (translation)
Take `⟨n, b, hb⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 hfg`. Establish `hbM : ∀ i, b i ∈ M` using `fun i => hb ▸ Submodule.subset_span ⟨i, rfl⟩`. Establish `hsurj : Function.Surjective (Fintype.linearCombination LL b)`. Rewrite using `[← LinearMap.range_eq_top, Fintype.range_linearCombination, ← hspan, ← hb, Submodule.span_span_of_tower]`. Establish `hopen : IsOpenMap (Fintype.linearCombination LL b)` using `IsModuleTopology.isOpenMap_of_surjective hsurj`.

Use `haveI := IsModuleTopology.topologicalAddGroup LL V`. Establish `hU : IsOpen (Set.pi Set.univ fun _ : Fin n => Set.range (algebraMap O LL))` using `isOpen_set_pi Set.finite_univ fun _ _ => hO`. Use `M.toAddSubgroup.isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset ((hopen _ hU).mem_nhds ⟨0, fun _ _ => ⟨0, by simp⟩, map_zero _⟩) ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[Fintype.linearCombination_apply]`.

Use `M.sum_mem fun i _ => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `hx i (Set.mem_univ i)`. Rewrite using `[← ha, algebraMap_smul]`. Conclude with `M.smul_mem a (hbM i)`.
-/
theorem isOpen_of_fg_of_span_eq_top {LL O V : Type} [Field LL] [TopologicalSpace LL]
    [IsTopologicalRing LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] [TopologicalSpace V] [IsModuleTopology LL V]
    (hO : IsOpen (Set.range (algebraMap O LL))) (M : Submodule O V) (hfg : M.FG)
    (hspan : Submodule.span LL (M : Set V) = ⊤) : IsOpen (M : Set V) := by
  obtain ⟨n, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  have hbM : ∀ i, b i ∈ M := fun i => hb ▸ Submodule.subset_span ⟨i, rfl⟩
  have hsurj : Function.Surjective (Fintype.linearCombination LL b) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, ← hspan, ← hb,
      Submodule.span_span_of_tower]
  have hopen : IsOpenMap (Fintype.linearCombination LL b) :=
    IsModuleTopology.isOpenMap_of_surjective hsurj
  haveI := IsModuleTopology.topologicalAddGroup LL V
  have hU : IsOpen (Set.pi Set.univ fun _ : Fin n => Set.range (algebraMap O LL)) :=
    isOpen_set_pi Set.finite_univ fun _ _ => hO
  refine M.toAddSubgroup.isOpen_of_mem_nhds (g := 0)
    (Filter.mem_of_superset ((hopen _ hU).mem_nhds ⟨0, fun _ _ => ⟨0, by simp⟩, map_zero _⟩) ?_)
  rintro _ ⟨x, hx, rfl⟩
  rw [Fintype.linearCombination_apply]
  refine M.sum_mem fun i _ => ?_
  obtain ⟨a, ha⟩ := hx i (Set.mem_univ i)
  rw [← ha, algebraMap_smul]
  exact M.smul_mem a (hbM i)

/- English proof (translation)
Introduce `G _ _ Qp _ _ LL _ _ _ O _ _ h T`. Use `haveI := h.2.2.2.1`. Conclude with `isOpen_of_fg_of_span_eq_top h.2.2.2.2 T.L.T T.L.fg T.L.span`.
-/
theorem locLat_isOpen : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] [TopologicalSpace Qp] {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL], GoodO (Qp := Qp) LL O → ∀ T : LocLat G Qp LL O, IsOpen (T.L.T : Set T.V) := by
  intro G _ _ Qp _ _ LL _ _ _ O _ _ h T
  haveI := h.2.2.2.1
  exact isOpen_of_fg_of_span_eq_top h.2.2.2.2 T.L.T T.L.fg T.L.span

end GlobalTheory.Cyc
