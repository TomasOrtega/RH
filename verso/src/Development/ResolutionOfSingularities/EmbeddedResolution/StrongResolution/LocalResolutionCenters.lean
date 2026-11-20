import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionData
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrongResolution
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem comp_base_apply {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (z : ↥A) :
    (a ≫ b).base z = b.base (a.base z) := by
  simp

/- English proof (translation)
Rewrite using `[← comp_base_apply, e.inv_hom_id]`. Simplify using the standard rewrite rules.
-/
private theorem hom_base_inv_base_apply {A B : Scheme.{u}} (e : A ≅ B) (z : ↥B) :
    e.hom.base (e.inv.base z) = z := by
  rw [← comp_base_apply, e.inv_hom_id]
  simp

/- English proof (translation)
Rewrite using `[Scheme.IdealSheafData.support_comap]`. Conclude with `hz`.
-/
private theorem mem_support_comap_of_mem_support {Z W : Scheme.{u}} (g : Z ⟶ W) (I : W.IdealSheafData)
    (z : ↥Z) (hz : g.base z ∈ I.support) : z ∈ (I.comap g).support := by
  rw [Scheme.IdealSheafData.support_comap]
  exact hz

/- English proof (translation)
Introduce `i hi x hx`. Choose the witnesses or unpack the hypotheses as in `⟨i₀, u, hu⟩ : ∃ (i₀ : d.cover.I₀) (u : ↥(d.cover.X i₀)), (d.cover.f i₀).base u = (s.projectionToBase i).base x := by`. Take `⟨u, hu⟩` from `d.cover.covers ((s.projectionToBase i).base x)`. Conclude with `⟨d.cover.idx ((s.projectionToBase i).base x), u, hu⟩`. Take `⟨w, hw1, hw2⟩` from `Scheme.Pullback.exists_preimage_pullback u x hu`.

Establish `hw1' : (pullback.fst (d.cover.f i₀) (s.projectionToBase i)).base w = u` using `hw1`. Establish `hw2' : (pullback.snd (d.cover.f i₀) (s.projectionToBase i)).base w = x` using `hw2`. Establish `hws : w ∈ ((s.center i).comap (pullback.snd (d.cover.f i₀) (s.projectionToBase i))).support`. Use `mem_support_comap_of_mem_support _ _ _ ?_` and prove the remaining obligations. Rewrite using `[hw2']`.

Conclude with `hx`. Take `⟨l, hl, hr⟩` from `(d.exists_reindex_eq_iff_exists_mem_support i₀ i hi).2 ⟨w, hws⟩`. Substitute `hr` using the available equality. Establish `ht : ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w) ∈ ((d.seq i₀).center l).support`. Rewrite using `[d.localSequence_center_eq_comap i₀ l hl]`.

Use `mem_support_comap_of_mem_support _ _ _ ?_` and prove the remaining obligations. Rewrite using `[comp_base_apply, hom_base_inv_base_apply, hw2']`. Conclude with `hx`. Establish `key : ((d.seq i₀).projectionToBase l).base ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w) = (pullback.fst (d.cover.f i₀) (s.projectionToBase (d.reindex i₀ l))).base w`. Rewrite using `[← d.schemeAtIsoPullback_hom_fst i₀ l hl.le, comp_base_apply, hom_base_inv_base_apply]`.

Establish `hres` using `d.isResolution i₀`. Unfold `FunctorialResolution.EmbeddedResolution.IsStrongResolution at hres`. Take `⟨-, -, -, -, hC, -⟩` from `hres`. Establish `hCt : ((d.seq i₀).projectionToBase l).base ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w) ∈ ((smoothLocusComplement (d.cover.f i₀ ≫ f) : TopologicalSpace.Closeds ↥(d.cover.X i₀)) : Set ↥(d.cover.X i₀))` using `hC l hl _ ht`. Rewrite `hCt` using `[← d.preimage_smoothLocusComplement_cover_map i₀]`.

Establish `hfin : (d.cover.f i₀).base (((d.seq i₀).projectionToBase l).base ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w)) ∈ ((smoothLocusComplement f : TopologicalSpace.Closeds ↥X) : Set ↥X)` using `hCt`. Use `show (s.projectionToBase (d.reindex i₀ l)).base x ∈ ((smoothLocusComplement f : TopologicalSpace.Closeds ↥X) : Set ↥X)`. Rewrite using `[← hu, ← hw1', ← key]`. Conclude with `hfin`.
-/
theorem centersLieOver_smoothLocusComplement (d : LocalResolutionData k f s) :
    s.CentersLieOver ((smoothLocusComplement f : TopologicalSpace.Closeds ↥X) : Set ↥X) := by
  intro i hi x hx
  obtain ⟨i₀, u, hu⟩ : ∃ (i₀ : d.cover.I₀) (u : ↥(d.cover.X i₀)),
      (d.cover.f i₀).base u = (s.projectionToBase i).base x := by
    obtain ⟨u, hu⟩ := d.cover.covers ((s.projectionToBase i).base x)
    exact ⟨d.cover.idx ((s.projectionToBase i).base x), u, hu⟩
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback u x hu
  have hw1' : (pullback.fst (d.cover.f i₀) (s.projectionToBase i)).base w = u := hw1
  have hw2' : (pullback.snd (d.cover.f i₀) (s.projectionToBase i)).base w = x := hw2
  have hws : w ∈ ((s.center i).comap (pullback.snd (d.cover.f i₀) (s.projectionToBase i))).support := by
    refine mem_support_comap_of_mem_support _ _ _ ?_
    rw [hw2']
    exact hx
  obtain ⟨l, hl, hr⟩ := (d.exists_reindex_eq_iff_exists_mem_support i₀ i hi).2 ⟨w, hws⟩
  subst hr
  have ht : ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w) ∈ ((d.seq i₀).center l).support := by
    rw [d.localSequence_center_eq_comap i₀ l hl]
    refine mem_support_comap_of_mem_support _ _ _ ?_
    rw [comp_base_apply, hom_base_inv_base_apply, hw2']
    exact hx
  have key : ((d.seq i₀).projectionToBase l).base ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w)
      = (pullback.fst (d.cover.f i₀) (s.projectionToBase (d.reindex i₀ l))).base w := by
    rw [← d.schemeAtIsoPullback_hom_fst i₀ l hl.le, comp_base_apply, hom_base_inv_base_apply]
  have hres := d.isResolution i₀
  unfold FunctorialResolution.EmbeddedResolution.IsStrongResolution at hres
  obtain ⟨-, -, -, -, hC, -⟩ := hres
  have hCt : ((d.seq i₀).projectionToBase l).base ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w) ∈
      ((smoothLocusComplement (d.cover.f i₀ ≫ f) : TopologicalSpace.Closeds ↥(d.cover.X i₀)) :
        Set ↥(d.cover.X i₀)) := hC l hl _ ht
  rw [← d.preimage_smoothLocusComplement_cover_map i₀] at hCt
  have hfin : (d.cover.f i₀).base
      (((d.seq i₀).projectionToBase l).base ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w)) ∈
      ((smoothLocusComplement f : TopologicalSpace.Closeds ↥X) : Set ↥X) := hCt
  show (s.projectionToBase (d.reindex i₀ l)).base x ∈
    ((smoothLocusComplement f : TopologicalSpace.Closeds ↥X) : Set ↥X)
  rw [← hu, ← hw1', ← key]
  exact hfin

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution
