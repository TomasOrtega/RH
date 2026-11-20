import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.EtaleCohomology.EtaleTrace.LCompDecPf
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

/- English proof (translation)
Introduce `k _ _ X Y p r π hπ hfin t U hU`. Take `⟨t0, ht0⟩` from `t`. Express the relevant statement in the definitionally equal form `↑U = (Set.range t0)ᶜ at hU`. Establish `hA : IsLocallyArtinian (pullback π t0)` using `IsLocallyArtinian.of_locallyQuasiFinite (pullback.snd π t0)`. Establish `hD : DiscreteTopology ↥(pullback π t0)` using `inferInstance`.

Establish `hF : Finite ↥(pullback π t0)`. Establish `h` using `(pullback.snd π t0).finite_preimage_singleton (IsLocalRing.closedPoint k)`. Rewrite using `[← Set.finite_univ_iff]`. Use `h.subset fun z _ => ?_` and prove the remaining obligations. Conclude with `Subsingleton.elim _ _`.

Use `haveI : Fintype ↥(pullback π t0) := Fintype.ofFinite _`. Set `c : ↥(S k)` to `IsLocalRing.closedPoint k`. Set `e : ↥(pullback π t0) → (S k ⟶ pullback π t0)` to `fun z => pointOfClosedPoint (pullback.snd π t0) z (isClosed_discrete _)`. Establish `he : ∀ z, e z ≫ pullback.snd π t0 = 𝟙 _` using `fun z => pointOfClosedPoint_comp _ _ _`. Establish `he' : ∀ z, e z c = z` using `fun z => pointOfClosedPoint_apply _ _ _ _`.

Set `g : ↥(pullback π t0) → Pt p` to `fun z => ⟨e z ≫ pullback.fst π t0, by`. Rewrite using `[Category.assoc, ← hπ, ← Category.assoc (pullback.fst π t0), pullback.condition, Category.assoc, ht0, Category.comp_id, he]⟩`. Use `⟨Finset.univ.image g, ?_⟩` and prove the remaining obligations. Unfold `OffPts`. Rewrite using `[Scheme.Hom.coe_preimage, hU, Set.preimage_compl]`.

Use `congr 1`. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_range, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_iUnion, exists_prop]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`.

Take `⟨z, hz1, -⟩` from `Scheme.Pullback.exists_preimage_pullback x a ha.symm`. Use `⟨g z, ⟨z, rfl⟩, c, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(e z ≫ pullback.fst π t0) c = x`. Rewrite using `[Scheme.Hom.comp_apply, he', hz1]`. Introduce and unpack `⟨y, ⟨z, rfl⟩, b, rfl⟩`.

Use `⟨(e z ≫ pullback.snd π t0) b, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(e z ≫ pullback.snd π t0 ≫ t0) b = (e z ≫ pullback.fst π t0 ≫ π) b`. Rewrite using `[pullback.condition]`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.finFib_holds :
    UpperTheory.Gal.KunnethLefschetz.FinFib := by
  intro k _ _ X Y p r π hπ hfin t U hU
  classical
  obtain ⟨t0, ht0⟩ := t
  change ↑U = (Set.range t0)ᶜ at hU
  have hA : IsLocallyArtinian (pullback π t0) :=
    IsLocallyArtinian.of_locallyQuasiFinite (pullback.snd π t0)
  have hD : DiscreteTopology ↥(pullback π t0) := inferInstance
  have hF : Finite ↥(pullback π t0) := by
    have h := (pullback.snd π t0).finite_preimage_singleton (IsLocalRing.closedPoint k)
    rw [← Set.finite_univ_iff]
    refine h.subset fun z _ => ?_
    exact Subsingleton.elim _ _
  haveI : Fintype ↥(pullback π t0) := Fintype.ofFinite _
  let c : ↥(S k) := IsLocalRing.closedPoint k
  let e : ↥(pullback π t0) → (S k ⟶ pullback π t0) := fun z =>
    pointOfClosedPoint (pullback.snd π t0) z (isClosed_discrete _)
  have he : ∀ z, e z ≫ pullback.snd π t0 = 𝟙 _ := fun z => pointOfClosedPoint_comp _ _ _
  have he' : ∀ z, e z c = z := fun z => pointOfClosedPoint_apply _ _ _ _
  let g : ↥(pullback π t0) → Pt p := fun z =>
    ⟨e z ≫ pullback.fst π t0, by
      rw [Category.assoc, ← hπ, ← Category.assoc (pullback.fst π t0), pullback.condition,
        Category.assoc, ht0, Category.comp_id, he]⟩
  refine ⟨Finset.univ.image g, ?_⟩
  unfold OffPts
  rw [Scheme.Hom.coe_preimage, hU, Set.preimage_compl]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_range, Finset.mem_image, Finset.mem_univ, true_and,
    Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback x a ha.symm
    refine ⟨g z, ⟨z, rfl⟩, c, ?_⟩
    change (e z ≫ pullback.fst π t0) c = x
    rw [Scheme.Hom.comp_apply, he', hz1]
  · rintro ⟨y, ⟨z, rfl⟩, b, rfl⟩
    refine ⟨(e z ≫ pullback.snd π t0) b, ?_⟩
    change (e z ≫ pullback.snd π t0 ≫ t0) b = (e z ≫ pullback.fst π t0 ≫ π) b
    rw [pullback.condition]
