import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumOfDescendedMultiplicationImpor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOpenPartGroupSchemeProductMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenPartProductMapIrreducibleFibresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearOpenPullbackToSelfProductSurjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.Desc

/- English proof (translation)
Establish `: Smooth G'.hom` using `hG.smooth`. Establish `: GeometricallyConnected G'.hom` using `hG.geomConnected`. Establish `hc : ConnectedSpace (pullback (pullback.snd G'.hom p) t : Scheme.{0})` using `GeometricallyConnected.geometrically_connectedSpace (f := G'.hom) (t ≫ p) _ _ ((IsPullback.of_hasPullback (pullback.snd G'.hom p) t).paste_horiz (IsPullback.of_hasPullback G'.hom p))`. Establish `hs : Smooth (pullback.snd (pullback.snd G'.hom p) t)` using `inferInstance`. Conclude with `GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace K _ (pullback.snd (pullback.snd G'.hom p) t) hs hc`.
-/
theorem irreducibleSpace_fibre_pullback (S : Scheme.{0}) (G' : Over S) [GrpObj G'] (hG : IsSemiAbelian G') {T : Scheme.{0}} (p : T ⟶ S)
    (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ T) :
    IrreducibleSpace (pullback ((Over.pullback p).obj G').hom t : Scheme.{0}) := by
  have : Smooth G'.hom := hG.smooth
  have : GeometricallyConnected G'.hom := hG.geomConnected
  have hc : ConnectedSpace (pullback (pullback.snd G'.hom p) t : Scheme.{0}) :=
    GeometricallyConnected.geometrically_connectedSpace (f := G'.hom) (t ≫ p) _ _
      ((IsPullback.of_hasPullback (pullback.snd G'.hom p) t).paste_horiz (IsPullback.of_hasPullback G'.hom p))
  have hs : Smooth (pullback.snd (pullback.snd G'.hom p) t) := inferInstance
  exact GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace K _ (pullback.snd (pullback.snd G'.hom p) t) hs hc

/- English proof (translation)
Establish `t : IsPullback (pullback.snd N.U.hom (pullback.fst π π ≫ π)) (toS N p hp ≫ pullback.fst N.U.hom π) (p ≫ π) N.U.hom`. Rewrite using `[toS, pullback.lift_fst, hp]`. Conclude with `(IsPullback.of_hasPullback _ _).flip`. Establish `s : IsPullback (pullback.snd N.U.hom (pullback.fst π π ≫ π)) (toS N p hp) p (pullback.snd N.U.hom π)` using `IsPullback.of_bot t (by rw [toS, pullback.lift_snd]) (IsPullback.of_hasPullback N.U.hom π).flip`. Use `IsPullback.of_right ?_ (by rw [embL, pullback.lift_fst]) (IsPullback.of_hasPullback G.hom p).flip` and prove the remaining obligations.

Rewrite using `[embL, pullback.lift_snd, N.u_over]`. Conclude with `s`.
-/
theorem isPullback_embL {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}
    (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    IsPullback (embL N p hp) (toS N p hp) (pullback.fst G.hom p) N.u := by
  have t : IsPullback (pullback.snd N.U.hom (pullback.fst π π ≫ π)) (toS N p hp ≫ pullback.fst N.U.hom π) (p ≫ π) N.U.hom := by
    rw [toS, pullback.lift_fst, hp]; exact (IsPullback.of_hasPullback _ _).flip
  have s : IsPullback (pullback.snd N.U.hom (pullback.fst π π ≫ π)) (toS N p hp) p (pullback.snd N.U.hom π) :=
    IsPullback.of_bot t (by rw [toS, pullback.lift_snd]) (IsPullback.of_hasPullback N.U.hom π).flip
  refine IsPullback.of_right ?_ (by rw [embL, pullback.lift_fst]) (IsPullback.of_hasPullback G.hom p).flip
  rw [embL, pullback.lift_snd, N.u_over]; exact s

/- English proof (translation)
Use `N.isOpen` as an intermediate fact. Conclude with `MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_embL N p hp).flip this`.
-/
theorem isOpenImmersion_embL {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}
    (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) : IsOpenImmersion (embL N p hp) := by
  have := N.isOpen
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_embL N p hp).flip this

/- English proof (translation)
Introduce `R _ _ _ _ S π _ hπ _ G' _ _ hG N p hp`. Establish `: Smooth G'.hom` using `hG.smooth`. Establish `: IsSeparated G'.hom` using `hG.separated`. Establish `: QuasiCompact N.U.hom` using `N.quasiCompact`. Establish `ho : IsOpenImmersion (emb N p hp).left` using `isOpenImmersion_embL N p hp`.

Establish `hfl : Flat ((Over.pullback p).obj G').hom`. Express the relevant statement in the definitionally equal form `Flat (pullback.snd G'.hom p)`. Use `infer_instance`. Use `⟨GlobalTheory.T.flat_openPart_groupScheme_productMap _ _ _ _ ho hfl, GlobalTheory.T.surjective_openPart_productMap_irreducible_fibres _ _ _ _ ho (GlobalTheory.T.nearOpenPullbackToSelfProduct_surjective R S π hπ G' N) (irreducibleSpace_fibre_pullback S G' hG p), ?_⟩` and prove the remaining obligations. Establish `: QuasiCompact (UT N ⊗ UT N).hom`.

Express the relevant statement in the definitionally equal form `QuasiCompact (pullback.fst (UT N).hom (UT N).hom ≫ (UT N).hom)`. Establish `h1 : QuasiCompact (UT N).hom`. Express the relevant statement in the definitionally equal form `QuasiCompact (pullback.snd N.U.hom (pullback.fst π π ≫ π))`. Use `infer_instance`. Establish `h2 : QuasiCompact (pullback.fst (UT N).hom (UT N).hom)` using `inferInstance`.

Use `infer_instance`. Establish `: QuasiSeparated ((Over.pullback p).obj G').hom`. Express the relevant statement in the definitionally equal form `QuasiSeparated (pullback.snd G'.hom p)`. Use `infer_instance`. Establish `hw : (Desc.sum N p hp).left ≫ ((Over.pullback p).obj G').hom = (UT N ⊗ UT N).hom` using `Over.w _`.

Establish `: QuasiCompact ((Desc.sum N p hp).left ≫ ((Over.pullback p).obj G').hom)` using `by rw [hw]; infer_instance`. Conclude with `QuasiCompact.of_comp _ (((Over.pullback p).obj G').hom)`.
-/
theorem sum_flat_surjective_quasiCompact : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', ∀ (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π), Flat (Desc.sum N p hp).left ∧ Surjective (Desc.sum N p hp).left ∧ QuasiCompact (Desc.sum N p hp).left := by
  intro R _ _ _ _ S π _ hπ _ G' _ _ hG N p hp
  have : Smooth G'.hom := hG.smooth
  have : IsSeparated G'.hom := hG.separated
  have : QuasiCompact N.U.hom := N.quasiCompact
  have ho : IsOpenImmersion (emb N p hp).left := isOpenImmersion_embL N p hp
  have hfl : Flat ((Over.pullback p).obj G').hom := by
    change Flat (pullback.snd G'.hom p); infer_instance
  refine ⟨GlobalTheory.T.flat_openPart_groupScheme_productMap _ _ _ _ ho hfl, GlobalTheory.T.surjective_openPart_productMap_irreducible_fibres _ _ _ _ ho (GlobalTheory.T.nearOpenPullbackToSelfProduct_surjective R S π hπ G' N) (irreducibleSpace_fibre_pullback S G' hG p), ?_⟩
  have : QuasiCompact (UT N ⊗ UT N).hom := by
    change QuasiCompact (pullback.fst (UT N).hom (UT N).hom ≫ (UT N).hom)
    have h1 : QuasiCompact (UT N).hom := by
      change QuasiCompact (pullback.snd N.U.hom (pullback.fst π π ≫ π)); infer_instance
    have h2 : QuasiCompact (pullback.fst (UT N).hom (UT N).hom) := inferInstance
    infer_instance
  have : QuasiSeparated ((Over.pullback p).obj G').hom := by
    change QuasiSeparated (pullback.snd G'.hom p); infer_instance
  have hw : (Desc.sum N p hp).left ≫ ((Over.pullback p).obj G').hom = (UT N ⊗ UT N).hom := Over.w _
  have : QuasiCompact ((Desc.sum N p hp).left ≫ ((Over.pullback p).obj G').hom) := by rw [hw]; infer_instance
  exact QuasiCompact.of_comp _ (((Over.pullback p).obj G').hom)
end GlobalTheory.Mum.Desc
