import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QuasiFiniteAtGenericPointOfIsDominant

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
/- English proof (translation)
Unfold `_root_.GlobalTheory.SS.SmConn at hG hG'`. Take `⟨-, hsm, hsep, hqc, hgc⟩` from `hG`. Take `⟨-, hsm', hsep', hqc', hgc'⟩` from `hG'`. Establish `hw : i.left ≫ G'.hom = G.hom` using `Over.w i`. Establish `: Subsingleton (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)` using `inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))`.

Establish `: Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)` using `inferInstanceAs (Nonempty (Spec (CommRingCat.of k)))`. Establish `: ConnectedSpace G.left` using `GeometricallyConnected.connectedSpace_of_subsingleton G.hom`. Establish `: ConnectedSpace G'.left` using `GeometricallyConnected.connectedSpace_of_subsingleton G'.hom`. Establish `: IsIntegral G.left` using `_root_.GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace (K := k) G.hom`. Establish `: IsIntegral G'.left` using `_root_.GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace (K := k) G'.hom`.

Establish `: LocallyOfFiniteType (i.left ≫ G'.hom)` using `by rw [hw]; infer_instance`. Establish `: LocallyOfFiniteType i.left` using `locallyOfFiniteType_of_comp i.left G'.hom`. Establish `: JacobsonSpace G'.left` using `LocallyOfFiniteType.jacobsonSpace (Y := Spec _) G'.hom`. Establish `hcl : closedPoints G'.left ⊆ Set.range i.left`. Introduce `y hy`.

Take `⟨x, hx⟩` from `hpts (Over.homMk (pointOfClosedPoint (K := k) G'.hom y hy) (pointOfClosedPoint_comp _ _ _))`. Use `⟨x.left (IsLocalRing.closedPoint k), ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun φ : 𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G' => φ.left (IsLocalRing.closedPoint k)) hx`. Simplify using `only [Over.comp_left, Scheme.Hom.comp_apply] at h`. Conclude with `h.trans (pointOfClosedPoint_apply _ _ _ _)`.

Establish `hgen : i.left (genericPoint G.left) = genericPoint G'.left`. Establish `hη : closure {genericPoint G.left} = Set.univ` using `genericPoint_spec G.left`. Establish `h1 : closure (Set.range i.left) = Set.univ` using `Set.eq_univ_of_univ_subset (closure_closedPoints (X := G'.left) ▸ closure_mono hcl)`. Establish `h2 : Set.range i.left ⊆ closure {i.left (genericPoint G.left)}`. Introduce and unpack `_ ⟨x, rfl⟩`.

Conclude with `map_mem_closure i.left.continuous (hη ▸ Set.mem_univ x) (by simp)`. Establish `h3 : IsGenericPoint (i.left (genericPoint G.left)) Set.univ`. Use `Set.eq_univ_of_univ_subset ?_` and prove the remaining obligations. Rewrite using `[← h1]`. Simplify using `using closure_mono h2`.

Conclude with `h3.eq (genericPoint_spec G'.left)`. Establish `hq : i.left.QuasiFiniteAt (genericPoint G.left)`. Rewrite using `[Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]`. Establish `hfib : ∀ a : i.left.fiber (i.left (genericPoint G.left)), i.left.fiberι _ a = genericPoint G.left`. Introduce `a`.

Establish `ha : i.left.fiberι _ a ∈ i.left ⁻¹' {i.left (genericPoint G.left)}`. Rewrite using `[← Scheme.Hom.range_fiberι]`. Conclude with `Set.mem_range_self a`. Use `_root_.GlobalTheory.OntoFinite.eq_genericPoint (K := k) G'.hom i.left g (by rw [hw]; exact hgG) hgG' _ ?_` and prove the remaining obligations. Rewrite using `[← hgen]`.

Conclude with `ha`. Establish `: Subsingleton (i.left.fiber (i.left (genericPoint G.left)))` using `⟨fun a b => (i.left.fiberι _).isEmbedding.injective ((hfib a).trans (hfib b).symm)⟩`. Use `isOpen_univ` and compare the differences between its conclusion and the goal. Conclude with `Set.eq_univ_of_forall fun b => Subsingleton.elim b _`. Establish `: LocallyQuasiFinite i.left` using `_root_.GlobalTheory.OntoFinite.locallyQuasiFinite_of_quasiFiniteAt (K := k) i _ hq`.

Establish `hpb : IsPullback (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left i.left (η[G'] : 𝟙_ _ ⟶ G').left` using `IsPullback.map (Over.forget _) (IsPullback.of_hasPullback _ _)`. Establish `: LocallyQuasiFinite (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left` using `MorphismProperty.of_isPullback hpb ‹_›`. Establish `hsec : (η[G'] : 𝟙_ _ ⟶ G').left ≫ G'.hom = 𝟙 _` using `Over.w _`. Establish `: IsClosedImmersion ((η[G'] : 𝟙_ _ ⟶ G').left ≫ G'.hom)` using `by rw [hsec]; infer_instance`. Establish `: IsClosedImmersion (η[G'] : 𝟙_ _ ⟶ G').left` using `IsClosedImmersion.of_comp _ G'.hom`.

Establish `: IsClosedImmersion (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left` using `MorphismProperty.of_isPullback hpb.flip ‹_›`. Establish `hw2 : (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left ≫ 𝟙 _ = (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left ≫ G.hom`. Conclude with `(Over.w (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G'))).trans (Over.w (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G'))).symm`. Establish `: QuasiCompact (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left`. Establish `h2 : QuasiCompact ((pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left ≫ G.hom)` using `inferInstance`.

Rewrite `h2` using `[← hw2, Category.comp_id]`. Conclude with `h2`. Establish `: IsLocallyArtinian (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k))).left` using `inferInstanceAs (IsLocallyArtinian (Spec (CommRingCat.of k)))`. Conclude with `IsFinite.of_locallyQuasiFinite _`.
-/
private theorem isFinite_pullback_unit_of_surjective_on_points (k : Type) [Field k] [IsAlgClosed k]
    (G G' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) [GrpObj G] [GrpObj G'] (g : ℕ) (hG : _root_.GlobalTheory.SS.SmConn G)
    (hG' : _root_.GlobalTheory.SS.SmConn G') (hgG : SmoothOfRelativeDimension g G.hom)
    (hgG' : SmoothOfRelativeDimension g G'.hom) (i : G ⟶ G') [IsMonHom i]
    (hpts : ∀ y : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G'), ∃ x : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G), x ≫ i = y) :
    IsFinite (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left := by
  unfold _root_.GlobalTheory.SS.SmConn at hG hG'
  obtain ⟨-, hsm, hsep, hqc, hgc⟩ := hG
  obtain ⟨-, hsm', hsep', hqc', hgc'⟩ := hG'
  have hw : i.left ≫ G'.hom = G.hom := Over.w i
  have : Subsingleton (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  have : Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := inferInstanceAs (Nonempty (Spec (CommRingCat.of k)))
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace_of_subsingleton G.hom
  have : ConnectedSpace G'.left := GeometricallyConnected.connectedSpace_of_subsingleton G'.hom
  have : IsIntegral G.left := _root_.GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace (K := k) G.hom
  have : IsIntegral G'.left := _root_.GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace (K := k) G'.hom
  have : LocallyOfFiniteType (i.left ≫ G'.hom) := by rw [hw]; infer_instance
  have : LocallyOfFiniteType i.left := locallyOfFiniteType_of_comp i.left G'.hom
  have : JacobsonSpace G'.left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) G'.hom
  have hcl : closedPoints G'.left ⊆ Set.range i.left := by
    intro y hy
    obtain ⟨x, hx⟩ := hpts (Over.homMk (pointOfClosedPoint (K := k) G'.hom y hy)
      (pointOfClosedPoint_comp _ _ _))
    refine ⟨x.left (IsLocalRing.closedPoint k), ?_⟩
    have h := congrArg (fun φ : 𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G' => φ.left (IsLocalRing.closedPoint k)) hx
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at h
    exact h.trans (pointOfClosedPoint_apply _ _ _ _)
  have hgen : i.left (genericPoint G.left) = genericPoint G'.left := by
    have hη : closure {genericPoint G.left} = Set.univ := genericPoint_spec G.left
    have h1 : closure (Set.range i.left) = Set.univ :=
      Set.eq_univ_of_univ_subset (closure_closedPoints (X := G'.left) ▸ closure_mono hcl)
    have h2 : Set.range i.left ⊆ closure {i.left (genericPoint G.left)} := by
      rintro _ ⟨x, rfl⟩
      exact map_mem_closure i.left.continuous (hη ▸ Set.mem_univ x) (by simp)
    have h3 : IsGenericPoint (i.left (genericPoint G.left)) Set.univ := by
      refine Set.eq_univ_of_univ_subset ?_
      rw [← h1]
      simpa using closure_mono h2
    exact h3.eq (genericPoint_spec G'.left)
  have hq : i.left.QuasiFiniteAt (genericPoint G.left) := by
    rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
    have hfib : ∀ a : i.left.fiber (i.left (genericPoint G.left)),
        i.left.fiberι _ a = genericPoint G.left := by
      intro a
      have ha : i.left.fiberι _ a ∈ i.left ⁻¹' {i.left (genericPoint G.left)} := by
        rw [← Scheme.Hom.range_fiberι]; exact Set.mem_range_self a
      refine _root_.GlobalTheory.OntoFinite.eq_genericPoint (K := k) G'.hom i.left g (by rw [hw]; exact hgG)
        hgG' _ ?_
      rw [← hgen]; exact ha
    have : Subsingleton (i.left.fiber (i.left (genericPoint G.left))) :=
      ⟨fun a b => (i.left.fiberι _).isEmbedding.injective ((hfib a).trans (hfib b).symm)⟩
    convert isOpen_univ
    exact Set.eq_univ_of_forall fun b => Subsingleton.elim b _
  have : LocallyQuasiFinite i.left :=
    _root_.GlobalTheory.OntoFinite.locallyQuasiFinite_of_quasiFiniteAt (K := k) i _ hq
  have hpb : IsPullback (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left
      (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left i.left (η[G'] : 𝟙_ _ ⟶ G').left :=
    IsPullback.map (Over.forget _) (IsPullback.of_hasPullback _ _)
  have : LocallyQuasiFinite (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left :=
    MorphismProperty.of_isPullback hpb ‹_›
  have hsec : (η[G'] : 𝟙_ _ ⟶ G').left ≫ G'.hom = 𝟙 _ := Over.w _
  have : IsClosedImmersion ((η[G'] : 𝟙_ _ ⟶ G').left ≫ G'.hom) := by rw [hsec]; infer_instance
  have : IsClosedImmersion (η[G'] : 𝟙_ _ ⟶ G').left := IsClosedImmersion.of_comp _ G'.hom
  have : IsClosedImmersion (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left :=
    MorphismProperty.of_isPullback hpb.flip ‹_›
  have hw2 : (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left ≫ 𝟙 _ =
      (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left ≫ G.hom := by
    exact (Over.w (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G'))).trans
      (Over.w (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G'))).symm
  have : QuasiCompact (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left := by
    have h2 : QuasiCompact ((pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left ≫ G.hom) := inferInstance
    rw [← hw2, Category.comp_id] at h2
    exact h2
  have : IsLocallyArtinian (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k))).left :=
    inferInstanceAs (IsLocallyArtinian (Spec (CommRingCat.of k)))
  exact IsFinite.of_locallyQuasiFinite _

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in

/- English proof (translation)
Introduce `k _ _ G G' _ _ g hG hG' hgG hgG' i _ hpts`. Conclude with `isFinite_pullback_unit_of_surjective_on_points k G G' g hG hG' hgG hgG' i hpts`.
-/
theorem _root_.GlobalTheory.SS.isFinite_ker_of_surjective_points_of_dim_eq : ∀ (k : Type) [Field k] [IsAlgClosed k]
    (G G' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) [GrpObj G] [GrpObj G'] (g : ℕ), _root_.GlobalTheory.SS.SmConn G →
    _root_.GlobalTheory.SS.SmConn G' → SmoothOfRelativeDimension g G.hom →
    SmoothOfRelativeDimension g G'.hom → ∀ i : G ⟶ G', IsMonHom i →
    (∀ y : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G'), ∃ x : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G), x ≫ i = y) →
    IsFinite (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left := by
  intro k _ _ G G' _ _ g hG hG' hgG hgG' i _ hpts
  exact isFinite_pullback_unit_of_surjective_on_points k G G' g hG hG' hgG hgG' i hpts

end GlobalTheory.SS
