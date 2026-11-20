import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiDefs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.PrwZar.Z2

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

/- English proof (translation)
Establish `sec : σ.left ≫ G'.hom = 𝟙 _` using `by simpa using Over.w σ`. Take `⟨τ, hτ⟩` from `GlobalTheory.exists_factor_of_lift_fromSpecResidueField G'.hom p (Scheme.fromSpecResidueField _ p ≫ σ.left) (by rw [Category.assoc, sec, Category.comp_id]; rfl) a (ha.trans (congrArg (fun q => σ.left q) (Scheme.fromSpecResidueField_apply p _)).symm)`. Rewrite using `[← hτ]`. Simplify using `only [Category.assoc, sec, Category.comp_id]`.
-/
private theorem pfiF_fib_subset_lemma {G' : Over (Sp Ω)} (σ : 𝟙_ (Over (Sp Ω)) ⟶ G') {K : Type} [Field K]
    (a : Spec (CommRingCat.of K) ⟶ G'.left) (p : (𝟙_ (Over (Sp Ω))).left)
    (ha : a (IsLocalRing.closedPoint K) = σ.left p) :
    a = (a ≫ G'.hom) ≫ σ.left := by
  have sec : σ.left ≫ G'.hom = 𝟙 _ := by simpa using Over.w σ
  obtain ⟨τ, hτ⟩ := GlobalTheory.exists_factor_of_lift_fromSpecResidueField G'.hom p
    (Scheme.fromSpecResidueField _ p ≫ σ.left)
    (by rw [Category.assoc, sec, Category.comp_id]; rfl) a
    (ha.trans (congrArg (fun q => σ.left q) (Scheme.fromSpecResidueField_apply p _)).symm)
  rw [← hτ]
  simp only [Category.assoc, sec, Category.comp_id]

/- English proof (translation)
Use `haveI : IsFinite H.hom := hH`. Use `haveI : IsProper G.hom := hG.proper`. Use `haveI : IsLocallyArtinian H.left := .of_locallyQuasiFinite H.hom`. Use `haveI : CompactSpace H.left := QuasiCompact.compactSpace_of_compactSpace H.hom`. Use `haveI : IsProper (j.left ≫ G.hom) := by rw [Over.w j]; infer_instance`.

Use `haveI : IsProper j.left := IsProper.of_comp j.left G.hom`. Use `haveI : Finite H.left := finite_of_compact_of_discrete`. Use `⟨Set.finite_range _, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨h, rfl⟩`. Establish `hc` using `j.left.isClosedMap {h} (isClosed_discrete _)`.

Simplify `hc` using `[Set.image_singleton]`.
-/
theorem pfiF_range_finite_closed {G : Over (Sp Ω)} [GrpObj G] (hG : IsAbelianScheme G) (H : Over (Sp Ω))
    (j : H ⟶ G) (hH : IsFinite H.hom) :
    (Set.range j.left).Finite ∧ ∀ z ∈ Set.range j.left, IsClosed ({z} : Set G.left) := by
  haveI : IsFinite H.hom := hH
  haveI : IsProper G.hom := hG.proper
  haveI : IsLocallyArtinian H.left := .of_locallyQuasiFinite H.hom
  haveI : CompactSpace H.left := QuasiCompact.compactSpace_of_compactSpace H.hom
  haveI : IsProper (j.left ≫ G.hom) := by rw [Over.w j]; infer_instance
  haveI : IsProper j.left := IsProper.of_comp j.left G.hom
  haveI : Finite H.left := finite_of_compact_of_discrete
  refine ⟨Set.finite_range _, ?_⟩
  rintro _ ⟨h, rfl⟩
  have hc := j.left.isClosedMap {h} (isClosed_discrete _)
  simpa [Set.image_singleton] using hc

/- English proof (translation)
Set `T : Over (Sp Ω)` to `Over.mk (G.left.fromSpecResidueField y ≫ G.hom)`. Set `x : T ⟶ G` to `Over.homMk (G.left.fromSpecResidueField y) rfl`. Set `c : T ⟶ G` to `toUnit T ≫ s`. Establish `e1` using `Scheme.fromSpecResidueField_apply y (IsLocalRing.closedPoint (G.left.residueField y))`. Establish `hfy : (G.left.fromSpecResidueField y ≫ f.left) (IsLocalRing.closedPoint _) = (s ≫ f).left p` using `(congrArg f.left e1).trans hy`.

Establish `key` using `pfiF_fib_subset_lemma (s ≫ f) (G.left.fromSpecResidueField y ≫ f.left) p hfy`. Establish `hxc : x ≫ f = c ≫ f`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `G.left.fromSpecResidueField y ≫ f.left = (toUnit T ≫ (s ≫ f)).left`. Establish `hb : (G.left.fromSpecResidueField y ≫ f.left) ≫ G'.hom = (toUnit T).left`.

Simplify using `[T]`. Rewrite using `[Over.comp_left]`. Conclude with `key.trans (congrArg (· ≫ (s ≫ f).left) hb)`. Establish `hx' : (x * c⁻¹) ≫ f = 1`. Express the relevant statement in the definitionally equal form `(IsMonHom.monoidHom f T) (x * c⁻¹) = 1`.

Rewrite using `[map_mul, map_inv]`. Express the relevant statement in the definitionally equal form `(x ≫ f) * (c ≫ f)⁻¹ = 1`. Rewrite using `[hxc, mul_inv_cancel]`. Take `⟨z, hz⟩` from `hj T _ hx'`. Establish `hxz : x = z ≫ (j * (toUnit H ≫ s))`.

Establish `hm : z ≫ (j * (toUnit H ≫ s)) = (z ≫ j) * c`. Rewrite using `[Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift, ← Category.assoc z (toUnit H) s, toUnit_unique (z ≫ toUnit H) (toUnit T)]`. Rewrite using `[hm, hz, inv_mul_cancel_right]`. Use `⟨z.left (IsLocalRing.closedPoint (G.left.residueField y)), ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg (fun g : T ⟶ G => g.left (IsLocalRing.closedPoint (G.left.residueField y))) hxz`.

Conclude with `h2.symm.trans e1`.
-/
private theorem pfiF_fib_closed_lemma_2 {G G' : Over (Sp Ω)} [GrpObj G] [GrpObj G'] (f : G ⟶ G')
    [IsMonHom f] (H : Over (Sp Ω)) (j : H ⟶ G)
    (hj : ∀ (T : Over (Sp Ω)) (x : T ⟶ G), x ≫ f = 1 → ∃ z : T ⟶ H, z ≫ j = x)
    (s : 𝟙_ (Over (Sp Ω)) ⟶ G) (p : (𝟙_ (Over (Sp Ω))).left) (y : G.left)
    (hy : f.left y = f.left (s.left p)) : y ∈ Set.range (j * (toUnit H ≫ s)).left := by
  let T : Over (Sp Ω) := Over.mk (G.left.fromSpecResidueField y ≫ G.hom)
  let x : T ⟶ G := Over.homMk (G.left.fromSpecResidueField y) rfl
  let c : T ⟶ G := toUnit T ≫ s
  have e1 := Scheme.fromSpecResidueField_apply y (IsLocalRing.closedPoint (G.left.residueField y))
  have hfy : (G.left.fromSpecResidueField y ≫ f.left) (IsLocalRing.closedPoint _) =
      (s ≫ f).left p :=
    (congrArg f.left e1).trans hy
  have key := pfiF_fib_subset_lemma (s ≫ f) (G.left.fromSpecResidueField y ≫ f.left) p hfy
  have hxc : x ≫ f = c ≫ f := by
    apply Over.OverMorphism.ext
    change G.left.fromSpecResidueField y ≫ f.left = (toUnit T ≫ (s ≫ f)).left
    have hb : (G.left.fromSpecResidueField y ≫ f.left) ≫ G'.hom = (toUnit T).left := by
      simp [T]
    rw [Over.comp_left]
    exact key.trans (congrArg (· ≫ (s ≫ f).left) hb)
  have hx' : (x * c⁻¹) ≫ f = 1 := by
    change (IsMonHom.monoidHom f T) (x * c⁻¹) = 1
    rw [map_mul, map_inv]
    change (x ≫ f) * (c ≫ f)⁻¹ = 1
    rw [hxc, mul_inv_cancel]
  obtain ⟨z, hz⟩ := hj T _ hx'
  have hxz : x = z ≫ (j * (toUnit H ≫ s)) := by
    have hm : z ≫ (j * (toUnit H ≫ s)) = (z ≫ j) * c := by
      rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift, ← Category.assoc z (toUnit H) s,
        toUnit_unique (z ≫ toUnit H) (toUnit T)]
    rw [hm, hz, inv_mul_cancel_right]
  refine ⟨z.left (IsLocalRing.closedPoint (G.left.residueField y)), ?_⟩
  have h2 := congrArg
    (fun g : T ⟶ G => g.left (IsLocalRing.closedPoint (G.left.residueField y))) hxz
  exact h2.symm.trans e1

/- English proof (translation)
Use `haveI : LocallyOfFiniteType G.hom := by haveI := hG.smooth; infer_instance`. Take `⟨s, hs⟩` from `GlobalTheory.RationalPoint.exists_pt_mem (X := G) hx ⟨x, rfl⟩`. Establish `hsx : s.left (IsLocalRing.closedPoint Ω) = x` using `hs`. Establish `hsub : f.left ⁻¹' {f.left x} ⊆ Set.range (j * (toUnit H ≫ s)).left` using `fun y hy => pfiF_fib_closed_lemma_2 f H j hj s (IsLocalRing.closedPoint Ω) y ((hy : f.left y = f.left x).trans (congrArg f.left hsx).symm)`. Take `⟨hfin, hcl⟩` from `pfiF_range_finite_closed hG H (j * (toUnit H ≫ s)) hH`.

Conclude with `⟨hfin.subset hsub, fun z hz => hcl z (hsub hz)⟩`.
-/
theorem pfiF_fib_closed {G G' : Over (Sp Ω)} [GrpObj G] [GrpObj G'] (hG : IsAbelianScheme G) (f : G ⟶ G')
    [IsMonHom f] (H : Over (Sp Ω)) (j : H ⟶ G) (hH : IsFinite H.hom)
    (hj : ∀ (T : Over (Sp Ω)) (x : T ⟶ G), x ≫ f = 1 → ∃ z : T ⟶ H, z ≫ j = x)
    (x : G.left) (hx : IsClosed ({x} : Set G.left)) :
    (f.left ⁻¹' {f.left x}).Finite ∧ ∀ z ∈ f.left ⁻¹' {f.left x}, IsClosed ({z} : Set G.left) := by
  haveI : LocallyOfFiniteType G.hom := by haveI := hG.smooth; infer_instance
  obtain ⟨s, hs⟩ := GlobalTheory.RationalPoint.exists_pt_mem (X := G) hx ⟨x, rfl⟩
  have hsx : s.left (IsLocalRing.closedPoint Ω) = x := hs
  have hsub : f.left ⁻¹' {f.left x} ⊆ Set.range (j * (toUnit H ≫ s)).left := fun y hy =>
    pfiF_fib_closed_lemma_2 f H j hj s (IsLocalRing.closedPoint Ω) y
      ((hy : f.left y = f.left x).trans (congrArg f.left hsx).symm)
  obtain ⟨hfin, hcl⟩ := pfiF_range_finite_closed hG H (j * (toUnit H ≫ s)) hH
  exact ⟨hfin.subset hsub, fun z hz => hcl z (hsub hz)⟩

/- English proof (translation)
Use `haveI : IsProper G.hom := hG.proper`. Use `haveI : IsProper G'.hom := hG'.proper`. Use `haveI : IsProper (f.left ≫ G'.hom) := by rw [Over.w f]; infer_instance`. Use `haveI : IsProper f.left := IsProper.of_comp f.left G'.hom`. Use `haveI : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) G.hom`.

Use `haveI : LocallyQuasiFinite f.left := GlobalTheory.locallyQuasiFinite_of_finite_fibres_closedPoints f.left fun y hy => (pfiF_fib_closed hG f H j hH hj y hy).1`. Conclude with `IsFinite.of_isProper_of_locallyQuasiFinite f.left`.
-/
theorem isFinite_of_ker {Ω : Type} [Field Ω] [IsAlgClosed Ω] {G G' : Over (Sp Ω)} [GrpObj G] [GrpObj G']
    (hG : IsAbelianScheme G) (hG' : IsAbelianScheme G') (f : G ⟶ G') [IsMonHom f] (H : Over (Sp Ω))
    (j : H ⟶ G) (hH : IsFinite H.hom)
    (hj : ∀ (T : Over (Sp Ω)) (x : T ⟶ G), x ≫ f = 1 → ∃ z : T ⟶ H, z ≫ j = x) : IsFinite f.left := by
  haveI : IsProper G.hom := hG.proper
  haveI : IsProper G'.hom := hG'.proper
  haveI : IsProper (f.left ≫ G'.hom) := by rw [Over.w f]; infer_instance
  haveI : IsProper f.left := IsProper.of_comp f.left G'.hom
  haveI : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) G.hom
  haveI : LocallyQuasiFinite f.left :=
    GlobalTheory.locallyQuasiFinite_of_finite_fibres_closedPoints f.left fun y hy =>
      (pfiF_fib_closed hG f H j hH hj y hy).1
  exact IsFinite.of_isProper_of_locallyQuasiFinite f.left

end PositivityTheory.PrwZar.Z2
