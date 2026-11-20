import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackIsoBaseChangeOverReducedClosedFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointRangeEqFixedGroupImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedSpecialFibreGlobalField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FibConn

/- English proof (translation)
Establish `h1 : Set.range ν ⊆ Set.range j.coborderRange.ι`. Use `h.trans ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨j.liftCoborder x, by rw [← Scheme.Hom.comp_apply, Scheme.Hom.liftCoborder_ι]⟩`. Set `ν'` to `IsOpenImmersion.lift j.coborderRange.ι ν h1`.

Establish `hν' : ν' ≫ j.coborderRange.ι = ν` using `IsOpenImmersion.lift_fac _ _ _`. Establish `h2 : Set.range ν' ⊆ Set.range j.liftCoborder`. Introduce and unpack `_ ⟨q, rfl⟩`. Take `⟨x, hx⟩` from `h ⟨q, rfl⟩`. Use `⟨x, j.coborderRange.ι.isOpenEmbedding.injective ?_⟩` and prove the remaining obligations.

Rewrite using `[← Scheme.Hom.comp_apply, Scheme.Hom.liftCoborder_ι, hx, ← Scheme.Hom.comp_apply, hν']`. Use `haveI : Surjective (pullback.snd j.liftCoborder ν') := ⟨by`. Rewrite using `[← Set.range_eq_univ, Scheme.Pullback.range_snd]`. Conclude with `Set.eq_univ_of_forall fun y => h2 ⟨y, rfl⟩⟩`. Use `haveI := isIso_of_isClosedImmersion_of_surjective (pullback.snd j.liftCoborder ν')`.

Establish `key : pullback.fst j.liftCoborder ν' ≫ j = pullback.snd j.liftCoborder ν' ≫ ν`. Use `congrArg (· ≫ j.coborderRange.ι) (pullback.condition (f := j.liftCoborder) (g := ν'))` as an intermediate fact. Simplify using `only [Category.assoc, Scheme.Hom.liftCoborder_ι, hν'] at this`. Conclude with `this`. Use `⟨inv (pullback.snd j.liftCoborder ν') ≫ pullback.fst j.liftCoborder ν', ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, key, IsIso.inv_hom_id_assoc]`.
-/
theorem lfac {X P : Scheme.{0}} (j : X ⟶ P) [IsImmersion j] (Ω : Type) [Field Ω] (ν : Sp Ω ⟶ P)
    (h : Set.range ν ⊆ Set.range j) : ∃ y₀ : Sp Ω ⟶ X, y₀ ≫ j = ν := by
  have h1 : Set.range ν ⊆ Set.range j.coborderRange.ι := by
    refine h.trans ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨j.liftCoborder x, by rw [← Scheme.Hom.comp_apply, Scheme.Hom.liftCoborder_ι]⟩
  let ν' := IsOpenImmersion.lift j.coborderRange.ι ν h1
  have hν' : ν' ≫ j.coborderRange.ι = ν := IsOpenImmersion.lift_fac _ _ _
  have h2 : Set.range ν' ⊆ Set.range j.liftCoborder := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨x, hx⟩ := h ⟨q, rfl⟩
    refine ⟨x, j.coborderRange.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.liftCoborder_ι, hx, ← Scheme.Hom.comp_apply, hν']
  haveI : Surjective (pullback.snd j.liftCoborder ν') := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd]
    exact Set.eq_univ_of_forall fun y => h2 ⟨y, rfl⟩⟩
  haveI := isIso_of_isClosedImmersion_of_surjective (pullback.snd j.liftCoborder ν')
  have key : pullback.fst j.liftCoborder ν' ≫ j = pullback.snd j.liftCoborder ν' ≫ ν := by
    have := congrArg (· ≫ j.coborderRange.ι) (pullback.condition (f := j.liftCoborder) (g := ν'))
    simp only [Category.assoc, Scheme.Hom.liftCoborder_ι, hν'] at this
    exact this
  refine ⟨inv (pullback.snd j.liftCoborder ν') ≫ pullback.fst j.liftCoborder ν', ?_⟩
  rw [Category.assoc, key, IsIso.inv_hom_id_assoc]

/- English proof (translation)
Use `haveI : ConnectedSpace (pullback l (pullback.fst f ν) : Scheme.{0}) := (pullbackRightPullbackFstIso f ν l).hom.homeomorph.connectedSpace_iff.2 hc`. Use `Function.Surjective.connectedSpace (f := pullback.snd l (pullback.fst f ν)) ?_ (pullback.snd l (pullback.fst f ν)).continuous` and prove the remaining obligations. Introduce `z`. Take `⟨w, hw⟩` from `h z`. Take `⟨d, -, hd⟩` from `Scheme.Pullback.exists_preimage_pullback w z hw`.

Conclude with `⟨d, hd⟩`.
-/
theorem lsurj {X Y W Z : Scheme.{0}} (l : W ⟶ X) (f : X ⟶ Y) (ν : Z ⟶ Y)
    (h : ∀ z : (pullback f ν : Scheme.{0}), pullback.fst f ν z ∈ Set.range l)
    (hc : ConnectedSpace (pullback (l ≫ f) ν : Scheme.{0})) : ConnectedSpace (pullback f ν : Scheme.{0}) := by
  haveI : ConnectedSpace (pullback l (pullback.fst f ν) : Scheme.{0}) :=
    (pullbackRightPullbackFstIso f ν l).hom.homeomorph.connectedSpace_iff.2 hc
  refine Function.Surjective.connectedSpace (f := pullback.snd l (pullback.fst f ν)) ?_
    (pullback.snd l (pullback.fst f ν)).continuous
  intro z
  obtain ⟨w, hw⟩ := h z
  obtain ⟨d, -, hd⟩ := Scheme.Pullback.exists_preimage_pullback w z hw
  exact ⟨d, hd⟩

/- English proof (translation)
Use `set F := e ≫ pullback.fst a k ≫ j with hF`. Use `set G := y₀ ≫ j with hG`. Establish `c0 : pullback.fst F G ≫ e ≫ pullback.fst a k = pullback.snd F G ≫ y₀`. Rewrite using `[← cancel_mono j]`. Use `pullback.condition (f := F) (g := G)` as an intermediate fact.

Simplify using `only [hF, hG, Category.assoc] at this ⊢`. Conclude with `this`. Establish `c1 : (pullback.fst (y₀ ≫ a) k ≫ y₀) ≫ a = pullback.snd (y₀ ≫ a) k ≫ k`. Rewrite using `[Category.assoc]`. Conclude with `pullback.condition`.

Set `m₀ : pullback (y₀ ≫ a) k ⟶ pullback a k` to `pullback.lift (pullback.fst _ _ ≫ y₀) (pullback.snd _ _) c1`. Establish `c2 : (m₀ ≫ inv e) ≫ F = pullback.fst (y₀ ≫ a) k ≫ G`. Simplify using `only [hF, hG, m₀, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst_assoc]`. Set `m : pullback (y₀ ≫ a) k ⟶ pullback F G` to `pullback.lift (m₀ ≫ inv e) (pullback.fst _ _) c2`. Establish `c3 : pullback.snd F G ≫ y₀ ≫ a = (pullback.fst F G ≫ e ≫ pullback.snd a k) ≫ k`.

Rewrite using `[← Category.assoc, ← c0]`. Simplify using `only [Category.assoc, pullback.condition]`. Set `n : pullback F G ⟶ pullback (y₀ ≫ a) k` to `pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ e ≫ pullback.snd a k) c3`. Set `φ : pullback (y₀ ≫ a) k ≅ pullback F G` to `{ hom := m, inv := n hom_inv_id := by`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Simplify using `only [m, n, Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]`. Simplify using `only [m, n, m₀, Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd, IsIso.inv_hom_id_assoc, Category.id_comp]`. Use `inv_hom_id := by`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[← cancel_mono e]`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [m, n, m₀, Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst, IsIso.inv_hom_id_assoc, Category.id_comp]`. Conclude with `c0.symm`. Simplify using `only [m, n, m₀, Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd, IsIso.inv_hom_id_assoc, Category.id_comp]`. Simplify using `only [m, n, Category.assoc, pullback.lift_snd, pullback.lift_fst, Category.id_comp] }`.

Use `haveI : IsIso φ.hom := Iso.isIso_hom φ`. Conclude with `φ.hom.homeomorph.connectedSpace_iff.1 hc`.
-/
theorem liso {W Y T P Z B : Scheme.{0}} (a : Y ⟶ B) (k : T ⟶ B) (e : W ⟶ pullback a k) [IsIso e]
    (j : Y ⟶ P) [Mono j] (y₀ : Z ⟶ Y) (hc : ConnectedSpace (pullback (y₀ ≫ a) k : Scheme.{0})) :
    ConnectedSpace (pullback (e ≫ pullback.fst a k ≫ j) (y₀ ≫ j) : Scheme.{0}) := by
  set F := e ≫ pullback.fst a k ≫ j with hF
  set G := y₀ ≫ j with hG
  have c0 : pullback.fst F G ≫ e ≫ pullback.fst a k = pullback.snd F G ≫ y₀ := by
    rw [← cancel_mono j]
    have := pullback.condition (f := F) (g := G)
    simp only [hF, hG, Category.assoc] at this ⊢
    exact this
  have c1 : (pullback.fst (y₀ ≫ a) k ≫ y₀) ≫ a = pullback.snd (y₀ ≫ a) k ≫ k := by
    rw [Category.assoc]; exact pullback.condition
  let m₀ : pullback (y₀ ≫ a) k ⟶ pullback a k := pullback.lift (pullback.fst _ _ ≫ y₀) (pullback.snd _ _) c1
  have c2 : (m₀ ≫ inv e) ≫ F = pullback.fst (y₀ ≫ a) k ≫ G := by
    simp only [hF, hG, m₀, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst_assoc]
  let m : pullback (y₀ ≫ a) k ⟶ pullback F G := pullback.lift (m₀ ≫ inv e) (pullback.fst _ _) c2
  have c3 : pullback.snd F G ≫ y₀ ≫ a = (pullback.fst F G ≫ e ≫ pullback.snd a k) ≫ k := by
    rw [← Category.assoc, ← c0]
    simp only [Category.assoc, pullback.condition]
  let n : pullback F G ⟶ pullback (y₀ ≫ a) k := pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ e ≫ pullback.snd a k) c3
  let φ : pullback (y₀ ≫ a) k ≅ pullback F G :=
    { hom := m, inv := n
      hom_inv_id := by
        apply pullback.hom_ext
        · simp only [m, n, Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
        · simp only [m, n, m₀, Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd, IsIso.inv_hom_id_assoc,
            Category.id_comp]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [← cancel_mono e]
          apply pullback.hom_ext
          · simp only [m, n, m₀, Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst, IsIso.inv_hom_id_assoc,
              Category.id_comp]
            exact c0.symm
          · simp only [m, n, m₀, Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd, IsIso.inv_hom_id_assoc,
              Category.id_comp]
        · simp only [m, n, Category.assoc, pullback.lift_snd, pullback.lift_fst, Category.id_comp] }
  haveI : IsIso φ.hom := Iso.isIso_hom φ
  exact φ.hom.homeomorph.connectedSpace_iff.1 hc

/- English proof (translation)
Use `haveI : Surjective i := ⟨hs⟩`. Set `q` to `pullback.fst (pullback.snd h s) i`. Establish `hq : Function.Surjective q` using `(inferInstance : Surjective q).surj`. Use `haveI : Nonempty (pullback (pullback.snd h s) i : Scheme.{0}) := ⟨(hq (Nonempty.some inferInstance)).choose⟩`. Use `haveI : ConnectedSpace (pullback (pullback.snd h s) i : Scheme.{0}) := by`.

Use `connectedSpace_iff_univ.2 ⟨Set.univ_nonempty, ?_⟩` and prove the remaining obligations. Use `(q.isClosedEmbedding.isInducing.isPreconnected_image).1 ?_` and prove the remaining obligations. Rewrite using `[Set.image_univ, hq.range_eq]`. Conclude with `isPreconnected_univ`. Conclude with `(pullbackLeftPullbackSndIso h s i).hom.homeomorph.connectedSpace_iff.1 this`.
-/
theorem lred {X Y Z W : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i] (hs : Function.Surjective i)
    (s : Y ⟶ W) (h : Z ⟶ W) (hc : ConnectedSpace (pullback h s : Scheme.{0})) :
    ConnectedSpace (pullback h (i ≫ s) : Scheme.{0}) := by
  haveI : Surjective i := ⟨hs⟩
  let q := pullback.fst (pullback.snd h s) i
  have hq : Function.Surjective q := (inferInstance : Surjective q).surj
  haveI : Nonempty (pullback (pullback.snd h s) i : Scheme.{0}) :=
    ⟨(hq (Nonempty.some inferInstance)).choose⟩
  haveI : ConnectedSpace (pullback (pullback.snd h s) i : Scheme.{0}) := by
    refine connectedSpace_iff_univ.2 ⟨Set.univ_nonempty, ?_⟩
    refine (q.isClosedEmbedding.isInducing.isPreconnected_image).1 ?_
    rw [Set.image_univ, hq.range_eq]
    exact isPreconnected_univ
  exact (pullbackLeftPullbackSndIso h s i).hom.homeomorph.connectedSpace_iff.1 this

/- English proof (translation)
Introduce `R _ _ _ S π hπ G' _ hG E hconn Ω _ _ ν hex`. Take `⟨g, hg, p, hp⟩` from `hex`. Take `⟨y, hy⟩` from `(GlobalTheory.Mum.Emb.range_closed R S π G' E).1 g hg`. Use `haveI := E.imm`. Establish `hrange : Set.range ν ⊆ Set.range E.j`.

Introduce and unpack `_ ⟨q, rfl⟩`. Rewrite using `[Subsingleton.elim q p, hp, hy]`. Conclude with `⟨y, rfl⟩`. Take `⟨y₀, hy₀⟩` from `lfac E.j Ω ν hrange`. Set `κ₀ : ResidueField R →+* Ω` to `(Spec.preimage (y₀ ≫ E.Y.hom)).hom`.

Establish `hκ₀ : y₀ ≫ E.Y.hom = spMap κ₀`. Simplify using `[κ₀, spMap]`. Use `haveI := hπ`. Set `ρ` to `spMap (residue R)`. Set `S₀` to `pullback π ρ`.

Use `haveI : IsLocallyNoetherian S₀ := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd π ρ)`. Set `T` to `S₀.nilradical.subscheme`. Set `i : T ⟶ S₀` to `S₀.nilradical.subschemeι`. Use `haveI : IsReduced T := GlobalTheory.RedFibreField.isReduced_nilradical_subscheme _`. Use `haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian i`.

Establish `hi : Function.Surjective i`. Rewrite using `[← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι, Scheme.support_nilradical]`. Both sides reduce to the same expression. Set `t` to `i ≫ pullback.fst π ρ`. Set `kk` to `i ≫ pullback.snd π ρ`.

Take `⟨e, l, -, hl1, hl2⟩` from `GlobalTheory.T.pullback_iso_baseChange_over_reduced_closedFibre R S π G' hG E T t kk inferInstance inferInstance (by show i ≫ pullback.fst π ρ ≫ π = (i ≫ pullback.snd π ρ) ≫ ρ; rw [pullback.condition, Category.assoc])`. Apply `lsurj l E.f ν` to reduce the goal to its premises. Introduce `z`. Establish `h1 : E.f (pullback.fst E.f ν z) = ν (pullback.snd E.f ν z)`. Rewrite using `[← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]`.

Establish `h3 : ν (pullback.snd E.f ν z) = E.f g` using `by rw [Subsingleton.elim (pullback.snd E.f ν z) p, hp]`. Establish `h4 : ∀ b : E.H.toScheme, PSpace.str R E.N (E.f b) = π (G'.hom (E.H.ι b))` using `fun b => by`. Rewrite using `[← Scheme.Hom.comp_apply, E.f_over]`. Both sides reduce to the same expression. Establish `h2 : π (G'.hom (E.H.ι (pullback.fst E.f ν z))) = closedPoint R`.

Rewrite using `[← h4, h1, h3, h4, hg]`. Establish `h5 : G'.hom (E.H.ι (pullback.fst E.f ν z)) ∈ Set.range (pullback.fst π ρ)`. Rewrite using `[Scheme.Pullback.range_fst]`. Conclude with `⟨closedPoint (ResidueField R), (IsLocalRing.comap_closedPoint (residue R)).trans h2.symm⟩`. Take `⟨w, hw⟩` from `h5`.

Take `⟨u, rfl⟩` from `hi w`. Take `⟨d, hd1, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := G'.hom) (g := t) (E.H.ι (pullback.fst E.f ν z)) u hw.symm`. Use `⟨d, E.H.ι.isOpenEmbedding.injective ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, hl1, hd1]`. Rewrite using `[hl2, ← hy₀]`.

Apply `liso E.Y.hom kk e.hom E.j y₀` to reduce the goal to its premises. Rewrite using `[hκ₀]`. Apply `lred i hi` to reduce the goal to its premises. Establish `hc` using `hconn Ω κ₀`. Establish `hcomp : spMap (κ₀.comp (residue R)) = spMap κ₀ ≫ ρ`.

Simplify using `only [ρ, spMap, ← Spec.map_comp]`. Both sides reduce to the same expression. Rewrite `hc` using `[hcomp]`. Apply the tactic sequence `exact ((pullbackLeftPullbackSndIso π ρ (spMap κ₀)).symm ≪≫ pullbackSymmetry _ _).hom.homeomorph.connectedSpace_iff.1 hc`.
-/
theorem fib_conn : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → ∀ (G' : Over S) [GrpObj G'], Smooth G'.hom → ∀ (E : Emb π G'), (∀ (K : Type) [Field K] (κ : ResidueField R →+* K), ConnectedSpace (pullback π (spMap (κ.comp (residue R))) : Scheme.{0})) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ν : Sp Ω ⟶ PSpace R E.N), (∃ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g ∈ Set.range ν) → ConnectedSpace (pullback E.f ν : Scheme.{0}) := by
  intro R _ _ _ S π hπ G' _ hG E hconn Ω _ _ ν hex
  obtain ⟨g, hg, p, hp⟩ := hex
  obtain ⟨y, hy⟩ := (GlobalTheory.Mum.Emb.range_closed R S π G' E).1 g hg
  haveI := E.imm
  have hrange : Set.range ν ⊆ Set.range E.j := by
    rintro _ ⟨q, rfl⟩
    rw [Subsingleton.elim q p, hp, hy]
    exact ⟨y, rfl⟩
  obtain ⟨y₀, hy₀⟩ := lfac E.j Ω ν hrange
  let κ₀ : ResidueField R →+* Ω := (Spec.preimage (y₀ ≫ E.Y.hom)).hom
  have hκ₀ : y₀ ≫ E.Y.hom = spMap κ₀ := by
    simp [κ₀, spMap]
  haveI := hπ
  let ρ := spMap (residue R)
  let S₀ := pullback π ρ
  haveI : IsLocallyNoetherian S₀ := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd π ρ)
  let T := S₀.nilradical.subscheme
  let i : T ⟶ S₀ := S₀.nilradical.subschemeι
  haveI : IsReduced T := GlobalTheory.RedFibreField.isReduced_nilradical_subscheme _
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian i
  have hi : Function.Surjective i := by
    rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι, Scheme.support_nilradical]
    rfl
  let t := i ≫ pullback.fst π ρ
  let kk := i ≫ pullback.snd π ρ
  obtain ⟨e, l, -, hl1, hl2⟩ := GlobalTheory.T.pullback_iso_baseChange_over_reduced_closedFibre R S π G' hG E T t kk inferInstance inferInstance
    (by show i ≫ pullback.fst π ρ ≫ π = (i ≫ pullback.snd π ρ) ≫ ρ; rw [pullback.condition, Category.assoc])
  apply lsurj l E.f ν
  · intro z
    have h1 : E.f (pullback.fst E.f ν z) = ν (pullback.snd E.f ν z) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    have h3 : ν (pullback.snd E.f ν z) = E.f g := by rw [Subsingleton.elim (pullback.snd E.f ν z) p, hp]
    have h4 : ∀ b : E.H.toScheme, PSpace.str R E.N (E.f b) = π (G'.hom (E.H.ι b)) := fun b => by
      rw [← Scheme.Hom.comp_apply, E.f_over]
      rfl
    have h2 : π (G'.hom (E.H.ι (pullback.fst E.f ν z))) = closedPoint R := by
      rw [← h4, h1, h3, h4, hg]
    have h5 : G'.hom (E.H.ι (pullback.fst E.f ν z)) ∈ Set.range (pullback.fst π ρ) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨closedPoint (ResidueField R), (IsLocalRing.comap_closedPoint (residue R)).trans h2.symm⟩
    obtain ⟨w, hw⟩ := h5
    obtain ⟨u, rfl⟩ := hi w
    obtain ⟨d, hd1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G'.hom) (g := t)
      (E.H.ι (pullback.fst E.f ν z)) u hw.symm
    refine ⟨d, E.H.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hl1, hd1]
  · rw [hl2, ← hy₀]
    apply liso E.Y.hom kk e.hom E.j y₀
    rw [hκ₀]
    apply lred i hi
    have hc := hconn Ω κ₀
    have hcomp : spMap (κ₀.comp (residue R)) = spMap κ₀ ≫ ρ := by
      simp only [ρ, spMap, ← Spec.map_comp]
      rfl
    rw [hcomp] at hc
    exact ((pullbackLeftPullbackSndIso π ρ (spMap κ₀)).symm ≪≫ pullbackSymmetry _ _).hom.homeomorph.connectedSpace_iff.1 hc

end GlobalTheory.Mum.FibConn
