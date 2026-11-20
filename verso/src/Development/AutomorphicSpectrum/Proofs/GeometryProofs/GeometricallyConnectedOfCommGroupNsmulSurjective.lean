import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedSpaceOfDivisible
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Approx

/- English proof (translation)
Establish `: JacobsonSpace X` using `LocallyOfFiniteType.jacobsonSpace f`. Take `⟨x, -, hc⟩` from `nonempty_inter_closedPoints (Set.univ_nonempty (α := X)) isClosed_univ.isLocallyClosed`. Conclude with `⟨pointOfClosedPoint (K := K) f x hc, pointOfClosedPoint_comp (K := K) f x hc⟩`.
-/
theorem exists_section_of_nonempty {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (f : X ⟶ Sp K) [LocallyOfFiniteType f] [Nonempty X] : ∃ s : Sp K ⟶ X, s ≫ f = 𝟙 _ := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, -, hc⟩ := nonempty_inter_closedPoints (Set.univ_nonempty (α := X))
    isClosed_univ.isLocallyClosed
  exact ⟨pointOfClosedPoint (K := K) f x hc, pointOfClosedPoint_comp (K := K) f x hc⟩

/- English proof (translation)
Establish `h1 : LocallyOfFiniteType (m.left ≫ H.hom)` using `by rw [Over.w m]; infer_instance`. Establish `h2 : LocallyOfFiniteType m.left` using `locallyOfFiniteType_of_comp m.left H.hom`. Set `q : pullback m.left x.left ⟶ Sp K` to `pullback.snd m.left x.left`. Establish `h3 : LocallyOfFiniteType q` using `inferInstanceAs (LocallyOfFiniteType (pullback.snd m.left x.left))`. Establish `h4 : Surjective q` using `inferInstanceAs (Surjective (pullback.snd m.left x.left))`.

Establish `h5 : Nonempty ↥(pullback m.left x.left)`. Take `⟨w, -⟩` from `q.surjective (default : PrimeSpectrum K)`. Conclude with `⟨w⟩`. Take `⟨s, hs⟩` from `exists_section_of_nonempty q`. Use `⟨Over.homMk (s ≫ pullback.fst m.left x.left) ?_, ?_⟩` and prove the remaining obligations.

Establish `hx : x.left ≫ H.hom = 𝟙 _` using `Over.w x`. Establish `hm` using `Over.w m`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Category.assoc (pullback.fst m.left x.left), pullback.condition]`. Simplify using `[q]`.

Use `_ = 𝟙 _ := by`. Rewrite using `[hx]`. Express the relevant statement in the definitionally equal form `s ≫ q ≫ 𝟙 (Sp K) = _`. Rewrite using `[Category.comp_id]`. Conclude with `hs`.

Use `ext1`. Express the relevant statement in the definitionally equal form `(s ≫ pullback.fst m.left x.left) ≫ m.left = x.left`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc]`. Express the relevant statement in the definitionally equal form `(s ≫ q) ≫ x.left = x.left`. Rewrite using `[hs]`.

Conclude with `Category.id_comp _`.
-/
theorem exists_comp_eq_of_surjective {K : Type} [Field K] [IsAlgClosed K] (H : Over (Sp K))
    [LocallyOfFiniteType H.hom] (m : H ⟶ H) [Surjective m.left] (x : 𝟙_ (Over (Sp K)) ⟶ H) :
    ∃ y : 𝟙_ (Over (Sp K)) ⟶ H, y ≫ m = x := by
  have h1 : LocallyOfFiniteType (m.left ≫ H.hom) := by rw [Over.w m]; infer_instance
  have h2 : LocallyOfFiniteType m.left := locallyOfFiniteType_of_comp m.left H.hom
  let q : pullback m.left x.left ⟶ Sp K := pullback.snd m.left x.left
  have h3 : LocallyOfFiniteType q := inferInstanceAs (LocallyOfFiniteType (pullback.snd m.left x.left))
  have h4 : Surjective q := inferInstanceAs (Surjective (pullback.snd m.left x.left))
  have h5 : Nonempty ↥(pullback m.left x.left) := by
    obtain ⟨w, -⟩ := q.surjective (default : PrimeSpectrum K)
    exact ⟨w⟩
  obtain ⟨s, hs⟩ := exists_section_of_nonempty q
  refine ⟨Over.homMk (s ≫ pullback.fst m.left x.left) ?_, ?_⟩
  · have hx : x.left ≫ H.hom = 𝟙 _ := Over.w x
    have hm := Over.w m
    calc (s ≫ pullback.fst m.left x.left) ≫ H.hom
        = s ≫ pullback.fst m.left x.left ≫ m.left ≫ H.hom := by rw [hm]; simp
      _ = s ≫ q ≫ x.left ≫ H.hom := by
          rw [← Category.assoc (pullback.fst m.left x.left), pullback.condition]; simp [q]
      _ = 𝟙 _ := by
          rw [hx]
          change s ≫ q ≫ 𝟙 (Sp K) = _
          rw [Category.comp_id]; exact hs
  · ext1
    change (s ≫ pullback.fst m.left x.left) ≫ m.left = x.left
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (s ≫ q) ≫ x.left = x.left
    rw [hs]
    exact Category.id_comp _

/- English proof (translation)
Introduce `S G _ _ hl hq hn`. Use `⟨fun k _ y Z a b hZ => ?_⟩` and prove the remaining obligations. Set `L` to `AlgebraicClosure k`. Set `j : Sp L ⟶ Spec (.of k)` to `Spec.map (CommRingCat.ofHom (algebraMap k L))`. Set `t : Sp L ⟶ S` to `j ≫ y`.

Set `H : Over (Sp L)` to `(Over.pullback t).obj G`. Establish `hlH : LocallyOfFiniteType H.hom` using `inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom t))`. Establish `hqH : QuasiCompact H.hom` using `inferInstanceAs (QuasiCompact (pullback.snd G.hom t))`. Establish `hconn : ConnectedSpace H.left`. Use `GlobalTheory.CompanionTheory.Ar.Approx.connectedSpace_of_divisible L H hlH hqH fun n hn0 x => ?_` and prove the remaining obligations.

Establish `e : (Over.pullback t).map ((𝟙 G) ^ n) = (𝟙 H) ^ n`. Use `map_pow (Over.pullback t).homMonoidHom (𝟙 G) n` as an intermediate fact. Simplify using `using this`. Establish `hs : Surjective ((𝟙 H) ^ n : H ⟶ H).left`. Establish `hG` using `hn n hn0`.

Establish `sq : IsPullback ((Over.pullback t).map ((𝟙 G) ^ n)).left (pullback.fst G.hom t) (pullback.fst G.hom t) ((𝟙 G) ^ n : G ⟶ G).left`. Establish `hA : ((Over.pullback t).map ((𝟙 G) ^ n)).left ≫ pullback.fst G.hom t = pullback.fst G.hom t ≫ ((𝟙 G) ^ n : G ⟶ G).left` using `pullback.lift_fst _ _ _`. Establish `hB : ((Over.pullback t).map ((𝟙 G) ^ n)).left ≫ pullback.snd G.hom t = pullback.snd G.hom t` using `Over.w ((Over.pullback t).map ((𝟙 G) ^ n))`. Establish `rect : IsPullback (((Over.pullback t).map ((𝟙 G) ^ n)).left ≫ pullback.snd G.hom t) (pullback.fst G.hom t) t (((𝟙 G) ^ n : G ⟶ G).left ≫ G.hom)`. Rewrite using `[hB, Over.w ((𝟙 G) ^ n : G ⟶ G)]`.

Conclude with `(IsPullback.of_hasPullback _ _).flip`. Conclude with `IsPullback.of_right rect hA (IsPullback.of_hasPullback _ _).flip`. Rewrite using `[← e]`. Conclude with `MorphismProperty.of_isPullback (P := @Surjective) sq.flip hG`. Take `⟨w, hw⟩` from `exists_comp_eq_of_surjective H ((𝟙 H) ^ n) x`.

Use `⟨w, ?_⟩` and prove the remaining obligations. Rewrite using `[← hw, MonObj.comp_pow, Category.comp_id]`. Establish `hj : Surjective j` using `⟨fun z => ⟨default, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩`. Establish `big : IsPullback (pullback.fst b j ≫ a) (pullback.snd b j) G.hom t` using `(IsPullback.of_hasPullback b j).paste_horiz hZ`. Establish `hc' : ConnectedSpace ↥(pullback G.hom t)` using `hconn`.

Establish `hsurj : Surjective (big.isoPullback.inv ≫ pullback.fst b j)` using `inferInstance`. Conclude with `(big.isoPullback.inv ≫ pullback.fst b j).surjective.connectedSpace (big.isoPullback.inv ≫ pullback.fst b j).continuous`.
-/
theorem geometricallyConnected_of_surjective_pow : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], LocallyOfFiniteType G.hom → QuasiCompact G.hom → (∀ n : ℕ, n ≠ 0 → Surjective ((𝟙 G) ^ n : G ⟶ G).left) → GeometricallyConnected G.hom := by
  intro S G _ _ hl hq hn
  refine ⟨fun k _ y Z a b hZ => ?_⟩
  let L := AlgebraicClosure k
  let j : Sp L ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let t : Sp L ⟶ S := j ≫ y
  let H : Over (Sp L) := (Over.pullback t).obj G
  have hlH : LocallyOfFiniteType H.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom t))
  have hqH : QuasiCompact H.hom := inferInstanceAs (QuasiCompact (pullback.snd G.hom t))
  have hconn : ConnectedSpace H.left := by
    refine GlobalTheory.CompanionTheory.Ar.Approx.connectedSpace_of_divisible L H hlH hqH fun n hn0 x => ?_
    have e : (Over.pullback t).map ((𝟙 G) ^ n) = (𝟙 H) ^ n := by
      have := map_pow (Over.pullback t).homMonoidHom (𝟙 G) n
      simpa using this
    have hs : Surjective ((𝟙 H) ^ n : H ⟶ H).left := by
      have hG := hn n hn0
      have sq : IsPullback ((Over.pullback t).map ((𝟙 G) ^ n)).left (pullback.fst G.hom t)
          (pullback.fst G.hom t) ((𝟙 G) ^ n : G ⟶ G).left := by
        have hA : ((Over.pullback t).map ((𝟙 G) ^ n)).left ≫ pullback.fst G.hom t =
            pullback.fst G.hom t ≫ ((𝟙 G) ^ n : G ⟶ G).left := pullback.lift_fst _ _ _
        have hB : ((Over.pullback t).map ((𝟙 G) ^ n)).left ≫ pullback.snd G.hom t =
            pullback.snd G.hom t := Over.w ((Over.pullback t).map ((𝟙 G) ^ n))
        have rect : IsPullback (((Over.pullback t).map ((𝟙 G) ^ n)).left ≫ pullback.snd G.hom t)
            (pullback.fst G.hom t) t (((𝟙 G) ^ n : G ⟶ G).left ≫ G.hom) := by
          rw [hB, Over.w ((𝟙 G) ^ n : G ⟶ G)]
          exact (IsPullback.of_hasPullback _ _).flip
        exact IsPullback.of_right rect hA (IsPullback.of_hasPullback _ _).flip
      rw [← e]
      exact MorphismProperty.of_isPullback (P := @Surjective) sq.flip hG
    obtain ⟨w, hw⟩ := exists_comp_eq_of_surjective H ((𝟙 H) ^ n) x
    refine ⟨w, ?_⟩
    rw [← hw, MonObj.comp_pow, Category.comp_id]
  have hj : Surjective j := ⟨fun z => ⟨default, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  have big : IsPullback (pullback.fst b j ≫ a) (pullback.snd b j) G.hom t :=
    (IsPullback.of_hasPullback b j).paste_horiz hZ
  have hc' : ConnectedSpace ↥(pullback G.hom t) := hconn
  have hsurj : Surjective (big.isoPullback.inv ≫ pullback.fst b j) := inferInstance
  exact (big.isoPullback.inv ≫ pullback.fst b j).surjective.connectedSpace
    (big.isoPullback.inv ≫ pullback.fst b j).continuous

end GlobalTheory.CompanionTheory.Ar.Approx
