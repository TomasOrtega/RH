import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ T q hq U hU x hx`. Assume the negation of the conclusion as `hxU`. Use `set c : Sp R := closedPoint R`. Establish `hc : IsClosed ({c} : Set (Sp R))` using `(PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 (IsLocalRing.maximalIdeal.isMaximal R)`. Establish `hft : LocallyOfFiniteType (q.fiberToSpecResidueField c)` using `inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))`.

Establish `: JacobsonSpace (q.fiber c)` using `LocallyOfFiniteType.jacobsonSpace (q.fiberToSpecResidueField c)`. Set `e` to `q.fiberι c`. Establish `hemb : Topology.IsClosedEmbedding e`. Use `⟨IsPreimmersion.isEmbedding e, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.Hom.range_fiberι]`.

Conclude with `hc.preimage q.continuous`. Set `Z : Set T` to `closure {x} ∩ (U : Set T)ᶜ`. Establish `hZ : IsClosed Z` using `isClosed_closure.inter U.isOpen.isClosed_compl`. Choose the witnesses or unpack the hypotheses as in `⟨x', hx'⟩ : x ∈ Set.range e := by`. Rewrite using `[Scheme.Hom.range_fiberι]`.

Conclude with `hx`. Establish `hne : (e ⁻¹' Z).Nonempty` using `⟨x', by show e x' ∈ Z`. Rewrite using `[hx']`. Conclude with `⟨subset_closure rfl, hxU⟩⟩`. Take `⟨y, hyZ, hyc⟩` from `nonempty_inter_closedPoints hne (hZ.preimage e.continuous).isLocallyClosed`.

Establish `hyc' : IsClosed ({e y} : Set T)`. Rewrite using `[← Set.image_singleton]`. Conclude with `hemb.isClosedMap _ hyc`. Establish `hqy : q (e y) = c`. Establish `: e y ∈ Set.range e` using `⟨y, rfl⟩`.

Rewrite `this` using `[Scheme.Hom.range_fiberι]`. Conclude with `this`. Conclude with `hyZ.2 (hU _ hyc' hqy)`.
-/
theorem mem_of_closedPoints_closedFibre_mem : ∀ (R : Type) [CommRing R] [IsLocalRing R] (T : Scheme.{0}) (q : T ⟶ Sp R),
    LocallyOfFiniteType q → ∀ U : T.Opens, (∀ x : T, IsClosed ({x} : Set T) → q x = closedPoint R → x ∈ U) →
    ∀ x : T, q x = closedPoint R → x ∈ U := by
  intro R _ _ T q hq U hU x hx
  by_contra hxU
  set c : Sp R := closedPoint R
  have hc : IsClosed ({c} : Set (Sp R)) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 (IsLocalRing.maximalIdeal.isMaximal R)
  have hft : LocallyOfFiniteType (q.fiberToSpecResidueField c) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  have : JacobsonSpace (q.fiber c) := LocallyOfFiniteType.jacobsonSpace (q.fiberToSpecResidueField c)
  let e := q.fiberι c
  have hemb : Topology.IsClosedEmbedding e := by
    refine ⟨IsPreimmersion.isEmbedding e, ?_⟩
    rw [Scheme.Hom.range_fiberι]
    exact hc.preimage q.continuous
  let Z : Set T := closure {x} ∩ (U : Set T)ᶜ
  have hZ : IsClosed Z := isClosed_closure.inter U.isOpen.isClosed_compl
  obtain ⟨x', hx'⟩ : x ∈ Set.range e := by
    rw [Scheme.Hom.range_fiberι]; exact hx
  have hne : (e ⁻¹' Z).Nonempty := ⟨x', by
    show e x' ∈ Z
    rw [hx']; exact ⟨subset_closure rfl, hxU⟩⟩
  obtain ⟨y, hyZ, hyc⟩ := nonempty_inter_closedPoints hne (hZ.preimage e.continuous).isLocallyClosed
  have hyc' : IsClosed ({e y} : Set T) := by
    rw [← Set.image_singleton]
    exact hemb.isClosedMap _ hyc
  have hqy : q (e y) = c := by
    have : e y ∈ Set.range e := ⟨y, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  exact hyZ.2 (hU _ hyc' hqy)

end GlobalTheory.Mum
