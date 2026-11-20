import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Chart

/- English proof (translation)
Set `k : Over.mk (spMap g ≫ x) ⟶ Over.mk x` to `Over.homMk (spMap g) rfl`. Establish `h : (1 : Over.mk (spMap g ≫ x) ⟶ G) = k ≫ (1 : Over.mk x ⟶ G)`. Rewrite using `[Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (k ≫ toUnit _) (toUnit _)]`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem one_left_spMap {S : Scheme.{0}} (G : Over S) [GrpObj G] {R A : Type} [CommRing R] [CommRing A]
    (x : Sp R ⟶ S) (g : R →+* A) :
    (1 : Over.mk (spMap g ≫ x) ⟶ G).left = spMap g ≫ (1 : Over.mk x ⟶ G).left := by
  let k : Over.mk (spMap g ≫ x) ⟶ Over.mk x := Over.homMk (spMap g) rfl
  have h : (1 : Over.mk (spMap g ≫ x) ⟶ G) = k ≫ (1 : Over.mk x ⟶ G) := by
    rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (k ≫ toUnit _) (toUnit _)]
  rw [h]; rfl

/- English proof (translation)
Set `t : Sp R ⟶ G.left` to `(1 : Over.mk x ⟶ G).left`. Set `q : PrimeSpectrum R` to `⟨p, inferInstance⟩`. Set `q' : Sp R` to `q`. Take `⟨V, hV, hqV, -⟩` from `exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := G.hom (t q')) trivial`. Take `⟨U, hU, hqU, hUV⟩` from `exists_isAffineOpen_mem_and_subset (X := G.left) (U := G.hom ⁻¹ᵁ V) (x := t q') hqV`.

Establish `hUV' : U ≤ G.hom ⁻¹ᵁ V` using `hUV`. Establish `hopen : IsOpen {y : PrimeSpectrum R | t (show Sp R from y) ∈ U}` using `(t ⁻¹ᵁ U).isOpen`. Take `⟨_, ⟨f, rfl⟩, hqf, hsub⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show q ∈ _ from hqU) hopen`. Use `⟨f, hqf, U, V, hU, hV, hUV', HasRingHomProperty.appLE @Smooth G.hom inferInstance ⟨V, hV⟩ ⟨U, hU⟩ hUV', ?_⟩` and prove the remaining obligations. Set `a : Sp (Localization.Away f) ⟶ Sp R` to `spMap (algebraMap R (Localization.Away f))`.

Establish `hrange : Set.range (a ≫ t) ⊆ Set.range hU.fromSpec`. Rewrite using `[hU.range_fromSpec]`. Introduce and unpack `_ ⟨y, rfl⟩`. Apply `hsub` to reduce the goal to its premises. Establish `: (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) y ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f)))` using `⟨y, rfl⟩`.

Rewrite `this` using `[PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]`. Conclude with `this`. Set `l` to `IsOpenImmersion.lift hU.fromSpec (a ≫ t) hrange`. Use `⟨(Spec.preimage l).hom, ?_⟩` and prove the remaining obligations. Establish `hl : spMap (Spec.preimage l).hom = l`.

Simplify using `[spMap]`. Rewrite using `[one_left_spMap, hl]`. Conclude with `(IsOpenImmersion.lift_fac _ _ _).symm`.
-/
theorem exists_chart_at_point (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R]
    (x : Sp R ⟶ S) (p : Ideal R) [p.IsPrime] :
    ∃ f : R, f ∉ p ∧ ∃ (U : G.left.Opens) (V : S.Opens) (hU : IsAffineOpen U) (_ : IsAffineOpen V)
      (hUV : U ≤ G.hom ⁻¹ᵁ V),
      RingHom.Smooth (G.hom.appLE V U hUV).hom ∧
      ∃ u : Γ(G.left, U) →+* Localization.Away f,
        (1 : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ G).left = spMap u ≫ hU.fromSpec := by
  let t : Sp R ⟶ G.left := (1 : Over.mk x ⟶ G).left
  let q : PrimeSpectrum R := ⟨p, inferInstance⟩
  let q' : Sp R := q
  obtain ⟨V, hV, hqV, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := G.hom (t q')) trivial
  obtain ⟨U, hU, hqU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := G.left) (U := G.hom ⁻¹ᵁ V) (x := t q') hqV
  have hUV' : U ≤ G.hom ⁻¹ᵁ V := hUV
  have hopen : IsOpen {y : PrimeSpectrum R | t (show Sp R from y) ∈ U} := (t ⁻¹ᵁ U).isOpen
  obtain ⟨_, ⟨f, rfl⟩, hqf, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show q ∈ _ from hqU) hopen
  refine ⟨f, hqf, U, V, hU, hV, hUV', HasRingHomProperty.appLE @Smooth G.hom inferInstance ⟨V, hV⟩ ⟨U, hU⟩ hUV', ?_⟩
  let a : Sp (Localization.Away f) ⟶ Sp R := spMap (algebraMap R (Localization.Away f))
  have hrange : Set.range (a ≫ t) ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    apply hsub
    have : (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) y ∈
        Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) := ⟨y, rfl⟩
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f] at this
    exact this
  let l := IsOpenImmersion.lift hU.fromSpec (a ≫ t) hrange
  refine ⟨(Spec.preimage l).hom, ?_⟩
  have hl : spMap (Spec.preimage l).hom = l := by
    simp [spMap]
  rw [one_left_spMap, hl]
  exact (IsOpenImmersion.lift_fac _ _ _).symm

end GlobalTheory.CompanionTheory.Ar.Chart
