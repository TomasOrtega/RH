import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralAndIsNormalSchemeOfSmoothDvr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIsoOfIsOpenImmersionOfGeometricallyConnected

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible T`. Establish `: IsLocalization.Away π K`. Use `IsLocalization.Away.mk π (IsUnit.mk0 _ (by simpa using hπ.ne_zero)) (fun s => ?_) (fun a b hab => ⟨0, by simpa using IsFractionRing.injective T K hab⟩)` and prove the remaining obligations. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := T) s`. Take `⟨n, v, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hπ`.

Use `⟨n, a * (v⁻¹ : Tˣ), ?_⟩` and prove the remaining obligations. Establish `h1 : algebraMap T K π ≠ 0` using `by simpa using hπ.ne_zero`. Establish `h2 : algebraMap T K v ≠ 0` using `by simp`. Simplify using `only [map_mul, map_pow, map_units_inv]`. Clear the denominators using the available nonvanishing facts.

Conclude with `IsOpenImmersion.of_isLocalization π`.
-/
theorem isOpenImmersion_spMap_of_isDiscreteValuationRing (T K : Type) [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] :
    IsOpenImmersion (spMap (algebraMap T K)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T
  have : IsLocalization.Away π K := by
    refine IsLocalization.Away.mk π (IsUnit.mk0 _ (by simpa using hπ.ne_zero)) (fun s => ?_)
      (fun a b hab => ⟨0, by simpa using IsFractionRing.injective T K hab⟩)
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := T) s
    obtain ⟨n, v, rfl⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hπ
    refine ⟨n, a * (v⁻¹ : Tˣ), ?_⟩
    have h1 : algebraMap T K π ≠ 0 := by simpa using hπ.ne_zero
    have h2 : algebraMap T K v ≠ 0 := by simp
    simp only [map_mul, map_pow, map_units_inv]
    field_simp
  exact IsOpenImmersion.of_isLocalization π

/- English proof (translation)
Use `isDominant_spMap_of_isFractionRing T K` as an intermediate fact. Use `IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap T K))` as an intermediate fact. Set `g` to `pullback.fst f (spMap (algebraMap T K))`. Establish `: IsReduced X` using `IsSchemeTheoreticallyDominant.isReduced g`. Establish `: IsDominant g` using `inferInstance`.

Establish `h : IsIrreducible (closure (Set.range g))`. Rewrite using `[← Set.image_univ]`. Conclude with `((IrreducibleSpace.isIrreducible_univ _).image g g.continuous.continuousOn).closure`. Rewrite `h` using `[g.denseRange.closure_range]`. Establish `: IrreducibleSpace X` using `(irreducibleSpace_def X).mpr h`.

Conclude with `isIntegral_of_irreducibleSpace_of_isReduced X`.
-/
theorem isIntegral_of_flat_of_isIntegral_genericFibre (T K : Type) [CommRing T] [IsDomain T]
    [Field K] [Algebra T K] [IsFractionRing T K] {X : Scheme.{0}} (f : X ⟶ Sp T) [Flat f]
    [IsIntegral (pullback f (spMap (algebraMap T K)))] : IsIntegral X := by
  have := isDominant_spMap_of_isFractionRing T K
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap T K))
  let g := pullback.fst f (spMap (algebraMap T K))
  have : IsReduced X := IsSchemeTheoreticallyDominant.isReduced g
  have : IsDominant g := inferInstance
  have h : IsIrreducible (closure (Set.range g)) := by
    rw [← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ _).image g g.continuous.continuousOn).closure
  rw [g.denseRange.closure_range] at h
  have : IrreducibleSpace X := (irreducibleSpace_def X).mpr h
  exact isIntegral_of_irreducibleSpace_of_isReduced X

/- English proof (translation)
Introduce `T K _ _ _ _ _ _ Ga G _ _ p _ _ _ _ _ _ _ _ _`. Set `t` to `spMap (algebraMap T K)`. Establish `: IsOpenImmersion t` using `isOpenImmersion_spMap_of_isDiscreteValuationRing T K`. Establish `hc : ConnectedSpace ((Over.pullback t).obj G).left` using `GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback G.hom t)`. Take `⟨hG, hN⟩` from `isIntegral_and_isNormalScheme_of_smooth_dvr T K G ‹_› hc`.

Set `q : pullback Ga.hom t ⟶ pullback G.hom t` to `((Over.pullback t).map p).left`. Establish `: IsIso q` using `inferInstanceAs (IsIso ((Over.forget _).map ((Over.pullback t).map p)))`. Establish `e : q ≫ pullback.fst G.hom t = pullback.fst Ga.hom t ≫ p.left` using `pullback.lift_fst _ _ _`. Establish `: ConnectedSpace ↥(pullback G.hom t)` using `hc`. Establish `: IsIntegral (pullback G.hom t)` using `isIntegral_of_isOpenImmersion (pullback.fst G.hom t)`.

Establish `: Nonempty ↥(pullback Ga.hom t)` using `⟨inv q (Classical.arbitrary _)⟩`. Establish `: IsIntegral (pullback Ga.hom t)` using `isIntegral_of_isOpenImmersion q`. Establish `: IsIntegral Ga.left` using `isIntegral_of_flat_of_isIntegral_genericFibre T K Ga.hom`. Set `j` to `pullback.fst Ga.hom t`. Establish `: IsOpenImmersion (j.opensRange.ι ≫ p.left)`.

Rewrite using `[← j.isoOpensRange_inv_comp, Category.assoc, ← e]`. Use `infer_instance`. Establish `: IsOpenImmersion p.left` using `isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict p.left (fun y ↦ (hN y).2) j.opensRange ⟨⟨j (Classical.arbitrary _), _, rfl⟩⟩`. Conclude with `isIso_of_isOpenImmersion_of_geometricallyConnected _ Ga G p ‹_› ‹_› inferInstance ‹_›`.
-/
theorem isIso_of_quasiFinite_of_isIso_genericFibre_dvr :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
      [IsFractionRing T K] (Ga G : Over (Sp T)) [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G), IsMonHom p →
      Flat Ga.hom → IsSeparated p.left → LocallyOfFiniteType p.left → QuasiCompact p.left →
      LocallyQuasiFinite p.left → Smooth G.hom → GeometricallyConnected G.hom →
      IsIso ((Over.pullback (spMap (algebraMap T K))).map p) → IsIso p := by
  intro T K _ _ _ _ _ _ Ga G _ _ p _ _ _ _ _ _ _ _ _
  let t := spMap (algebraMap T K)
  have : IsOpenImmersion t := isOpenImmersion_spMap_of_isDiscreteValuationRing T K
  have hc : ConnectedSpace ((Over.pullback t).obj G).left :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback G.hom t)
  obtain ⟨hG, hN⟩ := isIntegral_and_isNormalScheme_of_smooth_dvr T K G ‹_› hc
  let q : pullback Ga.hom t ⟶ pullback G.hom t := ((Over.pullback t).map p).left
  have : IsIso q := inferInstanceAs (IsIso ((Over.forget _).map ((Over.pullback t).map p)))
  have e : q ≫ pullback.fst G.hom t = pullback.fst Ga.hom t ≫ p.left := pullback.lift_fst _ _ _
  have : ConnectedSpace ↥(pullback G.hom t) := hc
  have : IsIntegral (pullback G.hom t) := isIntegral_of_isOpenImmersion (pullback.fst G.hom t)
  have : Nonempty ↥(pullback Ga.hom t) := ⟨inv q (Classical.arbitrary _)⟩
  have : IsIntegral (pullback Ga.hom t) := isIntegral_of_isOpenImmersion q
  have : IsIntegral Ga.left := isIntegral_of_flat_of_isIntegral_genericFibre T K Ga.hom
  let j := pullback.fst Ga.hom t
  have : IsOpenImmersion (j.opensRange.ι ≫ p.left) := by
    rw [← j.isoOpensRange_inv_comp, Category.assoc, ← e]
    infer_instance
  have : IsOpenImmersion p.left :=
    isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict p.left (fun y ↦ (hN y).2)
      j.opensRange ⟨⟨j (Classical.arbitrary _), _, rfl⟩⟩
  exact isIso_of_isOpenImmersion_of_geometricallyConnected _ Ga G p ‹_› ‹_› inferInstance ‹_›

end GlobalTheory
