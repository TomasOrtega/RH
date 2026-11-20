import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.KernelNoTorsion

/- English proof (translation)
Use `GlobalTheory.isClosedImmersion_equalizer_ι_of_isSeparated f hab` as an intermediate fact. Establish `hk : (equalizer.ι a b).ker = ⊥`. Establish `h` using `Scheme.Hom.le_ker_comp (equalizer.lift j hj) (equalizer.ι a b)`. Rewrite `h` using `[equalizer.lift_ι, j.ker_eq_bot]`. Conclude with `le_bot_iff.mp h`.

Establish `: IsIso (equalizer.ι a b)` using `IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hk`. Rewrite using `[← cancel_epi (equalizer.ι a b), equalizer.condition]`.
-/
theorem eq_of_isSchemeTheoreticallyDominant {X S Y Z : Scheme.{0}} (f : X ⟶ S) [IsSeparated f]
    {a b : Y ⟶ X} (hab : a ≫ f = b ≫ f) (j : Z ⟶ Y) [IsSchemeTheoreticallyDominant j]
    (hj : j ≫ a = j ≫ b) : a = b := by
  have := GlobalTheory.isClosedImmersion_equalizer_ι_of_isSeparated f hab
  have hk : (equalizer.ι a b).ker = ⊥ := by
    have h := Scheme.Hom.le_ker_comp (equalizer.lift j hj) (equalizer.ι a b)
    rw [equalizer.lift_ι, j.ker_eq_bot] at h
    exact le_bot_iff.mp h
  have : IsIso (equalizer.ι a b) := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hk
  rw [← cancel_epi (equalizer.ι a b), equalizer.condition]

/- English proof (translation)
Establish `: IsDominant (spMap (algebraMap T K))`. Rewrite using `[isDominant_iff]`. Use `(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap T K)).mpr ?_` and prove the remaining obligations. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective T K)]`. Conclude with `bot_le`.

Use `IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap T K))` as an intermediate fact. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `eq_of_isSchemeTheoreticallyDominant X.hom ((Over.w a).trans (Over.w b).symm) (pullback.fst Y.hom (spMap (algebraMap T K))) ?_` and prove the remaining obligations. Establish `h'` using `congr(($h).left ≫ pullback.fst X.hom (spMap (algebraMap T K)))`. Conclude with `(pullback.lift_fst _ _ _).symm.trans (h'.trans (pullback.lift_fst _ _ _))`.
-/
theorem eq_of_generic (T K : Type) [CommRing T] [IsDomain T] [Field K] [Algebra T K]
    [IsFractionRing T K] {Y X : Over (Sp T)} [Flat Y.hom] [IsSeparated X.hom] {a b : Y ⟶ X}
    (h : (Over.pullback (spMap (algebraMap T K))).map a =
      (Over.pullback (spMap (algebraMap T K))).map b) : a = b := by
  have : IsDominant (spMap (algebraMap T K)) := by
    rw [isDominant_iff]
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap T K)).mpr ?_
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective T K)]
    exact bot_le
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap T K))
  apply Over.OverMorphism.ext
  refine eq_of_isSchemeTheoreticallyDominant X.hom ((Over.w a).trans (Over.w b).symm)
    (pullback.fst Y.hom (spMap (algebraMap T K))) ?_
  have h' := congr(($h).left ≫ pullback.fst X.hom (spMap (algebraMap T K)))
  exact (pullback.lift_fst _ _ _).symm.trans (h'.trans (pullback.lift_fst _ _ _))

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, mulN, Hom.one_def, comp_toUnit_assoc]`. Consider the case `succ n ih => rw [pow_succ, mulN, Hom.mul_def, comp_lift_assoc, ih, Category.comp_id]`.
-/
theorem comp_mulN {S : Scheme.{0}} {Y G : Over S} [GrpObj G] (x : Y ⟶ G) (n : ℕ) :
    x ≫ mulN G n = x ^ n := by
  induction n with
  | zero => rw [pow_zero, mulN, Hom.one_def, comp_toUnit_assoc]
  | succ n ih => rw [pow_succ, mulN, Hom.mul_def, comp_lift_assoc, ih, Category.comp_id]

noncomputable def torsionLift {S : Scheme.{0}} {Y G : Over S} [GrpObj G] {n : ℕ} (x : Y ⟶ G)
    (hx : x ^ n = 1) : Y ⟶ torsion G n :=
  pullback.lift x (toUnit Y) (by rw [comp_mulN, hx, Hom.one_def])

/- English proof (translation)
The claim follows from `pullback.lift_fst _ _ _`.
-/
theorem torsionLift_ι {S : Scheme.{0}} {Y G : Over S} [GrpObj G] {n : ℕ} (x : Y ⟶ G)
    (hx : x ^ n = 1) : torsionLift x hx ≫ torsion.ι G n = x :=
  pullback.lift_fst _ _ _

/- English proof (translation)
The claim follows from `pullback.hom_ext h (toUnit_unique _ _)`.
-/
theorem torsion_hom_ext {S : Scheme.{0}} {Y G : Over S} [GrpObj G] {n : ℕ}
    {a b : Y ⟶ torsion G n} (h : a ≫ torsion.ι G n = b ≫ torsion.ι G n) : a = b :=
  pullback.hom_ext h (toUnit_unique _ _)

/- English proof (translation)
Rewrite using `[← comp_mulN, Hom.one_def]`. Use `(pullback.condition).trans ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `toUnit_unique _ _`.
-/
theorem torsionι_pow {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) :
    torsion.ι G n ^ n = 1 := by
  rw [← comp_mulN, Hom.one_def]
  refine (pullback.condition).trans ?_
  congr 1
  exact toUnit_unique _ _

/- English proof (translation)
Introduce `T K _ _ _ _ _ _ Ga G _ _ _ _ p n hp hsep hA hB hiso Y x hx hxp`. Establish `hq : (torsion.ι Ga n ≫ p) ^ n = 1`. Rewrite using `[← MonObj.pow_comp, torsionι_pow, MonObj.one_comp]`. Set `q : torsion Ga n ⟶ torsion G n` to `torsionLift _ hq`. Set `e : torsion Ga n ⟶ torsion G n` to `torsionLift 1 (one_pow n)`.

Establish `hopen` using `GlobalTheory.isOpenImmersion_equalizer_ι_left_of_unramified q e`. Establish `hflat : Flat (equalizer q e).hom`. Rewrite using `[← Over.w (equalizer.ι q e)]`. Use `infer_instance`. Establish `h1 : (equalizer.ι q e ≫ torsion.ι Ga n) ≫ p = (1 : equalizer q e ⟶ Ga) ≫ p`.

Use `equalizer.condition q e =≫ torsion.ι G n` as an intermediate fact. Rewrite `this` using `[Category.assoc, Category.assoc, torsionLift_ι, torsionLift_ι, MonObj.comp_one]`. Rewrite using `[Category.assoc, this, MonObj.one_comp]`. Establish `h2 : equalizer.ι q e ≫ torsion.ι Ga n = 1`. Apply `eq_of_generic T K` to reduce the goal to its premises.

Rewrite using `[← cancel_mono ((Over.pullback (spMap (algebraMap T K))).map p), ← Functor.map_comp, ← Functor.map_comp, h1]`. Establish `h3 : torsionLift x hx ≫ q = torsionLift x hx ≫ e`. Apply `torsion_hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, torsionLift_ι, torsionLift_ι, MonObj.comp_one, ← Category.assoc, torsionLift_ι, hxp]`. Rewrite using `[← torsionLift_ι x hx, ← equalizer.lift_ι (torsionLift x hx) h3, Category.assoc, h2, MonObj.comp_one]`.
-/
theorem eq_one_of_pow_eq_one_of_comp_eq_one :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (Ga G : Over (Sp T)) [GrpObj Ga] [GrpObj G] [IsCommMonObj Ga] [IsCommMonObj G] (p : Ga ⟶ G) (n : ℕ), IsMonHom p → IsSeparated Ga.hom → Etale (torsion Ga n).hom → Etale (torsion G n).hom → IsIso ((Over.pullback (spMap (algebraMap T K))).map p) → ∀ (Y : Over (Sp T)) (x : Y ⟶ Ga), x ^ n = 1 → x ≫ p = 1 → x = 1 := by
  intro T K _ _ _ _ _ _ Ga G _ _ _ _ p n hp hsep hA hB hiso Y x hx hxp
  have hq : (torsion.ι Ga n ≫ p) ^ n = 1 := by
    rw [← MonObj.pow_comp, torsionι_pow, MonObj.one_comp]
  let q : torsion Ga n ⟶ torsion G n := torsionLift _ hq
  let e : torsion Ga n ⟶ torsion G n := torsionLift 1 (one_pow n)
  have hopen := GlobalTheory.isOpenImmersion_equalizer_ι_left_of_unramified q e
  have hflat : Flat (equalizer q e).hom := by
    rw [← Over.w (equalizer.ι q e)]
    infer_instance
  have h1 : (equalizer.ι q e ≫ torsion.ι Ga n) ≫ p = (1 : equalizer q e ⟶ Ga) ≫ p := by
    have := equalizer.condition q e =≫ torsion.ι G n
    rw [Category.assoc, Category.assoc, torsionLift_ι, torsionLift_ι, MonObj.comp_one] at this
    rw [Category.assoc, this, MonObj.one_comp]
  have h2 : equalizer.ι q e ≫ torsion.ι Ga n = 1 := by
    apply eq_of_generic T K
    rw [← cancel_mono ((Over.pullback (spMap (algebraMap T K))).map p), ← Functor.map_comp,
      ← Functor.map_comp, h1]
  have h3 : torsionLift x hx ≫ q = torsionLift x hx ≫ e := by
    apply torsion_hom_ext
    rw [Category.assoc, Category.assoc, torsionLift_ι, torsionLift_ι, MonObj.comp_one,
      ← Category.assoc, torsionLift_ι, hxp]
  rw [← torsionLift_ι x hx, ← equalizer.lift_ι (torsionLift x hx) h3, Category.assoc, h2,
    MonObj.comp_one]

end GlobalTheory.KernelNoTorsion
