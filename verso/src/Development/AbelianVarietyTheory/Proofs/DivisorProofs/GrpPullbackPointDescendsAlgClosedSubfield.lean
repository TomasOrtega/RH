import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtalePointOfExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AlgClosedDescent

/- English proof (translation)
Introduce `K _ _ k₀ hk B₀ _ G _ π hB hG n hn y z₀ hz`. Use `haveI : IsAlgClosed k₀ := hk`. Establish `hs : spMap (algebraMap k₀ K) = spMap k₀.subtype` using `rfl`. Establish `hst` using `isGrpPullback_pullback B₀ (spMap (algebraMap k₀ K))`. Take `⟨e, he, heφ⟩` from `grpPullback_iso hG (hst.congr hs rfl)`.

Use `haveI := he`. Establish `hepi : Epi (spMap (algebraMap k₀ K))` using `Flat.epi_of_flat_of_surjective _`. Establish `hn' : (n : k₀) ≠ 0`. Introduce `h`. Establish `h2` using `congrArg (algebraMap k₀ K) h`.

Rewrite `h2` using `[map_natCast, map_zero]`. Conclude with `(Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)) h2`. Establish `hz0 : z₀ ≫ B₀.hom = 𝟙 _`. Rewrite using `[← cancel_epi (spMap (algebraMap k₀ K))]`. Establish `h1 : (y ^ n).left ≫ G.hom = 𝟙 _` using `Over.w (y ^ n)`.

Establish `h2` using `hG.1.w`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Category.assoc, ← Category.assoc, hs, hz]`. Use `_ = (y ^ n).left ≫ G.hom ≫ spMap k₀.subtype := by rw [h2]`. Use `_ = spMap (algebraMap k₀ K) ≫ 𝟙 _ := by`.

Rewrite using `[← Category.assoc, h1, Category.id_comp, Category.comp_id]`. Both sides reduce to the same expression. Set `z₀' : 𝟙_ (Over (Sp k₀)) ⟶ B₀` to `Over.homMk z₀ hz0`. Set `y'` to `y ≫ e.hom`. Establish `hpow : ∀ m : ℕ, (y ≫ e.hom) ^ m = (y ^ m) ≫ e.hom`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => rw [pow_zero, pow_zero, MonObj.one_comp]`. Consider the case `succ k ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]`. Establish `hy'n : y' ^ n = (y ^ n) ≫ e.hom` using `hpow n`.

Establish `hz' : (y' ^ n).left ≫ pullback.fst B₀.hom (spMap (algebraMap k₀ K)) = spMap (algebraMap k₀ K) ≫ z₀'.left`. Rewrite using `[hy'n, Over.comp_left, Category.assoc, heφ]`. Conclude with `hz`. Take `⟨y₀, -, hy₀⟩` from `(point_descent B₀ hB n hn' y' z₀' hz').exists`. Use `⟨y₀.left, ?_⟩` and prove the remaining obligations.

Rewrite using `[← heφ, ← Category.assoc]`. Conclude with `hy₀`.
-/
theorem grpPullback_point_descends : ∀ (K : Type) [Field K] [CharZero K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] (G : Over (Sp K)) [GrpObj G] (π : G.left ⟶ B₀.left), IsAbelianScheme B₀ → IsGrpPullback G B₀ (spMap k₀.subtype) π → ∀ (n : ℕ), 0 < n → ∀ (y : 𝟙_ (Over (Sp K)) ⟶ G) (z₀ : Sp k₀ ⟶ B₀.left), (y ^ n).left ≫ π = spMap k₀.subtype ≫ z₀ → ∃ y₀ : Sp k₀ ⟶ B₀.left, y.left ≫ π = spMap k₀.subtype ≫ y₀ := by
  intro K _ _ k₀ hk B₀ _ G _ π hB hG n hn y z₀ hz
  haveI : IsAlgClosed k₀ := hk
  have hs : spMap (algebraMap k₀ K) = spMap k₀.subtype := rfl
  have hst := isGrpPullback_pullback B₀ (spMap (algebraMap k₀ K))
  obtain ⟨e, he, heφ⟩ := grpPullback_iso hG (hst.congr hs rfl)
  haveI := he
  have hepi : Epi (spMap (algebraMap k₀ K)) := Flat.epi_of_flat_of_surjective _
  have hn' : (n : k₀) ≠ 0 := by
    intro h
    have h2 := congrArg (algebraMap k₀ K) h
    rw [map_natCast, map_zero] at h2
    exact (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)) h2
  have hz0 : z₀ ≫ B₀.hom = 𝟙 _ := by
    rw [← cancel_epi (spMap (algebraMap k₀ K))]
    have h1 : (y ^ n).left ≫ G.hom = 𝟙 _ := Over.w (y ^ n)
    have h2 := hG.1.w
    calc spMap (algebraMap k₀ K) ≫ z₀ ≫ B₀.hom = (y ^ n).left ≫ π ≫ B₀.hom := by
          rw [← Category.assoc, ← Category.assoc, hs, hz]
      _ = (y ^ n).left ≫ G.hom ≫ spMap k₀.subtype := by rw [h2]
      _ = spMap (algebraMap k₀ K) ≫ 𝟙 _ := by
          rw [← Category.assoc, h1, Category.id_comp, Category.comp_id]; rfl
  let z₀' : 𝟙_ (Over (Sp k₀)) ⟶ B₀ := Over.homMk z₀ hz0
  let y' := y ≫ e.hom
  have hpow : ∀ m : ℕ, (y ≫ e.hom) ^ m = (y ^ m) ≫ e.hom := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
    | succ k ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]
  have hy'n : y' ^ n = (y ^ n) ≫ e.hom := hpow n
  have hz' : (y' ^ n).left ≫ pullback.fst B₀.hom (spMap (algebraMap k₀ K)) =
      spMap (algebraMap k₀ K) ≫ z₀'.left := by
    rw [hy'n, Over.comp_left, Category.assoc, heφ]
    exact hz
  obtain ⟨y₀, -, hy₀⟩ := (point_descent B₀ hB n hn' y' z₀' hz').exists
  refine ⟨y₀.left, ?_⟩
  rw [← heφ, ← Category.assoc]
  exact hy₀

end GlobalTheory.AlgClosedDescent
