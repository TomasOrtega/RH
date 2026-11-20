import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterLe
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinitePlaceSumLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField MvPolynomial

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.FinitePlaceSumBound.finitePlace_sum_le v s f hB h`.
-/
theorem finitePlace_sum_le {K : Type*} [Field K] [NumberField K] (v : FinitePlace K) {α : Type*}
    (s : Finset α) (f : α → K) {B : ℝ} (hB : 0 ≤ B) (h : ∀ a ∈ s, v (f a) ≤ B) :
    v (∑ a ∈ s, f a) ≤ B :=
  _root_.UpperTheory.Reformulated.B.FinitePlaceSumBound.finitePlace_sum_le v s f hB h

/- English proof (translation)
Introduce `ι _ _ n x v F d hF`. Establish `hle : ∀ k i, v (coordVec x k i) ≤ ⨆ j, v (coordVec x k j)` using `fun k i ↦ le_ciSup (f := fun j ↦ v (coordVec x k j)) (Set.finite_range _).bddAbove i`. Establish `hM0 : ∀ k, 0 ≤ ⨆ j, v (coordVec x k j)` using `fun k ↦ (apply_nonneg v _).trans (hle k 0)`. Establish `hna : IsNonarchimedean (v : coordField x → ℝ)` using `fun a b ↦ v.add_le a b`. Establish `hW : IsWeightedHomogeneous (coordDeg n) F d` using `(geoMultiHomog_iff F d).mp hF`.

Unfold `evalCone`. Rewrite using `[eval₂_eq']`. Use `finitePlace_sum_le v _ _ (Finset.prod_nonneg fun k _ ↦ pow_nonneg (hM0 k) _) fun m hm ↦ ?_` and prove the remaining obligations. Establish `hw : ∀ k, ∑ i, m ⟨k, i⟩ = d k` using `fun k ↦ by`. Rewrite using `[← weight_coordDeg_apply, hW (mem_support_iff.mp hm)]`.

Establish `hc : v ((Int.castRingHom (coordField x)) (F.coeff m)) ≤ 1`. Simplify using `using IsNonarchimedean.apply_intCast_le_one (f := v) hna (n := F.coeff m)`. Rewrite using `[map_mul, map_prod]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_pow]`.

Conclude with `pow_le_pow_left₀ (apply_nonneg v _) (hle _ _) _`. Use `_ = ∏ k, (⨆ j, v (coordVec x k j)) ^ d k := by`. Rewrite using `[one_mul, Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[Finset.prod_pow_eq_pow_sum, hw k]`.
-/
theorem OrbitCenterLe.proof : OrbitCenterLe.Statement := by
  intro ι _ _ n x v F d hF
  classical
  have hle : ∀ k i, v (coordVec x k i) ≤ ⨆ j, v (coordVec x k j) := fun k i ↦
    le_ciSup (f := fun j ↦ v (coordVec x k j)) (Set.finite_range _).bddAbove i
  have hM0 : ∀ k, 0 ≤ ⨆ j, v (coordVec x k j) := fun k ↦ (apply_nonneg v _).trans (hle k 0)
  have hna : IsNonarchimedean (v : coordField x → ℝ) := fun a b ↦ v.add_le a b
  have hW : IsWeightedHomogeneous (coordDeg n) F d := (geoMultiHomog_iff F d).mp hF
  unfold evalCone
  rw [eval₂_eq']
  refine finitePlace_sum_le v _ _
    (Finset.prod_nonneg fun k _ ↦ pow_nonneg (hM0 k) _) fun m hm ↦ ?_
  have hw : ∀ k, ∑ i, m ⟨k, i⟩ = d k := fun k ↦ by
    rw [← weight_coordDeg_apply, hW (mem_support_iff.mp hm)]
  have hc : v ((Int.castRingHom (coordField x)) (F.coeff m)) ≤ 1 := by
    simpa using IsNonarchimedean.apply_intCast_le_one (f := v) hna (n := F.coeff m)
  rw [map_mul, map_prod]
  calc v ((Int.castRingHom (coordField x)) (F.coeff m)) * ∏ p, v (coordVec x p.1 p.2 ^ m p)
      ≤ 1 * ∏ p : Coord n, (⨆ j, v (coordVec x p.1 j)) ^ m p := by
        gcongr with p
        rw [map_pow]; exact pow_le_pow_left₀ (apply_nonneg v _) (hle _ _) _
    _ = ∏ k, (⨆ j, v (coordVec x k j)) ^ d k := by
        rw [one_mul, Fintype.prod_sigma]
        refine Finset.prod_congr rfl fun k _ ↦ ?_
        dsimp only
        rw [Finset.prod_pow_eq_pow_sum, hw k]

end GroundTheory.Heights₂.Heights
