import Mathlib
open scoped NNReal TensorProduct

namespace GlobalTheory

open Polynomial

/- English proof (translation)
Take `⟨a, ha⟩` from `hnt.exists_abv_gt_one`. Use `letI : NontriviallyNormedField (WithAbs f) := NontriviallyNormedField.ofNormNeOne ⟨WithAbs.toAbs f a, by`. Introduce `h; rw [WithAbs.toAbs_eq_zero] at h; rw [h, map_zero] at ha; linarith, by`. Rewrite using `[WithAbs.norm_toAbs_eq]`. Conclude with `ha.ne'⟩`.

Use `haveI : IsUltrametricDist (WithAbs f) := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun x y => hna x.ofAbs y.ofAbs`. Use `haveI : IsScalarTower K (WithAbs f) Ω := inferInstance`. Use `haveI : Algebra.IsAlgebraic (WithAbs f) Ω := Algebra.IsAlgebraic.tower_top (K := K) (WithAbs f)`. Establish `hmin : ∀ x : Ω, minpoly (WithAbs f) x = (minpoly K x).map (algebraMap K (WithAbs f))`. Introduce `x`.

Establish `hx : IsIntegral K x` using `(Algebra.IsAlgebraic.isAlgebraic x).isIntegral`. Establish `hmap : (minpoly K x).map (algebraMap K (WithAbs f)) = Polynomial.mapEquiv (WithAbs.equiv f).symm (minpoly K x)`. Rewrite using `[Polynomial.mapEquiv_apply]`. Both sides reduce to the same expression. Use `symm`.

Apply `minpoly.eq_of_irreducible_of_monic` to reduce the goal to its premises. Rewrite using `[hmap]`. Conclude with `(MulEquiv.irreducible_iff _).mpr (minpoly.irreducible hx)`. Rewrite using `[Polynomial.aeval_map_algebraMap]`. Conclude with `minpoly.aeval K x`.

Conclude with `(minpoly.monic hx).map _`. Set `v : Valuation Ω ℝ≥0` to `{ toFun := fun x => ⟨spectralNorm (WithAbs f) Ω x, spectralNorm_nonneg x⟩ map_zero' := by ext; exact spectralNorm_zero map_one' := by ext; exact spectralNorm_one map_mul' := fun x y => by ext; exact spectralAlgNorm_mul (K := WithAbs f) (L := Ω) x y map_add_le_max' := fun x y => b …`. Conclude with `isNonarchimedean_spectralNorm x y }`. Establish `hv : ∀ x : Ω, (v x : ℝ) = spectralNorm (WithAbs f) Ω x` using `fun _ => rfl`. Use `⟨v, fun x => ?_, fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[hv]`. Establish `: algebraMap K Ω x = algebraMap (WithAbs f) Ω (WithAbs.toAbs f x)` using `rfl`. Rewrite using `[this, spectralNorm_extends, WithAbs.norm_toAbs_eq]`. Establish `hx : IsIntegral (WithAbs f) x` using `(Algebra.IsAlgebraic.isAlgebraic x).isIntegral`. Rewrite using `[← NNReal.coe_le_coe, NNReal.coe_one, hv]`.

Use `show spectralValue (minpoly (WithAbs f) x) ≤ 1 ↔ _`. Rewrite using `[spectralValue_le_one_iff (minpoly.monic hx), hmin x]`. Use `forall_congr' fun i => ?_` and prove the remaining obligations. Rewrite using `[Polynomial.coeff_map, WithAbs.algebraMap_right_apply, WithAbs.norm_toAbs_eq]`. Both sides reduce to the same expression.
-/
theorem exists_spectralValuation (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (f : AbsoluteValue K ℝ) (hna : IsNonarchimedean f) (hnt : f.IsNontrivial)
    (hc : CompleteSpace (WithAbs f)) :
    ∃ v : Valuation Ω ℝ≥0, (∀ x : K, (v (algebraMap K Ω x) : ℝ) = f x) ∧
      ∀ x : Ω, v x ≤ 1 ↔ ∀ i, f ((minpoly K x).coeff i) ≤ 1 := by
  obtain ⟨a, ha⟩ := hnt.exists_abv_gt_one
  letI : NontriviallyNormedField (WithAbs f) :=
    NontriviallyNormedField.ofNormNeOne ⟨WithAbs.toAbs f a, by
      intro h; rw [WithAbs.toAbs_eq_zero] at h; rw [h, map_zero] at ha; linarith, by
      rw [WithAbs.norm_toAbs_eq]; exact ha.ne'⟩
  haveI : IsUltrametricDist (WithAbs f) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun x y => hna x.ofAbs y.ofAbs
  haveI : IsScalarTower K (WithAbs f) Ω := inferInstance
  haveI : Algebra.IsAlgebraic (WithAbs f) Ω := Algebra.IsAlgebraic.tower_top (K := K) (WithAbs f)
  have hmin : ∀ x : Ω, minpoly (WithAbs f) x = (minpoly K x).map (algebraMap K (WithAbs f)) := by
    intro x
    have hx : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    have hmap : (minpoly K x).map (algebraMap K (WithAbs f)) =
        Polynomial.mapEquiv (WithAbs.equiv f).symm (minpoly K x) := by
      rw [Polynomial.mapEquiv_apply]; rfl
    symm
    apply minpoly.eq_of_irreducible_of_monic
    · rw [hmap]; exact (MulEquiv.irreducible_iff _).mpr (minpoly.irreducible hx)
    · rw [Polynomial.aeval_map_algebraMap]; exact minpoly.aeval K x
    · exact (minpoly.monic hx).map _
  let v : Valuation Ω ℝ≥0 :=
    { toFun := fun x => ⟨spectralNorm (WithAbs f) Ω x, spectralNorm_nonneg x⟩
      map_zero' := by ext; exact spectralNorm_zero
      map_one' := by ext; exact spectralNorm_one
      map_mul' := fun x y => by
        ext; exact spectralAlgNorm_mul (K := WithAbs f) (L := Ω) x y
      map_add_le_max' := fun x y => by
        show spectralNorm (WithAbs f) Ω (x + y) ≤ max (spectralNorm (WithAbs f) Ω x) (spectralNorm (WithAbs f) Ω y)
        exact isNonarchimedean_spectralNorm x y }
  have hv : ∀ x : Ω, (v x : ℝ) = spectralNorm (WithAbs f) Ω x := fun _ => rfl
  refine ⟨v, fun x => ?_, fun x => ?_⟩
  · rw [hv]
    have : algebraMap K Ω x = algebraMap (WithAbs f) Ω (WithAbs.toAbs f x) := rfl
    rw [this, spectralNorm_extends, WithAbs.norm_toAbs_eq]
  · have hx : IsIntegral (WithAbs f) x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    rw [← NNReal.coe_le_coe, NNReal.coe_one, hv]
    show spectralValue (minpoly (WithAbs f) x) ≤ 1 ↔ _
    rw [spectralValue_le_one_iff (minpoly.monic hx), hmin x]
    refine forall_congr' fun i => ?_
    rw [Polynomial.coeff_map, WithAbs.algebraMap_right_apply, WithAbs.norm_toAbs_eq]
    rfl

end GlobalTheory
