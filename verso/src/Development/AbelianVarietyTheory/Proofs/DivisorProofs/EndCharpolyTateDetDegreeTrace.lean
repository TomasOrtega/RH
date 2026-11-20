import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDegreePolynomialMapEqCharpolyRatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyEndCharpolySpecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleFreeFinrankTwoMulDim
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

/- English proof (translation)
Set `b` to `Module.finBasis F W`. Rewrite using `[LinearMap.trace_eq_matrix_trace F b, Matrix.trace_eq_neg_charpoly_nextCoeff, LinearMap.charpoly_toMatrix]`.
-/
theorem linTrace_eq_neg_nextCoeff {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (g : Module.End F W) :
    LinearMap.trace F W g = -g.charpoly.nextCoeff := by
  classical
  let b := Module.finBasis F W
  rw [LinearMap.trace_eq_matrix_trace F b, Matrix.trace_eq_neg_charpoly_nextCoeff,
    LinearMap.charpoly_toMatrix]

/- English proof (translation)
Take `⟨⟨hm, hd, hev⟩, -⟩` from `GlobalTheory.T.abelianVarietyEndCharpoly_spec K A f`. Establish `key` using `GlobalTheory.T.abelianVariety_degreePolynomial_map_eq_charpoly_rationalTate K l hl A f ((charpoly f).map (algebraMap ℤ ℚ)) (hm.map _) (by rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℚ)), hd]) (fun n => by`. Rewrite using `[Polynomial.eval_intCast_map, Int.cast_id, hev n]`. Use the proof step `simp)`. Rewrite using `[← key, Polynomial.map_map]`.

Use `congr 1`.
-/
theorem charpoly_map_vmap {K : Type} [Field K] (l : ℕ) [Fact l.Prime] (hl : (l : K) ≠ 0) (A : AbVar K)
    [Module.Finite ℚ_[l] (Vl l A)] (f : End A) :
    (charpoly f).map (algebraMap ℤ ℚ_[l]) = (vmap l (A := A) (B := A) f).charpoly := by
  obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec K A f
  have key := GlobalTheory.T.abelianVariety_degreePolynomial_map_eq_charpoly_rationalTate K l hl A f ((charpoly f).map (algebraMap ℤ ℚ)) (hm.map _)
    (by rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℚ)), hd])
    (fun n => by
      rw [Polynomial.eval_intCast_map, Int.cast_id, hev n]
      simp)
  rw [← key, Polynomial.map_map]
  congr 1

end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

/- English proof (translation)
Introduce `K _ l _ hl A f`. Use `⟨fun {_} => charpoly_map_vmap l hl A f, fun {_ _} => ?_, ?_, ?_⟩` and prove the remaining obligations. Apply `Polynomial.map_injective (algebraMap ℤ_[l] ℚ_[l]) (IsFractionRing.injective ℤ_[l] ℚ_[l])` to reduce the goal to its premises. Rewrite using `[Polynomial.map_map, ← LinearMap.charpoly_baseChange]`. Establish `hc : (algebraMap ℤ_[l] ℚ_[l]).comp (algebraMap ℤ ℤ_[l]) = algebraMap ℤ ℚ_[l]` using `Subsingleton.elim _ _`.

Rewrite using `[hc]`. Conclude with `charpoly_map_vmap l hl A f`. Take `⟨-, -, -, hfin, hrk⟩` from `tl_free_finrank K l hl A`. Establish `hneg : vmap l (A` using `A) (B := A) f = (-1 : ℚ_[l]) • vmap l (A := A) (B := A) (-f) := by`. Simplify using `only [vmap, map_neg, LinearMap.baseChange_neg, neg_one_smul, neg_neg]`.

Establish `hev` using `(GlobalTheory.T.abelianVarietyEndCharpoly_spec K A (-f)).1.2.2 0`. Rewrite `hev` using `[Int.cast_zero, zero_sub, neg_neg]`. Rewrite using `[hneg, LinearMap.det_smul, LinearMap.det_eq_sign_charpoly_coeff, ← charpoly_map_vmap l hl A (-f), Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero, hev, hrk, pow_mul, neg_one_sq, one_pow]`. Simplify using the standard rewrite rules. Take `⟨-, -, -, hfin, -⟩` from `tl_free_finrank K l hl A`.

Rewrite using `[linTrace_eq_neg_nextCoeff, ← charpoly_map_vmap l hl A f, Polynomial.nextCoeff_map (RingHom.injective_int (algebraMap ℤ ℚ_[l])), trace]`. Simplify using the standard rewrite rules.
-/
theorem charpoly_tate_det_trace : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K) (f : End A), (∀ [Module.Finite ℚ_[l] (Vl l A)], (charpoly f).map (algebraMap ℤ ℚ_[l]) = (vmap l (A := A) (B := A) f).charpoly) ∧ (∀ [Module.Free ℤ_[l] (Tl l A)] [Module.Finite ℤ_[l] (Tl l A)], (charpoly f).map (algebraMap ℤ ℤ_[l]) = (tend l A f).charpoly) ∧ LinearMap.det (vmap l (A := A) (B := A) f) = (deg (A := A) (B := A) f : ℚ_[l]) ∧ LinearMap.trace ℚ_[l] _ (vmap l (A := A) (B := A) f) = (trace f : ℚ_[l]) := by
  intro K _ l _ hl A f
  refine ⟨fun {_} => charpoly_map_vmap l hl A f, fun {_ _} => ?_, ?_, ?_⟩
  · apply Polynomial.map_injective (algebraMap ℤ_[l] ℚ_[l]) (IsFractionRing.injective ℤ_[l] ℚ_[l])
    rw [Polynomial.map_map, ← LinearMap.charpoly_baseChange]
    have hc : (algebraMap ℤ_[l] ℚ_[l]).comp (algebraMap ℤ ℤ_[l]) = algebraMap ℤ ℚ_[l] := Subsingleton.elim _ _
    rw [hc]
    exact charpoly_map_vmap l hl A f
  · obtain ⟨-, -, -, hfin, hrk⟩ := tl_free_finrank K l hl A
    have hneg : vmap l (A := A) (B := A) f = (-1 : ℚ_[l]) • vmap l (A := A) (B := A) (-f) := by
      simp only [vmap, map_neg, LinearMap.baseChange_neg, neg_one_smul, neg_neg]
    have hev := (GlobalTheory.T.abelianVarietyEndCharpoly_spec K A (-f)).1.2.2 0
    rw [Int.cast_zero, zero_sub, neg_neg] at hev
    rw [hneg, LinearMap.det_smul, LinearMap.det_eq_sign_charpoly_coeff, ← charpoly_map_vmap l hl A (-f),
      Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero, hev, hrk, pow_mul, neg_one_sq, one_pow]
    simp
  · obtain ⟨-, -, -, hfin, -⟩ := tl_free_finrank K l hl A
    rw [linTrace_eq_neg_nextCoeff, ← charpoly_map_vmap l hl A f,
      Polynomial.nextCoeff_map (RingHom.injective_int (algebraMap ℤ ℚ_[l])), trace]
    simp

end GlobalTheory.AV.AbVar
