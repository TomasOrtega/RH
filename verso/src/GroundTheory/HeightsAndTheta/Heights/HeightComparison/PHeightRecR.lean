import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightRecR
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitDivVertical
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitFiniteSum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitArchSum
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Comparison
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [DecidableEq ι] in

/- English proof (translation)
Use `conv_lhs => rw [s.as_sum]`. Use `conv_rhs => rw [s.as_sum, eval₂_sum]`. Rewrite using `[map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m hm ↦ ?_` and prove the remaining obligations. Establish `hmon : ∏ p ∈ m.support, (X p.1 : MvPolynomial ι Ω) ^ m p = ∏ k, X k ^ a k`.

Rewrite using `[Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp ↦ by`. Rewrite using `[Finsupp.notMem_support_iff.mp hp, pow_zero]), Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Use `show ∏ i, (X k : MvPolynomial ι Ω) ^ m ⟨k, i⟩ = _`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hs m hm k]`.

Rewrite using `[Geo.mConeMap, aeval_monomial, eval₂_monomial, Finsupp.prod, Finsupp.prod]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, hmon, map_mul, map_prod, map_pow, eq_intCast, map_intCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mConeMap_of_isMultiHomog {Ω : Type*} [Field Ω] (y : Coord n → Ω)
    (s : MvPolynomial (Coord n) ℤ) (a : ι → ℕ) (hs : Geo.IsMultiHomog (ι := blockIdx n) s a) :
    Geo.mConeMap (ι := blockIdx n) y s = C (eval₂ (Int.castRingHom Ω) y s) * ∏ k, X k ^ a k := by
  classical
  conv_lhs => rw [s.as_sum]
  conv_rhs => rw [s.as_sum, eval₂_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hmon : ∏ p ∈ m.support, (X p.1 : MvPolynomial ι Ω) ^ m p = ∏ k, X k ^ a k := by
    rw [Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp ↦ by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero]), Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    show ∏ i, (X k : MvPolynomial ι Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hs m hm k]
  rw [Geo.mConeMap, aeval_monomial, eval₂_monomial, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, hmon, map_mul, map_prod, map_pow, eq_intCast,
    map_intCast]
  ring

/- English proof (translation)
Introduce `h`. Apply `hW` to reduce the goal to its premises. Establish `e : eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) (flatCone x) s = algebraMap (coordField x) (AlgebraicClosure ℚ) (evalCone (coordVec x) s)`. Rewrite using `[← evalCone_map]`. Both sides reduce to the same expression.

Rewrite using `[orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_isMultiHomog _ s a hs, e, h, map_zero, map_zero, zero_mul]`.
-/
theorem evalCone_coordVec_ne_zero (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ)
    (a : ι → ℕ) (hs : Geo.IsMultiHomog (ι := blockIdx n) s a) (hW : s ∉ orbitIdeal x) :
    evalCone (coordVec x) s ≠ 0 := by
  intro h
  apply hW
  have e : eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) (flatCone x) s =
      algebraMap (coordField x) (AlgebraicClosure ℚ) (evalCone (coordVec x) s) := by
    rw [← evalCone_map]
    rfl
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_isMultiHomog _ s a hs, e, h,
    map_zero, map_zero, zero_mul]

/- English proof (translation)
Introduce `ι _ _ _ n I A x s hx hs`. Take `⟨a, _, hsa, hsW⟩` from `id hs`. Establish `ht : evalCone (coordVec x) s ≠ 0` using `evalCone_coordVec_ne_zero x s a hsa hsW`. Establish `e1 : Geo.recR I (orbitIdeal x) (Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) A.toGeo s = (∑ᶠ V ∈ Geo.divSupp (orbitIdeal x) s, (Geo.multAt (orbitIdeal x ⊔ Ideal.span {s}) V : ℝ) * ((Geo.geoNum (ι` using `blockIdx n) 0 V Fin.elim0 : ℝ) * Real.log (Geo.charOf V))) - Geo.arInt (orbitIdeal x) s A.toGeo (Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) := by`. Unfold `Geo.recR`.

Use `congr 1`. Use `finsum_mem_congr rfl fun V hV' ↦ ?_` and prove the remaining obligations. Rewrite using `[if_neg (hV ι n A x s hx hs V hV')]`. Use `congr 4`. Use function extensionality and compare the values at `j`.

Conclude with `j.elim0`. Establish `hpos : ∀ σ : coordField x →+* ℂ, 0 < A.metric (fun k i ↦ σ (coordVec x k i))` using `fun σ ↦ A.metric_pos _ (blockNonzero_sigma hx σ)`. Establish `e2 : ∀ σ : coordField x →+* ℂ, Real.log (‖evalCone (fun k i ↦ σ (coordVec x k i)) s‖ / A.metric (fun k i ↦ σ (coordVec x k i))) = Real.log ‖σ (evalCone (coordVec x) s)‖ - Real.log (A.metric (fun k i ↦ σ (coordVec x k i)))` using `fun σ ↦ by`. Rewrite using `[evalCone_map, Real.log_div (norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr ht)) (hpos σ).ne']`. Establish `hsupp1 : (Function.support fun v : FinitePlace (coordField x) ↦ finiteTerm A v (coordVec x)).Finite` using `finite_support_height A x hx`.

Establish `hsupp2 : (Function.support fun v : FinitePlace (coordField x) ↦ Real.log (v (evalCone (coordVec x) s))).Finite`. Use `Set.Finite.subset (FinitePlace.hasFiniteMulSupport ht) fun v hv h ↦ hv ?_` and prove the remaining obligations. Simplify using `only [h, Real.log_one]`. Establish `hprod` using `sum_log_places_eq_zero ht`. Rewrite using `[e1, hF ι n A x s hx hs, hA ι n A x s hx hs, finsum_sub_distrib hsupp1 hsupp2, Finset.sum_congr rfl fun σ _ ↦ e2 σ, Finset.sum_sub_distrib, height]`.

Simplify using `only [finiteTerm]`. Take the linear combination `(-((Geo.degC (ι := blockIdx n) (orbitIdeal x) : ℝ) / Module.finrank ℚ (coordField x))) * hprod`.
-/
theorem HeightRecR.proof (hV : OrbitDivVertical.Statement) (hF : OrbitFiniteSum.Statement)
    (hA : OrbitArchSum.Statement) : HeightRecR.Statement := by
  intro ι _ _ _ n I A x s hx hs
  obtain ⟨a, _, hsa, hsW⟩ := id hs
  have ht : evalCone (coordVec x) s ≠ 0 := evalCone_coordVec_ne_zero x s a hsa hsW
  have e1 : Geo.recR I (orbitIdeal x) (Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) A.toGeo s =
      (∑ᶠ V ∈ Geo.divSupp (orbitIdeal x) s,
        (Geo.multAt (orbitIdeal x ⊔ Ideal.span {s}) V : ℝ) *
          ((Geo.geoNum (ι := blockIdx n) 0 V Fin.elim0 : ℝ) * Real.log (Geo.charOf V))) -
      Geo.arInt (orbitIdeal x) s A.toGeo (Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) := by
    unfold Geo.recR
    congr 1
    refine finsum_mem_congr rfl fun V hV' ↦ ?_
    rw [if_neg (hV ι n A x s hx hs V hV')]
    congr 4
    funext j
    exact j.elim0
  have hpos : ∀ σ : coordField x →+* ℂ, 0 < A.metric (fun k i ↦ σ (coordVec x k i)) :=
    fun σ ↦ A.metric_pos _ (blockNonzero_sigma hx σ)
  have e2 : ∀ σ : coordField x →+* ℂ,
      Real.log (‖evalCone (fun k i ↦ σ (coordVec x k i)) s‖ /
          A.metric (fun k i ↦ σ (coordVec x k i))) =
        Real.log ‖σ (evalCone (coordVec x) s)‖ -
          Real.log (A.metric (fun k i ↦ σ (coordVec x k i))) := fun σ ↦ by
    rw [evalCone_map, Real.log_div (norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr ht)) (hpos σ).ne']
  have hsupp1 : (Function.support fun v : FinitePlace (coordField x) ↦
      finiteTerm A v (coordVec x)).Finite := finite_support_height A x hx
  have hsupp2 : (Function.support fun v : FinitePlace (coordField x) ↦
      Real.log (v (evalCone (coordVec x) s))).Finite := by
    refine Set.Finite.subset (FinitePlace.hasFiniteMulSupport ht) fun v hv h ↦ hv ?_
    simp only [h, Real.log_one]
  have hprod := sum_log_places_eq_zero ht
  rw [e1, hF ι n A x s hx hs, hA ι n A x s hx hs, finsum_sub_distrib hsupp1 hsupp2,
    Finset.sum_congr rfl fun σ _ ↦ e2 σ, Finset.sum_sub_distrib, height]
  simp only [finiteTerm]
  linear_combination (-((Geo.degC (ι := blockIdx n) (orbitIdeal x) : ℝ) /
    Module.finrank ℚ (coordField x))) * hprod

end

end GroundTheory.Heights₂.Heights
