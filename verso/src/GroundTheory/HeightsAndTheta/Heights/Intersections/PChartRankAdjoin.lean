import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsChartRankAdjoin
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumPoint
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace ChartRankAdjoin

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ'] (z : (Σ k, ι k) → Φ') (j : ∀ k, ι k)

def affCoord : (Σ k, ι k) → Φ' := fun q => z q / z ⟨q.1, j q.1⟩

variable {z j}

/- English proof (translation)
Proceed by induction on `m using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add m m' hm hm'`. Rewrite using `[← mul_one (1 : Φ), ← monomial_mul, map_mul, map_mul, map_add, ← hm, ← hm']`. Simplify using `only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `single p n`. Rewrite using `[← X_pow_eq_monomial, map_pow, map_pow, Finsupp.weight_single, Fintype.prod_eq_single p.1 (fun k hk => by simp [NumbersDVR.blockWeight, hk])]`. Simplify using `only [affCoord, aeval_X, NumbersDVR.blockWeight, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, div_pow]`. Rewrite using `[div_mul_cancel₀ _ (pow_ne_zero _ (hz p.1))]`.
-/
theorem aeval_monomial_mul (hz : ∀ k, z ⟨k, j k⟩ ≠ 0) (m : (Σ k, ι k) →₀ ℕ) :
    aeval (affCoord z j) (monomial m (1 : Φ)) *
        ∏ k, z ⟨k, j k⟩ ^ (Finsupp.weight (NumbersDVR.blockWeight ι) m k) =
      aeval z (monomial m (1 : Φ)) := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add m m' hm hm' =>
    rw [← mul_one (1 : Φ), ← monomial_mul, map_mul, map_mul, map_add, ← hm, ← hm']
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring
  | single p n =>
    rw [← X_pow_eq_monomial, map_pow, map_pow, Finsupp.weight_single,
      Fintype.prod_eq_single p.1 (fun k hk => by simp [NumbersDVR.blockWeight, hk])]
    simp only [affCoord, aeval_X, NumbersDVR.blockWeight, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one, div_pow]
    rw [div_mul_cancel₀ _ (pow_ne_zero _ (hz p.1))]

/- English proof (translation)
Establish `hw` using `(Bridge.isMultiHomog_iff h a).mpr hh`. Use `conv_rhs => rw [h.as_sum]`. Use `conv_lhs => rw [h.as_sum]`. Rewrite using `[map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations.

Establish `hw' : Finsupp.weight (NumbersDVR.blockWeight ι) m = a` using `hw (mem_support_iff.mp hm)`. Establish `hmon : monomial m (coeff m h) = coeff m h • monomial m (1 : Φ)`. Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[hmon, map_smul, map_smul, smul_mul_assoc, ← hw', aeval_monomial_mul hz]`.
-/
theorem aeval_mul_of_isMultiHomog [∀ k, Fintype (ι k)] (hz : ∀ k, z ⟨k, j k⟩ ≠ 0) {h : MRingOver Φ ι} {a : K → ℕ}
    (hh : IsMultiHomog h a) : aeval (affCoord z j) h * ∏ k, z ⟨k, j k⟩ ^ a k = aeval z h := by
  have hw := (Bridge.isMultiHomog_iff h a).mpr hh
  conv_rhs => rw [h.as_sum]
  conv_lhs => rw [h.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw' : Finsupp.weight (NumbersDVR.blockWeight ι) m = a := hw (mem_support_iff.mp hm)
  have hmon : monomial m (coeff m h) = coeff m h • monomial m (1 : Φ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmon, map_smul, map_smul, smul_mul_assoc, ← hw', aeval_monomial_mul hz]

/- English proof (translation)
Establish `hprod : ∀ a : K → ℕ, ∏ k, z ⟨k, j k⟩ ^ a k ≠ 0` using `fun a => Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hz k)`. Establish `hunit : Ideal.span (Set.range fun k => (X ⟨k, j k⟩ : MRingOver Φ ι) - 1) ≤ RingHom.ker (aeval (affCoord z j) : MRingOver Φ ι →ₐ[Φ] Φ')`. Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Simplify using `only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, aeval_X, affCoord]`.

Rewrite using `[div_self (hz k), sub_self]`. Use `le_antisymm (sup_le ?_ hunit) fun f hf => ?_` and prove the remaining obligations. Take `⟨S, hS, hPS⟩` from `hP`. Rewrite using `[hPS, Ideal.span_le]`. Introduce `s hs`.

Take `⟨a, ha⟩` from `hS s hs`. Establish `hsP : s ∈ RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ')`. Rewrite using `[hPS]`. Conclude with `Ideal.subset_span hs`. Establish `h1` using `aeval_mul_of_isMultiHomog hz ha`.

Rewrite `h1` using `[RingHom.mem_ker.mp hsP]`. Conclude with `RingHom.mem_ker.mpr ((mul_eq_zero.mp h1).resolve_right (hprod a))`. Take `⟨N, hN⟩` from `NumbersDVR.IntNumPoint.exists_homog_congr j f`. Take `⟨h, hh, hc⟩` from `hN N le_rfl`. Establish `hfh : f - h ∈ NumbersDVR.IntNumPoint.chartUnitIdeal (F` using `Φ) j := Ideal.Quotient.eq.mp hc`.

Establish `h0 : aeval (affCoord z j) h = 0`. Use `RingHom.mem_ker.mp (hunit hfh)` as an intermediate fact. Rewrite `this` using `[map_sub, RingHom.mem_ker.mp hf, zero_sub, neg_eq_zero]`. Then use the resulting hypothesis. Establish `hhP : h ∈ RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ')`. Rewrite using `[RingHom.mem_ker, ← aeval_mul_of_isMultiHomog hz ((Bridge.isMultiHomog_iff h N).mp hh), h0, zero_mul]`.

Establish `: f = (f - h) + h` using `by ring`. Rewrite using `[this]`. Conclude with `Ideal.add_mem _ (Ideal.mem_sup_right hfh) (Ideal.mem_sup_left hhP)`.
-/
theorem chartIdeal_eq_ker [∀ k, Fintype (ι k)] (hz : ∀ k, z ⟨k, j k⟩ ≠ 0)
    (hP : IsMultiHomogIdeal (RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ'))) :
    chartIdeal (RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ')) j =
      RingHom.ker (aeval (affCoord z j) : MRingOver Φ ι →ₐ[Φ] Φ') := by
  have hprod : ∀ a : K → ℕ, ∏ k, z ⟨k, j k⟩ ^ a k ≠ 0 :=
    fun a => Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hz k)
  have hunit : Ideal.span (Set.range fun k => (X ⟨k, j k⟩ : MRingOver Φ ι) - 1) ≤
      RingHom.ker (aeval (affCoord z j) : MRingOver Φ ι →ₐ[Φ] Φ') := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, aeval_X, affCoord]
    rw [div_self (hz k), sub_self]
  refine le_antisymm (sup_le ?_ hunit) fun f hf => ?_
  · obtain ⟨S, hS, hPS⟩ := hP
    rw [hPS, Ideal.span_le]
    intro s hs
    obtain ⟨a, ha⟩ := hS s hs
    have hsP : s ∈ RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ') := by
      rw [hPS]; exact Ideal.subset_span hs
    have h1 := aeval_mul_of_isMultiHomog hz ha
    rw [RingHom.mem_ker.mp hsP] at h1
    exact RingHom.mem_ker.mpr ((mul_eq_zero.mp h1).resolve_right (hprod a))
  · obtain ⟨N, hN⟩ := NumbersDVR.IntNumPoint.exists_homog_congr j f
    obtain ⟨h, hh, hc⟩ := hN N le_rfl
    have hfh : f - h ∈ NumbersDVR.IntNumPoint.chartUnitIdeal (F := Φ) j := Ideal.Quotient.eq.mp hc
    have h0 : aeval (affCoord z j) h = 0 := by
      have := RingHom.mem_ker.mp (hunit hfh)
      rwa [map_sub, RingHom.mem_ker.mp hf, zero_sub, neg_eq_zero] at this
    have hhP : h ∈ RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ') := by
      rw [RingHom.mem_ker, ← aeval_mul_of_isMultiHomog hz ((Bridge.isMultiHomog_iff h N).mp hh), h0,
        zero_mul]
    have : f = (f - h) + h := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_right hfh) (Ideal.mem_sup_left hhP)

end ChartRankAdjoin

/- English proof (translation)
Introduce `K _ ι _ Φ Φ' _ _ _ z j hz hP`. Establish `hker` using `ChartRankAdjoin.chartIdeal_eq_ker hz hP`. Establish `e : (fun q : Σ k, ι k => z q / z ⟨q.1, j q.1⟩) = ChartRankAdjoin.affCoord z j` using `rfl`. Rewrite using `[e, ptDeg, hker, (Ideal.quotientKerEquivRange (aeval (ChartRankAdjoin.affCoord z j) : MRingOver Φ ι →ₐ[Φ] Φ')).toLinearEquiv.finrank_eq, aeval_range, ← IntermediateField.finrank_eq_finrank_subalgebra]`. Distinguish the cases in `halg : ∀ q, IsAlgebraic Φ (ChartRankAdjoin.affCoord z j q)`.

Rewrite using `[IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (by rintro _ ⟨q, rfl⟩; exact halg q)]`. Use `push Not at halg`. Take `⟨q, hq⟩` from `halg`. Establish `hinf : ∀ B : Subalgebra Φ Φ', ChartRankAdjoin.affCoord z j q ∈ B → ¬ Module.Finite Φ B` using `fun B hB hfin => hq ((IsAlgebraic.of_finite Φ (⟨_, hB⟩ : B)).algHom B.val)`. Establish `h1 : ChartRankAdjoin.affCoord z j q ∈ Algebra.adjoin Φ (Set.range (ChartRankAdjoin.affCoord z j))` using `Algebra.subset_adjoin ⟨q, rfl⟩`.

Establish `h2 : ChartRankAdjoin.affCoord z j q ∈ (IntermediateField.adjoin Φ (Set.range (ChartRankAdjoin.affCoord z j))).toSubalgebra` using `IntermediateField.subset_adjoin Φ _ ⟨q, rfl⟩`. Rewrite using `[Module.finrank_of_not_finite (hinf _ h1), Module.finrank_of_not_finite (hinf _ h2)]`.
-/
theorem ChartRankAdjoin.proof : ChartRankAdjoin.Statement := by
  classical
  intro K _ ι _ Φ Φ' _ _ _ z j hz hP
  have hker := ChartRankAdjoin.chartIdeal_eq_ker hz hP
  have e : (fun q : Σ k, ι k => z q / z ⟨q.1, j q.1⟩) = ChartRankAdjoin.affCoord z j := rfl
  rw [e, ptDeg, hker,
    (Ideal.quotientKerEquivRange (aeval (ChartRankAdjoin.affCoord z j) :
      MRingOver Φ ι →ₐ[Φ] Φ')).toLinearEquiv.finrank_eq, aeval_range,
    ← IntermediateField.finrank_eq_finrank_subalgebra]
  by_cases halg : ∀ q, IsAlgebraic Φ (ChartRankAdjoin.affCoord z j q)
  · rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (by rintro _ ⟨q, rfl⟩; exact halg q)]
  · push Not at halg
    obtain ⟨q, hq⟩ := halg
    have hinf : ∀ B : Subalgebra Φ Φ', ChartRankAdjoin.affCoord z j q ∈ B → ¬ Module.Finite Φ B :=
      fun B hB hfin => hq ((IsAlgebraic.of_finite Φ (⟨_, hB⟩ : B)).algHom B.val)
    have h1 : ChartRankAdjoin.affCoord z j q ∈ Algebra.adjoin Φ (Set.range (ChartRankAdjoin.affCoord z j)) :=
      Algebra.subset_adjoin ⟨q, rfl⟩
    have h2 : ChartRankAdjoin.affCoord z j q ∈
        (IntermediateField.adjoin Φ (Set.range (ChartRankAdjoin.affCoord z j))).toSubalgebra :=
      IntermediateField.subset_adjoin Φ _ ⟨q, rfl⟩
    rw [Module.finrank_of_not_finite (hinf _ h1), Module.finrank_of_not_finite (hinf _ h2)]

end GroundTheory.Heights₂.Heights.Inter
