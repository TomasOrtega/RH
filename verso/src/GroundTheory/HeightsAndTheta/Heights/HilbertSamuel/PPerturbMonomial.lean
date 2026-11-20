import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturbMonomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenDegAmple
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallGenTwist
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPerturbSemipos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry SectionBoundedMul SmallGenTwist

noncomputable section

namespace PerturbedMonomialBound

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Use `⟨∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k), fun k => ?_, fun z => ?_⟩` and prove the remaining obligations. Simplify using `only [Finsupp.finsetSum_apply]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [sum_single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Establish `h : chartMono c d = monomial (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ)`.

Rewrite using `[chartMono, monomial_sum_one]`. Conclude with `Finset.prod_congr rfl fun k _ => X_pow_eq_monomial`. Establish `e1` using `eval_chartMono z c d`. Rewrite `e1` using `[h, map_monomial, eval_monomial, Finsupp.prod_fintype _ _ (fun i => by simp)]`. Simplify using `using e1`.
-/
theorem chartMono_exponent (c : ∀ k, ι k) (d : K → ℕ) :
    ∃ μ : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = d k) ∧
      ∀ z : (Σ k, ι k) → ℂ, ∏ p, z p ^ μ p = ∏ k, z ⟨k, c k⟩ ^ d k := by
  classical
  refine ⟨∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k), fun k => ?_, fun z => ?_⟩
  · simp only [Finsupp.finsetSum_apply]
    rw [Finset.sum_comm]
    simp only [sum_single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have h : chartMono c d = monomial (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ) := by
      rw [chartMono, monomial_sum_one]
      exact Finset.prod_congr rfl fun k _ => X_pow_eq_monomial
    have e1 := eval_chartMono z c d
    rw [h, map_monomial, eval_monomial, Finsupp.prod_fintype _ _ (fun i => by simp)] at e1
    simpa using e1

/- English proof (translation)
Use `set e := Fintype.equivFin (∀ k, ι k) with he_def`. Use `⟨Fintype.card (∀ k, ι k), fun j => aeval y (chartMono (e.symm j) a), fun j => ?_, ?_, fun j => ?_⟩` and prove the remaining obligations. Introduce `c hc beta_reduce`. Rewrite using `[aeval_chartMono, ← Finset.prod_mul_distrib]`. Use `prod_mem fun k _ => ?_` and prove the remaining obligations.

Establish `hmem : y ⟨k, (e.symm j) k⟩ / y ⟨k, c k⟩ ∈ chartRingZ y c` using `Algebra.subset_adjoin ⟨⟨k, (e.symm j) k⟩, rfl⟩`. Use `pow_mem hmem (a k) using 1` and compare the differences between its conclusion and the goal. Simplify using `[ha, div_eq_mul_inv, zpow_neg, zpow_natCast, mul_pow, inv_pow]`. Introduce `c hc`. Apply the tactic sequence `refine ⟨fun j => if e.symm j = c then 1 else 0, fun j => by beta_reduce; split_ifs <;> simp, ?_⟩`.

Rewrite using `[Fintype.sum_equiv e.symm _ (fun i => (if i = c then (1 : Ω) else 0) * (aeval y (chartMono i a) * ∏ k, y ⟨k, c k⟩ ^ (-A.a k))) (fun _ => rfl)]`. Simplify using `only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[aeval_chartMono, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one fun k _ => by`. Simplify using `[ha, zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ (hc k))]`.

Introduce `dg dh g h z hg hh hdeg he hz`. Establish `hd : dg = a + dh` using `funext fun k => by`. Use `hdeg k` as an intermediate fact. Simplify using `only [ha, Nat.cast_one, one_mul] at this`. Simplify using `only [Pi.add_apply]`.

Use linear arithmetic over natural numbers and integers. Establish `hF : IsMultiHomog (g - chartMono (e.symm j) a * h) dg` using `isMultiHomog_sub hg (by rw [hd]; exact isMultiHomog_mul (isMultiHomog_chartMono _ a) hh)`. Establish `h0 : aeval y (g - chartMono (e.symm j) a * h) = 0`. Rewrite using `[map_sub, map_mul, he, sub_self]`. Establish `hz0` using `hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF h0)`.

Simplify using `only [map_sub, map_mul, sub_eq_zero] at hz0`. Rewrite using `[hz0, norm_mul, eval_chartMono, pow_one, mul_comm]`. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Take `⟨μ, hμ, hzμ⟩` from `chartMono_exponent (e.symm j) a`. Rewrite using `[← hzμ z]`.

Conclude with `hB z hz μ hμ`.
-/
theorem smallGen_of_monomialsBounded (y : (Σ k, ι k) → Ω) (A : HermLine ι) (a : K → ℕ)
    (ha : A.a = fun k => (a k : ℤ)) (hB : MonomialsBounded (mCoordIdeal y) A a) : SmallGen y A := by
  classical
  set e := Fintype.equivFin (∀ k, ι k) with he_def
  refine ⟨Fintype.card (∀ k, ι k), fun j => aeval y (chartMono (e.symm j) a), fun j => ?_, ?_, fun j => ?_⟩
  · intro c hc
    beta_reduce
    rw [aeval_chartMono, ← Finset.prod_mul_distrib]
    refine prod_mem fun k _ => ?_
    have hmem : y ⟨k, (e.symm j) k⟩ / y ⟨k, c k⟩ ∈ chartRingZ y c :=
      Algebra.subset_adjoin ⟨⟨k, (e.symm j) k⟩, rfl⟩
    convert pow_mem hmem (a k) using 1
    simp [ha, div_eq_mul_inv, zpow_neg, zpow_natCast, mul_pow, inv_pow]
  · intro c hc
    refine ⟨fun j => if e.symm j = c then 1 else 0, fun j => by beta_reduce; split_ifs <;> simp, ?_⟩
    rw [Fintype.sum_equiv e.symm _ (fun i => (if i = c then (1 : Ω) else 0) *
      (aeval y (chartMono i a) * ∏ k, y ⟨k, c k⟩ ^ (-A.a k))) (fun _ => rfl)]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [aeval_chartMono, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => by
      simp [ha, zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ (hc k))]
  · intro dg dh g h z hg hh hdeg he hz
    have hd : dg = a + dh := funext fun k => by
      have := hdeg k
      simp only [ha, Nat.cast_one, one_mul] at this
      simp only [Pi.add_apply]
      omega
    have hF : IsMultiHomog (g - chartMono (e.symm j) a * h) dg :=
      isMultiHomog_sub hg (by rw [hd]; exact isMultiHomog_mul (isMultiHomog_chartMono _ a) hh)
    have h0 : aeval y (g - chartMono (e.symm j) a * h) = 0 := by
      rw [map_sub, map_mul, he, sub_self]
    have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF h0)
    simp only [map_sub, map_mul, sub_eq_zero] at hz0
    rw [hz0, norm_mul, eval_chartMono, pow_one, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    obtain ⟨μ, hμ, hzμ⟩ := chartMono_exponent (e.symm j) a
    rw [← hzμ z]
    exact hB z hz μ hμ

end PerturbedMonomialBound

open PerturbedMonomialBound in

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D a A P0 q _ hV _ ha hP0 hsemi hmono _`. Establish `hBa : (HermLine.zcomb A (fsH ι) q 1).a = fun k => (q : ℤ) * a k + 1`. Use function extensionality and compare the values at `k`. Simplify using `[HermLine.zcomb, ha, fsH_a]`. Use `⟨hP0, ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `PerturbSemipos.proof K ι P0 (mCoordIdeal y) A q 1 hsemi (by positivity) zero_le_one`. Rewrite using `[hBa]`. Use `hDeg K ι Ω y D _ hV fun k => ?_` and prove the remaining obligations. Establish `: (0 : ℤ) ≤ (q : ℤ) * a k` using `by positivity`. Use linear arithmetic over natural numbers and integers.

Establish `h` using `smallGen_zcomb y A (smallGen_of_monomialsBounded y A a ha hmono) q 1`. Rewrite `h` using `[Nat.cast_one]`. Conclude with `h`.
-/
theorem PerturbMonomial.proof (hDeg : GenDegAmple.Statement) : PerturbMonomial.Statement := by
  intro K _ ι _ Ω _ y D a A P0 q _ hV _ ha hP0 hsemi hmono _
  have hBa : (HermLine.zcomb A (fsH ι) q 1).a = fun k => (q : ℤ) * a k + 1 := by
    funext k
    simp [HermLine.zcomb, ha, fsH_a]
  refine ⟨hP0, ?_, ?_, ?_⟩
  · exact PerturbSemipos.proof K ι P0 (mCoordIdeal y) A q 1 hsemi (by positivity) zero_le_one
  · rw [hBa]
    refine hDeg K ι Ω y D _ hV fun k => ?_
    have : (0 : ℤ) ≤ (q : ℤ) * a k := by positivity
    omega
  · have h := smallGen_zcomb y A (smallGen_of_monomialsBounded y A a ha hmono) q 1
    rw [Nat.cast_one] at h
    exact h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
