import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartQuot
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.MemMCoordIdealIffOfIsWeightedHomogeneous
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [Fintype ι] [DecidableEq ι] in

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp only [map_add, Subalgebra.coe_add, IntermediateField.coe_add, hp, hq]`. Consider the case `mul_X p v hp`. Simplify using `only [map_mul, Subalgebra.coe_mul, IntermediateField.coe_mul, hp]`.

Simplify using `[chartEval, chartRatio]`.
-/
theorem val_chartEval_eq_aeval_div (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℤ) :
    (((chartEval x c f : chartRing x c) : ratioField x) : AlgebraicClosure ℚ) =
      aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, Subalgebra.coe_add, IntermediateField.coe_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, Subalgebra.coe_mul, IntermediateField.coe_mul, hp]
    simp [chartEval, chartRatio]

omit [Fintype ι] [DecidableEq ι] in

/- English proof (translation)
Introduce and unpack `⟨a, ha⟩`. Rewrite `ha` using `[chartRing, Algebra.adjoin_range_eq_range_aeval]`. Take `⟨f, rfl⟩` from `ha`. Use `⟨f, Subtype.ext ?_⟩` and prove the remaining obligations. Establish `h : (chartRing x c).val.comp (chartEval x c) = aeval (chartRatio x c)` using `MvPolynomial.algHom_ext fun p ↦ by simp [chartEval]`.

Conclude with `AlgHom.congr_fun h f`.
-/
theorem chartEval_surjective (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    Function.Surjective (chartEval x c) := by
  rintro ⟨a, ha⟩
  rw [chartRing, Algebra.adjoin_range_eq_range_aeval] at ha
  obtain ⟨f, rfl⟩ := ha
  refine ⟨f, Subtype.ext ?_⟩
  have h : (chartRing x c).val.comp (chartEval x c) = aeval (chartRatio x c) :=
    MvPolynomial.algHom_ext fun p ↦ by simp [chartEval]
  exact AlgHom.congr_fun h f

omit [Fintype ι] [DecidableEq ι] in

/- English proof (translation)
Rewrite using `[RingHom.mem_ker, ← val_chartEval_eq_aeval_div]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h]`. Both sides reduce to the same expression.

Introduce `h`. Conclude with `Subtype.ext (Subtype.ext h)`.
-/
theorem mem_ker_chartEval_iff (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℤ) :
    f ∈ RingHom.ker (chartEval x c) ↔ aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f = 0 := by
  rw [RingHom.mem_ker, ← val_chartEval_eq_aeval_div]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    exact Subtype.ext (Subtype.ext h)

/- English proof (translation)
Establish `h : algebraMap ℤ Ω = Int.castRingHom Ω` using `Subsingleton.elim _ _`. Rewrite using `[aeval_def, aeval_def, h]`. Conclude with `eval₂_scale_of_isWeightedHomogeneous t w hg`.
-/
theorem aeval_blockScale_of_isWeightedHomogeneous {Ω : Type*} [Field Ω] [Algebra ℤ Ω] (t : ι → Ω) (w : Coord n → Ω)
    {g : MvPolynomial (Coord n) ℤ} {m : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g m) :
    aeval (fun p ↦ t p.1 * w p) g = (∏ k, t k ^ m k) * aeval w g := by
  have h : algebraMap ℤ Ω = Int.castRingHom Ω := Subsingleton.elim _ _
  rw [aeval_def, aeval_def, h]
  exact eval₂_scale_of_isWeightedHomogeneous t w hg

/- English proof (translation)
Use `set J := Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1) with hJ`. Use `set z : Coord n → AlgebraicClosure ℚ := fun p ↦ x p.1 p.2 / x p.1 (c p.1) with hz`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `f hf`. Rewrite `hf` using `[mem_ker_chartEval_iff]`.

Use `set N : ι → ℕ := fun k ↦ (compDegs f).sup fun m ↦ m k with hN`. Establish `hle : ∀ m ∈ compDegs f, m ≤ N` using `fun m hm k ↦ Finset.le_sup (f := fun m : ι → ℕ ↦ m k) hm`. Use `set F := ∑ m ∈ compDegs f, weightedHomogeneousComponent (coordDeg n) m f * chartMonomial c (N - m) with hF`. Establish `hFJ : f - F ∈ J`. Establish `h1 : ∀ d, Ideal.Quotient.mk J (chartMonomial c d) = 1`.

Introduce `d`. Rewrite using `[chartMonomial, map_prod]`. Use `Finset.prod_eq_one fun k _ ↦ ?_` and prove the remaining obligations. Establish `hk : Ideal.Quotient.mk J (X ⟨k, c k⟩) = 1`. Rewrite using `[← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]`.

Conclude with `Ideal.subset_span ⟨k, rfl⟩`. Rewrite using `[map_pow, hk, one_pow]`. Rewrite using `[← Ideal.Quotient.eq, hF, map_sum]`. Simplify using `only [map_mul, h1, mul_one]`. Use `conv_lhs => rw [← sum_compDegs f]`.

Rewrite using `[map_sum]`. Establish `hFP : F ∈ orbitIdeal x`. Establish `hhom : IsWeightedHomogeneous (coordDeg n) F N`. Establish `: F ∈ weightedHomogeneousSubmodule ℤ (coordDeg n) N`. Use `Submodule.sum_mem _ fun m hm ↦ ?_` and prove the remaining obligations.

Establish `h2` using `(weightedHomogeneousComponent_isWeightedHomogeneous m f).mul (isWeightedHomogeneous_chartMonomial c (N - m))`. Rewrite `h2` using `[add_tsub_cancel_of_le (hle m hm)]`. Then use the resulting hypothesis. Conclude with `this`. Rewrite using `[orbitIdeal, mem_mCoordIdeal_iff_of_isWeightedHomogeneous _ hhom]`. Establish `hy : flatCone x = fun p ↦ x p.1 (c p.1) * z p`.

Use function extensionality and compare the values at `p`. Simplify using `only [hz, flatCone]`. Rewrite using `[mul_div_cancel₀ _ (hc p.1)]`. Establish `hterm : ∀ m ∈ compDegs f, aeval (flatCone x) (weightedHomogeneousComponent (coordDeg n) m f * chartMonomial c (N - m)) = (∏ k, x k (c k) ^ N k) * aeval z (weightedHomogeneousComponent (coordDeg n) m f)`. Introduce `m hm`.

Establish `hs` using `aeval_blockScale_of_isWeightedHomogeneous (fun k ↦ x k (c k)) z (weightedHomogeneousComponent_isWeightedHomogeneous m f)`. Establish `hmon : aeval (flatCone x) (chartMonomial c (N - m)) = ∏ k, x k (c k) ^ (N k - m k)`. Simplify using `[chartMonomial, map_prod, flatCone]`. Establish `hpow : ∏ k, x k (c k) ^ N k = (∏ k, x k (c k) ^ m k) * ∏ k, x k (c k) ^ (N k - m k)`. Rewrite using `[← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[← pow_add, Nat.add_sub_cancel' (hle m hm k)]`. Rewrite using `[map_mul, hmon, hpow]`. Rewrite using `[hy]`. Rewrite using `[hs]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hF, map_sum]`. Use `(Finset.sum_congr rfl hterm).trans ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, ← map_sum, sum_compDegs, show aeval z f = 0 from hf, mul_zero]`. Establish `: f = F + (f - F)` using `by ring`.

Rewrite using `[this]`. Conclude with `Ideal.add_mem _ (Ideal.mem_sup_left hFP) (Ideal.mem_sup_right hFJ)`. Use `sup_le (fun f hf ↦ ?_) (Ideal.span_le.mpr ?_)` and prove the remaining obligations. Rewrite using `[mem_ker_chartEval_iff]`. Rewrite `hf` using `[orbitIdeal, mem_mCoordIdeal_iff]`.

Rewrite using `[← sum_compDegs f, map_sum]`. Use `Finset.sum_eq_zero fun m _ ↦ ?_` and prove the remaining obligations. Establish `hs` using `aeval_blockScale_of_isWeightedHomogeneous (fun k ↦ (x k (c k))⁻¹) (flatCone x) (weightedHomogeneousComponent_isWeightedHomogeneous m f)`. Establish `hz' : (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) = fun p ↦ (x p.1 (c p.1))⁻¹ * flatCone x p`. Use function extensionality and compare the values at `p`.

Rewrite using `[div_eq_inv_mul]`. Both sides reduce to the same expression. Rewrite using `[hz', hs]`. Use `mul_eq_zero_of_right _ ?_` and prove the remaining obligations. Establish `h0` using `hf m`.

Rewrite `h0`, the goal using `[aeval_def, Subsingleton.elim (algebraMap ℤ _) (Int.castRingHom _)]`. Conclude with `h0`. Introduce and unpack `_ ⟨k, rfl⟩`. Rewrite using `[SetLike.mem_coe, mem_ker_chartEval_iff]`. Simplify using `[div_self (hc k)]`.
-/
theorem ker_chartEval (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) :
    RingHom.ker (chartEval x c) = orbitIdeal x ⊔
      Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1) := by
  set J := Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1) with hJ
  set z : Coord n → AlgebraicClosure ℚ := fun p ↦ x p.1 p.2 / x p.1 (c p.1) with hz
  apply le_antisymm
  · intro f hf
    rw [mem_ker_chartEval_iff] at hf
    set N : ι → ℕ := fun k ↦ (compDegs f).sup fun m ↦ m k with hN
    have hle : ∀ m ∈ compDegs f, m ≤ N := fun m hm k ↦ Finset.le_sup (f := fun m : ι → ℕ ↦ m k) hm
    set F := ∑ m ∈ compDegs f,
      weightedHomogeneousComponent (coordDeg n) m f * chartMonomial c (N - m) with hF
    have hFJ : f - F ∈ J := by
      have h1 : ∀ d, Ideal.Quotient.mk J (chartMonomial c d) = 1 := by
        intro d
        rw [chartMonomial, map_prod]
        refine Finset.prod_eq_one fun k _ ↦ ?_
        have hk : Ideal.Quotient.mk J (X ⟨k, c k⟩) = 1 := by
          rw [← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
          exact Ideal.subset_span ⟨k, rfl⟩
        rw [map_pow, hk, one_pow]
      rw [← Ideal.Quotient.eq, hF, map_sum]
      simp only [map_mul, h1, mul_one]
      conv_lhs => rw [← sum_compDegs f]
      rw [map_sum]
    have hFP : F ∈ orbitIdeal x := by
      have hhom : IsWeightedHomogeneous (coordDeg n) F N := by
        have : F ∈ weightedHomogeneousSubmodule ℤ (coordDeg n) N := by
          refine Submodule.sum_mem _ fun m hm ↦ ?_
          have h2 := (weightedHomogeneousComponent_isWeightedHomogeneous m f).mul
            (isWeightedHomogeneous_chartMonomial c (N - m))
          rwa [add_tsub_cancel_of_le (hle m hm)] at h2
        exact this
      rw [orbitIdeal, mem_mCoordIdeal_iff_of_isWeightedHomogeneous _ hhom]
      have hy : flatCone x = fun p ↦ x p.1 (c p.1) * z p := by
        funext p
        simp only [hz, flatCone]
        rw [mul_div_cancel₀ _ (hc p.1)]
      have hterm : ∀ m ∈ compDegs f,
          aeval (flatCone x) (weightedHomogeneousComponent (coordDeg n) m f * chartMonomial c (N - m)) =
            (∏ k, x k (c k) ^ N k) * aeval z (weightedHomogeneousComponent (coordDeg n) m f) := by
        intro m hm
        have hs := aeval_blockScale_of_isWeightedHomogeneous (fun k ↦ x k (c k)) z
          (weightedHomogeneousComponent_isWeightedHomogeneous m f)
        have hmon : aeval (flatCone x) (chartMonomial c (N - m)) = ∏ k, x k (c k) ^ (N k - m k) := by
          simp [chartMonomial, map_prod, flatCone]
        have hpow : ∏ k, x k (c k) ^ N k = (∏ k, x k (c k) ^ m k) * ∏ k, x k (c k) ^ (N k - m k) := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun k _ ↦ ?_
          rw [← pow_add, Nat.add_sub_cancel' (hle m hm k)]
        rw [map_mul, hmon, hpow]
        rw [hy]
        rw [hs]
        ring
      rw [hF, map_sum]
      refine (Finset.sum_congr rfl hterm).trans ?_
      rw [← Finset.mul_sum, ← map_sum, sum_compDegs, show aeval z f = 0 from hf, mul_zero]
    have : f = F + (f - F) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hFP) (Ideal.mem_sup_right hFJ)
  · refine sup_le (fun f hf ↦ ?_) (Ideal.span_le.mpr ?_)
    · rw [mem_ker_chartEval_iff]
      rw [orbitIdeal, mem_mCoordIdeal_iff] at hf
      rw [← sum_compDegs f, map_sum]
      refine Finset.sum_eq_zero fun m _ ↦ ?_
      have hs := aeval_blockScale_of_isWeightedHomogeneous (fun k ↦ (x k (c k))⁻¹) (flatCone x)
        (weightedHomogeneousComponent_isWeightedHomogeneous m f)
      have hz' : (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) =
          fun p ↦ (x p.1 (c p.1))⁻¹ * flatCone x p := by
        funext p
        rw [div_eq_inv_mul]
        rfl
      rw [hz', hs]
      refine mul_eq_zero_of_right _ ?_
      have h0 := hf m
      rw [aeval_def, Subsingleton.elim (algebraMap ℤ _) (Int.castRingHom _)] at h0 ⊢
      exact h0
    · rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, mem_ker_chartEval_iff]
      simp [div_self (hc k)]

/- English proof (translation)
Introduce `ι _ _ n x c hc V hV`. Establish `hsurj` using `chartEval_surjective x c`. Set `g : MvPolynomial (Coord n) ℤ →+* chartRing x c ⧸ chartPoint x c V` to `(Ideal.Quotient.mk _).comp (chartEval x c : MvPolynomial (Coord n) ℤ →+* chartRing x c)`. Establish `hg : Function.Surjective g` using `Ideal.Quotient.mk_surjective.comp hsurj`. Establish `hker : RingHom.ker g = V ⊔ Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1)`.

Use extensionality with `f`. Rewrite using `[RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (chartEval x c f) = 0 ↔ _`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, chartPoint, Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, ker_chartEval x c hc, ← sup_assoc, sup_eq_left.mpr hV]`. Conclude with `⟨(RingHom.quotientKerEquivOfSurjective hg).symm.trans (Ideal.quotEquivOfEq hker)⟩`.
-/
theorem OrbitChartQuot.proof : OrbitChartQuot.Statement := by
  intro ι _ _ n x c hc V hV
  have hsurj := chartEval_surjective x c
  let g : MvPolynomial (Coord n) ℤ →+* chartRing x c ⧸ chartPoint x c V :=
    (Ideal.Quotient.mk _).comp (chartEval x c : MvPolynomial (Coord n) ℤ →+* chartRing x c)
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hsurj
  have hker : RingHom.ker g =
      V ⊔ Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1) := by
    ext f
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk _ (chartEval x c f) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, chartPoint,
      Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, ker_chartEval x c hc,
      ← sup_assoc, sup_eq_left.mpr hV]
  exact ⟨(RingHom.quotientKerEquivOfSurjective hg).symm.trans (Ideal.quotEquivOfEq hker)⟩

/- English proof (translation)
The claim follows from `OrbitChartQuot.proof Unit _ samplePoint _ (fun _ ↦ by simp [samplePoint]) _ le_rfl`.
-/
example : Nonempty ((chartRing samplePoint (fun _ ↦ 0) ⧸
      chartPoint samplePoint (fun _ ↦ 0) (orbitIdeal samplePoint)) ≃+*
    (MvPolynomial (Coord (fun _ : Unit ↦ 1)) ℤ ⧸ (orbitIdeal samplePoint ⊔
      Ideal.span (Set.range fun k ↦ (X ⟨k, 0⟩ : MvPolynomial (Coord (fun _ : Unit ↦ 1)) ℤ) - 1)))) :=
  OrbitChartQuot.proof Unit _ samplePoint _ (fun _ ↦ by simp [samplePoint]) _ le_rfl

end

end GroundTheory.Heights₂.Heights
