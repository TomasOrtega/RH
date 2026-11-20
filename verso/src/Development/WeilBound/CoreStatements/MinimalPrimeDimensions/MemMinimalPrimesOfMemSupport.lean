import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Assembly
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMeetNull

set_option autoImplicit false

noncomputable section

open MvPolynomial MeasureTheory GroundTheory.Heights₂.Heights

namespace ChowFormHeightComparison₂.CF.C

variable {n : ℕ}

/- English proof (translation)
Establish `hu : IsUnit (Matrix.transpose h.mat)`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]`. Conclude with `h.isUnit_det`. Establish `h0 : (fun i => y i) = 0` using `Matrix.mulVec_injective_iff_isUnit.mpr hu (by rw [Matrix.mulVec_zero]; exact hy)`. Use extensionality with `i`.

Simplify using `using congrFun h0 i`.
-/
theorem eq_zero_of_pointOf_eq_zero (h : HermNorm n) {y : EuclideanSpace ℂ (Fin n)}
    (hy : h.pointOf y = 0) : y = 0 := by
  have hu : IsUnit (Matrix.transpose h.mat) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]; exact h.isUnit_det
  have h0 : (fun i => y i) = 0 :=
    Matrix.mulVec_injective_iff_isUnit.mpr hu (by rw [Matrix.mulVec_zero]; exact hy)
  ext i
  simpa using congrFun h0 i

/- English proof (translation)
Introduce and unpack `y ⟨hy1, hyJ⟩`. Establish `: (RingHom.ker (eval (h.pointOf y))).IsPrime` using `RingHom.ker_isPrime _`. Take `⟨W, hWmin, hWle⟩` from `Ideal.exists_minimalPrimes_le (fun q hq => (RingHom.mem_ker).2 (hyJ q hq) : J ≤ RingHom.ker (eval (h.pointOf y)))`. Distinguish the cases in `hrel : IsRelevant W`. Use `right`.

Establish `hmem : W ∈ (fundCycle J).support`. Rewrite using `[Finsupp.mem_support_iff]`. Unfold `fundCycle`. Rewrite using `[Finsupp.onFinset_apply, if_pos ⟨hWmin, hrel⟩, localMult_eq_one_of_isRadical hJ hWmin]`. Conclude with `one_ne_zero`.

Conclude with `Set.mem_biUnion hmem ⟨hy1, fun q hq => (RingHom.mem_ker).1 (hWle hq)⟩`. Use `left`. Use `eq_zero_of_pointOf_eq_zero h (funext fun j => ?_)` and prove the remaining obligations. Establish `hX : X j ∈ W`. Assume the negation of the conclusion as `hj`.

Conclude with `hrel ⟨j, hj⟩`. Simplify using `using (RingHom.mem_ker).1 (hWle hX)`.
-/
theorem coneBall_subset (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsRadical) :
    coneBall h J ⊆ {0} ∪ ⋃ W ∈ (fundCycle J).support, coneBall h W := by
  classical
  rintro y ⟨hy1, hyJ⟩
  have : (RingHom.ker (eval (h.pointOf y))).IsPrime := RingHom.ker_isPrime _
  obtain ⟨W, hWmin, hWle⟩ := Ideal.exists_minimalPrimes_le
    (fun q hq => (RingHom.mem_ker).2 (hyJ q hq) : J ≤ RingHom.ker (eval (h.pointOf y)))
  by_cases hrel : IsRelevant W
  · right
    have hmem : W ∈ (fundCycle J).support := by
      rw [Finsupp.mem_support_iff]
      unfold fundCycle
      rw [Finsupp.onFinset_apply, if_pos ⟨hWmin, hrel⟩, localMult_eq_one_of_isRadical hJ hWmin]
      exact one_ne_zero
    exact Set.mem_biUnion hmem ⟨hy1, fun q hq => (RingHom.mem_ker).1 (hWle hq)⟩
  · left
    refine eq_zero_of_pointOf_eq_zero h (funext fun j => ?_)
    have hX : X j ∈ W := by
      by_contra hj
      exact hrel ⟨j, hj⟩
    simpa using (RingHom.mem_ker).1 (hWle hX)

/- English proof (translation)
Rewrite using `[show ((2 * (e + 1) : ℕ) : ℝ) = (((2 * (e + 1) : ℕ) : NNReal) : ℝ) from (NNReal.coe_natCast _).symm]`. Use `hausdorffMeasure_of_dimH_lt ?_` and prove the remaining obligations. Rewrite using `[dimH_singleton, ENNReal.coe_natCast]`. Conclude with `(by omega : 0 < 2 * (e + 1))` after adjusting the coercions.
-/
theorem hausdorffMeasure_zero (e : ℕ) :
    Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) ({0} : Set (EuclideanSpace ℂ (Fin n))) = 0 := by
  rw [show ((2 * (e + 1) : ℕ) : ℝ) = (((2 * (e + 1) : ℕ) : NNReal) : ℝ) from
    (NNReal.coe_natCast _).symm]
  refine hausdorffMeasure_of_dimH_lt ?_
  rw [dimH_singleton, ENNReal.coe_natCast]
  exact_mod_cast (by omega : 0 < 2 * (e + 1))

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a t ha ih`. Establish `hs' : ∀ i ∈ t, MeasurableSet (s i)` using `fun i hi => hs i (Finset.mem_insert_of_mem hi)`. Establish `hf' : ∀ i ∈ t, IntegrableOn f (s i) μ` using `fun i hi => hf i (Finset.mem_insert_of_mem hi)`.

Establish `hdis : AEDisjoint μ (s a) (⋃ i ∈ t, s i)`. Express the relevant statement in the definitionally equal form `μ (s a ∩ ⋃ i ∈ t, s i) = 0`. Rewrite using `[Set.inter_iUnion₂]`. Use `(measure_biUnion_null_iff t.countable_toSet).2 fun i hi => ?_` and prove the remaining obligations. Conclude with `hd a (Finset.mem_insert_self a t) i (Finset.mem_insert_of_mem hi) (fun hai => ha (hai ▸ hi))`.

Rewrite using `[Finset.set_biUnion_insert, Finset.sum_insert ha, setIntegral_union₀ hdis (Finset.measurableSet_biUnion t hs').nullMeasurableSet (hf a (Finset.mem_insert_self a t)) (integrableOn_finset_iUnion.2 hf'), ih hs' (fun i hi j hj => hd i (Finset.mem_insert_of_mem hi) j (Finset.mem_inser …`.
-/
theorem setIntegral_finset_biUnion_ae {ι X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    (t : Finset ι) {s : ι → Set X} (hs : ∀ i ∈ t, MeasurableSet (s i))
    (hd : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → μ (s i ∩ s j) = 0) (hf : ∀ i ∈ t, IntegrableOn f (s i) μ) :
    ∫ x in ⋃ i ∈ t, s i, f x ∂μ = ∑ i ∈ t, ∫ x in s i, f x ∂μ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    have hs' : ∀ i ∈ t, MeasurableSet (s i) := fun i hi => hs i (Finset.mem_insert_of_mem hi)
    have hf' : ∀ i ∈ t, IntegrableOn f (s i) μ := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hdis : AEDisjoint μ (s a) (⋃ i ∈ t, s i) := by
      change μ (s a ∩ ⋃ i ∈ t, s i) = 0
      rw [Set.inter_iUnion₂]
      refine (measure_biUnion_null_iff t.countable_toSet).2 fun i hi => ?_
      exact hd a (Finset.mem_insert_self a t) i (Finset.mem_insert_of_mem hi)
        (fun hai => ha (hai ▸ hi))
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha,
      setIntegral_union₀ hdis (Finset.measurableSet_biUnion t hs').nullMeasurableSet
        (hf a (Finset.mem_insert_self a t)) (integrableOn_finset_iUnion.2 hf'),
      ih hs' (fun i hi j hj => hd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)) hf']

/- English proof (translation)
Establish `h` using `Finsupp.support_onFinset_subset hW`. Rewrite `h` using `[Set.Finite.mem_toFinset]`. Then use the resulting hypothesis.
-/
theorem mem_minimalPrimes_of_mem_support {J W : Ideal (MvPolynomial (Fin n) ℂ)}
    (hW : W ∈ (fundCycle J).support) : W ∈ J.minimalPrimes := by
  have h := Finsupp.support_onFinset_subset hW
  rwa [Set.Finite.mem_toFinset] at h

/- English proof (translation)
Establish `hp` using `hI.isPrime`. Establish `hDim : ConeDimOfChowForm.Statement` using `ConeDimOfChowForm.proof IncIdealDim.full IncIdealPrime.full`. Establish `hrad : (I.map (MvPolynomial.map σ)).IsRadical` using `RadicalBaseChange.proof K ℂ σ _ I hp.isRadical`. Take `⟨hproj, c, -, g, hg, -⟩` from `ChowFormBaseChange.full K n (e + 1) I f σ hI hf`. Establish `hav` using `BaseChangeAvoid.full K n I u σ hI hu`.

Use `set J := I.map (MvPolynomial.map σ) with hJ`. Use `set S := (fundCycle J).support with hS`. Use `set μ := Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (X := EuclideanSpace ℂ (Fin n)) with hμ`. Establish `hdimW : ∀ W ∈ S, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ ((e + 1 : ℕ) : WithBot ℕ∞)` using `fun W hW => (hDim ℂ n (e + 1) W (g W) (hproj W hW) (hg W hW)).le`. Establish `hJW : ∀ W ∈ S, J ≤ W` using `fun W hW => (mem_minimalPrimes_of_mem_support hW).1.2`.

Establish `hae : coneBall h J =ᵐ[μ] ⋃ W ∈ S, coneBall h W`. Use `ae_eq_set.2 ⟨measure_mono_null (fun y hy => ?_) (hausdorffMeasure_zero e), ?_⟩` and prove the remaining obligations. Break down `coneBall_subset h hrad hy.1 with h0 | h1` into its components or cases. Conclude with `h0`. Conclude with `absurd h1 hy.2`.

Establish `hsub : (⋃ W ∈ S, coneBall h W) ⊆ coneBall h J` using `Set.iUnion₂_subset fun W hW y (hy : y ∈ coneBall h W) => (⟨hy.1, fun q hq => hy.2 q (hJW W hW hq)⟩ : y ∈ coneBall h J)`. Rewrite using `[Set.sdiff_eq_empty.2 hsub, measure_empty]`. Establish `hint : ∀ W ∈ S, IntegrableOn (fun y => fsLog h (fun k => σ (u k)) (h.pointOf y)) (coneBall h W) μ` using `fun W hW => ConeFsLogIntegrable.full n e h W (g W) _ (hproj W hW) (hg W hW) (hav W hW)`. Establish `key` using `setIntegral_finset_biUnion_ae (μ := μ) (f := fun y => fsLog h (fun k => σ (u k)) (h.pointOf y)) S (fun W _ => measurableSet_coneBall h W) (fun W hW W' hW' hne => ConeMeetNull.proof ZeroLocusDimH.proof n e h W W' (hproj W hW).isPrime (hproj W' hW').isPrime hne (hdimW W hW) (hdimW …`. Use `⟨?_, ?_, ?_, fun q hq => ?_⟩` and prove the remaining obligations.

Establish `h1` using `(hDim K n (e + 1) I f hI hf).ge.trans (ringKrullDim_quotient_le I)`. Rewrite `h1` using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]`. Simplify using `only [Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h1`. Conclude with `h1` after adjusting the coercions. Conclude with `(integrableOn_finset_iUnion.2 hint).congr_set_ae hae`.

Unfold `cycleIntegral`. Rewrite using `[Finset.sum_congr rfl fun W hW => by rw [fundCycle_apply_of_isRadical hrad hW, Nat.cast_one, one_mul]]`. Unfold `coneIntegral`. Rewrite using `[← Finset.sum_div]`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `∑ W ∈ S, ∫ y in coneBall h W, fsLog h (fun k => σ (u k)) (h.pointOf y) ∂μ = ∫ y in coneBall h J, fsLog h (fun k => σ (u k)) (h.pointOf y) ∂μ`. Rewrite using `[setIntegral_congr_set hae, key]`. Establish `hsub : coneBall h J ∩ {y | eval (h.pointOf y) (MvPolynomial.map σ q) = 0} ⊆ {0} ∪ ⋃ W ∈ S, coneBall h W ∩ coneBall h (Ideal.span {MvPolynomial.map σ q})`. Introduce and unpack `y ⟨hy, hyq⟩`. Break down `coneBall_subset h hrad hy with h0 | h1` into its components or cases.

Conclude with `Or.inl h0`. Take `⟨W, hW, hyW⟩` from `Set.mem_iUnion₂.1 h1`. Use `Or.inr (Set.mem_iUnion₂.2 ⟨W, hW, hyW, hy.1, fun r hr => ?_⟩)` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 hr`. Rewrite using `[map_mul, show eval (h.pointOf y) (MvPolynomial.map σ q) = 0 from hyq, mul_zero]`.

Use `measure_mono_null hsub (measure_union_null (hausdorffMeasure_zero e) ((measure_biUnion_null_iff S.countable_toSet).2 fun W hW => ?_))` and prove the remaining obligations. Use `(hproj W hW).isPrime` as an intermediate fact. Use `ConeMeetNull.null_of_mem_not_mem ZeroLocusDimH.proof h W _ (hdimW W hW) _ (Ideal.mem_span_singleton_self _) fun hqW => hq ?_` and prove the remaining obligations. Rewrite using `[← BaseChangeAvoid.comap_eq_of_mem_minimalPrimes σ I (mem_minimalPrimes_of_mem_support hW)]`. Conclude with `hqW`.
-/
theorem cone_side {K : Type} [Field K] [NumberField K] {e : ℕ} {I : Ideal (MvPolynomial (Fin n) K)}
    (hI : IsProjPrime I) {f : MvPolynomial (Fin (e + 1) × Fin n) K} (hf : IsChowForm I (e + 1) f) (σ : K →+* ℂ)
    (h : HermNorm n) {u : Fin n → K} (hu : linForm u ∉ I) :
    e + 1 ≤ n ∧
    IntegrableOn (fun y => fsLog h (fun k => σ (u k)) (h.pointOf y)) (coneBall h (I.map (MvPolynomial.map σ)))
      (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) ∧
    cycleIntegral h (fundCycle (I.map (MvPolynomial.map σ))) e (fsLog h fun k => σ (u k)) =
      coneIntegral h (I.map (MvPolynomial.map σ)) e (fsLog h fun k => σ (u k)) ∧
    ∀ q : MvPolynomial (Fin n) K, q ∉ I → Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
      (coneBall h (I.map (MvPolynomial.map σ)) ∩ {y | eval (h.pointOf y) (MvPolynomial.map σ q) = 0}) = 0 := by
  classical
  have hp := hI.isPrime
  have hDim : ConeDimOfChowForm.Statement := ConeDimOfChowForm.proof IncIdealDim.full IncIdealPrime.full
  have hrad : (I.map (MvPolynomial.map σ)).IsRadical := RadicalBaseChange.proof K ℂ σ _ I hp.isRadical
  obtain ⟨hproj, c, -, g, hg, -⟩ := ChowFormBaseChange.full K n (e + 1) I f σ hI hf
  have hav := BaseChangeAvoid.full K n I u σ hI hu
  set J := I.map (MvPolynomial.map σ) with hJ
  set S := (fundCycle J).support with hS
  set μ := Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (X := EuclideanSpace ℂ (Fin n)) with hμ
  have hdimW : ∀ W ∈ S, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) :=
    fun W hW => (hDim ℂ n (e + 1) W (g W) (hproj W hW) (hg W hW)).le
  have hJW : ∀ W ∈ S, J ≤ W := fun W hW => (mem_minimalPrimes_of_mem_support hW).1.2
  have hae : coneBall h J =ᵐ[μ] ⋃ W ∈ S, coneBall h W := by
    refine ae_eq_set.2 ⟨measure_mono_null (fun y hy => ?_) (hausdorffMeasure_zero e), ?_⟩
    · rcases coneBall_subset h hrad hy.1 with h0 | h1
      · exact h0
      · exact absurd h1 hy.2
    · have hsub : (⋃ W ∈ S, coneBall h W) ⊆ coneBall h J :=
        Set.iUnion₂_subset fun W hW y (hy : y ∈ coneBall h W) =>
          (⟨hy.1, fun q hq => hy.2 q (hJW W hW hq)⟩ : y ∈ coneBall h J)
      rw [Set.sdiff_eq_empty.2 hsub, measure_empty]
  have hint : ∀ W ∈ S, IntegrableOn (fun y => fsLog h (fun k => σ (u k)) (h.pointOf y)) (coneBall h W) μ :=
    fun W hW => ConeFsLogIntegrable.full n e h W (g W) _ (hproj W hW) (hg W hW) (hav W hW)
  have key := setIntegral_finset_biUnion_ae (μ := μ) (f := fun y => fsLog h (fun k => σ (u k)) (h.pointOf y)) S
    (fun W _ => measurableSet_coneBall h W)
    (fun W hW W' hW' hne => ConeMeetNull.proof ZeroLocusDimH.proof n e h W W' (hproj W hW).isPrime
      (hproj W' hW').isPrime hne (hdimW W hW) (hdimW W' hW')) hint
  refine ⟨?_, ?_, ?_, fun q hq => ?_⟩
  · have h1 := (hDim K n (e + 1) I f hI hf).ge.trans (ringKrullDim_quotient_le I)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h1
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h1
    exact_mod_cast h1
  · exact (integrableOn_finset_iUnion.2 hint).congr_set_ae hae
  · unfold cycleIntegral
    rw [Finset.sum_congr rfl fun W hW => by rw [fundCycle_apply_of_isRadical hrad hW, Nat.cast_one, one_mul]]
    unfold coneIntegral
    rw [← Finset.sum_div]
    congr 1
    change ∑ W ∈ S, ∫ y in coneBall h W, fsLog h (fun k => σ (u k)) (h.pointOf y) ∂μ =
      ∫ y in coneBall h J, fsLog h (fun k => σ (u k)) (h.pointOf y) ∂μ
    rw [setIntegral_congr_set hae, key]
  · have hsub : coneBall h J ∩ {y | eval (h.pointOf y) (MvPolynomial.map σ q) = 0} ⊆
        {0} ∪ ⋃ W ∈ S, coneBall h W ∩ coneBall h (Ideal.span {MvPolynomial.map σ q}) := by
      rintro y ⟨hy, hyq⟩
      rcases coneBall_subset h hrad hy with h0 | h1
      · exact Or.inl h0
      · obtain ⟨W, hW, hyW⟩ := Set.mem_iUnion₂.1 h1
        refine Or.inr (Set.mem_iUnion₂.2 ⟨W, hW, hyW, hy.1, fun r hr => ?_⟩)
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
        rw [map_mul, show eval (h.pointOf y) (MvPolynomial.map σ q) = 0 from hyq, mul_zero]
    refine measure_mono_null hsub (measure_union_null (hausdorffMeasure_zero e)
      ((measure_biUnion_null_iff S.countable_toSet).2 fun W hW => ?_))
    have := (hproj W hW).isPrime
    refine ConeMeetNull.null_of_mem_not_mem ZeroLocusDimH.proof h W _ (hdimW W hW) _
      (Ideal.mem_span_singleton_self _) fun hqW => hq ?_
    rw [← BaseChangeAvoid.comap_eq_of_mem_minimalPrimes σ I (mem_minimalPrimes_of_mem_support hW)]
    exact hqW

end ChowFormHeightComparison₂.CF.C
