import ReciprocityTheory.SemistableReduction.AeBlockSphereEvalNeZero
import ReciprocityTheory.SemistableReduction.GaussAbsMulOfMonomialOrder

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory NumberField

/- English proof (translation)
Establish `hfin : (⋃ s ∈ f.support, Function.mulSupport fun w : FinitePlace K => w (f.coeff s)).Finite` using `Set.Finite.biUnion f.support.finite_toSet fun s hs => FinitePlace.hasFiniteMulSupport (MvPolynomial.mem_support_iff.1 hs)`. Use `hfin.subset fun w hw => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hnot`. Apply `hw` to reduce the goal to its premises. Simplify using `only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at hnot`.

Establish `h1 : gaussAbs w f = 1`. Apply `le_antisymm` to reduce the goal to its premises. Use `gauss_abs_le_of_coeff_le w f zero_le_one fun s => ?_` and prove the remaining obligations. Distinguish the cases in `hs : s ∈ f.support`. Conclude with `(hnot s hs).le`.

Rewrite using `[MvPolynomial.notMem_support_iff.1 hs, map_zero]`. Conclude with `zero_le_one`. Take `⟨s, hs, h⟩` from `gauss_abs_attained_at_coeff w f hf`. Rewrite using `[h, hnot s hs]`. Simplify using `[h1]`.
-/
theorem gauss_abs_log_support_finite {K : Type*} [Field K] [NumberField K] {σ : Type*}
    (f : MvPolynomial σ K) (hf : f ≠ 0) :
    (Function.support fun w : FinitePlace K => Real.log (gaussAbs w f)).Finite := by
  have hfin : (⋃ s ∈ f.support, Function.mulSupport fun w : FinitePlace K => w (f.coeff s)).Finite :=
    Set.Finite.biUnion f.support.finite_toSet fun s hs =>
      FinitePlace.hasFiniteMulSupport (MvPolynomial.mem_support_iff.1 hs)
  refine hfin.subset fun w hw => ?_
  by_contra hnot
  apply hw
  simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at hnot
  have h1 : gaussAbs w f = 1 := by
    apply le_antisymm
    · refine gauss_abs_le_of_coeff_le w f zero_le_one fun s => ?_
      by_cases hs : s ∈ f.support
      · exact (hnot s hs).le
      · rw [MvPolynomial.notMem_support_iff.1 hs, map_zero]
        exact zero_le_one
    · obtain ⟨s, hs, h⟩ := gauss_abs_attained_at_coeff w f hf
      rw [h, hnot s hs]
  simp [h1]

/- English proof (translation)
Unfold `IsMultiHomogeneous at hf ⊢`. Use `first`. Consider the case `exact fun d hd => hf d (by rwa [MvPolynomial.support_map_of_injective _ φ.injective] at hd)`. Consider the case `exact fun b => (hf b).map φ`. Consider the case `simpa [MvPolynomial.support_map_of_injective _ φ.injective] using hf`.

Consider the case `(intro d hd`. Simplify using `only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map, ne_eq, map_eq_zero] at hd`. Conclude with `hf d (by simpa using hd))`.
-/
theorem isMultiHomogeneous_map_ring {K : Type*} [Field K] {B n : ℕ} (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) K) (hf : IsMultiHomogeneous a f) (φ : K →+* ℂ) :
    IsMultiHomogeneous a (MvPolynomial.map φ f) := by
  unfold IsMultiHomogeneous at hf ⊢
  first
  | exact fun d hd => hf d (by rwa [MvPolynomial.support_map_of_injective _ φ.injective] at hd)
  | exact fun b => (hf b).map φ
  | simpa [MvPolynomial.support_map_of_injective _ φ.injective] using hf
  | (intro d hd
     simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map, ne_eq, map_eq_zero] at hd
     exact hf d (by simpa using hd))

/- English proof (translation)
Unfold `blockSphereMean`. Rewrite using `[← integral_add (hInt B n a F hF0 hF) (hInt B n a' G hG0 hG)]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_blockSphere_eval_ne_zero B n a F hF0 hF, ae_blockSphere_eval_ne_zero B n a' G hG0 hG] with z hz1 hz2`. Rewrite using `[map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hz1) (norm_ne_zero_iff.2 hz2)]`.
-/
theorem sphere_mean_mul_multihomogeneous (hInt : SphereLogIntegrableStatement) (B n : ℕ) (a a' : Fin B → ℕ)
    (F G : MvPolynomial (Fin B × Fin n) ℂ) (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (hF : IsMultiHomogeneous a F) (hG : IsMultiHomogeneous a' G) :
    blockSphereMean B n (F * G) = blockSphereMean B n F + blockSphereMean B n G := by
  unfold blockSphereMean
  rw [← integral_add (hInt B n a F hF0 hF) (hInt B n a' G hG0 hG)]
  refine integral_congr_ae ?_
  filter_upwards [ae_blockSphere_eval_ne_zero B n a F hF0 hF, ae_blockSphere_eval_ne_zero B n a' G hG0 hG]
    with z hz1 hz2
  rw [map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hz1) (norm_ne_zero_iff.2 hz2)]

/- English proof (translation)
Unfold `h0`. Establish `hfin : ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w (f * g)) = ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w f) + ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w g)`. Rewrite using `[← finsum_add_distrib (gauss_abs_log_support_finite f hf) (gauss_abs_log_support_finite g hg)]`. Use `finsum_congr fun w => ?_` and prove the remaining obligations. Rewrite using `[gauss_abs_mul w f g hf hg, Real.log_mul (gauss_abs_pos_of_ne_zero w f hf).ne' (gauss_abs_pos_of_ne_zero w g hg).ne']`.

Establish `hinf : ∑ φ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map φ (f * g)) = ∑ φ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map φ f) + ∑ φ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map φ g)`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun φ _ => ?_` and prove the remaining obligations. Establish `hinj` using `MvPolynomial.map_injective φ φ.injective (σ := Fin B × Fin n)`. Rewrite using `[map_mul]`.

Conclude with `sphere_mean_mul_multihomogeneous hInt B n a a' _ _ (fun h => hf (hinj (by rw [h, map_zero]))) (fun h => hg (hinj (by rw [h, map_zero]))) (isMultiHomogeneous_map_ring a f haf φ) (isMultiHomogeneous_map_ring a' g hbg φ)`. Rewrite using `[hfin, hinf]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gauss_height_mul_multihomogeneous (hInt : SphereLogIntegrableStatement) {K : Type*} [Field K] [NumberField K]
    (B n : ℕ) (a a' : Fin B → ℕ) (f g : MvPolynomial (Fin B × Fin n) K) (hf : f ≠ 0) (hg : g ≠ 0)
    (haf : IsMultiHomogeneous a f) (hbg : IsMultiHomogeneous a' g) :
    h0 (f * g) = h0 f + h0 g := by
  unfold h0
  have hfin : ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w (f * g)) =
      ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w f) + ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w g) := by
    rw [← finsum_add_distrib (gauss_abs_log_support_finite f hf) (gauss_abs_log_support_finite g hg)]
    refine finsum_congr fun w => ?_
    rw [gauss_abs_mul w f g hf hg, Real.log_mul (gauss_abs_pos_of_ne_zero w f hf).ne'
      (gauss_abs_pos_of_ne_zero w g hg).ne']
  have hinf : ∑ φ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map φ (f * g)) =
      ∑ φ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map φ f) +
        ∑ φ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map φ g) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun φ _ => ?_
    have hinj := MvPolynomial.map_injective φ φ.injective (σ := Fin B × Fin n)
    rw [map_mul]
    exact sphere_mean_mul_multihomogeneous hInt B n a a' _ _
      (fun h => hf (hinj (by rw [h, map_zero])))
      (fun h => hg (hinj (by rw [h, map_zero])))
      (isMultiHomogeneous_map_ring a f haf φ) (isMultiHomogeneous_map_ring a' g hbg φ)
  rw [hfin, hinf]
  ring

/- English proof (translation)
Unfold `h0`. Establish `hG : ∀ w : FinitePlace K, gaussAbs w (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) = w c`. Introduce `w`. Apply `le_antisymm` to reduce the goal to its premises. Use `gauss_abs_le_of_coeff_le w _ (apply_nonneg w c) fun s => ?_` and prove the remaining obligations.

Rewrite using `[MvPolynomial.coeff_C]`. Use `split_ifs`. Conclude with `le_rfl`. Rewrite using `[map_zero]`. Conclude with `apply_nonneg w c`.

Use `coeff_le_gauss_abs w (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) 0` as an intermediate fact. Rewrite `this` using `[MvPolynomial.coeff_C, if_pos rfl]`. Then use the resulting hypothesis. Repeatedly rewrite using `[hG]`. Establish `hP : IsProbabilityMeasure (blockSphereProb B n)`. Establish `: NeZero n` using `⟨hn.ne'⟩`.

Establish `hne : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ 0`. Rewrite using `[Ne, Measure.measure_univ_eq_zero]`. Conclude with `Measure.toSphere_ne_zero _`. Establish `: IsProbabilityMeasure (sphereProb n)`. Unfold `sphereProb`.

Conclude with `ProbabilityTheory.cond_isProbabilityMeasure hne`. Unfold `blockSphereProb`. Use `infer_instance`. Establish `hM : ∀ φ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map φ (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K)) = Real.log ‖φ c‖`. Introduce `φ`.

Unfold `blockSphereMean`. Simplify using `[MvPolynomial.map_C, MvPolynomial.eval_C]`. Repeatedly rewrite using `[hM]`. Establish `hmul : (Function.mulSupport fun w : FinitePlace K => w c).Finite` using `FinitePlace.hasFiniteMulSupport hc`. Establish `h1 : ∑ᶠ w : FinitePlace K, Real.log (w c) = Real.log (∏ᶠ w : FinitePlace K, w c)`.

Rewrite using `[finsum_eq_sum_of_support_subset (s := hmul.toFinset), finprod_eq_prod_of_mulSupport_subset (s := hmul.toFinset) _ (by simp), Real.log_prod (fun w _ => (FinitePlace.pos_iff.2 hc).ne')]`. Introduce `w hw`. Simplify using `only [Set.Finite.coe_toFinset, Function.mem_mulSupport]`. Introduce `h1`. Apply `hw` to reduce the goal to its premises.

Simplify using `[h1]`. Establish `h2 : ∑ φ : K →+* ℂ, Real.log ‖φ c‖ = Real.log |Algebra.norm ℚ c|`. Rewrite using `[← Real.log_prod (fun φ _ => norm_ne_zero_iff.2 ((map_ne_zero φ).2 hc))]`. Use `congr 1`. Use `congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ c)` as an intermediate fact.

Rewrite `this` using `[norm_prod]`. Rewrite using `[Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => ‖φ c‖) (fun φ => ‖φ c‖) (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← this]`. Rewrite using `[eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]`. Rewrite using `[h1, h2, FinitePlace.prod_eq_inv_abs_norm hc]`. Use `push_cast`.

Rewrite using `[Real.log_inv, neg_add_cancel, zero_div]`.
-/
theorem gauss_height_const_eq_zero {K : Type*} [Field K] [NumberField K] (B n : ℕ) (hn : 0 < n) (c : K)
    (hc : c ≠ 0) : h0 (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) = 0 := by
  unfold h0

  have hG : ∀ w : FinitePlace K, gaussAbs w (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) = w c := by
    intro w
    apply le_antisymm
    · refine gauss_abs_le_of_coeff_le w _ (apply_nonneg w c) fun s => ?_
      rw [MvPolynomial.coeff_C]
      split_ifs
      · exact le_rfl
      · rw [map_zero]; exact apply_nonneg w c
    · have := coeff_le_gauss_abs w (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) 0
      rwa [MvPolynomial.coeff_C, if_pos rfl] at this
  simp_rw [hG]

  have hP : IsProbabilityMeasure (blockSphereProb B n) := by
    have : NeZero n := ⟨hn.ne'⟩
    have hne : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ 0 := by
      rw [Ne, Measure.measure_univ_eq_zero]
      exact Measure.toSphere_ne_zero _
    have : IsProbabilityMeasure (sphereProb n) := by
      unfold sphereProb
      exact ProbabilityTheory.cond_isProbabilityMeasure hne
    unfold blockSphereProb
    infer_instance
  have hM : ∀ φ : K →+* ℂ, blockSphereMean B n
      (MvPolynomial.map φ (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K)) = Real.log ‖φ c‖ := by
    intro φ
    unfold blockSphereMean
    simp [MvPolynomial.map_C, MvPolynomial.eval_C]
  simp_rw [hM]

  have hmul : (Function.mulSupport fun w : FinitePlace K => w c).Finite :=
    FinitePlace.hasFiniteMulSupport hc
  have h1 : ∑ᶠ w : FinitePlace K, Real.log (w c) = Real.log (∏ᶠ w : FinitePlace K, w c) := by
    rw [finsum_eq_sum_of_support_subset (s := hmul.toFinset),
      finprod_eq_prod_of_mulSupport_subset (s := hmul.toFinset) _ (by simp),
      Real.log_prod (fun w _ => (FinitePlace.pos_iff.2 hc).ne')]
    intro w hw
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hw
    simp [h1]
  have h2 : ∑ φ : K →+* ℂ, Real.log ‖φ c‖ = Real.log |Algebra.norm ℚ c| := by
    rw [← Real.log_prod (fun φ _ => norm_ne_zero_iff.2 ((map_ne_zero φ).2 hc))]
    congr 1
    have := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ c)
    rw [norm_prod] at this
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => ‖φ c‖) (fun φ => ‖φ c‖)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← this]
    rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2, FinitePlace.prod_eq_inv_abs_norm hc]
  push_cast
  rw [Real.log_inv, neg_add_cancel, zero_div]

/- English proof (translation)
Introduce `K _ _ B n a a' f g hn hf hg haf hbg`. Use `⟨gauss_height_mul_multihomogeneous hInt B n a a' f g hf hg haf hbg, fun c hc => ?_⟩` and prove the remaining obligations. Establish `hC : IsMultiHomogeneous (fun _ : Fin B => 0) (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K)`. Introduce `s hs b`. Rewrite `hs` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_C]`.

Use `split_ifs at hs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Conclude with `absurd rfl hs`. Establish `hC0 : (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) ≠ 0`.

Rewrite using `[Ne, MvPolynomial.C_eq_zero]` and apply the resulting hypothesis. Rewrite using `[gauss_height_mul_multihomogeneous hInt B n _ a _ f hC0 hf hC haf, gauss_height_const_eq_zero B n hn c hc, zero_add]`.
-/
theorem gauss_height_add_of_sphere (hInt : SphereLogIntegrableStatement) : HeightAdditiveStatement := by
  intro K _ _ B n a a' f g hn hf hg haf hbg
  refine ⟨gauss_height_mul_multihomogeneous hInt B n a a' f g hf hg haf hbg, fun c hc => ?_⟩
  have hC : IsMultiHomogeneous (fun _ : Fin B => 0) (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) := by
    intro s hs b
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hs
    split_ifs at hs with h
    · subst h; simp
    · exact absurd rfl hs
  have hC0 : (MvPolynomial.C c : MvPolynomial (Fin B × Fin n) K) ≠ 0 := by
    rwa [Ne, MvPolynomial.C_eq_zero]
  rw [gauss_height_mul_multihomogeneous hInt B n _ a _ f hC0 hf hC haf, gauss_height_const_eq_zero B n hn c hc, zero_add]

end ReciprocityTheory.MultiplicativeHeights
