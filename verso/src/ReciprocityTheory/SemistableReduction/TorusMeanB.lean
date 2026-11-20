import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
import ReciprocityTheory.SemistableReduction.TorusMeanA

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Real Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev unitIntervalMeasure : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)

instance isProbabilityMeasure_torusProb (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (torusProb ι) := by
  unfold torusProb; infer_instance

def tmUpd (i : ι) : (ι → ℝ) × ℝ → (ι → ℝ) := fun p => update p.1 i p.2

/- English proof (translation)
Use `first`. Consider the case `exact measurable_update' (a := i)`. Consider the case `exact measurable_pi_iff.mpr fun j => by`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality.

Simplify `measurable_snd` using `[tmUpd]`. Simplify `(measurable_pi_apply j).comp measurable_fst` using `[tmUpd, Function.update_of_ne h]`.
-/
lemma measurable_tmUpd (i : ι) : Measurable (tmUpd i) := by
  first
  | exact measurable_update' (a := i)
  | exact measurable_pi_iff.mpr fun j => by
      by_cases h : j = i
      · subst h; simpa [tmUpd] using measurable_snd
      · simpa [tmUpd, Function.update_of_ne h] using (measurable_pi_apply j).comp measurable_fst

/- English proof (translation)
Use extensionality with `⟨θ, t⟩`. Simplify using `only [Set.mem_preimage, tmUpd, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun j => ?_, by simpa using h i⟩` and prove the remaining obligations.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify `h j` using `[hj]`. Introduce and unpack `⟨h1, h2⟩ j`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `using h2`. Simplify `h1 j` using `[hj]`.
-/
lemma tmUpd_preimage_pi (i : ι) (s : ι → Set ℝ) :
    tmUpd i ⁻¹' (Set.univ.pi s) = (Set.univ.pi (update s i Set.univ)) ×ˢ s i := by
  ext ⟨θ, t⟩
  simp only [Set.mem_preimage, tmUpd, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
  constructor
  · intro h
    refine ⟨fun j => ?_, by simpa using h i⟩
    by_cases hj : j = i
    · subst hj; simp
    · simpa [hj] using h j
  · rintro ⟨h1, h2⟩ j
    by_cases hj : j = i
    · subst hj; simpa using h2
    · simpa [hj] using h1 j

/- English proof (translation)
Use `⟨measurable_tmUpd i, ?_⟩` and prove the remaining obligations. Establish `h1 : (volume.restrict (Set.Ioc (0 : ℝ) 1)) Set.univ = 1` using `by simp`. Unfold `torusProb`. Use `(Measure.pi_eq fun s hs => ?_).symm` and prove the remaining obligations. Rewrite using `[Measure.map_apply (measurable_tmUpd i) (MeasurableSet.univ_pi hs), tmUpd_preimage_pi, Measure.prod_prod, Measure.pi_pi, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), ← Finset.mul_prod_erase Finset.univ (fun j => volume.restrict (Set.Ioc (0 : ℝ) 1) (s j)) (Finset.mem …`.

Establish `hp : ∏ j ∈ Finset.univ.erase i, volume.restrict (Set.Ioc (0 : ℝ) 1) (update s i Set.univ j) = ∏ j ∈ Finset.univ.erase i, volume.restrict (Set.Ioc (0 : ℝ) 1) (s j)` using `Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]`. Rewrite using `[hp, Function.update_self, h1, one_mul, mul_comm]`.
-/
lemma measurePreserving_tmUpd (i : ι) :
    MeasurePreserving (tmUpd i) ((torusProb ι).prod unitIntervalMeasure) (torusProb ι) := by
  refine ⟨measurable_tmUpd i, ?_⟩
  have h1 : (volume.restrict (Set.Ioc (0 : ℝ) 1)) Set.univ = 1 := by simp
  unfold torusProb
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (measurable_tmUpd i) (MeasurableSet.univ_pi hs), tmUpd_preimage_pi,
    Measure.prod_prod, Measure.pi_pi,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => volume.restrict (Set.Ioc (0 : ℝ) 1) (s j))
      (Finset.mem_univ i)]
  have hp : ∏ j ∈ Finset.univ.erase i, volume.restrict (Set.Ioc (0 : ℝ) 1) (update s i Set.univ j) =
      ∏ j ∈ Finset.univ.erase i, volume.restrict (Set.Ioc (0 : ℝ) 1) (s j) :=
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hp, Function.update_self, h1, one_mul, mul_comm]

/- English proof (translation)
Conclude with `(measurePreserving_tmUpd i).integrable_comp hF`.
-/
lemma tm_integrable_comp (i : ι) {F : (ι → ℝ) → ℝ} (hF : AEStronglyMeasurable F (torusProb ι)) :
    Integrable (F ∘ tmUpd i) ((torusProb ι).prod unitIntervalMeasure) ↔ Integrable F (torusProb ι) := by
  exact (measurePreserving_tmUpd i).integrable_comp hF

/- English proof (translation)
Establish `hmap` using `(measurePreserving_tmUpd i).map_eq`. Use `conv_lhs => rw [← hmap]`. Conclude with `integral_map (measurable_tmUpd i).aemeasurable (by rwa [hmap])`.
-/
lemma tm_integral_comp (i : ι) {F : (ι → ℝ) → ℝ} (hF : AEStronglyMeasurable F (torusProb ι)) :
    ∫ θ, F θ ∂(torusProb ι) = ∫ p, F (tmUpd i p) ∂((torusProb ι).prod unitIntervalMeasure) := by
  have hmap := (measurePreserving_tmUpd i).map_eq
  conv_lhs => rw [← hmap]
  exact integral_map (measurable_tmUpd i).aemeasurable (by rwa [hmap])

/- English proof (translation)
Rewrite using `[← (measurePreserving_tmUpd i).measure_preimage hS.nullMeasurableSet, Measure.prod_apply ((measurable_tmUpd i) hS)]`. Establish `h2 : (fun θ => unitIntervalMeasure (Prod.mk θ ⁻¹' (tmUpd i ⁻¹' S))) =ᵐ[torusProb ι] 0` using `h.mono fun θ hθ => hθ`. Rewrite using `[lintegral_congr_ae h2]`. Simplify using the standard rewrite rules.
-/
lemma tm_measure_null (i : ι) {S : Set (ι → ℝ)} (hS : MeasurableSet S)
    (h : ∀ᵐ θ ∂(torusProb ι), unitIntervalMeasure {t | update θ i t ∈ S} = 0) : torusProb ι S = 0 := by
  rw [← (measurePreserving_tmUpd i).measure_preimage hS.nullMeasurableSet,
    Measure.prod_apply ((measurable_tmUpd i) hS)]
  have h2 : (fun θ => unitIntervalMeasure (Prod.mk θ ⁻¹' (tmUpd i ⁻¹' S))) =ᵐ[torusProb ι] 0 :=
    h.mono fun θ hθ => hθ
  rw [lintegral_congr_ae h2]
  simp

def tmSlice (i : ι) (x : ι → ℂ) (f : MvPolynomial ι ℂ) : Polynomial ℂ :=
  ∑ s ∈ f.support, Polynomial.monomial (s i)
    (MvPolynomial.eval x (MvPolynomial.monomial (s.erase i) (f.coeff s)))

/- English proof (translation)
Simplify using `only [tmSlice, coeffIn, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, map_sum, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma tmSlice_coeff (i : ι) (x : ι → ℂ) (f : MvPolynomial ι ℂ) (k : ℕ) :
    (tmSlice i x f).coeff k = MvPolynomial.eval x (coeffIn i k f) := by
  simp only [tmSlice, coeffIn, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, map_sum,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Use `conv_lhs => rw [f.as_sum]`. Simplify using `only [tmSlice, map_sum, Polynomial.eval_finset_sum, Polynomial.eval_monomial, MvPolynomial.eval_monomial]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i, Function.update_self, Finsupp.erase_same, pow_zero, one_mul]`. Establish `hp : ∏ j ∈ ({i}ᶜ : Finset ι), update x i z j ^ s j = ∏ j ∈ ({i}ᶜ : Finset ι), x j ^ (Finsupp.erase i s) j` using `Finset.prod_congr rfl fun j hj => by`.

Establish `hji : j ≠ i` using `by simpa using hj`. Rewrite using `[Function.update_of_ne hji, Finsupp.erase_ne hji]`. Rewrite using `[hp]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma tm_eval_update (i : ι) (x : ι → ℂ) (z : ℂ) (f : MvPolynomial ι ℂ) :
    MvPolynomial.eval (update x i z) f = (tmSlice i x f).eval z := by
  conv_lhs => rw [f.as_sum]
  simp only [tmSlice, map_sum, Polynomial.eval_finset_sum, Polynomial.eval_monomial,
    MvPolynomial.eval_monomial]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i, Function.update_self,
    Finsupp.erase_same, pow_zero, one_mul]
  have hp : ∏ j ∈ ({i}ᶜ : Finset ι), update x i z j ^ s j =
      ∏ j ∈ ({i}ᶜ : Finset ι), x j ^ (Finsupp.erase i s) j :=
    Finset.prod_congr rfl fun j hj => by
      have hji : j ≠ i := by simpa using hj
      rw [Function.update_of_ne hji, Finsupp.erase_ne hji]
  rw [hp]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[torusPoint, circPt]`. Simplify using `[torusPoint, Function.update_of_ne h]`.
-/
lemma torusPoint_update (θ : ι → ℝ) (i : ι) (t : ℝ) :
    torusPoint (update θ i t) = update (torusPoint θ) i (circPt t) := by
  funext j
  by_cases h : j = i
  · subst h; simp [torusPoint, circPt]
  · simp [torusPoint, Function.update_of_ne h]

/- English proof (translation)
Simplify using `[torusPoint, Complex.norm_exp]`.
-/
lemma norm_torusPoint (θ : ι → ℝ) (j : ι) : ‖torusPoint θ j‖ = 1 := by simp [torusPoint, Complex.norm_exp]

/- English proof (translation)
Rewrite using `[MvPolynomial.eval_eq]`. Use `(norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun s _ => ?_))` and prove the remaining obligations. Rewrite using `[norm_mul, norm_prod]`. Simplify using `[norm_pow, norm_torusPoint]`.
-/
lemma norm_eval_torus_le (f : MvPolynomial ι ℂ) (θ : ι → ℝ) :
    ‖MvPolynomial.eval (torusPoint θ) f‖ ≤ ∑ s ∈ f.support, ‖f.coeff s‖ := by
  rw [MvPolynomial.eval_eq]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun s _ => ?_))
  rw [norm_mul, norm_prod]
  simp [norm_pow, norm_torusPoint]

/- English proof (translation)
Conclude with `(MvPolynomial.continuous_eval f).comp (continuous_pi fun j => by unfold torusPoint; fun_prop)`.
-/
lemma continuous_eval_torus (f : MvPolynomial ι ℂ) :
    Continuous fun θ : ι → ℝ => MvPolynomial.eval (torusPoint θ) f := by
  exact (MvPolynomial.continuous_eval f).comp (continuous_pi fun j => by unfold torusPoint; fun_prop)

/- English proof (translation)
The claim follows from `Real.measurable_log.comp (continuous_eval_torus f).norm.measurable`.
-/
lemma measurable_logEval (f : MvPolynomial ι ℂ) :
    Measurable fun θ : ι → ℝ => Real.log ‖MvPolynomial.eval (torusPoint θ) f‖ := Real.measurable_log.comp (continuous_eval_torus f).norm.measurable

/- English proof (translation)
Introduce `j hj`. Unfold `coeffIn at hj`. Establish `h1` using `MvPolynomial.vars_sum_subset _ _ hj`. Rewrite `h1` using `[Finset.mem_biUnion]`. Take `⟨s, hs, hjs⟩` from `h1`.

Establish `hsf : s ∈ f.support` using `(Finset.mem_filter.mp hs).1`. Rewrite `hjs` using `[MvPolynomial.vars_monomial (MvPolynomial.mem_support_iff.mp hsf), Finsupp.support_erase, Finset.mem_erase]`. Conclude with `Finset.mem_erase.mpr ⟨hjs.1, (MvPolynomial.mem_vars j).mpr ⟨s, hsf, hjs.2⟩⟩`.
-/
lemma vars_coeffIn_subset (i : ι) (k : ℕ) (f : MvPolynomial ι ℂ) :
    (coeffIn i k f).vars ⊆ f.vars.erase i := by
  intro j hj
  unfold coeffIn at hj
  have h1 := MvPolynomial.vars_sum_subset _ _ hj
  rw [Finset.mem_biUnion] at h1
  obtain ⟨s, hs, hjs⟩ := h1
  have hsf : s ∈ f.support := (Finset.mem_filter.mp hs).1
  rw [MvPolynomial.vars_monomial (MvPolynomial.mem_support_iff.mp hsf), Finsupp.support_erase,
    Finset.mem_erase] at hjs
  exact Finset.mem_erase.mpr ⟨hjs.1, (MvPolynomial.mem_vars j).mpr ⟨s, hsf, hjs.2⟩⟩

end ReciprocityTheory.MultiplicativeHeights
