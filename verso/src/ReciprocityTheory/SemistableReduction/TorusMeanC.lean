import ReciprocityTheory.SemistableReduction.TorusMeanB

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Real Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tmLog (f : MvPolynomial ι ℂ) (θ : ι → ℝ) : ℝ := Real.log ‖MvPolynomial.eval (torusPoint θ) f‖

/- English proof (translation)
The claim follows from `measurable_logEval f`.
-/
lemma measurable_tmLog (f : MvPolynomial ι ℂ) : Measurable (tmLog f) := measurable_logEval f

/- English proof (translation)
Rewrite using `[tmLog, torusPoint_update, tm_eval_update]`.
-/
lemma tmLog_update (f : MvPolynomial ι ℂ) (θ : ι → ℝ) (i : ι) (t : ℝ) :
    tmLog f (update θ i t) = Real.log ‖(tmSlice i (torusPoint θ) f).eval (circPt t)‖ := by
  rw [tmLog, torusPoint_update, tm_eval_update]

/- English proof (translation)
Unfold `tmLog`. Break down `eq_or_ne ‖MvPolynomial.eval (torusPoint θ) f‖ 0 with h | h` into its components or cases. Rewrite using `[h, Real.log_zero]`. Conclude with `posLog_nonneg`. Conclude with `(Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)) (norm_eval_torus_le f θ)).trans (le_max_right _ _)`.
-/
lemma tmLog_le (f : MvPolynomial ι ℂ) (θ : ι → ℝ) :
    tmLog f θ ≤ posLog (∑ s ∈ f.support, ‖f.coeff s‖) := by
  unfold tmLog
  rcases eq_or_ne ‖MvPolynomial.eval (torusPoint θ) f‖ 0 with h | h
  · rw [h, Real.log_zero]; exact posLog_nonneg
  · exact (Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h))
      (norm_eval_torus_le f θ)).trans (le_max_right _ _)

/- English proof (translation)
Unfold `coeffIn`. Rewrite using `[Finset.filter_false_of_mem, Finset.sum_empty]`. Introduce `s hs hsk`. Use `Finset.le_sup (f := fun s : ι →₀ ℕ => s i) hs` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
lemma coeffIn_eq_zero_of_lt (i : ι) (f : MvPolynomial ι ℂ) (k : ℕ)
    (hk : f.support.sup (fun s => s i) < k) : coeffIn i k f = 0 := by
  unfold coeffIn
  rw [Finset.filter_false_of_mem, Finset.sum_empty]
  intro s hs hsk
  have := Finset.le_sup (f := fun s : ι →₀ ℕ => s i) hs
  omega

/- English proof (translation)
Assume the negation of the conclusion as `h`. Simplify using `only [not_exists, not_not] at h`. Apply `hf` to reduce the goal to its premises. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `x`.

Establish `hs : tmSlice i x f = 0`. Use extensionality with `k`. Rewrite using `[tmSlice_coeff, h k]`. Simplify using the standard rewrite rules. Rewrite using `[← update_eq_self i x, tm_eval_update, hs]`.

Simplify using the standard rewrite rules.
-/
lemma exists_coeffIn_ne_zero (i : ι) (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    ∃ k, coeffIn i k f ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hf
  apply MvPolynomial.funext
  intro x
  have hs : tmSlice i x f = 0 := by
    ext k
    rw [tmSlice_coeff, h k]
    simp
  rw [← update_eq_self i x, tm_eval_update, hs]
  simp

/- English proof (translation)
Use `set T := (Finset.range (f.support.sup (fun s => s i) + 1)).filter (fun k => coeffIn i k f ≠ 0)`. Establish `hT : T.Nonempty`. Take `⟨k, hk⟩` from `exists_coeffIn_ne_zero i f hf`. Use `⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hk⟩⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`.

Conclude with `hk (coeffIn_eq_zero_of_lt i f k (by omega))`. Use `⟨T.max' hT, (Finset.mem_filter.mp (T.max'_mem hT)).2, fun k hk => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Distinguish the cases in `hkN : k < f.support.sup (fun s => s i) + 1`. Establish `: k ∈ T` using `Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkN, hne⟩`.

Conclude with `absurd (T.le_max' k this) (by omega)`. Conclude with `hne (coeffIn_eq_zero_of_lt i f k (by omega))`.
-/
lemma exists_top_coeffIn (i : ι) (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    ∃ d, coeffIn i d f ≠ 0 ∧ ∀ k, d < k → coeffIn i k f = 0 := by
  classical
  set T := (Finset.range (f.support.sup (fun s => s i) + 1)).filter (fun k => coeffIn i k f ≠ 0)
  have hT : T.Nonempty := by
    obtain ⟨k, hk⟩ := exists_coeffIn_ne_zero i f hf
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hk⟩⟩
    by_contra hlt
    exact hk (coeffIn_eq_zero_of_lt i f k (by omega))
  refine ⟨T.max' hT, (Finset.mem_filter.mp (T.max'_mem hT)).2, fun k hk => ?_⟩
  by_contra hne
  by_cases hkN : k < f.support.sup (fun s => s i) + 1
  · have : k ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkN, hne⟩
    exact absurd (T.le_max' k this) (by omega)
  · exact hne (coeffIn_eq_zero_of_lt i f k (by omega))

/- English proof (translation)
Use `MvPolynomial.eval₂Hom_eq_constantCoeff_of_vars (RingHom.id ℂ) (g := x) (p := f) (fun i hi => absurd (hf hi) (by simp))` as an intermediate fact. Simplify using `using this`.
-/
lemma eval_const_of_vars_empty (f : MvPolynomial ι ℂ) (hf : f.vars ⊆ ∅) (x : ι → ℂ) :
    MvPolynomial.eval x f = MvPolynomial.constantCoeff f := by
  have := MvPolynomial.eval₂Hom_eq_constantCoeff_of_vars (RingHom.id ℂ) (g := x) (p := f)
    (fun i hi => absurd (hf hi) (by simp))
  simpa using this

/- English proof (translation)
The claim follows from `(continuous_eval_torus f).measurable (measurableSet_singleton 0)`.
-/
lemma measurableSet_zeroTorus (f : MvPolynomial ι ℂ) :
    MeasurableSet {θ : ι → ℝ | MvPolynomial.eval (torusPoint θ) f = 0} :=
  (continuous_eval_torus f).measurable (measurableSet_singleton 0)

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Introduce `f hS hf`. Establish `hc : MvPolynomial.constantCoeff f ≠ 0`. Introduce `h0`.

Apply `hf` to reduce the goal to its premises. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `x`. Rewrite using `[eval_const_of_vars_empty f hS, h0]`. Simplify using the standard rewrite rules.

Establish `: {θ : ι → ℝ | MvPolynomial.eval (torusPoint θ) f = 0} = ∅`. Use extensionality with `θ`. Simplify using `[eval_const_of_vars_empty f hS, hc]`. Rewrite using `[this, measure_empty]`. Consider the case `insert i S' hi ih`.

Introduce `f hS hf`. Take `⟨d, hd, htop⟩` from `exists_top_coeffIn i f hf`. Establish `hg : torusProb ι {θ | MvPolynomial.eval (torusPoint θ) (coeffIn i d f) = 0} = 0`. Apply `ih _ _ hd` to reduce the goal to its premises. Introduce `j hj`.

Establish `h1` using `vars_coeffIn_subset i d f hj`. Rewrite `h1` using `[Finset.mem_erase]`. Establish `h2` using `hS h1.2`. Rewrite `h2` using `[Finset.mem_insert]`. Conclude with `h2.resolve_left h1.1`.

Apply `tm_measure_null i (measurableSet_zeroTorus f)` to reduce the goal to its premises. Establish `hae : ∀ᵐ θ ∂(torusProb ι), MvPolynomial.eval (torusPoint θ) (coeffIn i d f) ≠ 0`. Rewrite using `[ae_iff]`. Simplify using `using hg`. Use `filter_upwards [hae] with θ hθ`.

Establish `hp : tmSlice i (torusPoint θ) f ≠ 0`. Introduce `h0`. Apply `hθ` to reduce the goal to its premises. Rewrite using `[← tmSlice_coeff, h0, Polynomial.coeff_zero]`. Use `zero_set_circ_null _ hp` as an intermediate fact.

Use `this using 3 with t` and compare the differences between its conclusion and the goal. Simplify using `only [torusPoint_update, tm_eval_update]`.
-/
lemma torus_zero_set_measure_zero (S : Finset ι) : ∀ f : MvPolynomial ι ℂ, f.vars ⊆ S → f ≠ 0 →
    torusProb ι {θ | MvPolynomial.eval (torusPoint θ) f = 0} = 0 := by
  induction S using Finset.induction_on with
  | empty =>
    intro f hS hf
    have hc : MvPolynomial.constantCoeff f ≠ 0 := by
      intro h0
      apply hf
      apply MvPolynomial.funext
      intro x
      rw [eval_const_of_vars_empty f hS, h0]
      simp
    have : {θ : ι → ℝ | MvPolynomial.eval (torusPoint θ) f = 0} = ∅ := by
      ext θ
      simp [eval_const_of_vars_empty f hS, hc]
    rw [this, measure_empty]
  | insert i S' hi ih =>
    intro f hS hf
    obtain ⟨d, hd, htop⟩ := exists_top_coeffIn i f hf
    have hg : torusProb ι {θ | MvPolynomial.eval (torusPoint θ) (coeffIn i d f) = 0} = 0 := by
      apply ih _ _ hd
      intro j hj
      have h1 := vars_coeffIn_subset i d f hj
      rw [Finset.mem_erase] at h1
      have h2 := hS h1.2
      rw [Finset.mem_insert] at h2
      exact h2.resolve_left h1.1
    apply tm_measure_null i (measurableSet_zeroTorus f)
    have hae : ∀ᵐ θ ∂(torusProb ι), MvPolynomial.eval (torusPoint θ) (coeffIn i d f) ≠ 0 := by
      rw [ae_iff]; simpa using hg
    filter_upwards [hae] with θ hθ
    have hp : tmSlice i (torusPoint θ) f ≠ 0 := by
      intro h0
      apply hθ
      rw [← tmSlice_coeff, h0, Polynomial.coeff_zero]
    have := zero_set_circ_null _ hp
    convert this using 3 with t
    simp only [torusPoint_update, tm_eval_update]

/- English proof (translation)
The claim follows from `torus_zero_set_measure_zero Finset.univ f (Finset.subset_univ _) hf`.
-/
lemma tm_null (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    torusProb ι {θ | MvPolynomial.eval (torusPoint θ) f = 0} = 0 :=
  torus_zero_set_measure_zero Finset.univ f (Finset.subset_univ _) hf

end ReciprocityTheory.MultiplicativeHeights
