import Formalism.FlagUnipotentLattices.UnipotentStabiliserCharacterisation

namespace Formalism.HermitianLatticeCounting.P

section G0
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms

/- English proof (translation)
Introduce `E _ _ x hx`. Rewrite using `[InfinitePlace.prod_eq_abs_norm]`. Establish `h : (Algebra.norm ℤ x) ≠ 0`. Simplify `hx` using `[Algebra.norm_eq_zero_iff]`. Establish `h2 : (Algebra.norm ℚ (x : E)) = ((Algebra.norm ℤ x : ℤ) : ℚ)`.

Rewrite using `[Algebra.coe_norm_int]`. Rewrite using `[h2]`. Establish `: (1 : ℤ) ≤ |Algebra.norm ℤ x|` using `Int.one_le_abs h`. Conclude with `this` after adjusting the coercions.
-/
theorem integral_norm_estimate_holds : Formalism.HermitianLatticeCounting.ExpansionTerms.AlgebraicIntegerNormGeOne := by
  intro E _ _ x hx
  rw [InfinitePlace.prod_eq_abs_norm]
  have h : (Algebra.norm ℤ x) ≠ 0 := by
    simpa [Algebra.norm_eq_zero_iff] using hx
  have h2 : (Algebra.norm ℚ (x : E)) = ((Algebra.norm ℤ x : ℤ) : ℚ) := by
    rw [Algebra.coe_norm_int]
  rw [h2]
  have : (1 : ℤ) ≤ |Algebra.norm ℤ x| := Int.one_le_abs h
  exact_mod_cast this

/- English proof (translation)
Introduce `ι _ G hG h1`. Establish `h : ∀ v, max 1 (1 / G v) = max 1 (G v) / G v`. Introduce `v`. Establish `h0` using `hG v`. Break down `le_total 1 (G v) with h | h` into its components or cases.

Rewrite using `[max_eq_left, max_eq_right h, div_self h0.ne']`. Rewrite using `[div_le_one h0]`. Conclude with `h`. Rewrite using `[max_eq_right, max_eq_left h]`. Rewrite using `[le_div_iff₀ h0]`.

Simplify using `using h`. Repeatedly rewrite using `[h, Finset.prod_div_distrib]`. Apply `div_le_self` to reduce the goal to its premises. Conclude with `Finset.prod_nonneg fun v _ => by positivity`. Conclude with `h1`.
-/
theorem prod_max_inv_le_prod_max' : Formalism.HermitianLatticeCounting.ExpansionTerms.ProdMaxInvLeProdMax := by
  intro ι _ G hG h1
  have h : ∀ v, max 1 (1 / G v) = max 1 (G v) / G v := by
    intro v
    have h0 := hG v
    rcases le_total 1 (G v) with h | h
    · rw [max_eq_left, max_eq_right h, div_self h0.ne']
      rw [div_le_one h0]; exact h
    · rw [max_eq_right, max_eq_left h]
      rw [le_div_iff₀ h0]; simpa using h
  simp_rw [h, Finset.prod_div_distrib]
  apply div_le_self
  · exact Finset.prod_nonneg fun v _ => by positivity
  · exact h1

/- English proof (translation)
Introduce `P ι step d MM c q0 J hd h0 hs q`. Proceed by induction on `q with`. Consider the case `zero => intro μ j _ _`. Simplify using `using h0 μ j`. Consider the case `succ q ih`.

Introduce `μ j h1 h2`. Combine the equalities or inequalities in the displayed calculation. Conclude with `iSup_le fun s => ih _ _ (by have := hd μ s; omega) (by omega)`. Use `_ = c^(q+1) := by rw [pow_succ, mul_comm]`.
-/
theorem moment_recursion_iterate : Formalism.HermitianLatticeCounting.ExpansionTerms.MomentRecursionIterate := by
  intro P ι step d MM c q0 J hd h0 hs q
  induction q with
  | zero => intro μ j _ _; simpa using h0 μ j
  | succ q ih =>
    intro μ j h1 h2
    calc MM (q+1) μ j ≤ c * ⨆ s, MM q (step μ s) (j+2) := hs q μ j (by omega) (by omega)
      _ ≤ c * c^q := by
          gcongr
          exact iSup_le fun s => ih _ _ (by have := hd μ s; omega) (by omega)
      _ = c^(q+1) := by rw [pow_succ, mul_comm]

end G0

section G1
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms

/- English proof (translation)
Introduce `ι _ ro D D' hro hne hprod`. Rewrite using `[Set.disjoint_left]`. Introduce `x hx hx'`. Establish `hlt : ∀ v, ‖D v - D' v‖ < ro` using `fun v => by`. Establish `h1` using `hx v`.

Establish `h2` using `hx' v`. Combine the equalities or inequalities in the displayed calculation. Establish `hne' : Nonempty ι`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nonempty_iff]`.

Conclude with `hne (Subsingleton.elim _ _)`. Distinguish the cases in `h0 : ∃ v, ‖D v - D' v‖ = 0`. Take `⟨v, hv⟩` from `h0`. Establish `h1 : ∏ v, ‖D v - D' v‖ = 0` using `Finset.prod_eq_zero (Finset.mem_univ v) hv`. Establish `h2` using `pow_pos hro (Fintype.card ι)`.

Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [not_exists] at h0`. Establish `h1 : ∏ v, ‖D v - D' v‖ < ∏ _v : ι, ro` using `Finset.prod_lt_prod_of_nonempty (fun i _ => lt_of_le_of_ne (norm_nonneg _) (Ne.symm (h0 i))) (fun i _ => hlt i) Finset.univ_nonempty`. Simplify using `only [Finset.prod_const, Finset.card_univ] at h1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem disjointness_of_supports_holds : Formalism.HermitianLatticeCounting.ExpansionTerms.SeparatedPolydiscsDisjoint := by
  intro ι _ ro D D' hro hne hprod
  rw [Set.disjoint_left]
  intro x hx hx'
  have hlt : ∀ v, ‖D v - D' v‖ < ro := fun v => by
    have h1 := hx v
    have h2 := hx' v
    calc ‖D v - D' v‖ = ‖(x v - D' v) - (x v - D v)‖ := by ring_nf
      _ ≤ ‖x v - D' v‖ + ‖x v - D v‖ := norm_sub_le _ _
      _ < ro := by linarith
  have hne' : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hne (Subsingleton.elim _ _)
  by_cases h0 : ∃ v, ‖D v - D' v‖ = 0
  · obtain ⟨v, hv⟩ := h0
    have h1 : ∏ v, ‖D v - D' v‖ = 0 := Finset.prod_eq_zero (Finset.mem_univ v) hv
    have h2 := pow_pos hro (Fintype.card ι)
    linarith
  · simp only [not_exists] at h0
    have h1 : ∏ v, ‖D v - D' v‖ < ∏ _v : ι, ro :=
      Finset.prod_lt_prod_of_nonempty (fun i _ => lt_of_le_of_ne (norm_nonneg _) (Ne.symm (h0 i)))
        (fun i _ => hlt i) Finset.univ_nonempty
    simp only [Finset.prod_const, Finset.card_univ] at h1
    linarith

/- English proof (translation)
Establish `h` using `integrable_fun_norm_addHaar (E := ℂ) (volume : Measure ℂ) (f := f)`. Simplify `h` using `[Complex.finrank_real_complex]`.
-/
lemma integrable_radial_iff (f : ℝ → ℝ) :
    Integrable (fun x : ℂ => f ‖x‖) ↔ IntegrableOn (fun y : ℝ => y * f y) (Set.Ioi 0) := by
  have h := integrable_fun_norm_addHaar (E := ℂ) (volume : Measure ℂ) (f := f)
  simpa [Complex.finrank_real_complex] using h

/- English proof (translation)
Establish `h` using `integral_fun_norm_addHaar (E := ℂ) (volume : Measure ℂ) f`. Establish `hv : (volume : Measure ℂ).real (Metric.ball 0 1) = π`. Simplify using `[Measure.real, Complex.volume_ball]`. Rewrite using `[h, hv]`. Simplify using `[Complex.finrank_real_complex]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma integral_complex_radial_eq_two_pi_mul_integral_Ioi (f : ℝ → ℝ) :
    ∫ x : ℂ, f ‖x‖ = 2 * π * ∫ y in Set.Ioi (0 : ℝ), y * f y := by
  have h := integral_fun_norm_addHaar (E := ℂ) (volume : Measure ℂ) f
  have hv : (volume : Measure ℂ).real (Metric.ball 0 1) = π := by
    simp [Measure.real, Complex.volume_ball]
  rw [h, hv]
  simp [Complex.finrank_real_complex]
  ring

/- English proof (translation)
Establish `hpos : (1 + y ^ 2) ≠ 0` using `by positivity`. Establish `h1 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * y) y`. Simplify using `using ((hasDerivAt_id y).pow 2).const_add 1`. Establish `h2` using `(h1.inv hpos).const_mul (-(1 / 2) : ℝ)`. Establish `e : y * ((1 + y ^ 2) ^ 2)⁻¹ = -(1 / 2) * (-(2 * y) / (1 + y ^ 2) ^ 2)`.

Rewrite using `[div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h2`.
-/
lemma hasDerivAt_inv_one_add_sq (y : ℝ) :
    HasDerivAt (fun y : ℝ => -(1 / 2) * (1 + y ^ 2)⁻¹) (y * ((1 + y ^ 2) ^ 2)⁻¹) y := by
  have hpos : (1 + y ^ 2) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * y) y := by
    simpa using ((hasDerivAt_id y).pow 2).const_add 1
  have h2 := (h1.inv hpos).const_mul (-(1 / 2) : ℝ)
  have e : y * ((1 + y ^ 2) ^ 2)⁻¹ = -(1 / 2) * (-(2 * y) / (1 + y ^ 2) ^ 2) := by
    rw [div_eq_mul_inv]
    ring
  rw [e]
  exact h2

/- English proof (translation)
Establish `h1 : Filter.Tendsto (fun y : ℝ => 1 + y ^ 2) Filter.atTop Filter.atTop` using `Filter.tendsto_atTop_add_const_left _ 1 (Filter.tendsto_pow_atTop two_ne_zero)`. Establish `h2` using `(tendsto_inv_atTop_zero.comp h1).const_mul (-(1 / 2) : ℝ)`. Simplify using `using h2`.
-/
lemma tendsto_inv_one_add_sq_atTop :
    Filter.Tendsto (fun y : ℝ => -(1 / 2) * (1 + y ^ 2)⁻¹) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun y : ℝ => 1 + y ^ 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_left _ 1 (Filter.tendsto_pow_atTop two_ne_zero)
  have h2 := (tendsto_inv_atTop_zero.comp h1).const_mul (-(1 / 2) : ℝ)
  simpa using h2

/- English proof (translation)
Establish `hnn : ∀ y ∈ Set.Ioi (0 : ℝ), 0 ≤ y * ((1 + y ^ 2) ^ 2)⁻¹` using `fun y hy => by`. Establish `: (0 : ℝ) < y` using `hy`. Check the signs of the components of the expression. Prove the components needed by the constructor for the conclusion. Rewrite using `[integrable_radial_iff (fun y => ((1 + y ^ 2) ^ 2)⁻¹)]`.

Conclude with `integrableOn_Ioi_deriv_of_nonneg' (fun y _ => hasDerivAt_inv_one_add_sq y) hnn tendsto_inv_one_add_sq_atTop`. Rewrite using `[integral_complex_radial_eq_two_pi_mul_integral_Ioi (fun y => ((1 + y ^ 2) ^ 2)⁻¹), integral_Ioi_of_hasDerivAt_of_nonneg' (fun y _ => hasDerivAt_inv_one_add_sq y) hnn tendsto_inv_one_add_sq_atTop]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inverse_power_integral_pi : Formalism.HermitianLatticeCounting.ExpansionTerms.InversePowerIntegralPi := by
  have hnn : ∀ y ∈ Set.Ioi (0 : ℝ), 0 ≤ y * ((1 + y ^ 2) ^ 2)⁻¹ := fun y hy => by
    have : (0 : ℝ) < y := hy
    positivity
  constructor
  · rw [integrable_radial_iff (fun y => ((1 + y ^ 2) ^ 2)⁻¹)]
    exact integrableOn_Ioi_deriv_of_nonneg' (fun y _ => hasDerivAt_inv_one_add_sq y) hnn tendsto_inv_one_add_sq_atTop
  · rw [integral_complex_radial_eq_two_pi_mul_integral_Ioi (fun y => ((1 + y ^ 2) ^ 2)⁻¹),
      integral_Ioi_of_hasDerivAt_of_nonneg' (fun y _ => hasDerivAt_inv_one_add_sq y) hnn tendsto_inv_one_add_sq_atTop]
    ring

/- English proof (translation)
Establish `h1 : (1 : ℝ) ≤ (L / y) ^ K` using `Real.one_le_rpow ((one_le_div hy).2 h) hK`. Rewrite using `[TruncationCutoff, if_neg hy.ne', min_eq_left h1, mul_one]`.
-/
lemma mul_cutoff_of_le {K L y : ℝ} (hK : 0 ≤ K) (hy : 0 < y) (h : y ≤ L) : y * TruncationCutoff K L y = y := by
  have h1 : (1 : ℝ) ≤ (L / y) ^ K := Real.one_le_rpow ((one_le_div hy).2 h) hK
  rw [TruncationCutoff, if_neg hy.ne', min_eq_left h1, mul_one]

/- English proof (translation)
Establish `hy : 0 < y` using `hL.trans h`. Establish `h1 : (L / y) ^ K ≤ 1` using `Real.rpow_le_one (div_nonneg hL.le hy.le) ((div_le_one hy).2 h.le) hK`. Rewrite using `[TruncationCutoff, if_neg hy.ne', min_eq_right h1, Real.div_rpow hL.le hy.le, sub_eq_add_neg, Real.rpow_add hy, Real.rpow_one, Real.rpow_neg hy.le, div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma mul_cutoff_of_gt {K L y : ℝ} (hK : 0 ≤ K) (hL : 0 < L) (h : L < y) :
    y * TruncationCutoff K L y = L ^ K * y ^ (1 - K) := by
  have hy : 0 < y := hL.trans h
  have h1 : (L / y) ^ K ≤ 1 :=
    Real.rpow_le_one (div_nonneg hL.le hy.le) ((div_le_one hy).2 h.le) hK
  rw [TruncationCutoff, if_neg hy.ne', min_eq_right h1, Real.div_rpow hL.le hy.le, sub_eq_add_neg,
    Real.rpow_add hy, Real.rpow_one, Real.rpow_neg hy.le, div_eq_mul_inv]
  ring

/- English proof (translation)
The claim follows from `(integrableOn_congr_fun (fun _ hy => (mul_cutoff_of_le hK hy.1 hy.2).symm) measurableSet_Ioc).1 (continuous_id.integrableOn_Ioc)`.
-/
lemma integrable_cutoff_below {K L : ℝ} (hK : 0 ≤ K) :
    IntegrableOn (fun y : ℝ => y * TruncationCutoff K L y) (Set.Ioc 0 L) :=
  (integrableOn_congr_fun (fun _ hy => (mul_cutoff_of_le hK hy.1 hy.2).symm) measurableSet_Ioc).1
    (continuous_id.integrableOn_Ioc)

/- English proof (translation)
The claim follows from `(integrableOn_congr_fun (fun _ hy => (mul_cutoff_of_gt (by linarith) hL hy).symm) measurableSet_Ioi).1 ((integrableOn_Ioi_rpow_of_lt (by linarith : 1 - K < -1) hL).const_mul (L ^ K))`.
-/
lemma integrable_cutoff_beyond {K L : ℝ} (hK : 2 < K) (hL : 0 < L) :
    IntegrableOn (fun y : ℝ => y * TruncationCutoff K L y) (Set.Ioi L) :=
  (integrableOn_congr_fun (fun _ hy => (mul_cutoff_of_gt (by linarith) hL hy).symm) measurableSet_Ioi).1
    ((integrableOn_Ioi_rpow_of_lt (by linarith : 1 - K < -1) hL).const_mul (L ^ K))

/- English proof (translation)
Introduce `K L hK hL`. Establish `hK0 : 0 ≤ K` using `by linarith`. Establish `hU : Set.Ioi (0 : ℝ) = Set.Ioc 0 L ∪ Set.Ioi L` using `(Set.Ioc_union_Ioi_eq_Ioi hL.le).symm`. Prove the components needed by the constructor for the conclusion. Rewrite using `[integrable_radial_iff (fun y => TruncationCutoff K L y), hU]`.

Conclude with `(integrable_cutoff_below hK0).union (integrable_cutoff_beyond hK hL)`. Rewrite using `[integral_complex_radial_eq_two_pi_mul_integral_Ioi (fun y => TruncationCutoff K L y), hU, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi (integrable_cutoff_below hK0) (integrable_cutoff_beyond hK hL), setIntegral_congr_fun measurableSet_Ioc (fun y hy => mul_cu …`. Establish `e : L ^ K * L ^ (1 - K + 1) = L ^ 2`. Rewrite using `[← Real.rpow_add hL, ← Real.rpow_natCast]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hK2 : K - 2 ≠ 0` using `by linarith [hK]`. Establish `hK3 : 1 - K + 1 ≠ 0`. Introduce `h`.

Apply `hK2` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e2 : L ^ K * (-L ^ (1 - K + 1) / (1 - K + 1)) = L ^ 2 / (K - 2)`. Rewrite using `[← e]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cutoff_integral_formula : Formalism.HermitianLatticeCounting.ExpansionTerms.CutoffIntegralFormula := by
  intro K L hK hL
  have hK0 : 0 ≤ K := by linarith
  have hU : Set.Ioi (0 : ℝ) = Set.Ioc 0 L ∪ Set.Ioi L := (Set.Ioc_union_Ioi_eq_Ioi hL.le).symm
  constructor
  · rw [integrable_radial_iff (fun y => TruncationCutoff K L y), hU]
    exact (integrable_cutoff_below hK0).union (integrable_cutoff_beyond hK hL)
  · rw [integral_complex_radial_eq_two_pi_mul_integral_Ioi (fun y => TruncationCutoff K L y), hU,
      setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi (integrable_cutoff_below hK0)
        (integrable_cutoff_beyond hK hL),
      setIntegral_congr_fun measurableSet_Ioc (fun y hy => mul_cutoff_of_le hK0 hy.1 hy.2),
      setIntegral_congr_fun measurableSet_Ioi (fun y hy => mul_cutoff_of_gt hK0 hL hy),
      integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : 1 - K < -1) hL,
      ← intervalIntegral.integral_of_le hL.le, integral_id]
    have e : L ^ K * L ^ (1 - K + 1) = L ^ 2 := by
      rw [← Real.rpow_add hL, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    have hK2 : K - 2 ≠ 0 := by linarith [hK]
    have hK3 : 1 - K + 1 ≠ 0 := by
      intro h
      apply hK2
      linarith
    have e2 : L ^ K * (-L ^ (1 - K + 1) / (1 - K + 1)) = L ^ 2 / (K - 2) := by
      rw [← e]
      field_simp
      ring
    rw [e2]
    field_simp
    ring

end G1

section G2
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms

/- English proof (translation)
Use extensionality with `x`. Simplify using `[CenteredPolydisc, dist_eq_norm]`.
-/
lemma polydisc_eq_pi_ball {ι : Type} (ro : ℝ) (D : ι → ℂ) :
    CenteredPolydisc ro D = Set.pi Set.univ (fun v => Metric.ball (D v) (ro / 2)) := by
  ext x; simp [CenteredPolydisc, dist_eq_norm]

/- English proof (translation)
Rewrite using `[polydisc_eq_pi_ball, Measure.real, volume_pi_pi]`. Simplify using `only [Complex.volume_ball, Finset.prod_const, Finset.card_univ, ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_real_pi]`. Rewrite using `[ENNReal.toReal_ofReal (by positivity), mul_comm]`.
-/
lemma volume_real_E1polydisc_eq_pi_mul_sq_pow_card {ι : Type} [Fintype ι] (ro : ℝ) (hro : 0 < ro) (D : ι → ℂ) :
    (volume : Measure (ι → ℂ)).real (CenteredPolydisc ro D) = (π * (ro / 2) ^ 2) ^ Fintype.card ι := by
  rw [polydisc_eq_pi_ball, Measure.real, volume_pi_pi]
  simp only [Complex.volume_ball, Finset.prod_const, Finset.card_univ, ENNReal.toReal_pow,
    ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_real_pi]
  rw [ENNReal.toReal_ofReal (by positivity), mul_comm]

/- English proof (translation)
Rewrite using `[polydisc_eq_pi_ball]`. Conclude with `MeasurableSet.univ_pi fun v => measurableSet_ball`.
-/
lemma measurableSet_E1polydisc {ι : Type} [Fintype ι] (ro : ℝ) (D : ι → ℂ) : MeasurableSet (CenteredPolydisc ro D) := by
  rw [polydisc_eq_pi_ball]
  exact MeasurableSet.univ_pi fun v => measurableSet_ball

/- English proof (translation)
Establish `hF : Integrable (fun x : ι → ℂ => ∏ v, ψ v (x v))` using `Integrable.fintype_prod hint`. Rewrite using `[← integral_fintype_prod_volume_eq_prod (fun v => ψ v), Finset.sum_mul]`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `D _`.

Establish `h1 : ∫ _x in CenteredPolydisc ro D, (∏ v, φ v (D v)) = (∏ v, φ v (D v)) * (π * (ro / 2) ^ 2) ^ Fintype.card ι`. Rewrite using `[setIntegral_const, volume_real_E1polydisc_eq_pi_mul_sq_pow_card ro hro, smul_eq_mul, mul_comm]`. Rewrite using `[← h1]`. Apply `setIntegral_mono_on _ hF.integrableOn (measurableSet_E1polydisc ro D)` to reduce the goal to its premises. Introduce `x hx`.

Conclude with `Finset.prod_le_prod (fun v _ => hφ v _) (fun v _ => hcmp v _ _ (hx v))`. Rewrite using `[integrableOn_const_iff] right`. Establish `: (volume : Measure (ι → ℂ)) (CenteredPolydisc ro D) ≠ ⊤`. Rewrite using `[polydisc_eq_pi_ball, volume_pi_pi]`. Conclude with `ENNReal.prod_ne_top fun v _ => measure_ball_lt_top.ne`.

Conclude with `this.lt_top`. Use `_ = ∫ x in ⋃ D ∈ S, CenteredPolydisc ro D, ∏ v, ψ v (x v) := by`. Rewrite using `[integral_biUnion_finset S (fun D _ => measurableSet_E1polydisc ro D) _ (fun D _ => hF.integrableOn)]`. Introduce `D hD D' hD' hne`. Conclude with `hd ι ro D D' hro hne (hS D hD D' hD' hne)`.

Use `_ ≤ ∫ x : ι → ℂ, ∏ v, ψ v (x v) := setIntegral_le_integral hF (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun v _ => hψ v _)`.
-/
lemma separated_sum_le_prod_integrals (hd : SeparatedPolydiscsDisjoint) {ι : Type} [Fintype ι] (ro : ℝ) (S : Finset (ι → ℂ)) (hro : 0 < ro)
    (hS : IsNormSeparated ro S) (φ ψ : ι → ℂ → ℝ) (hψ : ∀ v z, 0 ≤ ψ v z)
    (hφ : ∀ v z, 0 ≤ φ v z)
    (hint : ∀ v, Integrable (ψ v)) (hcmp : ∀ v D x, ‖x - D‖ < ro / 2 → φ v D ≤ ψ v x) :
    (∑ D ∈ S, ∏ v, φ v (D v)) * (π * (ro / 2) ^ 2) ^ Fintype.card ι ≤ ∏ v, ∫ x, ψ v x := by
  have hF : Integrable (fun x : ι → ℂ => ∏ v, ψ v (x v)) := Integrable.fintype_prod hint
  rw [← integral_fintype_prod_volume_eq_prod (fun v => ψ v), Finset.sum_mul]
  calc ∑ D ∈ S, (∏ v, φ v (D v)) * (π * (ro / 2) ^ 2) ^ Fintype.card ι
      ≤ ∑ D ∈ S, ∫ x in CenteredPolydisc ro D, ∏ v, ψ v (x v) := by
        apply Finset.sum_le_sum
        intro D _
        have h1 : ∫ _x in CenteredPolydisc ro D, (∏ v, φ v (D v)) =
            (∏ v, φ v (D v)) * (π * (ro / 2) ^ 2) ^ Fintype.card ι := by
          rw [setIntegral_const, volume_real_E1polydisc_eq_pi_mul_sq_pow_card ro hro, smul_eq_mul, mul_comm]
        rw [← h1]
        apply setIntegral_mono_on _ hF.integrableOn (measurableSet_E1polydisc ro D)
        · intro x hx
          exact Finset.prod_le_prod (fun v _ => hφ v _) (fun v _ => hcmp v _ _ (hx v))
        · rw [integrableOn_const_iff]
          right
          have : (volume : Measure (ι → ℂ)) (CenteredPolydisc ro D) ≠ ⊤ := by
            rw [polydisc_eq_pi_ball, volume_pi_pi]
            exact ENNReal.prod_ne_top fun v _ => measure_ball_lt_top.ne
          exact this.lt_top
    _ = ∫ x in ⋃ D ∈ S, CenteredPolydisc ro D, ∏ v, ψ v (x v) := by
        rw [integral_biUnion_finset S (fun D _ => measurableSet_E1polydisc ro D) _ (fun D _ => hF.integrableOn)]
        intro D hD D' hD' hne
        exact hd ι ro D D' hro hne (hS D hD D' hD' hne)
    _ ≤ ∫ x : ι → ℂ, ∏ v, ψ v (x v) :=
        setIntegral_le_integral hF (Filter.Eventually.of_forall fun x =>
          Finset.prod_nonneg fun v _ => hψ v _)

/- English proof (translation)
Introduce `ι _ ro S hro hro1 hS`. Establish `h` using `separated_sum_le_prod_integrals hd ro S hro hS (fun _ z => ((1 + ‖z‖ ^ 2) ^ 2)⁻¹) (fun _ x => 4 * ((1 + ‖x‖ ^ 2) ^ 2)⁻¹) (fun _ _ => by positivity) (fun _ _ => by positivity) (fun _ => hi.1.const_mul 4) ?_`. Simplify using `only [integral_const_mul, hi.2, Finset.prod_const, Finset.card_univ] at h`. Establish `hV : 0 < (π * (ro / 2) ^ 2) ^ Fintype.card ι` using `by positivity`. Rewrite `h` using `[← le_div_iff₀ hV, ← div_pow]`.

Establish `: 4 * π / (π * (ro / 2) ^ 2) = 16 / ro ^ 2` using `by field_simp; ring`. Rewrite `h` using `[this]`. Then use the resulting hypothesis. Introduce `_ D x hx`. Establish `h1 : ‖x‖ ≤ ‖D‖ + 1 / 2`. Use `norm_le_norm_add_norm_sub' x D` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : 1 + ‖x‖ ^ 2 ≤ 2 * (1 + ‖D‖ ^ 2)`. Use polynomial arithmetic with `[norm_nonneg x, norm_nonneg D, sq_nonneg (‖D‖ - 1 / 2)]`. Establish `h3 : (1 + ‖x‖ ^ 2) ^ 2 ≤ 4 * (1 + ‖D‖ ^ 2) ^ 2`. Combine the equalities or inequalities in the displayed calculation.

Use `show ((1 + ‖D‖ ^ 2) ^ 2)⁻¹ ≤ 4 * ((1 + ‖x‖ ^ 2) ^ 2)⁻¹`. Rewrite using `[← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem separated_set_sum_bound_of_disjoint_integral (hd : SeparatedPolydiscsDisjoint) (hi : InversePowerIntegralPi) : SeparatedSetSumBound := by
  intro ι _ ro S hro hro1 hS
  have h := separated_sum_le_prod_integrals hd ro S hro hS (fun _ z => ((1 + ‖z‖ ^ 2) ^ 2)⁻¹)
    (fun _ x => 4 * ((1 + ‖x‖ ^ 2) ^ 2)⁻¹)
    (fun _ _ => by positivity) (fun _ _ => by positivity) (fun _ => hi.1.const_mul 4) ?_
  · simp only [integral_const_mul, hi.2, Finset.prod_const, Finset.card_univ] at h
    have hV : 0 < (π * (ro / 2) ^ 2) ^ Fintype.card ι := by positivity
    rw [← le_div_iff₀ hV, ← div_pow] at h
    have : 4 * π / (π * (ro / 2) ^ 2) = 16 / ro ^ 2 := by field_simp; ring
    rwa [this] at h
  · intro _ D x hx
    have h1 : ‖x‖ ≤ ‖D‖ + 1 / 2 := by
      have := norm_le_norm_add_norm_sub' x D
      linarith
    have h2 : 1 + ‖x‖ ^ 2 ≤ 2 * (1 + ‖D‖ ^ 2) := by
      nlinarith [norm_nonneg x, norm_nonneg D, sq_nonneg (‖D‖ - 1 / 2)]
    have h3 : (1 + ‖x‖ ^ 2) ^ 2 ≤ 4 * (1 + ‖D‖ ^ 2) ^ 2 := by
      calc (1 + ‖x‖ ^ 2) ^ 2 ≤ (2 * (1 + ‖D‖ ^ 2)) ^ 2 := by gcongr
        _ = 4 * (1 + ‖D‖ ^ 2) ^ 2 := by ring
    show ((1 + ‖D‖ ^ 2) ^ 2)⁻¹ ≤ 4 * ((1 + ‖x‖ ^ 2) ^ 2)⁻¹
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith

/- English proof (translation)
Unfold `TruncationCutoff`. Use `split_ifs`. Conclude with `zero_le_one`. Conclude with `le_min zero_le_one (Real.rpow_nonneg (div_nonneg hL ht) K)`.
-/
lemma E3cut_nonneg_of_nonneg_of_nonneg (K L t : ℝ) (hL : 0 ≤ L) (ht : 0 ≤ t) : 0 ≤ TruncationCutoff K L t := by
  unfold TruncationCutoff
  split_ifs
  · exact zero_le_one
  · exact le_min zero_le_one (Real.rpow_nonneg (div_nonneg hL ht) K)

/- English proof (translation)
Unfold `TruncationCutoff`. Use `split_ifs`. Conclude with `le_rfl`. Conclude with `min_le_left _ _`.
-/
lemma E3cut_le_one (K L t : ℝ) : TruncationCutoff K L t ≤ 1 := by
  unfold TruncationCutoff
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/- English proof (translation)
Establish `hL1 : ro ≤ max ro abelian₂` using `le_max_left _ _`. Establish `hL2 : abelian₂ ≤ max ro abelian₂` using `le_max_right _ _`. Use `set L := max ro abelian₂ with hL`. Establish `hL0 : 0 < L` using `lt_of_lt_of_le hro hL1`. Distinguish the cases in `hx0 : ‖x‖ = 0`.

Establish `: TruncationCutoff K (3 / 2 * L) ‖x‖ = 1` using `by simp [TruncationCutoff, hx0]`. Rewrite using `[this]`. Conclude with `E3cut_le_one _ _ _`. Establish `hxpos : 0 < ‖x‖` using `lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx0)`. Establish `: TruncationCutoff K (3 / 2 * L) ‖x‖ = min 1 ((3 / 2 * L / ‖x‖) ^ K)` using `by simp [TruncationCutoff, hx0]`.

Rewrite using `[this]`. Apply `le_min (E3cut_le_one _ _ _)` to reduce the goal to its premises. Distinguish the cases in `hc : ‖x‖ ≤ 3 / 2 * L`. Establish `h1 : 1 ≤ 3 / 2 * L / ‖x‖` using `by rwa [le_div_iff₀ hxpos, one_mul]`. Conclude with `le_trans (E3cut_le_one _ _ _) (Real.one_le_rpow h1 hK)`.

Rewrite `hc` using `[not_le]`. Establish `h1 : ‖x‖ ≤ ‖D‖ + ‖x - D‖` using `norm_le_norm_add_norm_sub' x D`. Establish `hD : ‖x‖ ≤ 3 / 2 * ‖D‖` using `by linarith`. Establish `hDpos : 0 < ‖D‖` using `by linarith`. Establish `: TruncationCutoff K abelian₂ ‖D‖ = min 1 ((abelian₂ / ‖D‖) ^ K)` using `by simp [TruncationCutoff, hDpos.ne']`.

Rewrite using `[this]`. Apply `le_trans (min_le_right _ _)` to reduce the goal to its premises. Apply `Real.rpow_le_rpow (by positivity) _ hK` to reduce the goal to its premises. Rewrite using `[div_le_div_iff₀ hDpos hxpos]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma cutoff_comparison_nearby (K ro abelian₂ : ℝ) (hK : 0 ≤ K) (hro : 0 < ro) (hLam : 0 < abelian₂) (D x : ℂ)
    (hx : ‖x - D‖ < ro / 2) :
    TruncationCutoff K abelian₂ ‖D‖ ≤ TruncationCutoff K (3 / 2 * max ro abelian₂) ‖x‖ := by
  have hL1 : ro ≤ max ro abelian₂ := le_max_left _ _
  have hL2 : abelian₂ ≤ max ro abelian₂ := le_max_right _ _
  set L := max ro abelian₂ with hL
  have hL0 : 0 < L := lt_of_lt_of_le hro hL1
  by_cases hx0 : ‖x‖ = 0
  · have : TruncationCutoff K (3 / 2 * L) ‖x‖ = 1 := by simp [TruncationCutoff, hx0]
    rw [this]; exact E3cut_le_one _ _ _
  · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx0)
    have : TruncationCutoff K (3 / 2 * L) ‖x‖ = min 1 ((3 / 2 * L / ‖x‖) ^ K) := by simp [TruncationCutoff, hx0]
    rw [this]
    apply le_min (E3cut_le_one _ _ _)
    by_cases hc : ‖x‖ ≤ 3 / 2 * L
    · have h1 : 1 ≤ 3 / 2 * L / ‖x‖ := by rwa [le_div_iff₀ hxpos, one_mul]
      exact le_trans (E3cut_le_one _ _ _) (Real.one_le_rpow h1 hK)
    · rw [not_le] at hc
      have h1 : ‖x‖ ≤ ‖D‖ + ‖x - D‖ := norm_le_norm_add_norm_sub' x D
      have hD : ‖x‖ ≤ 3 / 2 * ‖D‖ := by linarith
      have hDpos : 0 < ‖D‖ := by linarith
      have : TruncationCutoff K abelian₂ ‖D‖ = min 1 ((abelian₂ / ‖D‖) ^ K) := by simp [TruncationCutoff, hDpos.ne']
      rw [this]
      apply le_trans (min_le_right _ _)
      apply Real.rpow_le_rpow (by positivity) _ hK
      rw [div_le_div_iff₀ hDpos hxpos]
      calc abelian₂ * ‖x‖ ≤ L * (3 / 2 * ‖D‖) := by gcongr
        _ = 3 / 2 * L * ‖D‖ := by ring

/- English proof (translation)
Introduce `ι _ ro K abelian₂ S hro hK hLam hS`. Establish `hLpos : ∀ v, 0 < 3 / 2 * max ro (abelian₂ v)` using `fun v => by`. Establish `: 0 < max ro (abelian₂ v)` using `lt_of_lt_of_le hro (le_max_left _ _)`. Check the signs of the components of the expression. Establish `h` using `separated_sum_le_prod_integrals hd ro S hro hS (fun v z => TruncationCutoff K (abelian₂ v) ‖z‖) (fun v x => TruncationCutoff K (3 / 2 * max ro (abelian₂ v)) ‖x‖) (fun v z => E3cut_nonneg_of_nonneg_of_nonneg _ _ _ (hLpos v).le (norm_nonneg z)) (fun v z => E3cut_nonneg_of_nonneg_of …`.

Establish `hV : 0 < (π * (ro / 2) ^ 2) ^ Fintype.card ι` using `by positivity`. Rewrite `h` using `[← le_div_iff₀ hV]`. Use `le_trans h ?_` and prove the remaining obligations. Rewrite using `[← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_div_distrib]`. Apply `Finset.prod_le_prod` to reduce the goal to its premises.

Introduce `v _`. Rewrite using `[(hi K _ hK (hLpos v)).2]`. Establish `: 0 < K - 2` using `by linarith`. Use `hLpos v` as an intermediate fact. Check the signs of the components of the expression.

Introduce `v _`. Rewrite using `[(hi K _ hK (hLpos v)).2]`. Establish `hK2 : 0 < K - 2` using `by linarith`. Establish `hpw : (9 / 4 : ℝ) ≤ (3 / 2 : ℝ) ^ K`. Establish `: ((3 / 2 : ℝ)) ^ (2 : ℝ) ≤ (3 / 2 : ℝ) ^ K` using `Real.rpow_le_rpow_of_exponent_le (by norm_num) hK.le`.

Establish `h2 : ((3 / 2 : ℝ)) ^ (2 : ℝ) = 9 / 4`. Rewrite using `[Real.rpow_two]`. Evaluate the numerical expressions. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e1 : π * (3 / 2 * max ro (abelian₂ v)) ^ 2 * (K / (K - 2)) / (π * (ro / 2) ^ 2) = 4 * (9 / 4) * (K / (K - 2)) * (max ro (abelian₂ v)) ^ 2 / ro ^ 2` using `by field_simp; ring`.

Rewrite using `[e1]`. Apply the tactic sequence `have hk : 0 ≤ K / (K - 2) := by apply div_nonneg <;> linarith`. Use `gcongr`.
-/
theorem separated_cutoff_sum_of_disjoint_polydiscs (hd : SeparatedPolydiscsDisjoint) (hi : CutoffIntegralFormula) : SeparatedCutoffSum := by
  intro ι _ ro K abelian₂ S hro hK hLam hS
  have hLpos : ∀ v, 0 < 3 / 2 * max ro (abelian₂ v) := fun v => by
    have : 0 < max ro (abelian₂ v) := lt_of_lt_of_le hro (le_max_left _ _)
    positivity
  have h := separated_sum_le_prod_integrals hd ro S hro hS (fun v z => TruncationCutoff K (abelian₂ v) ‖z‖)
    (fun v x => TruncationCutoff K (3 / 2 * max ro (abelian₂ v)) ‖x‖)
    (fun v z => E3cut_nonneg_of_nonneg_of_nonneg _ _ _ (hLpos v).le (norm_nonneg z))
    (fun v z => E3cut_nonneg_of_nonneg_of_nonneg _ _ _ (hLam v).le (norm_nonneg z))
    (fun v => (hi K _ hK (hLpos v)).1)
    (fun v D x hx => cutoff_comparison_nearby K ro (abelian₂ v) (by linarith) hro (hLam v) D x hx)
  have hV : 0 < (π * (ro / 2) ^ 2) ^ Fintype.card ι := by positivity
  rw [← le_div_iff₀ hV] at h
  refine le_trans h ?_
  rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_div_distrib]
  apply Finset.prod_le_prod
  · intro v _
    rw [(hi K _ hK (hLpos v)).2]
    have : 0 < K - 2 := by linarith
    have := hLpos v
    positivity
  · intro v _
    rw [(hi K _ hK (hLpos v)).2]
    have hK2 : 0 < K - 2 := by linarith
    have hpw : (9 / 4 : ℝ) ≤ (3 / 2 : ℝ) ^ K := by
      have : ((3 / 2 : ℝ)) ^ (2 : ℝ) ≤ (3 / 2 : ℝ) ^ K :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hK.le
      have h2 : ((3 / 2 : ℝ)) ^ (2 : ℝ) = 9 / 4 := by
        rw [Real.rpow_two]; norm_num
      linarith
    have e1 : π * (3 / 2 * max ro (abelian₂ v)) ^ 2 * (K / (K - 2)) / (π * (ro / 2) ^ 2) =
        4 * (9 / 4) * (K / (K - 2)) * (max ro (abelian₂ v)) ^ 2 / ro ^ 2 := by
      field_simp; ring
    rw [e1]
    have hk : 0 ≤ K / (K - 2) := by apply div_nonneg <;> linarith
    gcongr

/- English proof (translation)
Introduce `K abelian₂ hK hLam S`. Set `f : GaussianInt → (Unit → ℂ)` to `fun a _ => (abelian₂ : ℂ) * GaussianInt.toComplex a`. Establish `hf : Function.Injective f`. Introduce `a b hab`. Establish `h0` using `congrFun hab ()`.

Simplify using `only [f] at h0`. Establish `hL : (abelian₂ : ℂ) ≠ 0` using `by exact_mod_cast hLam.ne'`. Conclude with `GaussianInt.toComplex_injective (mul_left_cancel₀ hL h0)`. Establish `hsep : IsNormSeparated abelian₂ (S.image f)`. Introduce `D hD D' hD' hne`.

Take `⟨a, _, rfl⟩` from `Finset.mem_image.1 hD`. Take `⟨b, _, rfl⟩` from `Finset.mem_image.1 hD'`. Establish `hab : a - b ≠ 0` using `fun h0 => hne (by rw [sub_eq_zero.1 h0])`. Simplify using `only [Fintype.card_unit, pow_one, Finset.univ_unique, Finset.prod_singleton, f]`. Rewrite using `[← mul_sub, ← GaussianInt.toComplex_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hLam.le]`.

Establish `h1 : (1 : ℝ) ≤ ‖GaussianInt.toComplex (a - b)‖`. Establish `hn : (1 : ℤ) ≤ (a - b).norm` using `GaussianInt.norm_pos.2 hab`. Establish `h2 : (1 : ℝ) ≤ Complex.normSq (GaussianInt.toComplex (a - b))`. Rewrite using `[← GaussianInt.intCast_real_norm]`. Conclude with `hn` after adjusting the coercions.

Rewrite `h2` using `[Complex.normSq_eq_norm_sq]`. Use polynomial arithmetic with `[norm_nonneg (GaussianInt.toComplex (a - b))]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h3` using `h Unit abelian₂ K (fun _ => abelian₂) (S.image f) hLam hK (fun _ => hLam) hsep`. Rewrite `h3` using `[Finset.sum_image (fun a _ b _ hab => hf hab)]`.

Simplify using `only [Finset.univ_unique, Finset.prod_singleton, max_self, f] at h3`. Establish `e : 4 * (3 / 2 : ℝ) ^ K * (K / (K - 2)) * abelian₂ ^ 2 / abelian₂ ^ 2 = 4 * (3 / 2 : ℝ) ^ K * (K / (K - 2))` using `by field_simp`. Rewrite `h3` using `[e]`. Then use the resulting hypothesis.
-/
theorem gaussian_lattice_cutoff_sum_of_separated_cutoff_sum (h : SeparatedCutoffSum) : GaussianLatticeCutoffSum := by
  intro K abelian₂ hK hLam S
  classical
  let f : GaussianInt → (Unit → ℂ) := fun a _ => (abelian₂ : ℂ) * GaussianInt.toComplex a
  have hf : Function.Injective f := by
    intro a b hab
    have h0 := congrFun hab ()
    simp only [f] at h0
    have hL : (abelian₂ : ℂ) ≠ 0 := by exact_mod_cast hLam.ne'
    exact GaussianInt.toComplex_injective (mul_left_cancel₀ hL h0)
  have hsep : IsNormSeparated abelian₂ (S.image f) := by
    intro D hD D' hD' hne
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hD
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hD'
    have hab : a - b ≠ 0 := fun h0 => hne (by rw [sub_eq_zero.1 h0])
    simp only [Fintype.card_unit, pow_one, Finset.univ_unique, Finset.prod_singleton, f]
    rw [← mul_sub, ← GaussianInt.toComplex_sub, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hLam.le]
    have h1 : (1 : ℝ) ≤ ‖GaussianInt.toComplex (a - b)‖ := by
      have hn : (1 : ℤ) ≤ (a - b).norm := GaussianInt.norm_pos.2 hab
      have h2 : (1 : ℝ) ≤ Complex.normSq (GaussianInt.toComplex (a - b)) := by
        rw [← GaussianInt.intCast_real_norm]; exact_mod_cast hn
      rw [Complex.normSq_eq_norm_sq] at h2
      nlinarith [norm_nonneg (GaussianInt.toComplex (a - b))]
    nlinarith
  have h3 := h Unit abelian₂ K (fun _ => abelian₂) (S.image f) hLam hK (fun _ => hLam) hsep
  rw [Finset.sum_image (fun a _ b _ hab => hf hab)] at h3
  simp only [Finset.univ_unique, Finset.prod_singleton, max_self, f] at h3
  have e : 4 * (3 / 2 : ℝ) ^ K * (K / (K - 2)) * abelian₂ ^ 2 / abelian₂ ^ 2 =
      4 * (3 / 2 : ℝ) ^ K * (K / (K - 2)) := by field_simp
  rwa [e] at h3

end G2

section G3
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms

/- English proof (translation)
Use `set J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) x * aa⁻¹ with hJ`. Establish `hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) x ≤ aa` using `(FractionalIdeal.spanSingleton_le_iff_mem).2 hx`. Establish `hJ1 : J ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hJ]`.

Conclude with `mul_le_mul_left hle _`. Use `_ = 1 := mul_inv_cancel₀ haa`. Take `⟨I, hI⟩` from `FractionalIdeal.le_one_iff_exists_coeIdeal.1 hJ1`. Establish `hJ0 : J ≠ 0`. Rewrite using `[hJ]`.

Conclude with `mul_ne_zero (by simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hx0) (inv_ne_zero haa)`. Establish `hI0 : I ≠ ⊥`. Introduce and unpack `rfl`. Apply `hJ0` to reduce the goal to its premises. Rewrite using `[← hI]`.

Simplify using the standard rewrite rules. Establish `hN : (1 : ℚ) ≤ FractionalIdeal.absNorm J`. Rewrite using `[← hI, FractionalIdeal.coeIdeal_absNorm]`. Establish `: Ideal.absNorm I ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`.

Conclude with `hI0`. Conclude with `Nat.one_le_iff_ne_zero.2 this` after adjusting the coercions. Establish `hprod : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) x = J * aa`. Rewrite using `[hJ, mul_assoc, inv_mul_cancel₀ haa, mul_one]`. Rewrite using `[← FractionalIdeal.absNorm_span_singleton (R := 𝓞 E), hprod, map_mul]`.

Conclude with `le_mul_of_one_le_left (FractionalIdeal.absNorm_nonneg _) hN`.
-/
lemma absNorm_le_abs_norm_of_mem' (E : Type) [Field E] [NumberField E]
    (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (haa : aa ≠ 0) (x : E) (hx : x ∈ aa) (hx0 : x ≠ 0) :
    FractionalIdeal.absNorm aa ≤ |Algebra.norm ℚ x| := by
  set J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E :=
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) x * aa⁻¹ with hJ
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) x ≤ aa :=
    (FractionalIdeal.spanSingleton_le_iff_mem).2 hx
  have hJ1 : J ≤ 1 := by
    calc J ≤ aa * aa⁻¹ := by
            rw [hJ]; exact mul_le_mul_left hle _
      _ = 1 := mul_inv_cancel₀ haa
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hJ1
  have hJ0 : J ≠ 0 := by
    rw [hJ]
    exact mul_ne_zero (by simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hx0) (inv_ne_zero haa)
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    apply hJ0; rw [← hI]; simp
  have hN : (1 : ℚ) ≤ FractionalIdeal.absNorm J := by
    rw [← hI, FractionalIdeal.coeIdeal_absNorm]
    have : Ideal.absNorm I ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hI0
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hprod : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) x = J * aa := by
    rw [hJ, mul_assoc, inv_mul_cancel₀ haa, mul_one]
  rw [← FractionalIdeal.absNorm_span_singleton (R := 𝓞 E), hprod, map_mul]
  exact le_mul_of_one_le_left (FractionalIdeal.absNorm_nonneg _) hN

/- English proof (translation)
Introduce `E _ _ _ aa haa x hx hx0`. Establish `h1` using `absNorm_le_abs_norm_of_mem' E aa haa x hx hx0`. Establish `h2 : (∏ w : InfinitePlace E, w x) ^ 2 = ((|Algebra.norm ℚ x| : ℚ) : ℝ)`. Rewrite using `[← InfinitePlace.prod_eq_abs_norm, ← Finset.prod_pow]`. Conclude with `Finset.prod_congr rfl fun w _ => by rw [IsTotallyComplex.mult_eq]`.

Establish `h3 : (0 : ℝ) ≤ ∏ w : InfinitePlace E, w x` using `Finset.prod_nonneg fun w _ => apply_nonneg w x`. Rewrite using `[← Real.sqrt_sq h3, h2]`. Conclude with `Real.sqrt_le_sqrt (by exact_mod_cast h1)`.
-/
theorem ideal_norm_product_lower_bound : Formalism.HermitianLatticeCounting.ExpansionTerms.IdealNormProductLowerBound := by
  intro E _ _ _ aa haa x hx hx0
  have h1 := absNorm_le_abs_norm_of_mem' E aa haa x hx hx0
  have h2 : (∏ w : InfinitePlace E, w x) ^ 2 = ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
    rw [← InfinitePlace.prod_eq_abs_norm, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun w _ => by rw [IsTotallyComplex.mult_eq]
  have h3 : (0 : ℝ) ≤ ∏ w : InfinitePlace E, w x := Finset.prod_nonneg fun w _ => apply_nonneg w x
  rw [← Real.sqrt_sq h3, h2]
  exact Real.sqrt_le_sqrt (by exact_mod_cast h1)

noncomputable def infinitePlaceEmbedding (E : Type) [Field E] (x : E) : InfinitePlace E → ℂ := fun w => w.embedding x

/- English proof (translation)
The claim follows from `InfinitePlace.norm_embedding_eq w x`.
-/
lemma norm_placeEmbedding (E : Type) [Field E] (x : E) (w : InfinitePlace E) : ‖infinitePlaceEmbedding E x w‖ = w x :=
  InfinitePlace.norm_embedding_eq w x

/- English proof (translation)
Rewrite using `[← InfinitePlace.norm_embedding_eq w (x - y), map_sub]`. Both sides reduce to the same expression.
-/
lemma norm_placeEmbedding_sub (E : Type) [Field E] (x y : E) (w : InfinitePlace E) :
    ‖infinitePlaceEmbedding E x w - infinitePlaceEmbedding E y w‖ = w (x - y) := by
  rw [← InfinitePlace.norm_embedding_eq w (x - y), map_sub]; rfl

/- English proof (translation)
Introduce `x y h`. Take `⟨w⟩` from `(inferInstance : Nonempty (InfinitePlace E))`. Conclude with `w.embedding.injective (congrFun h w)`.
-/
lemma placeEmbedding_injective (E : Type) [Field E] [NumberField E] : Function.Injective (infinitePlaceEmbedding E) := by
  intro x y h
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  exact w.embedding.injective (congrFun h w)

noncomputable def idealRadius (E : Type) [Field E] [NumberField E]
    (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℝ :=
  (FractionalIdeal.absNorm aa : ℝ) ^ (1 / (2 * (Fintype.card (InfinitePlace E) : ℝ)))

/- English proof (translation)
Establish `h0 : FractionalIdeal.absNorm aa ≠ 0`. Rewrite using `[Ne, FractionalIdeal.absNorm_eq_zero_iff]`. Conclude with `haa`. Conclude with `lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg aa) (Ne.symm h0)` after adjusting the coercions.
-/
lemma absNorm_pos_of_ne_zero (E : Type) [Field E] [NumberField E]
    (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (haa : aa ≠ 0) :
    (0 : ℝ) < (FractionalIdeal.absNorm aa : ℝ) := by
  have h0 : FractionalIdeal.absNorm aa ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact haa
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg aa) (Ne.symm h0)

/- English proof (translation)
The claim follows from `Real.rpow_pos_of_pos (absNorm_pos_of_ne_zero E aa haa) _`.
-/
lemma idealRadius_pos (E : Type) [Field E] [NumberField E]
    (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (haa : aa ≠ 0) : 0 < idealRadius E aa :=
  Real.rpow_pos_of_pos (absNorm_pos_of_ne_zero E aa haa) _

/- English proof (translation)
Conclude with `Fintype.card_pos` after adjusting the coercions.
-/
lemma card_infinite_places_pos (E : Type) [Field E] [NumberField E] :
    (0 : ℝ) < (Fintype.card (InfinitePlace E) : ℝ) := by
  exact_mod_cast Fintype.card_pos

/- English proof (translation)
Establish `hp` using `absNorm_pos_of_ne_zero E aa haa`. Establish `hc` using `card_infinite_places_pos E`. Rewrite using `[← pow_mul, idealRadius, ← Real.rpow_natCast, ← Real.rpow_mul hp.le]`. Establish `: 1 / (2 * (Fintype.card (InfinitePlace E) : ℝ)) * ((2 * Fintype.card (InfinitePlace E) : ℕ) : ℝ) = 1` using `by push_cast; field_simp`. Rewrite using `[this, Real.rpow_one]`.
-/
lemma radius_sq_pow_card_places (E : Type) [Field E] [NumberField E]
    (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (haa : aa ≠ 0) :
    (idealRadius E aa ^ 2) ^ Fintype.card (InfinitePlace E) = (FractionalIdeal.absNorm aa : ℝ) := by
  have hp := absNorm_pos_of_ne_zero E aa haa
  have hc := card_infinite_places_pos E
  rw [← pow_mul, idealRadius, ← Real.rpow_natCast, ← Real.rpow_mul hp.le]
  have : 1 / (2 * (Fintype.card (InfinitePlace E) : ℝ)) * ((2 * Fintype.card (InfinitePlace E) : ℕ) : ℝ) = 1 := by
    push_cast; field_simp
  rw [this, Real.rpow_one]

/- English proof (translation)
Establish `h` using `radius_sq_pow_card_places E aa haa`. Establish `h0 : 0 ≤ idealRadius E aa ^ Fintype.card (InfinitePlace E)` using `(pow_pos (idealRadius_pos E aa haa) _).le`. Rewrite using `[← h, ← pow_mul, mul_comm, pow_mul, Real.sqrt_sq h0]`.
-/
lemma radius_pow_card_places (E : Type) [Field E] [NumberField E]
    (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (haa : aa ≠ 0) :
    idealRadius E aa ^ Fintype.card (InfinitePlace E) = √(FractionalIdeal.absNorm aa : ℝ) := by
  have h := radius_sq_pow_card_places E aa haa
  have h0 : 0 ≤ idealRadius E aa ^ Fintype.card (InfinitePlace E) := (pow_pos (idealRadius_pos E aa haa) _).le
  rw [← h, ← pow_mul, mul_comm, pow_mul, Real.sqrt_sq h0]

open Classical in
/- English proof (translation)
Introduce `D hD D' hD' hne`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 hD`. Take `⟨y, hy, rfl⟩` from `Finset.mem_image.1 hD'`. Establish `hxy : x - y ≠ 0` using `fun h => hne (by rw [sub_eq_zero.1 h])`. Establish `hmem : x - y ∈ aa`.

Use `Submodule.sub_mem (aa : Submodule (𝓞 E) E) (hS x hx) (hS y hy)` as an intermediate fact. Conclude with `this`. Rewrite using `[radius_pow_card_places E aa haa]`. Repeatedly rewrite using `[norm_placeEmbedding_sub]`. Conclude with `hn E aa haa (x - y) hmem hxy`.
-/
lemma embedded_ideal_points_separated (hn : IdealNormProductLowerBound) (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (haa : aa ≠ 0) (S : Finset E)
    (hS : ∀ D ∈ S, D ∈ aa) : IsNormSeparated (idealRadius E aa) (S.image (infinitePlaceEmbedding E)) := by
  intro D hD D' hD' hne
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hD
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hD'
  have hxy : x - y ≠ 0 := fun h => hne (by rw [sub_eq_zero.1 h])
  have hmem : x - y ∈ aa := by
    have := Submodule.sub_mem (aa : Submodule (𝓞 E) E) (hS x hx) (hS y hy)
    exact this
  rw [radius_pow_card_places E aa haa]
  simp_rw [norm_placeEmbedding_sub]
  exact hn E aa haa (x - y) hmem hxy

open Classical in
/- English proof (translation)
Introduce `E _ _ _ aa haa h1 S hS`. Establish `hp` using `absNorm_pos_of_ne_zero E aa haa`. Establish `hro1 : idealRadius E aa ≤ 1` using `Real.rpow_le_one hp.le h1 (by have := card_infinite_places_pos E; positivity)`. Establish `h` using `hs (InfinitePlace E) (idealRadius E aa) (S.image (infinitePlaceEmbedding E)) (idealRadius_pos E aa haa) hro1 (embedded_ideal_points_separated hn E aa haa S hS)`. Rewrite `h` using `[Finset.sum_image (fun x _ y _ hxy => placeEmbedding_injective E hxy), div_pow, radius_sq_pow_card_places E aa haa]`.

Simplify `h` using `only [norm_placeEmbedding]`.
-/
theorem ideal_inverse_power_sum_of_norm_separated (hn : IdealNormProductLowerBound) (hs : SeparatedSetSumBound) : Formalism.HermitianLatticeCounting.ExpansionTerms.IdealInversePowerSum := by
  intro E _ _ _ aa haa h1 S hS
  have hp := absNorm_pos_of_ne_zero E aa haa
  have hro1 : idealRadius E aa ≤ 1 := Real.rpow_le_one hp.le h1 (by have := card_infinite_places_pos E; positivity)
  have h := hs (InfinitePlace E) (idealRadius E aa) (S.image (infinitePlaceEmbedding E)) (idealRadius_pos E aa haa) hro1
    (embedded_ideal_points_separated hn E aa haa S hS)
  rw [Finset.sum_image (fun x _ y _ hxy => placeEmbedding_injective E hxy), div_pow, radius_sq_pow_card_places E aa haa] at h
  simpa only [norm_placeEmbedding] using h

end G3

section G4
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms

/- English proof (translation)
Establish `h` using `Real.add_one_le_exp (x / Real.exp 1 - 1)`. Establish `he : 0 < Real.exp 1` using `Real.exp_pos 1`. Rewrite `h` using `[Real.exp_sub, le_div_iff₀ he]`. Establish `h2 : (x / Real.exp 1 - 1 + 1) * Real.exp 1 = x`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma le_exp_div_e (x : ℝ) : x ≤ Real.exp (x / Real.exp 1) := by
  have h := Real.add_one_le_exp (x / Real.exp 1 - 1)
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  rw [Real.exp_sub, le_div_iff₀ he] at h
  have h2 : (x / Real.exp 1 - 1 + 1) * Real.exp 1 = x := by
    field_simp
    ring
  linarith

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a l ih`. Rewrite using `[List.prod_cons, List.sum_cons]`. Rewrite using `[Nat.cast_mul, Nat.cast_add, add_div, Real.exp_add]`.

Conclude with `mul_le_mul (le_exp_div_e a) ih (Nat.cast_nonneg _) (Real.exp_pos _).le`.
-/
lemma list_prod_le_exp_sum_div_e (l : List ℕ) : ((l.prod : ℕ) : ℝ) ≤ Real.exp (((l.sum : ℕ) : ℝ) / Real.exp 1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons, List.sum_cons]
    rw [Nat.cast_mul, Nat.cast_add, add_div, Real.exp_add]
    exact mul_le_mul (le_exp_div_e a) ih (Nat.cast_nonneg _) (Real.exp_pos _).le

/- English proof (translation)
Introduce `n c`. Establish `h` using `list_prod_le_exp_sum_div_e c.blocks`. Rewrite `h` using `[c.blocks_sum]`. Then use the resulting hypothesis.
-/
theorem composition_block_prod_bound : Formalism.HermitianLatticeCounting.ExpansionTerms.CompositionBlockProdBound := by
  intro n c
  have h := list_prod_le_exp_sum_div_e c.blocks
  rwa [c.blocks_sum] at h

/- English proof (translation)
Unfold `ParitySign`. Use `push_cast`. Conclude with `pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)`.
-/
lemma E5sign_intCast_ne_zero {F : Type} [Field F] (k : ℕ) : ((ParitySign k : ℤ) : F) ≠ 0 := by
  unfold ParitySign
  push_cast
  exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)

/- English proof (translation)
Establish `h : univ.filter (fun a' : Fin p => a' ≤ a) = insert a (univ.filter (fun a' : Fin p => a' < a))`. Use extensionality with `x`. Simplify using `[le_iff_lt_or_eq, or_comm]`. Unfold `IndexedMinorEntry`. Rewrite using `[h, Finset.prod_insert (by simp), mul_comm]`.
-/
lemma signed_minor_split {F : Type} [Field F] {p : ℕ} (s : Fin p → ℕ) (t : Fin p → F) (a : Fin p) :
    IndexedMinorEntry s t a = (∏ a' ∈ univ.filter (fun a' : Fin p => a' < a), ((ParitySign (s a') : ℤ) : F) * t a' ^ s a') *
      (((ParitySign (s a) : ℤ) : F) * t a ^ s a) := by
  have h : univ.filter (fun a' : Fin p => a' ≤ a) = insert a (univ.filter (fun a' : Fin p => a' < a)) := by
    ext x
    simp [le_iff_lt_or_eq, or_comm]
  unfold IndexedMinorEntry
  rw [h, Finset.prod_insert (by simp), mul_comm]

/- English proof (translation)
Introduce `a`. Proceed by induction on `a using WellFoundedLT.induction with`. Consider the case `_ a ih`. Establish `h1` using `h a`. Rewrite `h1` using `[signed_minor_split, signed_minor_split]`.

Establish `h2 : (∏ a' ∈ univ.filter (fun a' : Fin p => a' < a), ((ParitySign (s a') : ℤ) : F) * t a' ^ s a') = ∏ a' ∈ univ.filter (fun a' : Fin p => a' < a), ((ParitySign (s a') : ℤ) : F) * t0 a' ^ s a'`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `x hx`. Rewrite using `[ih x (by simpa using hx)]`. Rewrite `h1` using `[h2]`.

Establish `h3 : (∏ a' ∈ univ.filter (fun a' : Fin p => a' < a), ((ParitySign (s a') : ℤ) : F) * t0 a' ^ s a') ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun x _ => mul_ne_zero (E5sign_intCast_ne_zero _) (pow_ne_zero _ (h0 x))`. Conclude with `mul_left_cancel₀ (E5sign_intCast_ne_zero _) (mul_left_cancel₀ h3 h1)`.
-/
lemma pow_eq_of_signed_minors_eq {F : Type} [Field F] {p : ℕ} (s : Fin p → ℕ) (t t0 : Fin p → F)
    (h0 : ∀ a, t0 a ≠ 0) (h : ∀ a, IndexedMinorEntry s t a = IndexedMinorEntry s t0 a) :
    ∀ a, t a ^ s a = t0 a ^ s a := by
  intro a
  induction a using WellFoundedLT.induction with
  | _ a ih =>
    have h1 := h a
    rw [signed_minor_split, signed_minor_split] at h1
    have h2 : (∏ a' ∈ univ.filter (fun a' : Fin p => a' < a), ((ParitySign (s a') : ℤ) : F) * t a' ^ s a') =
        ∏ a' ∈ univ.filter (fun a' : Fin p => a' < a), ((ParitySign (s a') : ℤ) : F) * t0 a' ^ s a' := by
      apply Finset.prod_congr rfl
      intro x hx
      rw [ih x (by simpa using hx)]
    rw [h2] at h1
    have h3 : (∏ a' ∈ univ.filter (fun a' : Fin p => a' < a), ((ParitySign (s a') : ℤ) : F) * t0 a' ^ s a') ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun x _ => mul_ne_zero (E5sign_intCast_ne_zero _) (pow_ne_zero _ (h0 x))
    exact mul_left_cancel₀ (E5sign_intCast_ne_zero _) (mul_left_cancel₀ h3 h1)

/- English proof (translation)
Introduce `F _ p s d T hs hT`. Break down `T.eq_empty_or_nonempty with rfl | ⟨t0, ht0⟩` into its components or cases. Simplify using the standard rewrite rules. Establish `hsub : T ⊆ Fintype.piFinset (fun a => (Polynomial.nthRoots (s a) (t0 a ^ s a)).toFinset)`. Introduce `t ht`.

Rewrite using `[Fintype.mem_piFinset]`. Introduce `a`. Rewrite using `[Multiset.mem_toFinset, Polynomial.mem_nthRoots (hs a)]`. Conclude with `pow_eq_of_signed_minors_eq s t t0 (hT t0 ht0).1 (fun a => ((hT t ht).2 a).trans ((hT t0 ht0).2 a).symm) a`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem block_end_minor_fibre_finite' : Formalism.HermitianLatticeCounting.ExpansionTerms.BlockEndMinorFibreFinite := by
  classical
  intro F _ p s d T hs hT
  rcases T.eq_empty_or_nonempty with rfl | ⟨t0, ht0⟩
  · simp
  have hsub : T ⊆ Fintype.piFinset (fun a => (Polynomial.nthRoots (s a) (t0 a ^ s a)).toFinset) := by
    intro t ht
    rw [Fintype.mem_piFinset]
    intro a
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (hs a)]
    exact pow_eq_of_signed_minors_eq s t t0 (hT t0 ht0).1 (fun a => ((hT t ht).2 a).trans ((hT t0 ht0).2 a).symm) a
  calc T.card ≤ (Fintype.piFinset (fun a => (Polynomial.nthRoots (s a) (t0 a ^ s a)).toFinset)).card :=
        Finset.card_le_card hsub
    _ = ∏ a, ((Polynomial.nthRoots (s a) (t0 a ^ s a)).toFinset).card := Fintype.card_piFinset _
    _ ≤ ∏ a, s a := Finset.prod_le_prod' fun a _ =>
        (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)

def scalarPoint {E : Type} [Field E] (x : E) : Σ c : Composition (0 + 1), (Fin c.length → E) :=
  ⟨Composition.ones 1, fun _ => x⟩

end G4

section G5
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms

/- English proof (translation)
Establish `h1 : Real.exp (1 / Real.exp 1) ≤ 2`. Establish `he : (2 : ℝ) ≤ Real.exp 1`. Use `Real.add_one_le_exp (1 : ℝ)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : 1 / Real.exp 1 ≤ 1 / 2`.

Apply `one_div_le_one_div_of_le (by norm_num) he` to reduce the goal to its premises. Establish `h3 : Real.exp (1 / 2) ≤ 2`. Establish `h4 : Real.exp (1 / 2) ^ 2 = Real.exp 1`. Rewrite using `[← Real.exp_nat_mul]`. Evaluate the numerical expressions.

Establish `h5 : Real.exp 1 < 4`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use polynomial arithmetic with `[Real.exp_pos (1 / 2 : ℝ)]`. Conclude with `(Real.exp_le_exp.mpr h2).trans h3`.

Establish `h2 : Real.exp ((n : ℝ) / Real.exp 1) = Real.exp (1 / Real.exp 1) ^ n`. Rewrite using `[← Real.exp_nat_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`.

Conclude with `pow_le_pow_left₀ (Real.exp_pos _).le h1 n`.
-/
lemma exp_div_e_le_two_pow (n : ℕ) : Real.exp ((n : ℝ) / Real.exp 1) ≤ 2 ^ n := by
  have h1 : Real.exp (1 / Real.exp 1) ≤ 2 := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have h2 : 1 / Real.exp 1 ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num) he
    have h3 : Real.exp (1 / 2) ≤ 2 := by
      have h4 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]; norm_num
      have h5 : Real.exp 1 < 4 := by
        have := Real.exp_one_lt_d9; linarith
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    exact (Real.exp_le_exp.mpr h2).trans h3
  have h2 : Real.exp ((n : ℝ) / Real.exp 1) = Real.exp (1 / Real.exp 1) ^ n := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [h2]
  exact pow_le_pow_left₀ (Real.exp_pos _).le h1 n

/- English proof (translation)
Introduce `E _ _ _ r S hS`. Use `(h E r S hS).trans ?_` and prove the remaining obligations. Use `set f := Fintype.card (InfinitePlace E) with hf`. Establish `hf1 : 1 ≤ f` using `Fintype.card_pos`. Establish `h1 : Real.exp (((r : ℝ) + 1) / Real.exp 1) ≤ 2 ^ (r + 1)`.

Use `exp_div_e_le_two_pow (r + 1)` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Establish `h2 : (2 : ℝ) ^ r ≤ 2 ^ (r + 1)` using `pow_le_pow_right₀ (by norm_num) (by omega)`. Establish `h3 : (2 : ℝ) ^ (r + 1) * 2 ^ (r + 1) = 4 ^ (r + 1)`.

Rewrite using `[← mul_pow]`. Evaluate the numerical expressions. Establish `h4 : (4 : ℝ) ^ (r + 1) ≤ 4 ^ (f * (r + 1))` using `pow_le_pow_right₀ (by norm_num) (by nlinarith)`. Establish `h5 : (64 : ℝ) ^ (f * (r + 1)) = 4 ^ (f * (r + 1)) * 16 ^ (f * (r + 1))`. Rewrite using `[← mul_pow]`.

Evaluate the numerical expressions. Rewrite using `[h5]`. Apply `mul_le_mul_of_nonneg_right _ (by positivity)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
theorem blockMinorSumPowSixtyFour_of_blockMinorSumExplicit (h : BlockMinorSumExplicit) : BlockMinorSumPowSixtyFour := by
  intro E _ _ _ r S hS
  refine (h E r S hS).trans ?_
  set f := Fintype.card (InfinitePlace E) with hf
  have hf1 : 1 ≤ f := Fintype.card_pos
  have h1 : Real.exp (((r : ℝ) + 1) / Real.exp 1) ≤ 2 ^ (r + 1) := by
    have := exp_div_e_le_two_pow (r + 1); push_cast at this; exact this
  have h2 : (2 : ℝ) ^ r ≤ 2 ^ (r + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : (2 : ℝ) ^ (r + 1) * 2 ^ (r + 1) = 4 ^ (r + 1) := by
    rw [← mul_pow]; norm_num
  have h4 : (4 : ℝ) ^ (r + 1) ≤ 4 ^ (f * (r + 1)) :=
    pow_le_pow_right₀ (by norm_num) (by nlinarith)
  have h5 : (64 : ℝ) ^ (f * (r + 1)) = 4 ^ (f * (r + 1)) * 16 ^ (f * (r + 1)) := by
    rw [← mul_pow]; norm_num
  rw [h5]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc (2 : ℝ) ^ r * Real.exp (((r : ℝ) + 1) / Real.exp 1) ≤ 2 ^ (r + 1) * 2 ^ (r + 1) :=
        mul_le_mul h2 h1 (Real.exp_pos _).le (by positivity)
    _ = 4 ^ (r + 1) := h3
    _ ≤ _ := h4

/- English proof (translation)
Establish `h` using `hs E 1 one_ne_zero (by simp) T (by`. Introduce `D hD`. Rewrite using `[FractionalIdeal.mem_one_iff]`. Conclude with `⟨⟨D, hT D hD⟩, rfl⟩)`. Simplify using `using h`.
-/
lemma integral_points_weight_sum_le (hs : IdealInversePowerSum) (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    (T : Finset E) (hT : ∀ x ∈ T, IsIntegral ℤ x) :
    ∑ D ∈ T, ∏ w : InfinitePlace E, ((1 + (w D) ^ 2) ^ 2)⁻¹ ≤ 16 ^ Fintype.card (InfinitePlace E) := by
  have h := hs E 1 one_ne_zero (by simp) T (by
    intro D hD
    rw [FractionalIdeal.mem_one_iff]
    exact ⟨⟨D, hT D hD⟩, rfl⟩)
  simpa using h

/- English proof (translation)
Use `set φ : E → ℝ := fun x => ∏ w : InfinitePlace E, ((1 + (w x) ^ 2) ^ 2)⁻¹ with hφ`. Establish `hφ0 : ∀ x, 0 ≤ φ x` using `fun x => Finset.prod_nonneg fun w _ => by positivity`. Apply the tactic sequence `set m : (Fin p → E) → (Fin p → E) := fun t a => IndexedMinorEntry s t a with hm`. Use `set g : (Fin p → E) → ℝ := fun d => ∏ a, φ (d a) with hg`. Establish `hg0 : ∀ d, 0 ≤ g d` using `fun d => Finset.prod_nonneg fun a _ => hφ0 _`.

Apply the tactic sequence `have e1 : ∀ t, (∏ a : Fin p, ∏ w : InfinitePlace E, (1 + (w (IndexedMinorEntry s t a)) ^ 2) ^ 2)⁻¹ = g (m t) := by`. Introduce `t`. Simplify using `only [hg, hφ, hm, Finset.prod_inv_distrib]`. Repeatedly rewrite using `[e1]`. Establish `hne : ∀ t ∈ T, ∀ a, t a ≠ 0`.

Introduce `t ht a h0`. Apply `(hT t ht a).2` to reduce the goal to its premises. Unfold `IndexedMinorEntry`. Apply `Finset.prod_eq_zero (i := a) (by simp)` to reduce the goal to its premises. Rewrite using `[h0, zero_pow (by have := hs1 a; omega), mul_zero]`.

Rewrite using `[← Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image m) (g := m) (fun x hx => Finset.mem_image_of_mem m hx)]`. Establish `e2 : ∀ d ∈ T.image m, ∑ t ∈ T with m t = d, g (m t) ≤ ((∏ a, s a : ℕ) : ℝ) * g d`. Introduce `d _`. Establish `: ∑ t ∈ T with m t = d, g (m t) = ∑ t ∈ T with m t = d, g d`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `t ht`. Rewrite using `[(Finset.mem_filter.mp ht).2]`. Rewrite using `[this, Finset.sum_const, nsmul_eq_mul]`. Apply `mul_le_mul_of_nonneg_right _ (hg0 d)` to reduce the goal to its premises. Use `hf E p s d (T.filter (fun t => m t = d)) hs1 (by` as an intermediate fact.

Introduce `t ht`. Take `⟨h1, h2⟩` from `Finset.mem_filter.mp ht`. Conclude with `⟨hne t h1, fun a => congrFun h2 a⟩)`. Conclude with `this` after adjusting the coercions. Use `(Finset.sum_le_sum e2).trans ?_` and prove the remaining obligations.

Rewrite using `[← Finset.mul_sum]`. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Use `set Ta : Fin p → Finset E := fun a => T.image (fun t => m t a) with hTa`. Establish `e3 : ∑ d ∈ T.image m, g d ≤ ∑ d ∈ Fintype.piFinset Ta, g d`. Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises.

Introduce `d hd`. Take `⟨t, ht, rfl⟩` from `Finset.mem_image.mp hd`. Rewrite using `[Fintype.mem_piFinset]`. Introduce `a`. Conclude with `Finset.mem_image.mpr ⟨t, ht, rfl⟩`.

Introduce `d _ _`. Conclude with `hg0 d`. Use `e3.trans ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_univ_sum Ta (fun _ x => φ x)]`. Establish `e4 : ∀ a ∈ (Finset.univ : Finset (Fin p)), ∑ x ∈ Ta a, φ x ≤ 16 ^ Fintype.card (InfinitePlace E)`.

Introduce `a _`. Apply `integral_points_weight_sum_le hs E` to reduce the goal to its premises. Introduce `x hx`. Take `⟨t, ht, rfl⟩` from `Finset.mem_image.mp hx`. Conclude with `(hT t ht a).1`.

Use `(Finset.prod_le_prod (fun a _ => Finset.sum_nonneg fun x _ => hφ0 x) e4).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]`.
-/
lemma integral_minors_weight_sum_le (hf : BlockEndMinorFibreFinite) (hs : IdealInversePowerSum) (E : Type) [Field E] [NumberField E]
    [NumberField.IsTotallyComplex E] (p : ℕ) (s : Fin p → ℕ) (hs1 : ∀ a, 1 ≤ s a)
    (T : Finset (Fin p → E))
    (hT : ∀ t ∈ T, ∀ a, IsIntegral ℤ (IndexedMinorEntry s t a) ∧ IndexedMinorEntry s t a ≠ 0) :
    ∑ t ∈ T, (∏ a : Fin p, ∏ w : InfinitePlace E, (1 + (w (IndexedMinorEntry s t a)) ^ 2) ^ 2)⁻¹ ≤
      ((∏ a, s a : ℕ) : ℝ) * 16 ^ (Fintype.card (InfinitePlace E) * p) := by
  classical
  set φ : E → ℝ := fun x => ∏ w : InfinitePlace E, ((1 + (w x) ^ 2) ^ 2)⁻¹ with hφ
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => Finset.prod_nonneg fun w _ => by positivity
  set m : (Fin p → E) → (Fin p → E) := fun t a => IndexedMinorEntry s t a with hm
  set g : (Fin p → E) → ℝ := fun d => ∏ a, φ (d a) with hg
  have hg0 : ∀ d, 0 ≤ g d := fun d => Finset.prod_nonneg fun a _ => hφ0 _
  have e1 : ∀ t, (∏ a : Fin p, ∏ w : InfinitePlace E, (1 + (w (IndexedMinorEntry s t a)) ^ 2) ^ 2)⁻¹ = g (m t) := by
    intro t
    simp only [hg, hφ, hm, Finset.prod_inv_distrib]
  simp_rw [e1]

  have hne : ∀ t ∈ T, ∀ a, t a ≠ 0 := by
    intro t ht a h0
    apply (hT t ht a).2
    unfold IndexedMinorEntry
    apply Finset.prod_eq_zero (i := a) (by simp)
    rw [h0, zero_pow (by have := hs1 a; omega), mul_zero]
  rw [← Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image m) (g := m)
    (fun x hx => Finset.mem_image_of_mem m hx)]
  have e2 : ∀ d ∈ T.image m, ∑ t ∈ T with m t = d, g (m t) ≤ ((∏ a, s a : ℕ) : ℝ) * g d := by
    intro d _
    have : ∑ t ∈ T with m t = d, g (m t) = ∑ t ∈ T with m t = d, g d := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [(Finset.mem_filter.mp ht).2]
    rw [this, Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (hg0 d)
    have := hf E p s d (T.filter (fun t => m t = d)) hs1 (by
      intro t ht
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp ht
      exact ⟨hne t h1, fun a => congrFun h2 a⟩)
    exact_mod_cast this
  refine (Finset.sum_le_sum e2).trans ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  set Ta : Fin p → Finset E := fun a => T.image (fun t => m t a) with hTa
  have e3 : ∑ d ∈ T.image m, g d ≤ ∑ d ∈ Fintype.piFinset Ta, g d := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hd
      rw [Fintype.mem_piFinset]
      intro a
      exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
    · intro d _ _; exact hg0 d
  refine e3.trans ?_
  rw [← Finset.prod_univ_sum Ta (fun _ x => φ x)]
  have e4 : ∀ a ∈ (Finset.univ : Finset (Fin p)), ∑ x ∈ Ta a, φ x ≤ 16 ^ Fintype.card (InfinitePlace E) := by
    intro a _
    apply integral_points_weight_sum_le hs E
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact (hT t ht a).1
  refine (Finset.prod_le_prod (fun a _ => Finset.sum_nonneg fun x _ => hφ0 x) e4).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

/- English proof (translation)
Introduce `E _ _ _ r S hS`. Use `set f := Fintype.card (InfinitePlace E) with hfdef`. Use `set B : ℝ := Real.exp (((r : ℝ) + 1) / Real.exp 1) * 16 ^ (f * (r + 1)) with hB`. Establish `hB0 : 0 ≤ B` using `by positivity`. Establish `key : ∀ c : Composition (r + 1), ∑ t ∈ S.preimage (Sigma.mk c) sigma_mk_injective.injOn, (blockMinorWeight (⟨c, t⟩ : Σ c : Composition (r + 1), (Fin c.length → E)))⁻¹ ≤ B`.

Introduce `c`. Establish `hmemT : ∀ t ∈ S.preimage (Sigma.mk c) sigma_mk_injective.injOn, (⟨c, t⟩ : Σ c : Composition (r + 1), (Fin c.length → E)) ∈ S` using `fun t ht => Finset.mem_preimage.mp ht`. Generalize the expression as in `S.preimage (Sigma.mk c) sigma_mk_injective.injOn = T at hmemT ⊢`. Apply the tactic sequence `have hpt : ∀ t ∈ T, ∀ a : Fin c.length, IsIntegral ℤ (IndexedMinorEntry c.blocksFun t a) ∧ IndexedMinorEntry c.blocksFun t a ≠ 0 := by`. Introduce `t ht`.

Establish `h` using `hS _ (hmemT t ht)`. Unfold `BlockEndMinorsIntegral at h`. Conclude with `h`. Establish `h1` using `integral_minors_weight_sum_le hf hs E c.length c.blocksFun (fun a => c.one_le_blocksFun a) T hpt`. Apply the tactic sequence `have h0 : ∀ t : Fin c.length → E, blockMinorWeight (⟨c, t⟩ : Σ c : Composition (r + 1), (Fin c.length → E)) = ∏ a : Fin c.length, ∏ w : InfinitePlace E, (1 + (w (IndexedMinorEntry c.blocksFun t a)) ^ 2) ^ 2 := fun t => rfl`.

Repeatedly rewrite using `[h0]`. Use `h1.trans ?_` and prove the remaining obligations. Establish `h2 : ((∏ a, c.blocksFun a : ℕ) : ℝ) ≤ Real.exp (((r : ℝ) + 1) / Real.exp 1)`. Use `hb (r + 1) c` as an intermediate fact. Establish `e : c.blocks.prod = ∏ a, c.blocksFun a`.

Rewrite using `[← c.ofFn_blocksFun, List.prod_ofFn]`. Rewrite `this` using `[e]`. Move the coercions through the operations in `at this ⊢`. Conclude with `this`. Establish `h3 : (16 : ℝ) ^ (f * c.length) ≤ 16 ^ (f * (r + 1))` using `pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ c.length_le)`.

Conclude with `mul_le_mul h2 h3 (by positivity) (Real.exp_pos _).le`. Establish `e0 : ∑ γ ∈ S, (blockMinorWeight γ)⁻¹ = ∑ c ∈ S.image Sigma.fst, ∑ t ∈ S.preimage (Sigma.mk c) sigma_mk_injective.injOn, (blockMinorWeight (⟨c, t⟩ : Σ c : Composition (r + 1), (Fin c.length → E)))⁻¹` using `by conv_lhs => rw [← Finset.sigma_image_fst_preimage_mk S]`. Rewrite using `[Finset.sum_sigma]`. Rewrite using `[e0]`. Use `(Finset.sum_le_sum fun c _ => key c).trans ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_const, nsmul_eq_mul]`. Establish `hc : ((S.image Sigma.fst).card : ℝ) ≤ 2 ^ r`. Establish `h1 : (S.image Sigma.fst).card ≤ Fintype.card (Composition (r + 1))` using `Finset.card_le_univ _`. Rewrite `h1` using `[composition_card]`. Simplify using `only [Nat.add_sub_cancel] at h1`.

Conclude with `h1` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation.
-/
theorem block_minor_sum_explicit_of_fibre_finite_of_prod_bound (hf : BlockEndMinorFibreFinite) (hb : CompositionBlockProdBound) (hs : IdealInversePowerSum) : BlockMinorSumExplicit := by
  classical
  intro E _ _ _ r S hS
  set f := Fintype.card (InfinitePlace E) with hfdef
  set B : ℝ := Real.exp (((r : ℝ) + 1) / Real.exp 1) * 16 ^ (f * (r + 1)) with hB
  have hB0 : 0 ≤ B := by positivity
  have key : ∀ c : Composition (r + 1),
      ∑ t ∈ S.preimage (Sigma.mk c) sigma_mk_injective.injOn, (blockMinorWeight (⟨c, t⟩ : Σ c : Composition (r + 1), (Fin c.length → E)))⁻¹ ≤ B := by
    intro c
    have hmemT : ∀ t ∈ S.preimage (Sigma.mk c) sigma_mk_injective.injOn,
        (⟨c, t⟩ : Σ c : Composition (r + 1), (Fin c.length → E)) ∈ S := fun t ht => Finset.mem_preimage.mp ht
    generalize S.preimage (Sigma.mk c) sigma_mk_injective.injOn = T at hmemT ⊢
    have hpt : ∀ t ∈ T, ∀ a : Fin c.length,
        IsIntegral ℤ (IndexedMinorEntry c.blocksFun t a) ∧ IndexedMinorEntry c.blocksFun t a ≠ 0 := by
      intro t ht
      have h := hS _ (hmemT t ht)
      unfold BlockEndMinorsIntegral at h
      exact h
    have h1 := integral_minors_weight_sum_le hf hs E c.length c.blocksFun (fun a => c.one_le_blocksFun a)
      T hpt
    have h0 : ∀ t : Fin c.length → E, blockMinorWeight (⟨c, t⟩ : Σ c : Composition (r + 1), (Fin c.length → E)) =
        ∏ a : Fin c.length, ∏ w : InfinitePlace E, (1 + (w (IndexedMinorEntry c.blocksFun t a)) ^ 2) ^ 2 := fun t => rfl
    simp_rw [h0]
    refine h1.trans ?_
    have h2 : ((∏ a, c.blocksFun a : ℕ) : ℝ) ≤ Real.exp (((r : ℝ) + 1) / Real.exp 1) := by
      have := hb (r + 1) c
      have e : c.blocks.prod = ∏ a, c.blocksFun a := by
        rw [← c.ofFn_blocksFun, List.prod_ofFn]
      rw [e] at this
      push_cast at this ⊢
      exact this
    have h3 : (16 : ℝ) ^ (f * c.length) ≤ 16 ^ (f * (r + 1)) :=
      pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ c.length_le)
    exact mul_le_mul h2 h3 (by positivity) (Real.exp_pos _).le
  have e0 : ∑ γ ∈ S, (blockMinorWeight γ)⁻¹ = ∑ c ∈ S.image Sigma.fst,
      ∑ t ∈ S.preimage (Sigma.mk c) sigma_mk_injective.injOn, (blockMinorWeight (⟨c, t⟩ : Σ c : Composition (r + 1), (Fin c.length → E)))⁻¹ := by
    conv_lhs => rw [← Finset.sigma_image_fst_preimage_mk S]
    rw [Finset.sum_sigma]
  rw [e0]
  refine (Finset.sum_le_sum fun c _ => key c).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ((S.image Sigma.fst).card : ℝ) ≤ 2 ^ r := by
    have h1 : (S.image Sigma.fst).card ≤ Fintype.card (Composition (r + 1)) := Finset.card_le_univ _
    rw [composition_card] at h1
    simp only [Nat.add_sub_cancel] at h1
    exact_mod_cast h1
  calc ((S.image Sigma.fst).card : ℝ) * B ≤ 2 ^ r * B := mul_le_mul_of_nonneg_right hc hB0
    _ = _ := by rw [hB]; ring

end G5

section G6
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms

/- English proof (translation)
Introduce `ι _ G D A hG h1 hD`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Finset.prod_pow, Finset.prod_pow]`. Conclude with `pow_le_pow_left₀ (Finset.prod_nonneg fun v _ => by positivity) (prod_max_inv_le_prod_max' ι G hG h1) A`. Apply `Finset.prod_le_prod` to reduce the goal to its premises.

Introduce `v _`. Check the signs of the components of the expression. Introduce `v _`. Apply `pow_le_pow_left₀ (by positivity)` to reduce the goal to its premises. Apply `max_le` to reduce the goal to its premises.

Use `sq_nonneg ‖D v‖` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `hD v` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem integral_norm_application_holds : Formalism.HermitianLatticeCounting.ExpansionTerms.NormGeOneMaxBound := by
  intro ι _ G D A hG h1 hD
  constructor
  · rw [Finset.prod_pow, Finset.prod_pow]
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun v _ => by positivity) (prod_max_inv_le_prod_max' ι G hG h1) A
  · apply Finset.prod_le_prod
    · intro v _; positivity
    · intro v _
      apply pow_le_pow_left₀ (by positivity)
      apply max_le
      · have := sq_nonneg ‖D v‖; linarith
      · have := hD v; linarith

noncomputable def boundPolynomial (r A' : ℕ) : MvPolynomial (Fin (r + 1) ⊕ Fin (r + 1)) NNReal :=
  (∏ l : Fin (r + 1), (1 + MvPolynomial.X (Sum.inl l) * MvPolynomial.X (Sum.inr l)) ^ 2) *
    (1 + MvPolynomial.X (Sum.inl (Fin.last r)) * MvPolynomial.X (Sum.inr (Fin.last r))) ^ A'

end G6

section G7
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
open scoped ENNReal

/- English proof (translation)
Break down `s.eq_empty_or_nonempty with rfl | hs` into its components or cases. Simplify using the standard rewrite rules. Establish `hn : (0:ℝ) < s.card` using `by exact_mod_cast hs.card_pos`. Establish `key` using `ENNReal.lintegral_prod_norm_pow_le (μ := μ) s (f := fun i ω => g i ω ^ s.card) (fun i hi => ((hg i hi).pow_const _).aemeasurable) (p := fun _ => (1:ℝ) / s.card) (by simp [hn.ne']) (fun _ _ => by positivity)`. Establish `e : ∀ x : ℝ≥0∞, (x ^ s.card) ^ ((1:ℝ) / s.card) = x`.

Introduce `x`. Rewrite using `[← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_one_div_cancel hn.ne', ENNReal.rpow_one]`. Simplify using `only [e] at key`. Use `key.trans (Finset.prod_le_prod' fun i hi => ?_)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
lemma holder_lintegral_prod_le {Ω ι : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι)
    (g : ι → Ω → ℝ≥0∞) (B : ι → ℝ≥0∞) (hg : ∀ i ∈ s, Measurable (g i))
    (h : ∀ i ∈ s, ∫⁻ ω, g i ω ^ s.card ∂μ ≤ B i ^ s.card) :
    ∫⁻ ω, ∏ i ∈ s, g i ω ∂μ ≤ ∏ i ∈ s, B i := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hn : (0:ℝ) < s.card := by exact_mod_cast hs.card_pos
  have key := ENNReal.lintegral_prod_norm_pow_le (μ := μ) s (f := fun i ω => g i ω ^ s.card)
    (fun i hi => ((hg i hi).pow_const _).aemeasurable) (p := fun _ => (1:ℝ) / s.card)
    (by simp [hn.ne']) (fun _ _ => by positivity)
  have e : ∀ x : ℝ≥0∞, (x ^ s.card) ^ ((1:ℝ) / s.card) = x := by
    intro x
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_one_div_cancel hn.ne', ENNReal.rpow_one]
  simp only [e] at key
  refine key.trans (Finset.prod_le_prod' fun i hi => ?_)
  calc _ ≤ (B i ^ s.card) ^ ((1:ℝ) / s.card) := ENNReal.rpow_le_rpow (h i hi) (by positivity)
    _ = B i := e _

/- English proof (translation)
Establish `t : ∀ (m : ℕ) ω, ∏ i ∈ range m, (M (i + 1) ω / M i ω) = M m ω / M 0 ω`. Introduce `m ω`. Proceed by induction on `m with`. Consider the case `zero => simp [(hpos 0 ω).ne']`. Consider the case `succ m ih`.

Rewrite using `[prod_range_succ, ih]`. Establish `h1` using `(hpos m ω).ne'`. Establish `h2` using `(hpos 0 ω).ne'`. Clear the denominators using the available nonvanishing facts. Establish `e : ∀ ω, ENNReal.ofReal ((M n ω / M 0 ω) ^ (2 * q)) = ∏ i ∈ range n, ENNReal.ofReal ((M (i + 1) ω / M i ω) ^ (2 * q))`.

Introduce `ω`. Rewrite using `[← t n ω, ← Finset.prod_pow, ENNReal.ofReal_prod_of_nonneg]`. Introduce `i _`. Establish `h1` using `hpos (i + 1) ω`. Establish `h2` using `hpos i ω`.

Check the signs of the components of the expression. Repeatedly rewrite using `[e]`. Rewrite using `[ENNReal.ofReal_prod_of_nonneg (fun i _ => pow_nonneg (hB i) _)]`. Apply `holder_lintegral_prod_le` to reduce the goal to its premises. Introduce `i _`.

Conclude with `ENNReal.measurable_ofReal.comp (((hm _).div (hm _)).pow_const _)`. Introduce `i hi`. Rewrite using `[card_range]`. Establish `h3` using `h i (mem_range.1 hi)`. Establish `e1 : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal (x ^ (2 * q)) ^ n = ENNReal.ofReal (x ^ (2 * (n * q)))`.

Introduce `x hx`. Rewrite using `[← ENNReal.ofReal_pow (pow_nonneg hx _), ← pow_mul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1 _ (hB i)]`.

Use `le_trans (le_of_eq ?_) h3` and prove the remaining obligations. Use `lintegral_congr fun ω => e1 _ ?_` and prove the remaining obligations. Establish `h1` using `hpos (i + 1) ω`. Establish `h2` using `hpos i ω`. Check the signs of the components of the expression.
-/
lemma moment_ratio_telescoping {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (M : ℕ → Ω → ℝ)
    (n q : ℕ) (B : ℕ → ℝ) (hm : ∀ i, Measurable (M i)) (hpos : ∀ i ω, 0 < M i ω) (hB : ∀ i, 0 ≤ B i)
    (h : ∀ i < n, ∫⁻ ω, ENNReal.ofReal ((M (i + 1) ω / M i ω) ^ (2 * (n * q))) ∂μ ≤
      ENNReal.ofReal (B i ^ (2 * (n * q)))) :
    ∫⁻ ω, ENNReal.ofReal ((M n ω / M 0 ω) ^ (2 * q)) ∂μ ≤ ENNReal.ofReal (∏ i ∈ range n, B i ^ (2 * q)) := by
  have t : ∀ (m : ℕ) ω, ∏ i ∈ range m, (M (i + 1) ω / M i ω) = M m ω / M 0 ω := by
    intro m ω
    induction m with
    | zero => simp [(hpos 0 ω).ne']
    | succ m ih =>
      rw [prod_range_succ, ih]
      have h1 := (hpos m ω).ne'
      have h2 := (hpos 0 ω).ne'
      field_simp
  have e : ∀ ω, ENNReal.ofReal ((M n ω / M 0 ω) ^ (2 * q)) =
      ∏ i ∈ range n, ENNReal.ofReal ((M (i + 1) ω / M i ω) ^ (2 * q)) := by
    intro ω
    rw [← t n ω, ← Finset.prod_pow, ENNReal.ofReal_prod_of_nonneg]
    intro i _
    have h1 := hpos (i + 1) ω
    have h2 := hpos i ω
    positivity
  simp_rw [e]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => pow_nonneg (hB i) _)]
  apply holder_lintegral_prod_le
  · intro i _
    exact ENNReal.measurable_ofReal.comp (((hm _).div (hm _)).pow_const _)
  · intro i hi
    rw [card_range]
    have h3 := h i (mem_range.1 hi)
    have e1 : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal (x ^ (2 * q)) ^ n = ENNReal.ofReal (x ^ (2 * (n * q))) := by
      intro x hx
      rw [← ENNReal.ofReal_pow (pow_nonneg hx _), ← pow_mul]
      congr 2
      ring
    rw [e1 _ (hB i)]
    refine le_trans (le_of_eq ?_) h3
    refine lintegral_congr fun ω => e1 _ ?_
    have h1 := hpos (i + 1) ω
    have h2 := hpos i ω
    positivity

/- English proof (translation)
Introduce `Ω _ μ _ r q l H0 R hm hpos hH0 hR h0 hc a`. Establish `ha : a.val ≤ r` using `Nat.lt_succ_iff.1 a.isLt`. Set `M : ℕ → Ω → ℝ` to `fun i ω => if i = 0 then 1 else l ⟨min (i - 1) r, by omega⟩ ω`. Set `B : ℕ → ℝ` to `fun i => if i = 0 then H0 else R`. Establish `hq : (a.val + 1) * q ≤ (r + 1) * q` using `Nat.mul_le_mul_right _ (by omega)`.

Establish `key` using `moment_ratio_telescoping μ M (a.val + 1) q B (by`. Introduce `i`. Distinguish the cases in `hi : i = 0`. Simplify using `only [M, hi, if_true]`. Conclude with `measurable_const`.

Simplify using `only [M, hi, if_false]`. Conclude with `hm _)`. Use the proof step `(by`. Introduce `i ω`. Distinguish the cases in `hi : i = 0`.

Simplify using `[M, hi]`. Simplify using `only [M, hi, if_false]`. Conclude with `hpos _ _)`. Use the proof step `(by`. Introduce `i`.

Distinguish the cases in `hi : i = 0`. Simplify using `[B, hi, hH0]`. Simplify using `[B, hi, hR])`. Use the proof step `(by`. Introduce `i hi`.

Break down `Nat.eq_zero_or_pos i with rfl | hi0` into its components or cases. Establish `e0 : (⟨min (0 + 1 - 1) r, by omega⟩ : Fin (r + 1)) = 0` using `Fin.ext (by simp)`. Simplify using `only [M, B, if_true, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, e0, div_one]`. Conclude with `h0 _ hq`. Take `⟨k, rfl⟩ : ∃ k, i = k + 1` from `⟨i - 1, by omega⟩`.

Establish `hk : k < r` using `by omega`. Establish `e1 : (⟨min (k + 1 + 1 - 1) r, by omega⟩ : Fin (r + 1)) = (⟨k, hk⟩ : Fin r).succ` using `Fin.ext (by simp; omega)`. Establish `e2 : (⟨min (k + 1 - 1) r, by omega⟩ : Fin (r + 1)) = (⟨k, hk⟩ : Fin r).castSucc` using `Fin.ext (by simp; omega)`. Simplify using `only [M, B, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, e1, e2]`. Conclude with `hc _ _ hq)`.

Establish `ea : (⟨min (a.val + 1 - 1) r, by omega⟩ : Fin (r + 1)) = a` using `Fin.ext (by simp; omega)`. Simplify using `only [M, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, if_true, ea, div_one] at key`. Use `key.trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`. Rewrite using `[prod_range_succ']`.

Simplify using `only [B, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, if_true, prod_const, card_range]`. Rewrite using `[← pow_mul, mul_comm]`.
-/
theorem corollary_upper_estimate_holds : Formalism.HermitianLatticeCounting.ExpansionTerms.MomentUpwardHolder := by
  intro Ω _ μ _ r q l H0 R hm hpos hH0 hR h0 hc a
  have ha : a.val ≤ r := Nat.lt_succ_iff.1 a.isLt
  let M : ℕ → Ω → ℝ := fun i ω => if i = 0 then 1 else l ⟨min (i - 1) r, by omega⟩ ω
  let B : ℕ → ℝ := fun i => if i = 0 then H0 else R
  have hq : (a.val + 1) * q ≤ (r + 1) * q := Nat.mul_le_mul_right _ (by omega)
  have key := moment_ratio_telescoping μ M (a.val + 1) q B
    (by
      intro i
      by_cases hi : i = 0
      · simp only [M, hi, if_true]; exact measurable_const
      · simp only [M, hi, if_false]; exact hm _)
    (by
      intro i ω
      by_cases hi : i = 0
      · simp [M, hi]
      · simp only [M, hi, if_false]; exact hpos _ _)
    (by
      intro i
      by_cases hi : i = 0
      · simp [B, hi, hH0]
      · simp [B, hi, hR])
    (by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · have e0 : (⟨min (0 + 1 - 1) r, by omega⟩ : Fin (r + 1)) = 0 := Fin.ext (by simp)
        simp only [M, B, if_true, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, e0, div_one]
        exact h0 _ hq
      · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        have hk : k < r := by omega
        have e1 : (⟨min (k + 1 + 1 - 1) r, by omega⟩ : Fin (r + 1)) = (⟨k, hk⟩ : Fin r).succ :=
          Fin.ext (by simp; omega)
        have e2 : (⟨min (k + 1 - 1) r, by omega⟩ : Fin (r + 1)) = (⟨k, hk⟩ : Fin r).castSucc :=
          Fin.ext (by simp; omega)
        simp only [M, B, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, e1, e2]
        exact hc _ _ hq)
  have ea : (⟨min (a.val + 1 - 1) r, by omega⟩ : Fin (r + 1)) = a := Fin.ext (by simp; omega)
  simp only [M, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, if_true, ea, div_one] at key
  refine key.trans (le_of_eq ?_)
  congr 1
  rw [prod_range_succ']
  simp only [B, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, if_true, prod_const, card_range]
  rw [← pow_mul, mul_comm]

/- English proof (translation)
Introduce `Ω _ μ _ r q l T R hm hpos hT hR hl hc a`. Establish `ha : a.val ≤ r` using `Nat.lt_succ_iff.1 a.isLt`. Set `M : ℕ → Ω → ℝ` to `fun i ω => l ⟨min (a.val + i) r, by omega⟩ ω`. Establish `hq : (r - a.val) * q ≤ (r + 1) * q` using `Nat.mul_le_mul_right _ (by omega)`. Establish `key` using `moment_ratio_telescoping μ M (r - a.val) q (fun _ => R) (fun i => hm _) (fun i ω => hpos _ _) (fun _ => hR) (by`.

Introduce `i hi`. Establish `hk : a.val + i < r` using `by omega`. Establish `e1 : (⟨min (a.val + (i + 1)) r, by omega⟩ : Fin (r + 1)) = (⟨a.val + i, hk⟩ : Fin r).succ` using `Fin.ext (by simp; omega)`. Establish `e2 : (⟨min (a.val + i) r, by omega⟩ : Fin (r + 1)) = (⟨a.val + i, hk⟩ : Fin r).castSucc` using `Fin.ext (by simp; omega)`. Simplify using `only [M, e1, e2]`.

Conclude with `hc _ _ hq)`. Establish `ea : (⟨min (a.val + 0) r, by omega⟩ : Fin (r + 1)) = a` using `Fin.ext (by simp; omega)`. Establish `er : (⟨min (a.val + (r - a.val)) r, by omega⟩ : Fin (r + 1)) = Fin.last r` using `Fin.ext (by simp; omega)`. Simplify using `only [M, ea, er, prod_const, card_range] at key`. Rewrite `key` using `[← pow_mul]`.

Use `le_trans (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_) key` and prove the remaining obligations. Establish `h1 : 1 ≤ l (Fin.last r) ω`. Establish `h2` using `hl ω`. Establish `h3` using `hpos (Fin.last r) ω`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h4` using `hpos a ω`. Apply `pow_le_pow_left₀ (by positivity)` to reduce the goal to its premises. Rewrite using `[div_eq_mul_inv]`. Conclude with `le_mul_of_one_le_left (by positivity) h1`.
-/
theorem corollary_lower_estimate_holds : Formalism.HermitianLatticeCounting.ExpansionTerms.MomentDownwardBound := by
  intro Ω _ μ _ r q l T R hm hpos hT hR hl hc a
  have ha : a.val ≤ r := Nat.lt_succ_iff.1 a.isLt
  let M : ℕ → Ω → ℝ := fun i ω => l ⟨min (a.val + i) r, by omega⟩ ω
  have hq : (r - a.val) * q ≤ (r + 1) * q := Nat.mul_le_mul_right _ (by omega)
  have key := moment_ratio_telescoping μ M (r - a.val) q (fun _ => R) (fun i => hm _) (fun i ω => hpos _ _) (fun _ => hR)
    (by
      intro i hi
      have hk : a.val + i < r := by omega
      have e1 : (⟨min (a.val + (i + 1)) r, by omega⟩ : Fin (r + 1)) = (⟨a.val + i, hk⟩ : Fin r).succ :=
        Fin.ext (by simp; omega)
      have e2 : (⟨min (a.val + i) r, by omega⟩ : Fin (r + 1)) = (⟨a.val + i, hk⟩ : Fin r).castSucc :=
        Fin.ext (by simp; omega)
      simp only [M, e1, e2]
      exact hc _ _ hq)
  have ea : (⟨min (a.val + 0) r, by omega⟩ : Fin (r + 1)) = a := Fin.ext (by simp; omega)
  have er : (⟨min (a.val + (r - a.val)) r, by omega⟩ : Fin (r + 1)) = Fin.last r := Fin.ext (by simp; omega)
  simp only [M, ea, er, prod_const, card_range] at key
  rw [← pow_mul] at key
  refine le_trans (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_) key
  have h1 : 1 ≤ l (Fin.last r) ω := by
    have h2 := hl ω
    have h3 := hpos (Fin.last r) ω
    nlinarith
  have h4 := hpos a ω
  apply pow_le_pow_left₀ (by positivity)
  rw [div_eq_mul_inv]
  exact le_mul_of_one_le_left (by positivity) h1

/- English proof (translation)
Introduce `Ω _ μ _ r q L l H1 hm hpos hH1 hL h`. Establish `hcard : (univ.filter (fun a : Fin (r + 1) => a.val < L)).card = L`. Use `Fin.card_filter_val_lt (n := r + 1) (m := L)` as an intermediate fact. Simplify `this` using `[hL]`. Establish `e : ∀ ω, ENNReal.ofReal ((∏ a ∈ univ.filter (fun a : Fin (r + 1) => a.val < L), l a ω) ^ (2 * q)) = ∏ a ∈ univ.filter (fun a : Fin (r + 1) => a.val < L), ENNReal.ofReal (l a ω ^ (2 * q))`.

Introduce `ω`. Rewrite using `[← Finset.prod_pow, ENNReal.ofReal_prod_of_nonneg]`. Introduce `i _`. Use `hpos i ω` as an intermediate fact. Check the signs of the components of the expression.

Repeatedly rewrite using `[e]`. Establish `key` using `holder_lintegral_prod_le μ (univ.filter (fun a : Fin (r + 1) => a.val < L)) (fun a ω => ENNReal.ofReal (l a ω ^ (2 * q))) (fun _ => ENNReal.ofReal (H1 ^ (2 * q))) (fun a _ => ENNReal.measurable_ofReal.comp ((hm a).pow_const _)) (by`. Introduce `a ha`. Rewrite using `[hcard]`. Establish `h3` using `h a (by simpa using ha)`.

Rewrite using `[← ENNReal.ofReal_pow (by positivity), ← pow_mul]`. Use `le_trans (le_of_eq ?_) h3` and prove the remaining obligations. Use `lintegral_congr fun ω => ?_` and prove the remaining obligations. Use `hpos a ω` as an intermediate fact. Rewrite using `[← ENNReal.ofReal_pow (by positivity), ← pow_mul])`.

Use `key.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[prod_const, hcard, ← ENNReal.ofReal_pow (by positivity), ← pow_mul]`.
-/
theorem corollary_product_estimate_holds : Formalism.HermitianLatticeCounting.ExpansionTerms.MomentProductBound := by
  intro Ω _ μ _ r q L l H1 hm hpos hH1 hL h
  have hcard : (univ.filter (fun a : Fin (r + 1) => a.val < L)).card = L := by
    have := Fin.card_filter_val_lt (n := r + 1) (m := L)
    simpa [hL] using this
  have e : ∀ ω, ENNReal.ofReal ((∏ a ∈ univ.filter (fun a : Fin (r + 1) => a.val < L), l a ω) ^ (2 * q)) =
      ∏ a ∈ univ.filter (fun a : Fin (r + 1) => a.val < L), ENNReal.ofReal (l a ω ^ (2 * q)) := by
    intro ω
    rw [← Finset.prod_pow, ENNReal.ofReal_prod_of_nonneg]
    intro i _
    have := hpos i ω
    positivity
  simp_rw [e]
  have key := holder_lintegral_prod_le μ (univ.filter (fun a : Fin (r + 1) => a.val < L))
    (fun a ω => ENNReal.ofReal (l a ω ^ (2 * q))) (fun _ => ENNReal.ofReal (H1 ^ (2 * q)))
    (fun a _ => ENNReal.measurable_ofReal.comp ((hm a).pow_const _))
    (by
      intro a ha
      rw [hcard]
      have h3 := h a (by simpa using ha)
      rw [← ENNReal.ofReal_pow (by positivity), ← pow_mul]
      refine le_trans (le_of_eq ?_) h3
      refine lintegral_congr fun ω => ?_
      have := hpos a ω
      rw [← ENNReal.ofReal_pow (by positivity), ← pow_mul])
  refine key.trans (le_of_eq ?_)
  rw [prod_const, hcard, ← ENNReal.ofReal_pow (by positivity), ← pow_mul]

/- English proof (translation)
Establish `h0 : 0 < (la * H1) ^ (2 * q)` using `by positivity`. Establish `h1 : μ {ω | ENNReal.ofReal ((la * H1) ^ (2 * q)) ≤ ENNReal.ofReal (f ω ^ (2 * q))} ≤ (∫⁻ ω, ENNReal.ofReal (f ω ^ (2 * q)) ∂μ) / ENNReal.ofReal ((la * H1) ^ (2 * q))` using `meas_ge_le_lintegral_div (ENNReal.measurable_ofReal.comp (hf.pow_const _)).aemeasurable (by simpa using h0) ENNReal.ofReal_ne_top`. Establish `h2 : {ω | la * H1 ≤ f ω} ⊆ {ω | ENNReal.ofReal ((la * H1) ^ (2 * q)) ≤ ENNReal.ofReal (f ω ^ (2 * q))}`. Introduce `ω hω`. Conclude with `ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hω _)`.

Use `(measure_mono h2).trans (h1.trans ?_)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Rewrite using `[mul_pow]`. Clear the denominators using the available nonvanishing facts.
-/
lemma chebyshev_moment_bound {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (q : ℕ) (H1 la : ℝ)
    (hf : Measurable f) (hH1 : 0 < H1) (hla : 0 < la)
    (h : ∫⁻ ω, ENNReal.ofReal (f ω ^ (2 * q)) ∂μ ≤ ENNReal.ofReal (H1 ^ (2 * q))) :
    μ {ω | la * H1 ≤ f ω} ≤ ENNReal.ofReal (1 / la ^ (2 * q)) := by
  have h0 : 0 < (la * H1) ^ (2 * q) := by positivity
  have h1 : μ {ω | ENNReal.ofReal ((la * H1) ^ (2 * q)) ≤ ENNReal.ofReal (f ω ^ (2 * q))} ≤
      (∫⁻ ω, ENNReal.ofReal (f ω ^ (2 * q)) ∂μ) / ENNReal.ofReal ((la * H1) ^ (2 * q)) :=
    meas_ge_le_lintegral_div (ENNReal.measurable_ofReal.comp (hf.pow_const _)).aemeasurable
      (by simpa using h0) ENNReal.ofReal_ne_top
  have h2 : {ω | la * H1 ≤ f ω} ⊆
      {ω | ENNReal.ofReal ((la * H1) ^ (2 * q)) ≤ ENNReal.ofReal (f ω ^ (2 * q))} := by
    intro ω hω
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hω _)
  refine (measure_mono h2).trans (h1.trans ?_)
  calc _ ≤ ENNReal.ofReal (H1 ^ (2 * q)) / ENNReal.ofReal ((la * H1) ^ (2 * q)) := by gcongr
    _ = ENNReal.ofReal (H1 ^ (2 * q) / (la * H1) ^ (2 * q)) := (ENNReal.ofReal_div_of_pos h0).symm
    _ = ENNReal.ofReal (1 / la ^ (2 * q)) := by
        congr 1
        rw [mul_pow]
        field_simp

/- English proof (translation)
Introduce `Ω _ μ _ r q l H1 la hm hpos hH1 hla hp hn`. Establish `hsub : {ω | ∃ a, la * H1 ≤ max (l a ω) (l a ω)⁻¹} ⊆ ⋃ a : Fin (r + 1), ({ω | la * H1 ≤ l a ω} ∪ {ω | la * H1 ≤ (l a ω)⁻¹})`. Introduce and unpack `ω ⟨a, ha⟩`. Rewrite using `[Set.mem_iUnion]`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Break down `le_max_iff.1 ha with h | h` into its components or cases. Conclude with `Or.inl h`. Conclude with `Or.inr h`. Establish `hone : ∀ a : Fin (r + 1), μ ({ω | la * H1 ≤ l a ω} ∪ {ω | la * H1 ≤ (l a ω)⁻¹}) ≤ ENNReal.ofReal (2 / la ^ (2 * q))`. Introduce `a`.

Establish `h1` using `chebyshev_moment_bound μ (l a) q H1 la (hm a) hH1 hla (hp a)`. Establish `h2` using `chebyshev_moment_bound μ (fun ω => (l a ω)⁻¹) q H1 la (hm a).inv hH1 hla (hn a)`. Use `(measure_union_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))` and prove the remaining obligations. Rewrite using `[← ENNReal.ofReal_add (by positivity) (by positivity)]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Use `(measure_mono hsub).trans ((measure_iUnion_fintype_le μ _).trans ?_)` and prove the remaining obligations. Use `(Finset.sum_le_sum fun a _ => hone a).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, show ((r + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((r : ℝ) + 1) by`. Rewrite using `[← ENNReal.ofReal_natCast]`.

Use `push_cast`. Use the proof step `rfl,`. Use the proof step `← ENNReal.ofReal_mul (by positivity)]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem corollary_mass_estimate_holds : Formalism.HermitianLatticeCounting.ExpansionTerms.MomentMassBound := by
  intro Ω _ μ _ r q l H1 la hm hpos hH1 hla hp hn
  have hsub : {ω | ∃ a, la * H1 ≤ max (l a ω) (l a ω)⁻¹} ⊆
      ⋃ a : Fin (r + 1), ({ω | la * H1 ≤ l a ω} ∪ {ω | la * H1 ≤ (l a ω)⁻¹}) := by
    rintro ω ⟨a, ha⟩
    rw [Set.mem_iUnion]
    refine ⟨a, ?_⟩
    rcases le_max_iff.1 ha with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hone : ∀ a : Fin (r + 1), μ ({ω | la * H1 ≤ l a ω} ∪ {ω | la * H1 ≤ (l a ω)⁻¹}) ≤
      ENNReal.ofReal (2 / la ^ (2 * q)) := by
    intro a
    have h1 := chebyshev_moment_bound μ (l a) q H1 la (hm a) hH1 hla (hp a)
    have h2 := chebyshev_moment_bound μ (fun ω => (l a ω)⁻¹) q H1 la (hm a).inv hH1 hla (hn a)
    refine (measure_union_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  refine (measure_mono hsub).trans ((measure_iUnion_fintype_le μ _).trans ?_)
  refine (Finset.sum_le_sum fun a _ => hone a).trans (le_of_eq ?_)
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    show ((r + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((r : ℝ) + 1) by
      rw [← ENNReal.ofReal_natCast]; push_cast; rfl,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/- English proof (translation)
Introduce `Ω _ μ _ r q l H0 R T hm hpos hH0 hR hT h0 hc hl`. Establish `hH0' : (0:ℝ) ≤ H0` using `by linarith`. Establish `hM1 : (1:ℝ) ≤ max 1 R` using `le_max_left _ _`. Establish `hMR : R ≤ max 1 R` using `le_max_right _ _`. Establish `hH1 : 0 < H0 * max 1 R ^ r` using `by positivity`.

Establish `hab : ∀ a, ∫⁻ ω, ENNReal.ofReal (l a ω ^ (2 * q)) ∂μ ≤ ENNReal.ofReal ((H0 * max 1 R ^ r) ^ (2 * q)) ∧ ∫⁻ ω, ENNReal.ofReal ((l a ω)⁻¹ ^ (2 * q)) ∂μ ≤ ENNReal.ofReal ((H0 * max 1 R ^ r) ^ (2 * q))`. Introduce `a`. Establish `ha : a.val ≤ r` using `Nat.lt_succ_iff.1 a.isLt`. Prove the components needed by the constructor for the conclusion. Use `(corollary_upper_estimate_holds Ω μ r q l H0 R hm hpos hH0' hR h0 hc a).trans (ENNReal.ofReal_le_ofReal ?_)` and prove the remaining obligations.

Rewrite using `[mul_pow, ← pow_mul]`. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_comm r]`. Conclude with `Nat.mul_le_mul_left _ ha)`.

Use `(corollary_lower_estimate_holds Ω μ r q l T R hm hpos hT hR hl hc a).trans (ENNReal.ofReal_le_ofReal ?_)` and prove the remaining obligations. Rewrite using `[mul_pow, ← pow_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_comm r]; exact Nat.mul_le_mul_left _ (by omega))`. Use `_ ≤ H0 ^ (2 * q) * max 1 R ^ (r * (2 * q)) := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hH0)`.

Use `⟨hab, fun la hla => ?_⟩` and prove the remaining obligations. Conclude with `corollary_mass_estimate_holds Ω μ r q l _ la hm hpos hH1 hla (fun a => (hab a).1) (fun a => (hab a).2)`.
-/
theorem corollary_consequence_holds : Formalism.HermitianLatticeCounting.ExpansionTerms.MomentBound₂ := by
  intro Ω _ μ _ r q l H0 R T hm hpos hH0 hR hT h0 hc hl
  have hH0' : (0:ℝ) ≤ H0 := by linarith
  have hM1 : (1:ℝ) ≤ max 1 R := le_max_left _ _
  have hMR : R ≤ max 1 R := le_max_right _ _
  have hH1 : 0 < H0 * max 1 R ^ r := by positivity
  have hab : ∀ a, ∫⁻ ω, ENNReal.ofReal (l a ω ^ (2 * q)) ∂μ ≤ ENNReal.ofReal ((H0 * max 1 R ^ r) ^ (2 * q)) ∧
      ∫⁻ ω, ENNReal.ofReal ((l a ω)⁻¹ ^ (2 * q)) ∂μ ≤ ENNReal.ofReal ((H0 * max 1 R ^ r) ^ (2 * q)) := by
    intro a
    have ha : a.val ≤ r := Nat.lt_succ_iff.1 a.isLt
    constructor
    · refine (corollary_upper_estimate_holds Ω μ r q l H0 R hm hpos hH0' hR h0 hc a).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [mul_pow, ← pow_mul]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc R ^ (2 * q * a.val) ≤ max 1 R ^ (2 * q * a.val) := pow_le_pow_left₀ hR hMR _
        _ ≤ max 1 R ^ (r * (2 * q)) := pow_le_pow_right₀ hM1 (by
            rw [mul_comm r]; exact Nat.mul_le_mul_left _ ha)
    · refine (corollary_lower_estimate_holds Ω μ r q l T R hm hpos hT hR hl hc a).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [mul_pow, ← pow_mul]
      calc R ^ (2 * q * (r - a.val)) ≤ max 1 R ^ (2 * q * (r - a.val)) := pow_le_pow_left₀ hR hMR _
        _ ≤ max 1 R ^ (r * (2 * q)) := pow_le_pow_right₀ hM1 (by
            rw [mul_comm r]; exact Nat.mul_le_mul_left _ (by omega))
        _ ≤ H0 ^ (2 * q) * max 1 R ^ (r * (2 * q)) :=
            le_mul_of_one_le_left (by positivity) (one_le_pow₀ hH0)
  refine ⟨hab, fun la hla => ?_⟩
  exact corollary_mass_estimate_holds Ω μ r q l _ la hm hpos hH1 hla (fun a => (hab a).1) (fun a => (hab a).2)

end G7

section G8
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms

/- English proof (translation)
Rewrite using `[← (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (q + 1) => ι)) (fun p => F (Fin.cons p.1 p.2)) F (fun _ => rfl)), Fintype.sum_prod_type_right]`.
-/
lemma sum_fin_succ_cons {ι M : Type} [Fintype ι] [AddCommMonoid M] (q : ℕ) (F : (Fin (q + 1) → ι) → M) :
    ∑ σ, F σ = ∑ τ : Fin q → ι, ∑ i : ι, F (Fin.cons i τ) := by
  rw [← (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (q + 1) => ι)) (fun p => F (Fin.cons p.1 p.2)) F
    (fun _ => rfl)), Fintype.sum_prod_type_right]

/- English proof (translation)
Simplify using `[List.ofFn_succ]`.
-/
lemma foldr_ofFn_cons {W ι : Type} (Eop : ι → W → W) (q : ℕ) (i : ι) (τ : Fin q → ι) (w : W) :
    (List.ofFn (Fin.cons i τ : Fin (q + 1) → ι)).foldr Eop w = Eop i ((List.ofFn τ).foldr Eop w) := by
  simp [List.ofFn_succ]

/- English proof (translation)
Proceed by induction on `q with`. Consider the case `zero => simp`. Consider the case `succ q ih`. Rewrite using `[sum_fin_succ_cons]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma iterate_sum_lower_bound {R W ι : Type} [CommSemiring R] [PartialOrder R] [IsOrderedRing R] [Fintype ι]
    (Eop : ι → W → W) (Φ : W → R) (κ : R) (hκ : 0 ≤ κ) (h : ∀ w, κ * Φ w ≤ ∑ i, Φ (Eop i w))
    (q : ℕ) (w : W) : κ ^ q * Φ w ≤ ∑ σ : Fin q → ι, Φ ((List.ofFn σ).foldr Eop w) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [sum_fin_succ_cons]
    calc κ ^ (q + 1) * Φ w = κ * (κ ^ q * Φ w) := by ring
      _ ≤ κ * ∑ τ : Fin q → ι, Φ ((List.ofFn τ).foldr Eop w) := mul_le_mul_of_nonneg_left ih hκ
      _ = ∑ τ : Fin q → ι, κ * Φ ((List.ofFn τ).foldr Eop w) := Finset.mul_sum _ _ _
      _ ≤ ∑ τ : Fin q → ι, ∑ i, Φ (Eop i ((List.ofFn τ).foldr Eop w)) :=
          Finset.sum_le_sum fun τ _ => h _
      _ = _ := by simp only [foldr_ofFn_cons]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simpa using hw`. Consider the case `cons i l ih`. Use `hF i _ _ ih` as an intermediate fact. Simplify `this` using `[List.foldr_cons, List.length_cons, mul_add, add_assoc]`.
-/
lemma foldr_mem_filtration {W ι : Type} (Eop : ι → W → W) (Fil : ℕ → Set W)
    (hF : ∀ i j w, w ∈ Fil j → Eop i w ∈ Fil (j + 2)) (j : ℕ) (w : W) (hw : w ∈ Fil j) (l : List ι) :
    l.foldr Eop w ∈ Fil (j + 2 * l.length) := by
  induction l with
  | nil => simpa using hw
  | cons i l ih =>
    have := hF i _ _ ih
    simpa [List.foldr_cons, List.length_cons, mul_add, add_assoc] using this

/- English proof (translation)
Proceed by induction on `q with`. Consider the case `zero => simp`. Consider the case `succ q ih`. Rewrite using `[sum_fin_succ_cons]`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_le_sum fun τ _ => hN _ _ ?_` and prove the remaining obligations. Use `foldr_mem_filtration Eop Fil hF j w hw (List.ofFn τ)` as an intermediate fact. Simplify using `using this`. Use `_ = c (j + 2 * q) * ∑ τ : Fin q → ι, Nw ((List.ofFn τ).foldr Eop w) := (Finset.mul_sum _ _ _).symm`. Use `_ ≤ c (j + 2 * q) * ((∏ i ∈ range q, c (j + 2 * i)) * Nw w) := mul_le_mul_of_nonneg_left ih (hc _)`.

Use `_ = (∏ i ∈ range (q + 1), c (j + 2 * i)) * Nw w := by rw [Finset.prod_range_succ]; ring`.
-/
lemma filtered_iterate_norm_bound {R W ι : Type} [CommSemiring R] [PartialOrder R] [IsOrderedRing R] [Fintype ι]
    (Eop : ι → W → W) (Nw : W → R) (Fil : ℕ → Set W) (c : ℕ → R) (hc : ∀ j, 0 ≤ c j)
    (hF : ∀ i j w, w ∈ Fil j → Eop i w ∈ Fil (j + 2))
    (hN : ∀ j w, w ∈ Fil j → ∑ i, Nw (Eop i w) ≤ c j * Nw w) (q j : ℕ) (w : W) (hw : w ∈ Fil j) :
    ∑ σ : Fin q → ι, Nw ((List.ofFn σ).foldr Eop w) ≤ (∏ i ∈ range q, c (j + 2 * i)) * Nw w := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [sum_fin_succ_cons]
    calc ∑ τ : Fin q → ι, ∑ i, Nw ((List.ofFn (Fin.cons i τ : Fin (q + 1) → ι)).foldr Eop w)
        = ∑ τ : Fin q → ι, ∑ i, Nw (Eop i ((List.ofFn τ).foldr Eop w)) := by simp only [foldr_ofFn_cons]
      _ ≤ ∑ τ : Fin q → ι, c (j + 2 * q) * Nw ((List.ofFn τ).foldr Eop w) := by
          refine Finset.sum_le_sum fun τ _ => hN _ _ ?_
          have := foldr_mem_filtration Eop Fil hF j w hw (List.ofFn τ)
          simpa using this
      _ = c (j + 2 * q) * ∑ τ : Fin q → ι, Nw ((List.ofFn τ).foldr Eop w) := (Finset.mul_sum _ _ _).symm
      _ ≤ c (j + 2 * q) * ((∏ i ∈ range q, c (j + 2 * i)) * Nw w) := mul_le_mul_of_nonneg_left ih (hc _)
      _ = (∏ i ∈ range (q + 1), c (j + 2 * i)) * Nw w := by rw [Finset.prod_range_succ]; ring

/- English proof (translation)
Introduce `Ω W ι _ _ ν Eop Ph κ Nw Fil c hm hI hk hF hN q j w hw`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_finsetSum _ (fun σ _ => hm _)]`. Conclude with `Finset.sum_congr rfl fun σ _ => hI _`. Use `_ ≤ (∏ i ∈ range q, c (j + 2 * i)) * Nw w := filtered_iterate_norm_bound Eop Nw Fil c (fun _ => zero_le) hF hN q j w hw`.
-/
theorem abstract_iteration_theorem_holds : Formalism.HermitianLatticeCounting.ExpansionTerms.SuperharmonicMomentBound := by
  intro Ω W ι _ _ ν Eop Ph κ Nw Fil c hm hI hk hF hN q j w hw
  calc ∫⁻ g, κ g ^ q * Ph w g ∂ν
      ≤ ∫⁻ g, ∑ σ : Fin q → ι, Ph ((List.ofFn σ).foldr Eop w) g ∂ν :=
        lintegral_mono fun g => iterate_sum_lower_bound Eop (fun w => Ph w g) (κ g) zero_le (fun w => hk w g) q w
    _ = ∑ σ : Fin q → ι, Nw ((List.ofFn σ).foldr Eop w) := by
        rw [lintegral_finsetSum _ (fun σ _ => hm _)]
        exact Finset.sum_congr rfl fun σ _ => hI _
    _ ≤ (∏ i ∈ range q, c (j + 2 * i)) * Nw w :=
        filtered_iterate_norm_bound Eop Nw Fil c (fun _ => zero_le) hF hN q j w hw

noncomputable def lOneNorm {P : Type} (a : P →₀ ℂ) : ℝ := a.sum fun _ c => ‖c‖

/- English proof (translation)
The claim follows from `Finsupp.sum_of_support_subset a hs _ (by simp)`.
-/
lemma lOneNorm_eq_sum {P : Type} (a : P →₀ ℂ) (s : Finset P) (hs : a.support ⊆ s) :
    lOneNorm a = ∑ i ∈ s, ‖a i‖ :=
  Finsupp.sum_of_support_subset a hs _ (by simp)

/- English proof (translation)
Establish `hs : (a + b).support ⊆ a.support ∪ b.support` using `Finsupp.support_add`. Rewrite using `[lOneNorm_eq_sum _ _ hs, lOneNorm_eq_sum a _ Finset.subset_union_left, lOneNorm_eq_sum b _ Finset.subset_union_right, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_le_sum fun i _ => by simpa using norm_add_le (a i) (b i)`.
-/
lemma lOneNorm_add_le {P : Type} (a b : P →₀ ℂ) : lOneNorm (a + b) ≤ lOneNorm a + lOneNorm b := by
  classical
  have hs : (a + b).support ⊆ a.support ∪ b.support := Finsupp.support_add
  rw [lOneNorm_eq_sum _ _ hs, lOneNorm_eq_sum a _ Finset.subset_union_left, lOneNorm_eq_sum b _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by simpa using norm_add_le (a i) (b i)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [lOneNorm]`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi]`. Conclude with `(lOneNorm_add_le _ _).trans (add_le_add le_rfl ih)`.
-/
lemma lOneNorm_sum_le {P κ : Type} (s : Finset κ) (x : κ → P →₀ ℂ) :
    lOneNorm (∑ i ∈ s, x i) ≤ ∑ i ∈ s, lOneNorm (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lOneNorm]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (lOneNorm_add_le _ _).trans (add_le_add le_rfl ih)

/- English proof (translation)
Simplify using `[lOneNorm]`.
-/
lemma lOneNorm_single {P : Type} (p : P) (c : ℂ) : lOneNorm (Finsupp.single p c) = ‖c‖ := by
  simp [lOneNorm]

/- English proof (translation)
Introduce `V P Λ _ _ _ jh Dop wt N1 Ninf lam Gam c0 q0 hGam hN1 hNinf hN10 hNinf0 hstep μ al`. Proceed by induction on `al with`. Consider the case `nil`. Introduce `_`. Use `⟨Finsupp.single 0 1, ?_, ?_, ?_⟩` and prove the remaining obligations.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Introduce `ν hν`. Establish `: ν = 0` using `by simpa using Finsupp.support_single_subset hν`. Substitute `this` using the available equality.

Simplify using `[hN10, hNinf0]`. Consider the case `cons l al ih`. Introduce `hq`. Simplify using `only [List.map_cons, List.sum_cons, List.prod_cons, List.length_cons] at hq ⊢`. Take `⟨a, ha1, ha2, ha3⟩` from `ih (by omega)`.

Establish `hb : ∀ ν, ∃ b : P →₀ ℂ, ν ∈ a.support → (Dop l (jh (μ + ν)) = b.sum (fun ν' c => c • jh (μ + ν + ν')) ∧ (b.sum fun _ c => ‖c‖) ≤ Gam ^ wt l ∧ ∀ ν' ∈ b.support, N1 ν' ≤ wt l ∧ Ninf ν' ≤ 1)`. Introduce `ν`. Distinguish the cases in `hν : ν ∈ a.support`. Establish `h1` using `(ha3 ν hν).1`. Establish `h2 : N1 (μ + ν - lam) ≤ N1 (μ - lam) + N1 ν`.

Establish `: μ + ν - lam = (μ - lam) + ν` using `by abel`. Rewrite using `[this]`. Conclude with `hN1 _ _`. Take `⟨b, hb⟩` from `hstep (μ + ν) l (by omega)`. Conclude with `⟨b, fun _ => hb⟩`.

Conclude with `⟨0, fun h => absurd h hν⟩`. Use `choose b hb using hb`. Set `a' : P →₀ ℂ` to `∑ ν ∈ a.support, ∑ ν' ∈ (b ν).support, Finsupp.single (ν + ν') (a ν * b ν ν')`. Use `⟨a', ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.End.mul_apply, ha1]`.

Establish `hΨ : a'.sum (fun ν c => c • jh (μ + ν)) = Finsupp.linearCombination ℂ (fun ν => jh (μ + ν)) a'` using `(Finsupp.linearCombination_apply ℂ a').symm`. Rewrite using `[hΨ]`. Simplify using `only [a', map_sum, Finsupp.linearCombination_single]`. Rewrite using `[Finsupp.sum, map_sum]`. Use `Finset.sum_congr rfl fun ν hν => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, (hb ν hν).1, Finsupp.sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun ν' _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul, add_assoc]`. Establish `h1 : lOneNorm a' ≤ ∑ ν ∈ a.support, ∑ ν' ∈ (b ν).support, ‖a ν‖ * ‖b ν ν'‖`. Use `(lOneNorm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => ?_)` and prove the remaining obligations.

Use `(lOneNorm_sum_le _ _).trans (Finset.sum_le_sum fun ν' _ => ?_)` and prove the remaining obligations. Rewrite using `[lOneNorm_single, norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun ν hν => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum]`.

Conclude with `mul_le_mul_of_nonneg_left (hb ν hν).2.1 (norm_nonneg _)`. Use `_ = (a.sum fun _ c => ‖c‖) * Gam ^ wt l := by rw [Finsupp.sum, Finset.sum_mul]`. Use `_ ≤ Gam ^ (al.map wt).sum * Gam ^ wt l := by gcongr`. Use `_ = Gam ^ (wt l + (al.map wt).sum) := by rw [← pow_add, add_comm]`. Introduce `ν'' h`.

Establish `h1` using `Finsupp.support_finsetSum h`. Rewrite `h1` using `[Finset.mem_biUnion]`. Take `⟨ν, hν, h2⟩` from `h1`. Establish `h3` using `Finsupp.support_finsetSum h2`. Rewrite `h3` using `[Finset.mem_biUnion]`.

Take `⟨ν', hν', h4⟩` from `h3`. Establish `h5 : ν'' = ν + ν'` using `by simpa using Finsupp.support_single_subset h4`. Substitute `h5` using the available equality. Establish `e1` using `hN1 ν ν'`. Establish `e2` using `hNinf ν ν'`.

Establish `e3` using `ha3 ν hν`. Establish `e4` using `(hb ν hν).2.2 ν' hν'`. Apply the tactic sequence `constructor <;> omega`.
-/
theorem iterated_sum_bound_holds : Formalism.HermitianLatticeCounting.ExpansionTerms.IteratedHighestWeightBound := by
  classical
  intro V P Λ _ _ _ jh Dop wt N1 Ninf lam Gam c0 q0 hGam hN1 hNinf hN10 hNinf0 hstep μ al
  induction al with
  | nil =>
    intro _
    refine ⟨Finsupp.single 0 1, ?_, ?_, ?_⟩
    · simp
    · simp
    · intro ν hν
      have : ν = 0 := by simpa using Finsupp.support_single_subset hν
      subst this
      simp [hN10, hNinf0]
  | cons l al ih =>
    intro hq
    simp only [List.map_cons, List.sum_cons, List.prod_cons, List.length_cons] at hq ⊢
    obtain ⟨a, ha1, ha2, ha3⟩ := ih (by omega)
    have hb : ∀ ν, ∃ b : P →₀ ℂ, ν ∈ a.support →
        (Dop l (jh (μ + ν)) = b.sum (fun ν' c => c • jh (μ + ν + ν')) ∧
        (b.sum fun _ c => ‖c‖) ≤ Gam ^ wt l ∧ ∀ ν' ∈ b.support, N1 ν' ≤ wt l ∧ Ninf ν' ≤ 1) := by
      intro ν
      by_cases hν : ν ∈ a.support
      · have h1 := (ha3 ν hν).1
        have h2 : N1 (μ + ν - lam) ≤ N1 (μ - lam) + N1 ν := by
          have : μ + ν - lam = (μ - lam) + ν := by abel
          rw [this]
          exact hN1 _ _
        obtain ⟨b, hb⟩ := hstep (μ + ν) l (by omega)
        exact ⟨b, fun _ => hb⟩
      · exact ⟨0, fun h => absurd h hν⟩
    choose b hb using hb
    let a' : P →₀ ℂ := ∑ ν ∈ a.support, ∑ ν' ∈ (b ν).support, Finsupp.single (ν + ν') (a ν * b ν ν')
    refine ⟨a', ?_, ?_, ?_⟩
    · rw [Module.End.mul_apply, ha1]
      have hΨ : a'.sum (fun ν c => c • jh (μ + ν)) =
          Finsupp.linearCombination ℂ (fun ν => jh (μ + ν)) a' :=
        (Finsupp.linearCombination_apply ℂ a').symm
      rw [hΨ]
      simp only [a', map_sum, Finsupp.linearCombination_single]
      rw [Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl fun ν hν => ?_
      rw [map_smul, (hb ν hν).1, Finsupp.sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun ν' _ => ?_
      rw [mul_smul, add_assoc]
    · have h1 : lOneNorm a' ≤ ∑ ν ∈ a.support, ∑ ν' ∈ (b ν).support, ‖a ν‖ * ‖b ν ν'‖ := by
        refine (lOneNorm_sum_le _ _).trans (Finset.sum_le_sum fun ν _ => ?_)
        refine (lOneNorm_sum_le _ _).trans (Finset.sum_le_sum fun ν' _ => ?_)
        rw [lOneNorm_single, norm_mul]
      calc (a'.sum fun _ c => ‖c‖) ≤ ∑ ν ∈ a.support, ∑ ν' ∈ (b ν).support, ‖a ν‖ * ‖b ν ν'‖ := h1
        _ ≤ ∑ ν ∈ a.support, ‖a ν‖ * Gam ^ wt l := by
            refine Finset.sum_le_sum fun ν hν => ?_
            rw [← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_left (hb ν hν).2.1 (norm_nonneg _)
        _ = (a.sum fun _ c => ‖c‖) * Gam ^ wt l := by rw [Finsupp.sum, Finset.sum_mul]
        _ ≤ Gam ^ (al.map wt).sum * Gam ^ wt l := by gcongr
        _ = Gam ^ (wt l + (al.map wt).sum) := by rw [← pow_add, add_comm]
    · intro ν'' h
      have h1 := Finsupp.support_finsetSum h
      rw [Finset.mem_biUnion] at h1
      obtain ⟨ν, hν, h2⟩ := h1
      have h3 := Finsupp.support_finsetSum h2
      rw [Finset.mem_biUnion] at h3
      obtain ⟨ν', hν', h4⟩ := h3
      have h5 : ν'' = ν + ν' := by simpa using Finsupp.support_single_subset h4
      subst h5
      have e1 := hN1 ν ν'
      have e2 := hNinf ν ν'
      have e3 := ha3 ν hν
      have e4 := (hb ν hν).2.2 ν' hν'
      constructor <;> omega

end G8

section Compose
open Formalism.HermitianLatticeCounting.ExpansionTerms

/- English proof (translation)
The claim follows from `separated_set_sum_bound_of_disjoint_integral disjointness_of_supports_holds inverse_power_integral_pi`.
-/
theorem separated_sum_estimate_second_holds : Formalism.HermitianLatticeCounting.ExpansionTerms.SeparatedSetSumBound := separated_set_sum_bound_of_disjoint_integral disjointness_of_supports_holds inverse_power_integral_pi
/- English proof (translation)
The claim follows from `separated_cutoff_sum_of_disjoint_polydiscs disjointness_of_supports_holds cutoff_integral_formula`.
-/
theorem separated_sum_estimate_holds : Formalism.HermitianLatticeCounting.ExpansionTerms.SeparatedCutoffSum := separated_cutoff_sum_of_disjoint_polydiscs disjointness_of_supports_holds cutoff_integral_formula
/- English proof (translation)
The claim follows from `gaussian_lattice_cutoff_sum_of_separated_cutoff_sum separated_sum_estimate_holds`.
-/
theorem gaussian_lattice_cutoff_sum : Formalism.HermitianLatticeCounting.ExpansionTerms.GaussianLatticeCutoffSum := gaussian_lattice_cutoff_sum_of_separated_cutoff_sum separated_sum_estimate_holds
/- English proof (translation)
The claim follows from `ideal_inverse_power_sum_of_norm_separated ideal_norm_product_lower_bound separated_sum_estimate_second_holds`.
-/
theorem ideal_sum_estimate_second_holds : Formalism.HermitianLatticeCounting.ExpansionTerms.IdealInversePowerSum := ideal_inverse_power_sum_of_norm_separated ideal_norm_product_lower_bound separated_sum_estimate_second_holds
/- English proof (translation)
The claim follows from `block_minor_sum_explicit_of_fibre_finite_of_prod_bound block_end_minor_fibre_finite' composition_block_prod_bound ideal_sum_estimate_second_holds`.
-/
theorem block_minor_sum_explicit : Formalism.HermitianLatticeCounting.ExpansionTerms.BlockMinorSumExplicit := block_minor_sum_explicit_of_fibre_finite_of_prod_bound block_end_minor_fibre_finite' composition_block_prod_bound ideal_sum_estimate_second_holds
/- English proof (translation)
The claim follows from `blockMinorSumPowSixtyFour_of_blockMinorSumExplicit block_minor_sum_explicit`.
-/
theorem block_minor_sum_pow_sixty_four : Formalism.HermitianLatticeCounting.ExpansionTerms.BlockMinorSumPowSixtyFour := blockMinorSumPowSixtyFour_of_blockMinorSumExplicit block_minor_sum_explicit

end Compose

end Formalism.HermitianLatticeCounting.P
