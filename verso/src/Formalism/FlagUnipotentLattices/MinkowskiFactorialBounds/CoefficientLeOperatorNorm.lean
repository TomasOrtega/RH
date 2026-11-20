import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound

open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder

namespace Formalism.HermitianLatticeCounting.P

/- English proof (translation)
Introduce `lam a b hab`. Proceed by induction on `a, hab using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ a hab ih`. Rewrite using `[Finset.sum_Ico_succ_top hab, ih]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gap_sum_bound : GapSum := by
  intro lam a b hab
  induction a, hab using Nat.le_induction with
  | base => simp
  | succ a hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih]; push_cast; ring

/- English proof (translation)
Introduce `H _ _ E U w hE hw hn`. Establish `: inner ℂ w (U w) = inner ℂ w ((E ∘L U ∘L E) w)`. Simplify using `only [ContinuousLinearMap.comp_apply, hw]`. Rewrite using `[← hE, hw]`. Rewrite using `[this]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem coefficient_le_operator_norm : CoeffLeOp := by
  intro H _ _ E U w hE hw hn
  have : inner ℂ w (U w) = inner ℂ w ((E ∘L U ∘L E) w) := by
    simp only [ContinuousLinearMap.comp_apply, hw]
    rw [← hE, hw]
  rw [this]
  calc ‖inner ℂ w ((E ∘L U ∘L E) w)‖ ≤ ‖w‖ * ‖(E ∘L U ∘L E) w‖ := norm_inner_le_norm _ _
    _ ≤ ‖w‖ * (‖E ∘L U ∘L E‖ * ‖w‖) := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ = _ := by rw [hn]; ring

/- English proof (translation)
Introduce `G H _ _ U P m hP hPU v hv hn g`. Establish `h1` using `congrArg (fun T : H →L[ℂ] H => T v) (hPU g)`. Simplify using `only [ContinuousLinearMap.comp_apply, hv, _root_.smul_apply] at h1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem projection_coefficient : ProjCoeff := by
  intro G H _ _ U P m hP hPU v hv hn g
  have h1 := congrArg (fun T : H →L[ℂ] H => T v) (hPU g)
  simp only [ContinuousLinearMap.comp_apply, hv, _root_.smul_apply] at h1
  calc inner ℂ v (U g v) = inner ℂ (P v) (U g v) := by rw [hv]
    _ = inner ℂ v (P (U g v)) := hP _ _
    _ = inner ℂ v (m g • v) := by rw [h1]
    _ = m g := by rw [inner_smul_right, inner_self_eq_norm_sq_to_K, hn]; simp

/- English proof (translation)
Introduce `q ε s hq hε h1 hs`. Establish `hq' : (1:ℝ) ≤ q` using `by exact_mod_cast hq`. Establish `hs0 : 0 < Real.sqrt (2 * (q:ℝ))` using `Real.sqrt_pos.mpr (by linarith)`. Use `le_min (by nlinarith) ?_` and prove the remaining obligations. Rewrite using `[le_div_iff₀ hs0]`.

Establish `: 0 < s` using `by linarith`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem minimum_linear_form : MinLinear := by
  intro q ε s hq hε h1 hs
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hs0 : 0 < Real.sqrt (2 * (q:ℝ)) := Real.sqrt_pos.mpr (by linarith)
  refine le_min (by nlinarith) ?_
  rw [le_div_iff₀ hs0]
  have : 0 < s := by linarith
  nlinarith

/- English proof (translation)
Introduce `a θ Θ P₀ hθ ha hstep`. Proceed by induction on `P₀ with`. Consider the case `zero => simp`. Consider the case `succ P ih`. Establish `h1` using `ih (fun Q hQ => hθ Q (by omega)) (fun Q hQ => hstep Q (by omega))`.

Establish `h2` using `hstep P (by omega)`. Establish `h3` using `hθ P (by omega)`. Establish `hΘ : 0 ≤ Θ` using `h3.1.trans h3.2`. Combine the equalities or inequalities in the displayed calculation. Conclude with `h2.trans (mul_le_mul_of_nonneg_right h3.2 (ha _))`.

Use `_ = _ := by ring`.
-/
theorem iterated_supremum_bound : IterSup := by
  intro a θ Θ P₀ hθ ha hstep
  induction P₀ with
  | zero => simp
  | succ P ih =>
    have h1 := ih (fun Q hQ => hθ Q (by omega)) (fun Q hQ => hstep Q (by omega))
    have h2 := hstep P (by omega)
    have h3 := hθ P (by omega)
    have hΘ : 0 ≤ Θ := h3.1.trans h3.2
    calc a 0 ≤ Θ ^ P * a P := h1
      _ ≤ Θ ^ P * (Θ * a (P + 1)) := by
          gcongr
          exact h2.trans (mul_le_mul_of_nonneg_right h3.2 (ha _))
      _ = _ := by ring

/- English proof (translation)
Introduce `q`. Simplify using `only [composition_card]`. Proceed by induction on `q with`. Consider the case `zero => simp`. Consider the case `succ q ih`.

Rewrite using `[Finset.sum_Icc_succ_top (by omega)]`. Simplify using `only [Nat.add_sub_cancel]`. Rewrite using `[pow_succ]`. Use linear arithmetic over natural numbers and integers.
-/
theorem type_count : TypeCount := by
  intro q
  simp only [composition_card]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp only [Nat.add_sub_cancel]
    rw [pow_succ]; omega

/- English proof (translation)
Introduce `X ι _ μ _ _ F h`. Establish `e : ∀ w x, star (F w x) * F w x = ((‖F w x‖^2 : ℝ) : ℂ)`. Introduce `w x`. Rewrite using `[Complex.star_def, Complex.conj_mul']`. Use `push_cast`.

Both sides reduce to the same expression. Establish `h1 : ∀ w, (∫ x, ((‖F w x‖^2 : ℝ) : ℂ) ∂μ) = 1`. Introduce `w`. Use `h w w` as an intermediate fact. Simplify using `only [e, if_true] at this`.

Conclude with `this`. Establish `hint : ∀ w, Integrable (fun x => ‖F w x‖^2) μ`. Introduce `w`. Assume the negation of the conclusion as `hn`. Establish `h2 : ¬ Integrable (fun x => ((‖F w x‖^2 : ℝ) : ℂ)) μ` using `fun hi => hn (by`.

Establish `h4` using `hi.re`. Simplify `h4)` using `[← Complex.ofReal_pow]`. Establish `h3` using `integral_undef h2`. Rewrite `h3` using `[h1 w]`. Conclude with `one_ne_zero h3`.

Rewrite using `[integral_finsetSum _ (fun w _ => hint w)]`. Establish `h2 : ∀ w, ∫ x, ‖F w x‖^2 ∂μ = 1`. Introduce `w`. Use `h1 w` as an intermediate fact. Rewrite `this` using `[integral_complex_ofReal]`.

Conclude with `this` after adjusting the coercions. Simplify using `[h2]`.
-/
theorem trace_diagonal_bis : TraceDiag := by
  intro X ι _ μ _ _ F h
  have e : ∀ w x, star (F w x) * F w x = ((‖F w x‖^2 : ℝ) : ℂ) := by
    intro w x
    rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  have h1 : ∀ w, (∫ x, ((‖F w x‖^2 : ℝ) : ℂ) ∂μ) = 1 := by
    intro w
    have := h w w
    simp only [e, if_true] at this
    exact this
  have hint : ∀ w, Integrable (fun x => ‖F w x‖^2) μ := by
    intro w
    by_contra hn
    have h2 : ¬ Integrable (fun x => ((‖F w x‖^2 : ℝ) : ℂ)) μ := fun hi => hn (by
      have h4 := hi.re
      simpa [← Complex.ofReal_pow] using h4)
    have h3 := integral_undef h2
    rw [h1 w] at h3
    exact one_ne_zero h3
  rw [integral_finsetSum _ (fun w _ => hint w)]
  have h2 : ∀ w, ∫ x, ‖F w x‖^2 ∂μ = 1 := by
    intro w
    have := h1 w
    rw [integral_complex_ofReal] at this
    exact_mod_cast this
  simp [h2]

/- English proof (translation)
Introduce `f j n0 hf hj hn`. Establish `hpos : 1 ≤ j * n0 * f` using `Nat.one_le_iff_ne_zero.mpr (by positivity)`. Take `⟨M, hM⟩ : ∃ M, 2 * j * n0 * f = (M + 1) + 1` from `⟨2 * (j * n0 * f) - 2, by`. Establish `: 2 * j * n0 * f = 2 * (j * n0 * f)` using `by ring`. Use the proof step `omega⟩`.

Establish `e : ∀ t : ℝ, t ^ (2 * j * n0 * f) * (2 * (f:ℝ) * j / t) = 2 * (f:ℝ) * j * t ^ (M + 1)`. Introduce `t`. Rewrite using `[hM]`. Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality.

Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e]`. Rewrite using `[intervalIntegral.integral_const_mul, integral_pow]`.

Establish `hMr : ((M + 1 : ℕ) : ℝ) + 1 = 2 * j * n0 * f` using `by exact_mod_cast hM.symm`. Rewrite using `[hM, hMr]`. Establish `: (0:ℝ) < j` using `by exact_mod_cast hj`. Establish `: (0:ℝ) < f` using `by exact_mod_cast hf`. Establish `: (0:ℝ) < n0` using `by exact_mod_cast hn`.

Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules.
-/
theorem tau_integral_formula : TauIntegral := by
  intro f j n0 hf hj hn
  have hpos : 1 ≤ j * n0 * f := Nat.one_le_iff_ne_zero.mpr (by positivity)
  obtain ⟨M, hM⟩ : ∃ M, 2 * j * n0 * f = (M + 1) + 1 := ⟨2 * (j * n0 * f) - 2, by
    have : 2 * j * n0 * f = 2 * (j * n0 * f) := by ring
    omega⟩
  have e : ∀ t : ℝ, t ^ (2 * j * n0 * f) * (2 * (f:ℝ) * j / t) = 2 * (f:ℝ) * j * t ^ (M + 1) := by
    intro t
    rw [hM]
    by_cases ht : t = 0
    · subst ht; simp
    · field_simp
      ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  have hMr : ((M + 1 : ℕ) : ℝ) + 1 = 2 * j * n0 * f := by exact_mod_cast hM.symm
  rw [hM, hMr]
  have : (0:ℝ) < j := by exact_mod_cast hj
  have : (0:ℝ) < f := by exact_mod_cast hf
  have : (0:ℝ) < n0 := by exact_mod_cast hn
  field_simp
  simp

/- English proof (translation)
Introduce `X _ μ _ K Rm Mod k0 hM hK hKR`. Rewrite using `[← integral_add_compl hM hK]`. Use `congr 1`. Establish `hR : IntegrableOn Rm Mod μ`. Establish `: IntegrableOn (fun x => K x - k0) Mod μ` using `hK.integrableOn.sub (integrable_const _)`.

Use `this.congr_fun (fun x hx => ?_) hM` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hKR x hx]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[setIntegral_congr_fun hM hKR, integral_add (integrable_const _) hR]`.

Simplify using `[mul_comm, Measure.real]`.
-/
theorem diagonal_splitting : DiagSplit := by
  intro X _ μ _ K Rm Mod k0 hM hK hKR
  rw [← integral_add_compl hM hK]
  congr 1
  have hR : IntegrableOn Rm Mod μ := by
    have : IntegrableOn (fun x => K x - k0) Mod μ := hK.integrableOn.sub (integrable_const _)
    refine this.congr_fun (fun x hx => ?_) hM
    simp only
    rw [hKR x hx]; ring
  rw [setIntegral_congr_fun hM hKR, integral_add (integrable_const _) hR]
  simp [mul_comm, Measure.real]

/- English proof (translation)
Introduce `G H _ _ U P m hP hPU v hv hcyc v' hv'`. Establish `h1 : ∀ g, P (U g v) = m g • v`. Introduce `g`. Establish `h1` using `congrArg (fun T : H →L[ℂ] H => T v) (hPU g)`. Simplify `h1` using `[hv]`.

Establish `hle : Submodule.span ℂ (Set.range fun g => U g v) ≤ (Submodule.span ℂ {v}).comap (P : H →ₗ[ℂ] H)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨g, rfl⟩`. Simplify using `only [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe, h1]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)`.

Establish `hclosed : IsClosed (((Submodule.span ℂ {v}).comap (P : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H)`. Establish `: IsClosed ((Submodule.span ℂ {v} : Submodule ℂ H) : Set H)` using `Submodule.closed_of_finiteDimensional _`. Conclude with `this.preimage P.continuous`. Establish `htop` using `Submodule.topologicalClosure_minimal _ hle hclosed`. Rewrite `htop` using `[hcyc]`.

Establish `: v' ∈ (Submodule.span ℂ {v}).comap (P : H →ₗ[ℂ] H)` using `htop trivial`. Simplify using `only [Submodule.mem_comap, ContinuousLinearMap.coe_coe, hv'] at this`. Take `⟨c, hc⟩` from `Submodule.mem_span_singleton.mp this`. Conclude with `⟨c, hc.symm⟩`.
-/
theorem rank_one_case : RankOne := by
  intro G H _ _ U P m hP hPU v hv hcyc v' hv'
  have h1 : ∀ g, P (U g v) = m g • v := by
    intro g
    have h1 := congrArg (fun T : H →L[ℂ] H => T v) (hPU g)
    simpa [hv] using h1
  have hle : Submodule.span ℂ (Set.range fun g => U g v) ≤ (Submodule.span ℂ {v}).comap (P : H →ₗ[ℂ] H) := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe, h1]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  have hclosed : IsClosed (((Submodule.span ℂ {v}).comap (P : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) := by
    have : IsClosed ((Submodule.span ℂ {v} : Submodule ℂ H) : Set H) := Submodule.closed_of_finiteDimensional _
    exact this.preimage P.continuous
  have htop := Submodule.topologicalClosure_minimal _ hle hclosed
  rw [hcyc] at htop
  have : v' ∈ (Submodule.span ℂ {v}).comap (P : H →ₗ[ℂ] H) := htop trivial
  simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe, hv'] at this
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
  exact ⟨c, hc.symm⟩

/- English proof (translation)
Introduce `C₂`. Establish `hl2 : 0 < Real.log 2` using `Real.log_pos (by norm_num)`. Use `⟨(120 + |C₂|) / Real.log 2, by positivity, ?_⟩` and prove the remaining obligations. Introduce `n q f b rd h hn hf hq hb hrd hh`. Establish `hn' : (1:ℝ) ≤ n` using `by exact_mod_cast hn`.

Establish `hf' : (1:ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `hqn : (q:ℝ)^2 ≤ n` using `by exact_mod_cast hq`. Establish `hq0 : (0:ℝ) ≤ q` using `Nat.cast_nonneg _`. Establish `hqn1 : (q:ℝ) ≤ n`. Establish `: q ≤ n` using `le_trans (Nat.le_self_pow (by norm_num) q) hq`.

Conclude with `this` after adjusting the coercions. Establish `hlog : Real.log 2 ≤ Real.log (b * rd)` using `Real.log_le_log (by norm_num) (by nlinarith)`. Establish `h19 : 0 < (n:ℝ)^19` using `by positivity`. Establish `hK : (120 + |C₂|) * (n:ℝ)^19 ≤ h`. Use `le_trans ?_ hh` and prove the remaining obligations.

Establish `h1 : (1:ℝ) ≤ (f:ℝ)^5` using `one_le_pow₀ hf'`. Establish `hA : 0 ≤ 120 + |C₂|` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts. Use `_ ≤ (120 + |C₂|) / Real.log 2 * (n:ℝ)^19 * (f:ℝ)^5 * Real.log (b*rd) := by gcongr`.

Establish `hq32 : (q:ℝ)^((3:ℝ)/2) ≤ n`. Break down `Nat.eq_zero_or_pos q with rfl | hqp` into its components or cases. Rewrite using `[Nat.cast_zero, Real.zero_rpow (by norm_num)]; positivity`. Establish `h1 : (1:ℝ) ≤ q` using `by exact_mod_cast hqp`. Combine the equalities or inequalities in the displayed calculation.

Establish `hsq : Real.sqrt q ≤ n` using `Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩`. Establish `hp2 : (n:ℝ)^2 ≤ (n:ℝ)^19` using `pow_le_pow_right₀ hn' (by norm_num)`. Establish `hp3 : (n:ℝ)^3 ≤ (n:ℝ)^19` using `pow_le_pow_right₀ hn' (by norm_num)`. Establish `hC : 0 ≤ |C₂| * (n:ℝ)^19` using `by positivity`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_abs_self _`. Use `_ = |C₂| * (n:ℝ)^3 := by ring`. Use `_ ≤ |C₂| * (n:ℝ)^19 := by gcongr`.

Use `_ ≤ h := by linarith`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem threshold_head_region : ThreshHead := by
  intro C₂
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(120 + |C₂|) / Real.log 2, by positivity, ?_⟩
  intro n q f b rd h hn hf hq hb hrd hh
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hqn : (q:ℝ)^2 ≤ n := by exact_mod_cast hq
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have hqn1 : (q:ℝ) ≤ n := by
    have : q ≤ n := le_trans (Nat.le_self_pow (by norm_num) q) hq
    exact_mod_cast this
  have hlog : Real.log 2 ≤ Real.log (b * rd) := Real.log_le_log (by norm_num) (by nlinarith)
  have h19 : 0 < (n:ℝ)^19 := by positivity
  have hK : (120 + |C₂|) * (n:ℝ)^19 ≤ h := by
    refine le_trans ?_ hh
    have h1 : (1:ℝ) ≤ (f:ℝ)^5 := one_le_pow₀ hf'
    have hA : 0 ≤ 120 + |C₂| := by positivity
    calc (120 + |C₂|) * (n:ℝ)^19 = (120 + |C₂|) / Real.log 2 * (n:ℝ)^19 * 1 * Real.log 2 := by
          field_simp
      _ ≤ (120 + |C₂|) / Real.log 2 * (n:ℝ)^19 * (f:ℝ)^5 * Real.log (b*rd) := by gcongr
  have hq32 : (q:ℝ)^((3:ℝ)/2) ≤ n := by
    rcases Nat.eq_zero_or_pos q with rfl | hqp
    · rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]; positivity
    · have h1 : (1:ℝ) ≤ q := by exact_mod_cast hqp
      calc (q:ℝ)^((3:ℝ)/2) ≤ (q:ℝ)^((2:ℝ)) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
        _ = (q:ℝ)^2 := Real.rpow_two _
        _ ≤ n := hqn
  have hsq : Real.sqrt q ≤ n := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hp2 : (n:ℝ)^2 ≤ (n:ℝ)^19 := pow_le_pow_right₀ hn' (by norm_num)
  have hp3 : (n:ℝ)^3 ≤ (n:ℝ)^19 := pow_le_pow_right₀ hn' (by norm_num)
  have hC : 0 ≤ |C₂| * (n:ℝ)^19 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · calc 120 * (n:ℝ) * (q:ℝ)^((3:ℝ)/2) ≤ 120 * (n:ℝ) * n := by gcongr
      _ = 120 * (n:ℝ)^2 := by ring
      _ ≤ h := by linarith
  · calc C₂ * (n:ℝ)^2 * Real.sqrt q ≤ |C₂| * (n:ℝ)^2 * n := by
          gcongr
          exact le_abs_self _
      _ = |C₂| * (n:ℝ)^3 := by ring
      _ ≤ |C₂| * (n:ℝ)^19 := by gcongr
      _ ≤ h := by linarith
  · calc 32 * (n:ℝ) * q ≤ 32 * (n:ℝ) * n := by gcongr
      _ = 32 * (n:ℝ)^2 := by ring
      _ < h := by linarith

/- English proof (translation)
Introduce `n q f c hn hf hq hc hc9`. Establish `hn' : (1:ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hf' : (1:ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `hqn1 : (q:ℝ) ≤ n`. Establish `: q ≤ n` using `le_trans (Nat.le_self_pow (by norm_num) q) hq`.

Conclude with `this` after adjusting the coercions. Establish `hq0 : (0:ℝ) ≤ q` using `Nat.cast_nonneg _`. Establish `hn0 : (0:ℝ) < n` using `by linarith`. Establish `hf0 : (0:ℝ) < f` using `by linarith`. Establish `e1 : (n:ℝ) * epsN c n f = c / ((n:ℝ)^7 * (f:ℝ)^2)`.

Unfold `epsN`. Clear the denominators using the available nonvanishing facts. Establish `k1 : (n:ℝ) * epsN c n f ≤ (1 / (300 * (n:ℝ)^3 * f))^2`. Rewrite using `[e1]`. Establish `e2 : (1 / (300 * (n:ℝ)^3 * f))^2 = (1/90000) / ((n:ℝ)^6 * (f:ℝ)^2)` using `by field_simp; norm_num`.

Rewrite using `[e2]`. Apply `div_le_div₀ (by norm_num) hc9 (by positivity)` to reduce the goal to its premises. Establish `: (n:ℝ)^6 ≤ (n:ℝ)^7` using `pow_le_pow_right₀ hn' (by norm_num)`. Use `gcongr`. Establish `k2 : Real.sqrt ((n:ℝ) * epsN c n f) ≤ 1 / (300 * (n:ℝ)^3 * f)` using `Real.sqrt_le_iff.mpr ⟨by positivity, k1⟩`.

Establish `hn3 : (1:ℝ) ≤ (n:ℝ)^3` using `one_le_pow₀ hn'`. Establish `k3 : 1 / (300 * (n:ℝ)^3 * f) ≤ 1 / 300`. Apply `div_le_div_of_nonneg_left (by norm_num) (by norm_num)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `he0 : 0 < epsN c n f` using `by unfold epsN; positivity`.

Establish `k4 : (n:ℝ) * epsN c n f ≤ 1`. Use `k1.trans ?_` and prove the remaining obligations. Establish `: 0 ≤ 1 / (300 * (n:ℝ)^3 * f)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Use `⟨?_, by linarith, k4, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Apply `div_le_div_of_nonneg_left (by norm_num) (by norm_num)` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: (n:ℝ) * epsN c n f ≤ (1/300)^2`. Use `k1.trans ?_` and prove the remaining obligations.

Establish `: 0 ≤ 1 / (300 * (n:ℝ)^3 * f)` using `by positivity`. Use `gcongr`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem delta_small : DeltaSmall := by
  intro n q f c hn hf hq hc hc9
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hqn1 : (q:ℝ) ≤ n := by
    have : q ≤ n := le_trans (Nat.le_self_pow (by norm_num) q) hq
    exact_mod_cast this
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have hn0 : (0:ℝ) < n := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  have e1 : (n:ℝ) * epsN c n f = c / ((n:ℝ)^7 * (f:ℝ)^2) := by
    unfold epsN; field_simp
  have k1 : (n:ℝ) * epsN c n f ≤ (1 / (300 * (n:ℝ)^3 * f))^2 := by
    rw [e1]
    have e2 : (1 / (300 * (n:ℝ)^3 * f))^2 = (1/90000) / ((n:ℝ)^6 * (f:ℝ)^2) := by
      field_simp; norm_num
    rw [e2]
    apply div_le_div₀ (by norm_num) hc9 (by positivity)
    have : (n:ℝ)^6 ≤ (n:ℝ)^7 := pow_le_pow_right₀ hn' (by norm_num)
    gcongr
  have k2 : Real.sqrt ((n:ℝ) * epsN c n f) ≤ 1 / (300 * (n:ℝ)^3 * f) :=
    Real.sqrt_le_iff.mpr ⟨by positivity, k1⟩
  have hn3 : (1:ℝ) ≤ (n:ℝ)^3 := one_le_pow₀ hn'
  have k3 : 1 / (300 * (n:ℝ)^3 * f) ≤ 1 / 300 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have he0 : 0 < epsN c n f := by unfold epsN; positivity
  have k4 : (n:ℝ) * epsN c n f ≤ 1 := by
    refine k1.trans ?_
    have : 0 ≤ 1 / (300 * (n:ℝ)^3 * f) := by positivity
    nlinarith
  refine ⟨?_, by linarith, k4, ?_⟩
  · calc 3 * Real.sqrt ((n:ℝ) * epsN c n f) * q * n * f
        ≤ 3 * (1 / (300 * (n:ℝ)^3 * f)) * n * n * f := by gcongr
      _ = 1 / (100 * n) := by field_simp; norm_num
      _ ≤ 1 / 100 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        linarith
  · have : (n:ℝ) * epsN c n f ≤ (1/300)^2 := by
      refine k1.trans ?_
      have : 0 ≤ 1 / (300 * (n:ℝ)^3 * f) := by positivity
      gcongr
    nlinarith

/- English proof (translation)
Introduce `n f N rd ρ hf hN hrd hρ`. Establish `hf' : (1:ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `hN' : (N:ℝ) ≤ 2 * (n:ℝ)^2 * f` using `by exact_mod_cast hN`. Establish `hs0 : 0 < Real.sqrt (f:ℝ)` using `Real.sqrt_pos.mpr (by linarith)`. Establish `hss : Real.sqrt (f:ℝ) * Real.sqrt (f:ℝ) = f` using `Real.mul_self_sqrt (by linarith)`.

Establish `hs1 : 1 ≤ Real.sqrt (f:ℝ)` using `Real.one_le_sqrt.mpr hf'`. Establish `h52 : (f:ℝ)^((5:ℝ)/2) = (f:ℝ)^2 * Real.sqrt f`. Rewrite using `[Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add (by linarith)]; norm_num`. Establish `hN0 : (0:ℝ) ≤ N` using `Nat.cast_nonneg _`. Establish `hn0 : (0:ℝ) ≤ n` using `Nat.cast_nonneg _`.

Rewrite using `[h52]`. Generalize the expression as in `Real.sqrt (f:ℝ) = s at *`. Establish `hfs : (f:ℝ) = s * s` using `hss.symm`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[div_le_iff₀ (by positivity)]`.

Establish `: 2 * (n:ℝ)^2 * s * rd * ρ * (s / (2 * rd * ρ)) = (n:ℝ)^2 * (s * s)` using `by field_simp`. Rewrite using `[this, ← hfs]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[div_le_iff₀ (by positivity)]`. Establish `: 8 * (n:ℝ)^4 * ((f:ℝ)^2 * s) * rd * ρ * (s / (2 * rd * ρ)) = 4 * (n:ℝ)^4 * (f:ℝ)^2 * (s * s)` using `by field_simp; ring`.

Rewrite using `[this, ← hfs]`. Establish `h2 : (N:ℝ)^2 ≤ (2 * (n:ℝ)^2 * f)^2` using `by gcongr`. Establish `h3 : (2 * (n:ℝ)^2 * f)^2 * 1 ≤ (2 * (n:ℝ)^2 * f)^2 * f` using `by gcongr`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[div_le_iff₀ (by positivity)]`.

Establish `: 8 * (n:ℝ)^6 * ((f:ℝ)^2 * s) * rd * ρ * (2 * (s / (2 * rd * ρ))) = 8 * (n:ℝ)^6 * (f:ℝ)^2 * (s * s)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this, ← hfs]`. Establish `h2 : (N:ℝ)^3 ≤ (2 * (n:ℝ)^2 * f)^3` using `by gcongr`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem covering_arithmetic : CoverArith := by
  intro n f N rd ρ hf hN hrd hρ
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hN' : (N:ℝ) ≤ 2 * (n:ℝ)^2 * f := by exact_mod_cast hN
  have hs0 : 0 < Real.sqrt (f:ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hss : Real.sqrt (f:ℝ) * Real.sqrt (f:ℝ) = f := Real.mul_self_sqrt (by linarith)
  have hs1 : 1 ≤ Real.sqrt (f:ℝ) := Real.one_le_sqrt.mpr hf'
  have h52 : (f:ℝ)^((5:ℝ)/2) = (f:ℝ)^2 * Real.sqrt f := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add (by linarith)]; norm_num
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
  rw [h52]
  generalize Real.sqrt (f:ℝ) = s at *
  have hfs : (f:ℝ) = s * s := hss.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    have : 2 * (n:ℝ)^2 * s * rd * ρ * (s / (2 * rd * ρ)) = (n:ℝ)^2 * (s * s) := by field_simp
    rw [this, ← hfs]; linarith
  · rw [div_le_iff₀ (by positivity)]
    have : 8 * (n:ℝ)^4 * ((f:ℝ)^2 * s) * rd * ρ * (s / (2 * rd * ρ)) = 4 * (n:ℝ)^4 * (f:ℝ)^2 * (s * s) := by
      field_simp; ring
    rw [this, ← hfs]
    have h2 : (N:ℝ)^2 ≤ (2 * (n:ℝ)^2 * f)^2 := by gcongr
    have h3 : (2 * (n:ℝ)^2 * f)^2 * 1 ≤ (2 * (n:ℝ)^2 * f)^2 * f := by gcongr
    nlinarith
  · rw [div_le_iff₀ (by positivity)]
    have : 8 * (n:ℝ)^6 * ((f:ℝ)^2 * s) * rd * ρ * (2 * (s / (2 * rd * ρ))) = 8 * (n:ℝ)^6 * (f:ℝ)^2 * (s * s) := by
      field_simp
    rw [this, ← hfs]
    have h2 : (N:ℝ)^3 ≤ (2 * (n:ℝ)^2 * f)^3 := by gcongr
    nlinarith

/- English proof (translation)
Introduce `f j ts h0 h1`. Repeatedly rewrite using `[div_eq_mul_inv]`. Rewrite using `[intervalIntegral.integral_const_mul, integral_inv_of_pos h0 (by norm_num)]`. Use `congr 2`. Clear the denominators using the available nonvanishing facts.
-/
theorem log_volume_formula : LogVolume := by
  intro f j ts h0 h1
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos h0 (by norm_num)]
  congr 2
  field_simp

/- English proof (translation)
Introduce `a q τ ha haq hτ hlast h1`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hq0 : q ≠ 0` using `by omega`. Establish `hx0 : 0 < (2 * τ 1) ^ ((1:ℝ) / q)` using `Real.rpow_pos_of_pos (by have := hτ 1; linarith) _`.

Establish `hx1 : (2 * τ 1) ^ ((1:ℝ) / q) ≤ 1` using `Real.rpow_le_one (by have := hτ 1; linarith) (by linarith) (by positivity)`. Establish `hxq : ((2 * τ 1) ^ ((1:ℝ) / q)) ^ q = 2 * τ 1`. Rewrite using `[one_div]`. Conclude with `Real.rpow_inv_natCast_pow (by have := hτ 1; linarith) hq0`. Generalize the expression as in `(2 * τ 1) ^ ((1:ℝ) / q) = x at *`.

Establish `key : ∀ k, 1 ≤ k → k ≤ a → x ^ k * τ (k + 1) < τ 1`. Introduce `k hk`. Proceed by induction on `k, hk using Nat.le_induction with`. Consider the case `base`. Introduce `_`.

Use `hcon 1 le_rfl ha` as an intermediate fact. Rewrite `this` using `[lt_div_iff₀ (hτ _)]`. Simplify using `using this`. Consider the case `succ k hk ih`. Introduce `hka`.

Establish `h2` using `hcon (k + 1) (by omega) hka`. Rewrite `h2` using `[lt_div_iff₀ (hτ _)]`. Establish `h3` using `ih (by omega)`. Combine the equalities or inequalities in the displayed calculation. Establish `h4` using `key a ha le_rfl`.

Rewrite `h4` using `[hlast]`. Establish `h5 : x ^ q ≤ x ^ a` using `pow_le_pow_of_le_one hx0.le hx1 haq`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gap_pigeonhole : GapPigeonhole := by
  intro a q τ ha haq hτ hlast h1
  by_contra hcon
  push Not at hcon
  have hq0 : q ≠ 0 := by omega
  have hx0 : 0 < (2 * τ 1) ^ ((1:ℝ) / q) := Real.rpow_pos_of_pos (by have := hτ 1; linarith) _
  have hx1 : (2 * τ 1) ^ ((1:ℝ) / q) ≤ 1 :=
    Real.rpow_le_one (by have := hτ 1; linarith) (by linarith) (by positivity)
  have hxq : ((2 * τ 1) ^ ((1:ℝ) / q)) ^ q = 2 * τ 1 := by
    rw [one_div]
    exact Real.rpow_inv_natCast_pow (by have := hτ 1; linarith) hq0
  generalize (2 * τ 1) ^ ((1:ℝ) / q) = x at *
  have key : ∀ k, 1 ≤ k → k ≤ a → x ^ k * τ (k + 1) < τ 1 := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro _
      have := hcon 1 le_rfl ha
      rw [lt_div_iff₀ (hτ _)] at this
      simpa using this
    | succ k hk ih =>
      intro hka
      have h2 := hcon (k + 1) (by omega) hka
      rw [lt_div_iff₀ (hτ _)] at h2
      have h3 := ih (by omega)
      calc x ^ (k + 1) * τ (k + 1 + 1) = x ^ k * (x * τ (k + 1 + 1)) := by ring
        _ ≤ x ^ k * τ (k + 1) := by gcongr
        _ < τ 1 := h3
  have h4 := key a ha le_rfl
  rw [hlast] at h4
  have h5 : x ^ q ≤ x ^ a := pow_le_pow_of_le_one hx0.le hx1 haq
  linarith

/- English proof (translation)
Introduce `ι _ _ n r τ k hτ hτ1 hk hr`. Establish `hf0 : (Fintype.card ι) ≠ 0` using `Fintype.card_ne_zero`. Establish `hfpos : (0:ℝ) < Fintype.card ι` using `by exact_mod_cast Nat.pos_of_ne_zero hf0`. Establish `hk0 : 0 < k` using `by linarith`. Establish `eP : (∏ v, k * Real.exp (r v)) ^ ((1 : ℝ) / Fintype.card ι) = k * Real.exp ((∑ v, r v) / Fintype.card ι)`.

Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum, Finset.card_univ, Real.mul_rpow (by positivity) (by positivity), one_div, Real.pow_rpow_inv_natCast hk0.le hf0, ← Real.exp_mul, div_eq_mul_inv]`. Rewrite using `[eP]`. Establish `hR : 0 ≤ (∑ v, r v) / Fintype.card ι` using `div_nonneg (Finset.sum_nonneg fun v _ => hr v) hfpos.le`. Use `set E := Real.exp ((∑ v, r v) / Fintype.card ι) with hE`. Establish `hE1 : 1 ≤ E` using `Real.one_le_exp hR`.

Establish `hτ2 : τ ^ 2 ≤ 1` using `pow_le_one₀ hτ.le hτ1`. Establish `hτ20 : 0 < τ ^ 2` using `by positivity`. Establish `h1 : 1 ≤ k * E / τ ^ 2`. Rewrite using `[le_div_iff₀ hτ20]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h2 : 1 + 2 * (k * E) / τ ^ 2 ≤ 3 * k / τ ^ 2 * E`. Establish `e : 3 * k / τ ^ 2 * E = 3 * (k * E / τ ^ 2)` using `by ring`. Establish `e' : 2 * (k * E) / τ ^ 2 = 2 * (k * E / τ ^ 2)` using `by ring`. Rewrite using `[e, e']`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation. Apply `pow_le_pow_left₀ (by positivity) h2` to reduce the goal to its premises. Use `_ = (3 * k / τ ^ 2) ^ (2 * n ^ 2 * Fintype.card ι) * E ^ (2 * n ^ 2 * Fintype.card ι) := mul_pow _ _ _`. Use `_ = _ := by`. Use `congr 1`.

Rewrite using `[hE, ← Real.exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem far_region_count : FarCount := by
  intro ι _ _ n r τ k hτ hτ1 hk hr
  have hf0 : (Fintype.card ι) ≠ 0 := Fintype.card_ne_zero
  have hfpos : (0:ℝ) < Fintype.card ι := by exact_mod_cast Nat.pos_of_ne_zero hf0
  have hk0 : 0 < k := by linarith
  have eP : (∏ v, k * Real.exp (r v)) ^ ((1 : ℝ) / Fintype.card ι)
      = k * Real.exp ((∑ v, r v) / Fintype.card ι) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum, Finset.card_univ,
      Real.mul_rpow (by positivity) (by positivity), one_div,
      Real.pow_rpow_inv_natCast hk0.le hf0, ← Real.exp_mul, div_eq_mul_inv]
  rw [eP]
  have hR : 0 ≤ (∑ v, r v) / Fintype.card ι := div_nonneg (Finset.sum_nonneg fun v _ => hr v) hfpos.le
  set E := Real.exp ((∑ v, r v) / Fintype.card ι) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp hR
  have hτ2 : τ ^ 2 ≤ 1 := pow_le_one₀ hτ.le hτ1
  have hτ20 : 0 < τ ^ 2 := by positivity
  have h1 : 1 ≤ k * E / τ ^ 2 := by
    rw [le_div_iff₀ hτ20]; nlinarith
  have h2 : 1 + 2 * (k * E) / τ ^ 2 ≤ 3 * k / τ ^ 2 * E := by
    have e : 3 * k / τ ^ 2 * E = 3 * (k * E / τ ^ 2) := by ring
    have e' : 2 * (k * E) / τ ^ 2 = 2 * (k * E / τ ^ 2) := by ring
    rw [e, e']; linarith
  calc (1 + 2 * (k * E) / τ ^ 2) ^ (2 * n ^ 2 * Fintype.card ι)
      ≤ (3 * k / τ ^ 2 * E) ^ (2 * n ^ 2 * Fintype.card ι) := by
        apply pow_le_pow_left₀ (by positivity) h2
    _ = (3 * k / τ ^ 2) ^ (2 * n ^ 2 * Fintype.card ι) * E ^ (2 * n ^ 2 * Fintype.card ι) := mul_pow _ _ _
    _ = _ := by
      congr 1
      rw [hE, ← Real.exp_nat_mul]
      congr 1
      push_cast
      field_simp

/- English proof (translation)
Introduce `n f τs hn hf hτ hnτ`. Establish `hn' : (1:ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hss : Real.sqrt (n:ℝ) ^ 2 = n` using `Real.sq_sqrt (by linarith)`. Establish `hfm : f ≤ n ^ 2 * f` using `Nat.le_mul_of_pos_left _ (by positivity)`. Establish `e1 : (3 * Real.sqrt n / τs ^ 2) ^ (2 * n ^ 2 * f) = (9 * n / τs ^ 4) ^ (n ^ 2 * f)`.

Rewrite using `[mul_assoc 2, pow_mul]`. Use `congr 1`. Rewrite using `[div_pow, mul_pow, hss]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (3 / τs) ^ (5 * n ^ 2 * f) = (243 / τs ^ 5) ^ (n ^ 2 * f)`.

Rewrite using `[mul_assoc 5, pow_mul]`. Use `congr 1`. Rewrite using `[div_pow]`. Evaluate the numerical expressions. Rewrite using `[e1, e2]`.

Combine the equalities or inequalities in the displayed calculation. Evaluate the numerical expressions. Use `_ = (9 * (n:ℝ) / τs ^ 4 * 4) ^ (n ^ 2 * f) := (mul_pow _ _ _).symm`. Use `_ ≤ (243 / τs ^ 5) ^ (n ^ 2 * f) := by`. Apply `pow_le_pow_left₀ (by positivity)` to reduce the goal to its premises.

Rewrite using `[div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]`. Establish `: 9 * (n:ℝ) * 4 * τs ^ 5 = 36 * (n * τs) * τs ^ 4` using `by ring`. Rewrite using `[this]`. Establish `h4 : 0 < τs ^ 4` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem far_region_prefactor : FarPrefactor := by
  intro n f τs hn hf hτ hnτ
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hss : Real.sqrt (n:ℝ) ^ 2 = n := Real.sq_sqrt (by linarith)
  have hfm : f ≤ n ^ 2 * f := Nat.le_mul_of_pos_left _ (by positivity)
  have e1 : (3 * Real.sqrt n / τs ^ 2) ^ (2 * n ^ 2 * f) = (9 * n / τs ^ 4) ^ (n ^ 2 * f) := by
    rw [mul_assoc 2, pow_mul]
    congr 1
    rw [div_pow, mul_pow, hss]; ring
  have e2 : (3 / τs) ^ (5 * n ^ 2 * f) = (243 / τs ^ 5) ^ (n ^ 2 * f) := by
    rw [mul_assoc 5, pow_mul]
    congr 1
    rw [div_pow]; norm_num
  rw [e1, e2]
  calc (9 * (n:ℝ) / τs ^ 4) ^ (n ^ 2 * f) * 4 ^ f
      ≤ (9 * (n:ℝ) / τs ^ 4) ^ (n ^ 2 * f) * 4 ^ (n ^ 2 * f) := by
        gcongr
        · norm_num
    _ = (9 * (n:ℝ) / τs ^ 4 * 4) ^ (n ^ 2 * f) := (mul_pow _ _ _).symm
    _ ≤ (243 / τs ^ 5) ^ (n ^ 2 * f) := by
        apply pow_le_pow_left₀ (by positivity)
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have : 9 * (n:ℝ) * 4 * τs ^ 5 = 36 * (n * τs) * τs ^ 4 := by ring
        rw [this]
        have h4 : 0 < τs ^ 4 := by positivity
        nlinarith

/- English proof (translation)
Introduce `R _ la d n q J f de k hla hde hk hk24 hd hJ hsmall`. Rewrite using `[← Finset.prod_mul_distrib]`. Establish `h1 : ∀ r, (1 + k * de / la r) ^ (d r * f) * la r ^ (d r * f) ≤ Real.exp (k * de * (d r * f : ℕ))`. Introduce `r`. Establish `hl` using `hla r`.

Rewrite using `[← mul_pow]`. Establish `e : (1 + k * de / la r) * la r = la r + k * de`. Clear denominators, using `[hl.1.ne']` for the nonvanishing conditions. Rewrite using `[e, mul_comm (k * de), Real.exp_nat_mul]`. Apply `pow_le_pow_left₀ (by have := mul_nonneg hk hde; linarith)` to reduce the goal to its premises.

Use `Real.add_one_le_exp (k * de)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Establish `h` using `hla r`. Establish `h2` using `div_nonneg (mul_nonneg hk hde) h.1.le`.

Conclude with `mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg h.1.le _))`. Use the proof step `(fun r _ => h1 r)`. Use `_ = Real.exp (k * de * ((∑ r, d r : ℕ) * f)) := by`. Rewrite using `[← Real.exp_sum, ← Finset.mul_sum]`. Use `congr 2`.

Use `push_cast`. Rewrite using `[Finset.sum_mul]`. Use `_ ≤ Real.exp (48 / 100) := by`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `hd' : ((∑ r, d r : ℕ) : ℝ) ≤ 2 * J * n` using `by exact_mod_cast hd`.

Establish `hJ' : (J:ℝ) ≤ q` using `by exact_mod_cast hJ`. Establish `hn0 : (0:ℝ) ≤ n` using `Nat.cast_nonneg _`. Establish `hf0 : (0:ℝ) ≤ f` using `Nat.cast_nonneg _`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hd'.trans (by gcongr)`.

Use `_ = 48 * (de * q * n * f) := by ring`. Use `_ ≤ 48 / 100 := by linarith`. Use `_ ≤ 2 := by`. Rewrite using `[← Real.le_log_iff_exp_le (by norm_num)]`. Use `Real.log_two_gt_d9` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem near_region_product : NearProduct := by
  intro R _ la d n q J f de k hla hde hk hk24 hd hJ hsmall
  rw [← Finset.prod_mul_distrib]
  have h1 : ∀ r, (1 + k * de / la r) ^ (d r * f) * la r ^ (d r * f)
      ≤ Real.exp (k * de * (d r * f : ℕ)) := by
    intro r
    have hl := hla r
    rw [← mul_pow]
    have e : (1 + k * de / la r) * la r = la r + k * de := by
      field_simp [hl.1.ne']
    rw [e, mul_comm (k * de), Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by have := mul_nonneg hk hde; linarith)
    have := Real.add_one_le_exp (k * de)
    linarith
  calc ∏ r, (1 + k * de / la r) ^ (d r * f) * la r ^ (d r * f)
      ≤ ∏ r, Real.exp (k * de * (d r * f : ℕ)) :=
        Finset.prod_le_prod (fun r _ => by
          have h := hla r
          have h2 := div_nonneg (mul_nonneg hk hde) h.1.le
          exact mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg h.1.le _))
          (fun r _ => h1 r)
    _ = Real.exp (k * de * ((∑ r, d r : ℕ) * f)) := by
        rw [← Real.exp_sum, ← Finset.mul_sum]
        congr 2
        push_cast
        rw [Finset.sum_mul]
    _ ≤ Real.exp (48 / 100) := by
        apply Real.exp_le_exp.mpr
        have hd' : ((∑ r, d r : ℕ) : ℝ) ≤ 2 * J * n := by exact_mod_cast hd
        have hJ' : (J:ℝ) ≤ q := by exact_mod_cast hJ
        have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
        have hf0 : (0:ℝ) ≤ f := Nat.cast_nonneg _
        calc k * de * ((∑ r, d r : ℕ) * f) ≤ 24 * de * ((2 * q * n) * f) := by
              gcongr
              exact hd'.trans (by gcongr)
          _ = 48 * (de * q * n * f) := by ring
          _ ≤ 48 / 100 := by linarith
    _ ≤ 2 := by
        rw [← Real.le_log_iff_exp_le (by norm_num)]
        have := Real.log_two_gt_d9
        linarith

/- English proof (translation)
Introduce `c hc`. Use `⟨c / 2, by positivity, ⌈Real.exp (2 / c)⌉₊, ?_⟩` and prove the remaining obligations. Introduce `n q J f hn hq hJ hf`. Establish `hn1 : Real.exp (2 / c) ≤ n` using `Nat.ceil_le.mp hn`. Establish `hn0 : (0:ℝ) < n` using `lt_of_lt_of_le (Real.exp_pos _) hn1`.

Establish `hlog : 2 / c ≤ Real.log n` using `(Real.le_log_iff_exp_le hn0).mpr hn1`. Establish `hlog' : 2 ≤ c * Real.log n`. Rewrite `hlog` using `[div_le_iff₀ hc]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hqn1 : (q:ℝ) ≤ n`.

Establish `: q ≤ n` using `le_trans (Nat.le_self_pow (by norm_num) q) hq`. Conclude with `this` after adjusting the coercions. Establish `hJ' : (1:ℝ) ≤ J` using `by exact_mod_cast hJ`. Establish `hf' : (1:ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `e2 : (2:ℝ) ^ q = Real.exp (q * Real.log 2)`.

Rewrite using `[mul_comm, ← Real.rpow_def_of_pos (by norm_num), Real.rpow_natCast]`. Rewrite using `[e2, ← Real.exp_add]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `hl2 : Real.log 2 ≤ 1`. Use `Real.log_two_lt_d9` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hl20 : 0 ≤ Real.log 2` using `Real.log_nonneg (by norm_num)`. Establish `hq0 : (0:ℝ) ≤ q` using `Nat.cast_nonneg _`. Establish `a1 : (q:ℝ) * Real.log 2 ≤ n` using `by nlinarith`. Establish `hx : 0 ≤ c * Real.log n` using `by linarith`.

Establish `a2 : c * Real.log n * (n * f) ≤ c * Real.log n * (J * (n * f))`. Apply `mul_le_mul_of_nonneg_left _ hx` to reduce the goal to its premises. Establish `: 0 ≤ (n:ℝ) * f` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `a3 : 2 * ((n:ℝ) * 1) ≤ c * Real.log n * (n * f)`.

Apply `mul_le_mul hlog' _ (by positivity) hx` to reduce the goal to its premises. Use `gcongr`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem probability_nonzero_index : ProbINonzero := by
  intro c hc
  refine ⟨c / 2, by positivity, ⌈Real.exp (2 / c)⌉₊, ?_⟩
  intro n q J f hn hq hJ hf
  have hn1 : Real.exp (2 / c) ≤ n := Nat.ceil_le.mp hn
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hn1
  have hlog : 2 / c ≤ Real.log n := (Real.le_log_iff_exp_le hn0).mpr hn1
  have hlog' : 2 ≤ c * Real.log n := by
    rw [div_le_iff₀ hc] at hlog; linarith
  have hqn1 : (q:ℝ) ≤ n := by
    have : q ≤ n := le_trans (Nat.le_self_pow (by norm_num) q) hq
    exact_mod_cast this
  have hJ' : (1:ℝ) ≤ J := by exact_mod_cast hJ
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have e2 : (2:ℝ) ^ q = Real.exp (q * Real.log 2) := by
    rw [mul_comm, ← Real.rpow_def_of_pos (by norm_num), Real.rpow_natCast]
  rw [e2, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have a1 : (q:ℝ) * Real.log 2 ≤ n := by nlinarith
  have hx : 0 ≤ c * Real.log n := by linarith
  have a2 : c * Real.log n * (n * f) ≤ c * Real.log n * (J * (n * f)) := by
    apply mul_le_mul_of_nonneg_left _ hx
    have : 0 ≤ (n:ℝ) * f := by positivity
    nlinarith
  have a3 : 2 * ((n:ℝ) * 1) ≤ c * Real.log n * (n * f) := by
    apply mul_le_mul hlog' _ (by positivity) hx
    gcongr
  nlinarith

/- English proof (translation)
Introduce `c A hc hA`. Use `set c2 := min c 1 with hc2`. Establish `hc20 : 0 < c2` using `lt_min hc one_pos`. Use `set L := 2 * Real.log (2 * (1 + 2 * A)) / c2 with hL`. Use `⟨c2 / 2, by positivity, max 3 ⌈L⌉₊, ?_⟩` and prove the remaining obligations.

Introduce `n f D Ds pr E₁ E₂ hn hf hD hDs hpr hpr2 hE1 hE2 hDeq`. Establish `hn3 : (3:ℝ) ≤ n` using `by exact_mod_cast (le_max_left _ _).trans hn`. Establish `hnL : L ≤ n` using `Nat.ceil_le.mp ((le_max_right _ _).trans hn)`. Establish `hf' : (1:ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `hn0 : (0:ℝ) < n` using `by linarith`.

Establish `hlog1 : 1 ≤ Real.log n`. Rewrite using `[Real.le_log_iff_exp_le hn0]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogn : Real.log n ≤ n` using `(Real.log_le_sub_one_of_pos hn0).trans (by linarith)`.

Use `set x := (n:ℝ) * f * Real.log n with hx`. Establish `hxn : (n:ℝ) ≤ x`. Establish `: (n:ℝ) * 1 * 1 ≤ n * f * Real.log n` using `by gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hx0 : 0 ≤ x` using `by linarith`.

Use `set G := Real.exp (-(c2 / 2 * x)) with hG`. Establish `hG0 : 0 < G` using `Real.exp_pos _`. Establish `hG1 : G ≤ 1`. Rewrite using `[hG]`. Apply `Real.exp_le_one_iff.mpr` to reduce the goal to its premises.

Establish `: 0 ≤ c2 / 2 * x` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hGA : 2 * (1 + 2 * A) * G ≤ 1`. Establish `hp : 0 < 2 * (1 + 2 * A)` using `by positivity`. Establish `: 2 * (1 + 2 * A) = Real.exp (Real.log (2 * (1 + 2 * A)))` using `(Real.exp_log hp).symm`.

Rewrite using `[this, hG, ← Real.exp_add]`. Apply `Real.exp_le_one_iff.mpr` to reduce the goal to its premises. Establish `h1 : L ≤ x` using `hnL.trans hxn`. Rewrite `h1` using `[hL, div_le_iff₀ hc20]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `he1 : Real.exp (-(c * n * f * Real.log n)) ≤ G * G`. Rewrite using `[hG, ← Real.exp_add]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `: c2 * x ≤ c * x`. Apply `mul_le_mul_of_nonneg_right (min_le_left _ _) hx0` to reduce the goal to its premises.

Establish `e : c * n * f * Real.log n = c * x` using `by rw [hx]; ring`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `he2 : Real.exp (-((n:ℝ) ^ 2 * f)) ≤ G * G`. Rewrite using `[hG, ← Real.exp_add]`.

Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `h1 : c2 * x ≤ 1 * x`. Apply `mul_le_mul_of_nonneg_right (min_le_right _ _) hx0` to reduce the goal to its premises. Establish `h2 : x ≤ (n:ℝ) ^ 2 * f`. Rewrite using `[hx]`.

Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e3 : Real.exp (-(c2 / 2 * n * f * Real.log n)) = G`. Rewrite using `[hG, hx]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e3]`. Generalize the expression as in `Real.exp (-(c * n * f * Real.log n)) = e1 at *`. Generalize the expression as in `Real.exp (-((n:ℝ) ^ 2 * f)) = e2 at *`. Establish `hGG : 0 ≤ G * G` using `by positivity`.

Establish `b1 : |E₁| ≤ A * (G * G) * Ds` using `hE1.trans (by gcongr)`. Establish `b2 : |E₂| ≤ A * (G * G) * D` using `hE2.trans (by gcongr)`. Establish `b3 : |Ds * (pr - 1)| ≤ G * G * Ds`. Rewrite using `[abs_mul, abs_of_nonneg hDs, mul_comm]`. Apply `mul_le_mul_of_nonneg_right _ hDs` to reduce the goal to its premises.

Apply the tactic sequence `rw [abs_le]; constructor <;> linarith`. Establish `hdiff : D - Ds = Ds * (pr - 1) + E₁ + E₂` using `by rw [hDeq]; ring`. Establish `b4 : |D - Ds| ≤ G * G * Ds + A * (G * G) * Ds + A * (G * G) * D`. Rewrite using `[hdiff]`. Combine the equalities or inequalities in the displayed calculation.

Establish `b5 : D ≤ Ds + |D - Ds|` using `by have := le_abs_self (D - Ds); linarith`. Establish `hAG : A * (G * G) ≤ 1 / 4`. Establish `: A * G ≤ 1 / 4` using `by nlinarith`. Establish `h0 : 0 ≤ A * G` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hAGG0 : 0 ≤ A * (G * G)` using `by positivity`. Establish `b6 : A * (G * G) * D ≤ A * (G * G) * Ds + 1 / 4 * |D - Ds|`. Combine the equalities or inequalities in the displayed calculation. Establish `b7 : |D - Ds| ≤ 2 * (1 + 2 * A) * G * (G * Ds)`. Establish `h0 : 0 ≤ G * G * Ds` using `by positivity`.

Establish `h1 : 0 ≤ A * (G * G) * Ds` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation.
-/
theorem final_sum_near_far : FinalSum := by
  intro c A hc hA
  set c2 := min c 1 with hc2
  have hc20 : 0 < c2 := lt_min hc one_pos
  set L := 2 * Real.log (2 * (1 + 2 * A)) / c2 with hL
  refine ⟨c2 / 2, by positivity, max 3 ⌈L⌉₊, ?_⟩
  intro n f D Ds pr E₁ E₂ hn hf hD hDs hpr hpr2 hE1 hE2 hDeq
  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
  have hnL : L ≤ n := Nat.ceil_le.mp ((le_max_right _ _).trans hn)
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hn0 : (0:ℝ) < n := by linarith
  have hlog1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn0]
    have := Real.exp_one_lt_d9; linarith
  have hlogn : Real.log n ≤ n := (Real.log_le_sub_one_of_pos hn0).trans (by linarith)
  set x := (n:ℝ) * f * Real.log n with hx
  have hxn : (n:ℝ) ≤ x := by
    have : (n:ℝ) * 1 * 1 ≤ n * f * Real.log n := by gcongr
    linarith
  have hx0 : 0 ≤ x := by linarith
  set G := Real.exp (-(c2 / 2 * x)) with hG
  have hG0 : 0 < G := Real.exp_pos _
  have hG1 : G ≤ 1 := by
    rw [hG]; apply Real.exp_le_one_iff.mpr
    have : 0 ≤ c2 / 2 * x := by positivity
    linarith
  have hGA : 2 * (1 + 2 * A) * G ≤ 1 := by
    have hp : 0 < 2 * (1 + 2 * A) := by positivity
    have : 2 * (1 + 2 * A) = Real.exp (Real.log (2 * (1 + 2 * A))) := (Real.exp_log hp).symm
    rw [this, hG, ← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    have h1 : L ≤ x := hnL.trans hxn
    rw [hL, div_le_iff₀ hc20] at h1
    linarith
  have he1 : Real.exp (-(c * n * f * Real.log n)) ≤ G * G := by
    rw [hG, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : c2 * x ≤ c * x := by
      apply mul_le_mul_of_nonneg_right (min_le_left _ _) hx0
    have e : c * n * f * Real.log n = c * x := by rw [hx]; ring
    rw [e]; linarith
  have he2 : Real.exp (-((n:ℝ) ^ 2 * f)) ≤ G * G := by
    rw [hG, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : c2 * x ≤ 1 * x := by
      apply mul_le_mul_of_nonneg_right (min_le_right _ _) hx0
    have h2 : x ≤ (n:ℝ) ^ 2 * f := by
      rw [hx]
      calc (n:ℝ) * f * Real.log n ≤ n * f * n := by gcongr
        _ = _ := by ring
    linarith
  have e3 : Real.exp (-(c2 / 2 * n * f * Real.log n)) = G := by
    rw [hG, hx]; congr 1; ring
  rw [e3]
  generalize Real.exp (-(c * n * f * Real.log n)) = e1 at *
  generalize Real.exp (-((n:ℝ) ^ 2 * f)) = e2 at *
  have hGG : 0 ≤ G * G := by positivity
  have b1 : |E₁| ≤ A * (G * G) * Ds := hE1.trans (by gcongr)
  have b2 : |E₂| ≤ A * (G * G) * D := hE2.trans (by gcongr)
  have b3 : |Ds * (pr - 1)| ≤ G * G * Ds := by
    rw [abs_mul, abs_of_nonneg hDs, mul_comm]
    apply mul_le_mul_of_nonneg_right _ hDs
    rw [abs_le]; constructor <;> linarith
  have hdiff : D - Ds = Ds * (pr - 1) + E₁ + E₂ := by rw [hDeq]; ring
  have b4 : |D - Ds| ≤ G * G * Ds + A * (G * G) * Ds + A * (G * G) * D := by
    rw [hdiff]
    calc _ ≤ |Ds * (pr - 1) + E₁| + |E₂| := abs_add_le _ _
      _ ≤ |Ds * (pr - 1)| + |E₁| + |E₂| := by gcongr; exact abs_add_le _ _
      _ ≤ _ := by linarith
  have b5 : D ≤ Ds + |D - Ds| := by have := le_abs_self (D - Ds); linarith
  have hAG : A * (G * G) ≤ 1 / 4 := by
    have : A * G ≤ 1 / 4 := by nlinarith
    have h0 : 0 ≤ A * G := by positivity
    nlinarith
  have hAGG0 : 0 ≤ A * (G * G) := by positivity
  have b6 : A * (G * G) * D ≤ A * (G * G) * Ds + 1 / 4 * |D - Ds| := by
    calc A * (G * G) * D ≤ A * (G * G) * (Ds + |D - Ds|) := by gcongr
      _ = A * (G * G) * Ds + A * (G * G) * |D - Ds| := by ring
      _ ≤ _ := by gcongr
  have b7 : |D - Ds| ≤ 2 * (1 + 2 * A) * G * (G * Ds) := by
    have h0 : 0 ≤ G * G * Ds := by positivity
    have h1 : 0 ≤ A * (G * G) * Ds := by positivity
    nlinarith
  calc |D - Ds| ≤ 2 * (1 + 2 * A) * G * (G * Ds) := b7
    _ ≤ 1 * (G * Ds) := by gcongr
    _ = G * Ds := one_mul _

/- English proof (translation)
Establish `hY0 : 0 < Y` using `by linarith`. Rewrite using `[Real.rpow_def_of_pos hY0]`. Establish `hlog : 1 / 2 ≤ Real.log Y`. Establish `h1` using `Real.log_two_gt_d9`. Establish `h2 : Real.log 2 ≤ Real.log Y` using `Real.log_le_log (by norm_num) hY`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `Real.add_one_le_exp (Real.log Y * (2 * C))` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma le_rpow_two_mul {Y C : ℝ} (hY : 2 ≤ Y) (hC : 0 ≤ C) : C ≤ Y ^ (2 * C) := by
  have hY0 : 0 < Y := by linarith
  rw [Real.rpow_def_of_pos hY0]
  have hlog : 1 / 2 ≤ Real.log Y := by
    have h1 := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY
    linarith
  have := Real.add_one_le_exp (Real.log Y * (2 * C))
  nlinarith

/- English proof (translation)
Establish `hn' : (1:ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hf' : (1:ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `hb1 : (1:ℝ) ≤ b` using `by linarith`. Unfold `Ydat`. Establish `hbY : b ≤ (n:ℝ) * f * rd * g * b`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨hb.trans hbY, ?_, ?_, ?_, ?_, hbY⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation.
-/
lemma ydat_facts {n f : ℕ} {rd g b : ℝ} (hn : 1 ≤ n) (hf : 1 ≤ f) (hrd : 1 ≤ rd) (hg : 1 ≤ g)
    (hb : 2 ≤ b) : 2 ≤ Ydat n f rd g b ∧ (n:ℝ) ≤ Ydat n f rd g b ∧ (f:ℝ) ≤ Ydat n f rd g b ∧
      rd ≤ Ydat n f rd g b ∧ g ≤ Ydat n f rd g b ∧ b ≤ Ydat n f rd g b := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hb1 : (1:ℝ) ≤ b := by linarith
  unfold Ydat
  have hbY : b ≤ (n:ℝ) * f * rd * g * b := by
    calc b = 1 * 1 * 1 * 1 * b := by ring
      _ ≤ _ := by gcongr
  refine ⟨hb.trans hbY, ?_, ?_, ?_, ?_, hbY⟩
  · calc (n:ℝ) = n * 1 * 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  · calc (f:ℝ) = 1 * f * 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  · calc rd = 1 * 1 * rd * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  · calc g = 1 * 1 * 1 * g * 1 := by ring
      _ ≤ _ := by gcongr

/- English proof (translation)
Unfold `b1 P0`. Use `push_cast`. Establish `hq' : (q:ℝ) ≤ Y` using `le_trans (by exact_mod_cast hqn) hnY`. Establish `hn0 : (0:ℝ) ≤ n` using `Nat.cast_nonneg _`. Establish `hf0 : (0:ℝ) ≤ f` using `Nat.cast_nonneg _`.

Establish `hq0 : (0:ℝ) ≤ q` using `Nat.cast_nonneg _`. Establish `h1 : b ^ 2 ≤ Y ^ 2` using `by gcongr`. Establish `h2 : 2 * (8 * (q:ℝ) * (n:ℝ) ^ 2 * f) * n ≤ Y * (Y ^ 3 * Y * Y ^ 2 * Y) * Y`. Establish `h8 : (8:ℝ) ≤ Y ^ 3`. Combine the equalities or inequalities in the displayed calculation.

Use `gcongr`. Establish `h3 : Y ^ 2 ≤ Y ^ 9` using `pow_le_pow_right₀ (by linarith) (by norm_num)`. Establish `h9 : 0 < Y ^ 9` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma b1_bound_le_power {n q f : ℕ} {b Y : ℝ} (hqn : q ≤ n) (hY : 2 ≤ Y) (hnY : (n:ℝ) ≤ Y) (hfY : (f:ℝ) ≤ Y)
    (hb0 : 0 ≤ b) (hbY : b ≤ Y) : b1 n q f b ≤ Y ^ 10 := by
  unfold b1 P0
  push_cast
  have hq' : (q:ℝ) ≤ Y := le_trans (by exact_mod_cast hqn) hnY
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hf0 : (0:ℝ) ≤ f := Nat.cast_nonneg _
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have h1 : b ^ 2 ≤ Y ^ 2 := by gcongr
  have h2 : 2 * (8 * (q:ℝ) * (n:ℝ) ^ 2 * f) * n ≤ Y * (Y ^ 3 * Y * Y ^ 2 * Y) * Y := by
    have h8 : (8:ℝ) ≤ Y ^ 3 := by
      calc (8:ℝ) = 2 ^ 3 := by norm_num
        _ ≤ Y ^ 3 := by gcongr
    gcongr
  have h3 : Y ^ 2 ≤ Y ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h9 : 0 < Y ^ 9 := by positivity
  nlinarith

/- English proof (translation)
Introduce `C n q f Y τ₁ τs θ Kxx Bs D volG volK hC hq hY hτ hττ hD hvK hvG hθ0 hθ hK hB hvol`. Establish `hY0 : 0 < Y` using `by linarith`. Establish `hq0 : q ≠ 0` using `by omega`. Use `set m : ℕ := n ^ 2 * f with hm`. Establish `hmr : (m:ℝ) = (n:ℝ) ^ 2 * f` using `by rw [hm]; push_cast; ring`.

Establish `hP : 2 * P0 n q f = q * (16 * m)` using `by rw [hm]; unfold P0; ring`. Establish `e4 : 4 * n ^ 2 * f = 4 * m` using `by rw [hm]; ring`. Establish `e12 : 12 * n ^ 2 * f = 12 * m` using `by rw [hm]; ring`. Rewrite `hK` using `[hP]`. Rewrite `hB` using `[e4]`.

Rewrite using `[e12]`. Establish `eC : C * (n:ℝ) ^ 2 * f = C * m` using `by rw [hmr]; ring`. Rewrite `hB`, `hvol` using `[eC]`. Establish `hT : θ ^ (q * (16 * m)) ≤ Y ^ (16 * q * C * m) * (2 * τ₁) ^ (16 * m)`. Combine the equalities or inequalities in the displayed calculation.

Use `congr 1`. Rewrite using `[← Real.rpow_mul_natCast hY0.le]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[pow_mul, one_div, Real.rpow_inv_natCast_pow (by linarith) hq0]`. Use `set a := Y ^ (C * m) with ha`. Establish `ha0 : 0 < a` using `Real.rpow_pos_of_pos hY0 _`. Establish `hT0 : 0 ≤ θ ^ (q * (16 * m))` using `pow_nonneg hθ0 _`. Establish `hi0 : 0 < (1 / τ₁) ^ (4 * m)` using `by positivity`.

Establish `s1 : volG * Kxx ≤ θ ^ (q * (16 * m)) * a * (1 / τ₁) ^ (4 * m) * D * a`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_left _ hvG` to reduce the goal to its premises. Conclude with `hK.trans (mul_le_mul_of_nonneg_left hB hT0)`. Use `_ = θ ^ (q * (16 * m)) * a * (1 / τ₁) ^ (4 * m) * D * (volG / volK) := by ring`.

Use `_ ≤ _ := by gcongr`. Establish `s2 : (2 * τ₁) ^ (16 * m) * (1 / τ₁) ^ (4 * m) = 2 ^ (16 * m) * τ₁ ^ (12 * m)`. Establish `: 16 * m = 12 * m + 4 * m` using `by ring`. Rewrite using `[mul_pow, one_div, inv_pow]`. Use `conv_lhs => rw [this, pow_add τ₁]`.

Establish `h4 : τ₁ ^ (4 * m) ≠ 0` using `by positivity`. Rewrite using `[← this]`. Clear the denominators using the available nonvanishing facts. Establish `s3 : (2:ℝ) ^ (16 * m) * τ₁ ^ (12 * m) ≤ Y ^ (16 * m) * τs ^ (12 * m)` using `by gcongr`. Establish `eY : Y ^ ((16 * q * C + 2 * C + 16) * (n:ℝ) ^ 2 * f) = Y ^ (16 * q * C * m) * a * a * Y ^ (16 * m)`.

Rewrite using `[ha, ← Real.rpow_natCast Y (16 * m), ← Real.rpow_add hY0, ← Real.rpow_add hY0, ← Real.rpow_add hY0]`. Use `congr 1`. Use `push_cast`. Rewrite using `[hmr]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[eY]`. Establish `hb0 : 0 < Y ^ (16 * q * C * m)` using `Real.rpow_pos_of_pos hY0 _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[s2]`. Use `gcongr`.

Use `_ = _ := by ring`.
-/
theorem deep_region_chain_height : DeepChainY := by
  intro C n q f Y τ₁ τs θ Kxx Bs D volG volK hC hq hY hτ hττ hD hvK hvG hθ0 hθ hK hB hvol
  have hY0 : 0 < Y := by linarith
  have hq0 : q ≠ 0 := by omega
  set m : ℕ := n ^ 2 * f with hm
  have hmr : (m:ℝ) = (n:ℝ) ^ 2 * f := by rw [hm]; push_cast; ring
  have hP : 2 * P0 n q f = q * (16 * m) := by rw [hm]; unfold P0; ring
  have e4 : 4 * n ^ 2 * f = 4 * m := by rw [hm]; ring
  have e12 : 12 * n ^ 2 * f = 12 * m := by rw [hm]; ring
  rw [hP] at hK
  rw [e4] at hB
  rw [e12]
  have eC : C * (n:ℝ) ^ 2 * f = C * m := by rw [hmr]; ring
  rw [eC] at hB hvol
  have hT : θ ^ (q * (16 * m)) ≤ Y ^ (16 * q * C * m) * (2 * τ₁) ^ (16 * m) := by
    calc θ ^ (q * (16 * m)) ≤ (Y ^ C * (2 * τ₁) ^ ((1:ℝ) / q)) ^ (q * (16 * m)) :=
          pow_le_pow_left₀ hθ0 hθ _
      _ = (Y ^ C) ^ (q * (16 * m)) * ((2 * τ₁) ^ ((1:ℝ) / q)) ^ (q * (16 * m)) := mul_pow _ _ _
      _ = _ := by
        congr 1
        · rw [← Real.rpow_mul_natCast hY0.le]
          congr 1; push_cast; ring
        · rw [pow_mul, one_div, Real.rpow_inv_natCast_pow (by linarith) hq0]
  set a := Y ^ (C * m) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hY0 _
  have hT0 : 0 ≤ θ ^ (q * (16 * m)) := pow_nonneg hθ0 _
  have hi0 : 0 < (1 / τ₁) ^ (4 * m) := by positivity
  have s1 : volG * Kxx ≤ θ ^ (q * (16 * m)) * a * (1 / τ₁) ^ (4 * m) * D * a := by
    calc volG * Kxx ≤ volG * (θ ^ (q * (16 * m)) * (a * (1 / τ₁) ^ (4 * m) * D / volK)) := by
          apply mul_le_mul_of_nonneg_left _ hvG
          exact hK.trans (mul_le_mul_of_nonneg_left hB hT0)
      _ = θ ^ (q * (16 * m)) * a * (1 / τ₁) ^ (4 * m) * D * (volG / volK) := by ring
      _ ≤ _ := by gcongr
  have s2 : (2 * τ₁) ^ (16 * m) * (1 / τ₁) ^ (4 * m) = 2 ^ (16 * m) * τ₁ ^ (12 * m) := by
    have : 16 * m = 12 * m + 4 * m := by ring
    rw [mul_pow, one_div, inv_pow]
    conv_lhs => rw [this, pow_add τ₁]
    have h4 : τ₁ ^ (4 * m) ≠ 0 := by positivity
    rw [← this]
    field_simp
  have s3 : (2:ℝ) ^ (16 * m) * τ₁ ^ (12 * m) ≤ Y ^ (16 * m) * τs ^ (12 * m) := by
    gcongr
  have eY : Y ^ ((16 * q * C + 2 * C + 16) * (n:ℝ) ^ 2 * f)
      = Y ^ (16 * q * C * m) * a * a * Y ^ (16 * m) := by
    rw [ha, ← Real.rpow_natCast Y (16 * m), ← Real.rpow_add hY0, ← Real.rpow_add hY0,
      ← Real.rpow_add hY0]
    congr 1; push_cast; rw [hmr]; ring
  rw [eY]
  have hb0 : 0 < Y ^ (16 * q * C * m) := Real.rpow_pos_of_pos hY0 _
  calc volG * Kxx ≤ θ ^ (q * (16 * m)) * a * (1 / τ₁) ^ (4 * m) * D * a := s1
    _ ≤ (Y ^ (16 * q * C * m) * (2 * τ₁) ^ (16 * m)) * a * (1 / τ₁) ^ (4 * m) * D * a := by gcongr
    _ = D * (Y ^ (16 * q * C * m) * a * a) * ((2 * τ₁) ^ (16 * m) * (1 / τ₁) ^ (4 * m)) := by ring
    _ ≤ D * (Y ^ (16 * q * C * m) * a * a) * (Y ^ (16 * m) * τs ^ (12 * m)) := by
        rw [s2]; gcongr
    _ = _ := by ring

/- English proof (translation)
Introduce `C hC`. Use `⟨2 * C + 2, by linarith, ?_⟩` and prove the remaining obligations. Introduce `n q f Y hq hY`. Establish `hY0 : 0 < Y` using `by linarith`. Establish `hq' : (1:ℝ) ≤ q` using `by exact_mod_cast hq`.

Rewrite using `[← Real.rpow_mul_natCast hY0.le, ← Real.rpow_add hY0, Real.rpow_def_of_pos hY0]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `hlog : 1 / 2 ≤ Real.log Y`. Establish `h1` using `Real.log_two_gt_d9`. Establish `h2 : Real.log 2 ≤ Real.log Y` using `Real.log_le_log (by norm_num) hY`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hm0 : 0 ≤ (n:ℝ) ^ 2 * f` using `by positivity`. Establish `hE : (16 * q * C + 2 * C + 16) * (n:ℝ) ^ 2 * f + -((2 * C + 2) * q) * ((12 * n ^ 2 * f : ℕ) : ℝ) ≤ -2 * ((n:ℝ) ^ 2 * f)`. Use `push_cast`. Establish `: (16 * q * C + 2 * C + 16) * (n:ℝ) ^ 2 * f + -((2 * C + 2) * q) * (12 * (n:ℝ) ^ 2 * f) = (-(8 * q * C) + 2 * C + 16 - 24 * q) * ((n:ℝ) ^ 2 * f)` using `by ring`.

Rewrite using `[this]`. Apply `mul_le_mul_of_nonneg_right _ hm0` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem deep_region_bound_height : DeepBoundY := by
  intro C hC
  refine ⟨2 * C + 2, by linarith, ?_⟩
  intro n q f Y hq hY
  have hY0 : 0 < Y := by linarith
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  rw [← Real.rpow_mul_natCast hY0.le, ← Real.rpow_add hY0, Real.rpow_def_of_pos hY0]
  apply Real.exp_le_exp.mpr
  have hlog : 1 / 2 ≤ Real.log Y := by
    have h1 := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY
    linarith
  have hm0 : 0 ≤ (n:ℝ) ^ 2 * f := by positivity
  have hE : (16 * q * C + 2 * C + 16) * (n:ℝ) ^ 2 * f
      + -((2 * C + 2) * q) * ((12 * n ^ 2 * f : ℕ) : ℝ) ≤ -2 * ((n:ℝ) ^ 2 * f) := by
    push_cast
    have : (16 * q * C + 2 * C + 16) * (n:ℝ) ^ 2 * f + -((2 * C + 2) * q) * (12 * (n:ℝ) ^ 2 * f)
        = (-(8 * q * C) + 2 * C + 16 - 24 * q) * ((n:ℝ) ^ 2 * f) := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_right _ hm0
    nlinarith
  nlinarith

/- English proof (translation)
Introduce `C hC`. Take `⟨C₁, hC₁, H⟩` from `deep_region_bound_height (2 * C + 18) (by linarith)`. Use `⟨C₁, hC₁, ?_⟩` and prove the remaining obligations. Introduce `n q f rd g b hn hq hqn hf hrd hg hb`. Take `⟨hY, hnY, hfY, hrdY, hgY, hbY⟩` from `ydat_facts hn hf hrd hg hb`.

Establish `hqn' : q ≤ n` using `le_trans (Nat.le_self_pow (by norm_num) q) hqn`. Establish `hb1` using `b1_bound_le_power (f := f) hqn' hY hnY hfY (by linarith) hbY`. Establish `H'` using `H n q f _ hq hY`. Generalize the expression as in `Ydat n f rd g b = Y at *`. Establish `hY0 : 0 < Y` using `by linarith`.

Establish `hY1 : 1 ≤ Y` using `by linarith`. Use `le_trans ?_ H'` and prove the remaining obligations. Establish `hb10 : 0 ≤ b1 n q f b` using `by unfold b1; positivity`. Establish `hbr : C * (n:ℝ) ^ 4 * (f:ℝ) ^ 2 * g * rd * b1 n q f b ≤ Y ^ (2 * C + 18)`. Establish `e : Y ^ (2 * C + 18) = Y ^ (2 * C) * Y ^ 4 * Y ^ 2 * Y * Y * Y ^ 10`.

Rewrite using `[Real.rpow_add hY0]`. Establish `: Y ^ (18:ℝ) = Y ^ 18` using `by exact_mod_cast Real.rpow_natCast Y 18`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Use `le_rpow_two_mul hY (by linarith : 0 ≤ C)` as an intermediate fact. Use `gcongr`. Apply `mul_le_mul_of_nonneg_right _ (by positivity)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_mul_natCast hY0.le, ← Real.rpow_add hY0]`.

Use `_ ≤ _ := by`. Apply `Real.rpow_le_rpow_of_exponent_le hY1` to reduce the goal to its premises. Use `push_cast`. Establish `hm0 : 0 ≤ (n:ℝ) ^ 2 * f` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem deep_region_bound : DeepBound := by
  intro C hC
  obtain ⟨C₁, hC₁, H⟩ := deep_region_bound_height (2 * C + 18) (by linarith)
  refine ⟨C₁, hC₁, ?_⟩
  intro n q f rd g b hn hq hqn hf hrd hg hb
  obtain ⟨hY, hnY, hfY, hrdY, hgY, hbY⟩ := ydat_facts hn hf hrd hg hb
  have hqn' : q ≤ n := le_trans (Nat.le_self_pow (by norm_num) q) hqn
  have hb1 := b1_bound_le_power (f := f) hqn' hY hnY hfY (by linarith) hbY
  have H' := H n q f _ hq hY
  generalize Ydat n f rd g b = Y at *
  have hY0 : 0 < Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  refine le_trans ?_ H'
  have hb10 : 0 ≤ b1 n q f b := by unfold b1; positivity
  have hbr : C * (n:ℝ) ^ 4 * (f:ℝ) ^ 2 * g * rd * b1 n q f b ≤ Y ^ (2 * C + 18) := by
    have e : Y ^ (2 * C + 18) = Y ^ (2 * C) * Y ^ 4 * Y ^ 2 * Y * Y * Y ^ 10 := by
      rw [Real.rpow_add hY0]
      have : Y ^ (18:ℝ) = Y ^ 18 := by exact_mod_cast Real.rpow_natCast Y 18
      rw [this]; ring
    rw [e]
    have := le_rpow_two_mul hY (by linarith : 0 ≤ C)
    gcongr
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc Y ^ (C * (n:ℝ) ^ 2 * f) * (C * (n:ℝ) ^ 4 * (f:ℝ) ^ 2 * g * rd * b1 n q f b) ^ (16 * q * n ^ 2 * f)
      ≤ Y ^ (C * (n:ℝ) ^ 2 * f) * (Y ^ (2 * C + 18)) ^ (16 * q * n ^ 2 * f) := by
        gcongr
    _ = Y ^ (C * (n:ℝ) ^ 2 * f + (2 * C + 18) * ((16 * q * n ^ 2 * f : ℕ) : ℝ)) := by
        rw [← Real.rpow_mul_natCast hY0.le, ← Real.rpow_add hY0]
    _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hY1
        push_cast
        have hm0 : 0 ≤ (n:ℝ) ^ 2 * f := by positivity
        nlinarith

/- English proof (translation)
Introduce `C hC`. Use `⟨C ^ 2 + 12 * C + 31, by nlinarith, ?_⟩` and prove the remaining obligations. Introduce `n q f rd g b τ₁ τs ρ Kxx Bs D volG volK hn hq hqn hf hrd hg hb hτ hττ hD hvK hvG hρ0 hρ hK hB hvol`. Take `⟨hY, hnY, hfY, hrdY, hgY, hbY⟩` from `ydat_facts hn hf hrd hg hb`. Establish `hqn' : q ≤ n` using `le_trans (Nat.le_self_pow (by norm_num) q) hqn`.

Establish `hb1` using `b1_bound_le_power (f := f) hqn' hY hnY hfY (by linarith) hbY`. Establish `hb10 : 0 ≤ b1 n q f b` using `by unfold b1; positivity`. Generalize the expression as in `Ydat n f rd g b = Y at *`. Generalize the expression as in `b1 n q f b = b₁ at *`. Establish `hY0 : 0 < Y` using `by linarith`.

Establish `hY1 : 1 ≤ Y` using `by linarith`. Establish `hq0 : q ≠ 0` using `by omega`. Establish `hn0 : (0:ℝ) ≤ n` using `Nat.cast_nonneg _`. Establish `hf0 : (0:ℝ) ≤ f` using `Nat.cast_nonneg _`. Use `set m : ℕ := n ^ 2 * f with hm`.

Establish `hmr : (m:ℝ) = (n:ℝ) ^ 2 * f` using `by rw [hm]; push_cast; ring`. Establish `hP : 2 * P0 n q f = q * (16 * m)` using `by rw [hm]; unfold P0; ring`. Establish `e4 : 4 * n ^ 2 * f = 4 * m` using `by rw [hm]; ring`. Establish `e12 : 12 * n ^ 2 * f = 12 * m` using `by rw [hm]; ring`. Establish `e16 : 16 * q * n ^ 2 * f = q * (16 * m)` using `by rw [hm]; ring`.

Rewrite `hK` using `[hP]`. Rewrite `hB` using `[e4]`. Rewrite using `[e12, e16]`. Use `set W := (n:ℝ) ^ 4 * (f:ℝ) ^ 2 * g * rd * b₁ with hW`. Establish `hW0 : 0 ≤ W` using `by rw [hW]; positivity`.

Establish `hx0 : 0 ≤ (2 * τ₁) ^ ((1:ℝ) / q)` using `by positivity`. Establish `hT : (C * ρ * (n:ℝ) ^ 2 * f * b₁) ^ (q * (16 * m)) ≤ (C ^ 2 * W) ^ (q * (16 * m)) * (2 * τ₁) ^ (16 * m)`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Rewrite using `[hW]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = (C ^ 2 * W) ^ (q * (16 * m)) * ((2 * τ₁) ^ ((1:ℝ) / q)) ^ (q * (16 * m)) := mul_pow _ _ _`. Use `_ = _ := by`. Use `congr 1`. Rewrite using `[pow_mul, one_div, Real.rpow_inv_natCast_pow (by linarith) hq0]`.

Establish `hT0 : 0 ≤ (C * ρ * (n:ℝ) ^ 2 * f * b₁) ^ (q * (16 * m))` using `by positivity`. Establish `s1 : volG * Kxx ≤ (C * ρ * (n:ℝ) ^ 2 * f * b₁) ^ (q * (16 * m)) * D * (C * (n:ℝ) ^ 2 * b₁) ^ m * (C / τ₁) ^ (4 * m) * (C * n * rd * g) ^ m`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_left _ hvG` to reduce the goal to its premises. Conclude with `hK.trans (mul_le_mul_of_nonneg_left hB hT0)`.

Use `_ = (C * ρ * (n:ℝ) ^ 2 * f * b₁) ^ (q * (16 * m)) * D * (C * (n:ℝ) ^ 2 * b₁) ^ m * (C / τ₁) ^ (4 * m) * (volG / volK) := by`. Rewrite using `[div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ _ := by gcongr`. Establish `s2 : (2 * τ₁) ^ (16 * m) * (C / τ₁) ^ (4 * m) = (2 ^ 16 * C ^ 4) ^ m * τ₁ ^ (12 * m)`.

Establish `: 16 * m = 12 * m + 4 * m` using `by ring`. Rewrite using `[mul_pow 2 τ₁, div_pow]`. Use `conv_lhs => rw [this, pow_add τ₁]`. Establish `h4 : τ₁ ^ (4 * m) ≠ 0` using `by positivity`. Rewrite using `[← this, mul_pow, ← pow_mul, ← pow_mul]`.

Clear the denominators using the available nonvanishing facts. Establish `hCY` using `le_rpow_two_mul hY (by linarith : 0 ≤ C)`. Establish `s3 : 2 ^ 16 * C ^ 4 * (C * (n:ℝ) ^ 2 * b₁) * (C * n * rd * g) ≤ Y ^ (12 * C + 31)`. Establish `e : Y ^ (12 * C + 31) = Y ^ 16 * (Y ^ (2 * C)) ^ 4 * (Y ^ (2 * C) * Y ^ 2 * Y ^ 10) * (Y ^ (2 * C) * Y * Y * Y)`. Rewrite using `[Real.rpow_add hY0]`.

Establish `h31 : Y ^ (31:ℝ) = Y ^ 31` using `by exact_mod_cast Real.rpow_natCast Y 31`. Establish `h12 : Y ^ (12 * C) = (Y ^ (2 * C)) ^ 6`. Rewrite using `[← Real.rpow_mul_natCast hY0.le]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h31, h12]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `gcongr`.

Establish `s4 : (2 ^ 16 * C ^ 4) ^ m * (C * (n:ℝ) ^ 2 * b₁) ^ m * (C * n * rd * g) ^ m ≤ Y ^ ((C ^ 2 + 12 * C + 31) * (n:ℝ) ^ 2 * f)`. Rewrite using `[← mul_pow, ← mul_pow]`. Combine the equalities or inequalities in the displayed calculation. Apply `pow_le_pow_left₀ (by positivity) s3` to reduce the goal to its premises. Use `_ = Y ^ ((12 * C + 31) * m) := (Real.rpow_mul_natCast hY0.le _ _).symm`.

Use `_ ≤ _ := by`. Apply `Real.rpow_le_rpow_of_exponent_le hY1` to reduce the goal to its premises. Rewrite using `[hmr]`. Establish `hm0 : 0 ≤ (n:ℝ) ^ 2 * f` using `by positivity`. Use polynomial arithmetic with `[sq_nonneg C]`.

Establish `s5 : (C ^ 2 * W) ^ (q * (16 * m)) ≤ ((C ^ 2 + 12 * C + 31) * (n:ℝ) ^ 4 * (f:ℝ) ^ 2 * g * rd * b₁) ^ (q * (16 * m))`. Apply `pow_le_pow_left₀ (by positivity)` to reduce the goal to its premises. Establish `: (C ^ 2 + 12 * C + 31) * (n:ℝ) ^ 4 * (f:ℝ) ^ 2 * g * rd * b₁ = (C ^ 2 + 12 * C + 31) * W`. Rewrite using `[hW]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Apply `mul_le_mul_of_nonneg_right _ hW0` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Establish `s6 : τ₁ ^ (12 * m) ≤ τs ^ (12 * m)` using `by gcongr`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem deep_region_chain : DeepChain := by
  intro C hC
  refine ⟨C ^ 2 + 12 * C + 31, by nlinarith, ?_⟩
  intro n q f rd g b τ₁ τs ρ Kxx Bs D volG volK hn hq hqn hf hrd hg hb hτ hττ hD hvK hvG hρ0 hρ hK hB hvol
  obtain ⟨hY, hnY, hfY, hrdY, hgY, hbY⟩ := ydat_facts hn hf hrd hg hb
  have hqn' : q ≤ n := le_trans (Nat.le_self_pow (by norm_num) q) hqn
  have hb1 := b1_bound_le_power (f := f) hqn' hY hnY hfY (by linarith) hbY
  have hb10 : 0 ≤ b1 n q f b := by unfold b1; positivity
  generalize Ydat n f rd g b = Y at *
  generalize b1 n q f b = b₁ at *
  have hY0 : 0 < Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hq0 : q ≠ 0 := by omega
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hf0 : (0:ℝ) ≤ f := Nat.cast_nonneg _
  set m : ℕ := n ^ 2 * f with hm
  have hmr : (m:ℝ) = (n:ℝ) ^ 2 * f := by rw [hm]; push_cast; ring
  have hP : 2 * P0 n q f = q * (16 * m) := by rw [hm]; unfold P0; ring
  have e4 : 4 * n ^ 2 * f = 4 * m := by rw [hm]; ring
  have e12 : 12 * n ^ 2 * f = 12 * m := by rw [hm]; ring
  have e16 : 16 * q * n ^ 2 * f = q * (16 * m) := by rw [hm]; ring
  rw [hP] at hK
  rw [e4] at hB
  rw [e12, e16]
  set W := (n:ℝ) ^ 4 * (f:ℝ) ^ 2 * g * rd * b₁ with hW
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have hx0 : 0 ≤ (2 * τ₁) ^ ((1:ℝ) / q) := by positivity
  have hT : (C * ρ * (n:ℝ) ^ 2 * f * b₁) ^ (q * (16 * m)) ≤ (C ^ 2 * W) ^ (q * (16 * m)) * (2 * τ₁) ^ (16 * m) := by
    calc (C * ρ * (n:ℝ) ^ 2 * f * b₁) ^ (q * (16 * m))
        ≤ (C * (C * (n:ℝ) ^ 2 * f * g * rd * (2 * τ₁) ^ ((1:ℝ) / q)) * (n:ℝ) ^ 2 * f * b₁) ^ (q * (16 * m)) := by
          gcongr
      _ = ((C ^ 2 * W) * (2 * τ₁) ^ ((1:ℝ) / q)) ^ (q * (16 * m)) := by
          congr 1; rw [hW]; ring
      _ = (C ^ 2 * W) ^ (q * (16 * m)) * ((2 * τ₁) ^ ((1:ℝ) / q)) ^ (q * (16 * m)) := mul_pow _ _ _
      _ = _ := by
        congr 1
        rw [pow_mul, one_div, Real.rpow_inv_natCast_pow (by linarith) hq0]
  have hT0 : 0 ≤ (C * ρ * (n:ℝ) ^ 2 * f * b₁) ^ (q * (16 * m)) := by positivity
  have s1 : volG * Kxx ≤ (C * ρ * (n:ℝ) ^ 2 * f * b₁) ^ (q * (16 * m)) * D
      * (C * (n:ℝ) ^ 2 * b₁) ^ m * (C / τ₁) ^ (4 * m) * (C * n * rd * g) ^ m := by
    calc volG * Kxx ≤ volG * ((C * ρ * (n:ℝ) ^ 2 * f * b₁) ^ (q * (16 * m))
          * (D * volK⁻¹ * (C * (n:ℝ) ^ 2 * b₁) ^ m * (C / τ₁) ^ (4 * m))) := by
          apply mul_le_mul_of_nonneg_left _ hvG
          exact hK.trans (mul_le_mul_of_nonneg_left hB hT0)
      _ = (C * ρ * (n:ℝ) ^ 2 * f * b₁) ^ (q * (16 * m)) * D
          * (C * (n:ℝ) ^ 2 * b₁) ^ m * (C / τ₁) ^ (4 * m) * (volG / volK) := by
          rw [div_eq_mul_inv]; ring
      _ ≤ _ := by gcongr
  have s2 : (2 * τ₁) ^ (16 * m) * (C / τ₁) ^ (4 * m) = (2 ^ 16 * C ^ 4) ^ m * τ₁ ^ (12 * m) := by
    have : 16 * m = 12 * m + 4 * m := by ring
    rw [mul_pow 2 τ₁, div_pow]
    conv_lhs => rw [this, pow_add τ₁]
    have h4 : τ₁ ^ (4 * m) ≠ 0 := by positivity
    rw [← this, mul_pow, ← pow_mul, ← pow_mul]
    field_simp
  have hCY := le_rpow_two_mul hY (by linarith : 0 ≤ C)
  have s3 : 2 ^ 16 * C ^ 4 * (C * (n:ℝ) ^ 2 * b₁) * (C * n * rd * g) ≤ Y ^ (12 * C + 31) := by
    have e : Y ^ (12 * C + 31) = Y ^ 16 * (Y ^ (2 * C)) ^ 4 * (Y ^ (2 * C) * Y ^ 2 * Y ^ 10)
        * (Y ^ (2 * C) * Y * Y * Y) := by
      rw [Real.rpow_add hY0]
      have h31 : Y ^ (31:ℝ) = Y ^ 31 := by exact_mod_cast Real.rpow_natCast Y 31
      have h12 : Y ^ (12 * C) = (Y ^ (2 * C)) ^ 6 := by
        rw [← Real.rpow_mul_natCast hY0.le]; congr 1; push_cast; ring
      rw [h31, h12]; ring
    rw [e]
    gcongr
  have s4 : (2 ^ 16 * C ^ 4) ^ m * (C * (n:ℝ) ^ 2 * b₁) ^ m * (C * n * rd * g) ^ m
      ≤ Y ^ ((C ^ 2 + 12 * C + 31) * (n:ℝ) ^ 2 * f) := by
    rw [← mul_pow, ← mul_pow]
    calc _ ≤ (Y ^ (12 * C + 31)) ^ m := by
          apply pow_le_pow_left₀ (by positivity) s3
      _ = Y ^ ((12 * C + 31) * m) := (Real.rpow_mul_natCast hY0.le _ _).symm
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hY1
        rw [hmr]
        have hm0 : 0 ≤ (n:ℝ) ^ 2 * f := by positivity
        nlinarith [sq_nonneg C]
  have s5 : (C ^ 2 * W) ^ (q * (16 * m)) ≤ ((C ^ 2 + 12 * C + 31) * (n:ℝ) ^ 4 * (f:ℝ) ^ 2 * g * rd * b₁) ^ (q * (16 * m)) := by
    apply pow_le_pow_left₀ (by positivity)
    have : (C ^ 2 + 12 * C + 31) * (n:ℝ) ^ 4 * (f:ℝ) ^ 2 * g * rd * b₁ = (C ^ 2 + 12 * C + 31) * W := by
      rw [hW]; ring
    rw [this]
    apply mul_le_mul_of_nonneg_right _ hW0
    linarith
  have s6 : τ₁ ^ (12 * m) ≤ τs ^ (12 * m) := by gcongr
  calc volG * Kxx ≤ (C * ρ * (n:ℝ) ^ 2 * f * b₁) ^ (q * (16 * m)) * D
      * (C * (n:ℝ) ^ 2 * b₁) ^ m * (C / τ₁) ^ (4 * m) * (C * n * rd * g) ^ m := s1
    _ ≤ ((C ^ 2 * W) ^ (q * (16 * m)) * (2 * τ₁) ^ (16 * m)) * D
      * (C * (n:ℝ) ^ 2 * b₁) ^ m * (C / τ₁) ^ (4 * m) * (C * n * rd * g) ^ m := by gcongr
    _ = D * ((2 * τ₁) ^ (16 * m) * (C / τ₁) ^ (4 * m) * (C * (n:ℝ) ^ 2 * b₁) ^ m * (C * n * rd * g) ^ m)
        * (C ^ 2 * W) ^ (q * (16 * m)) := by ring
    _ = D * ((2 ^ 16 * C ^ 4) ^ m * (C * (n:ℝ) ^ 2 * b₁) ^ m * (C * n * rd * g) ^ m)
        * (C ^ 2 * W) ^ (q * (16 * m)) * τ₁ ^ (12 * m) := by rw [s2]; ring
    _ ≤ _ := by gcongr

/- English proof (translation)
Establish `hn' : (1:ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hf' : (1:ℝ) ≤ f` using `by exact_mod_cast hf`. Unfold `Ydat`. Rewrite using `[Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]`.
-/
lemma log_ydat {n f : ℕ} {rd g b : ℝ} (hn : 1 ≤ n) (hf : 1 ≤ f) (hrd : 1 ≤ rd) (hg : 1 ≤ g)
    (hb : 2 ≤ b) : Real.log (Ydat n f rd g b)
      = Real.log n + Real.log f + Real.log rd + Real.log g + Real.log b := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  unfold Ydat
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]

/- English proof (translation)
Introduce `C' c Cg hC' hc hCg`. Use `⟨C' * (Cg + 6) / c ^ 2, by positivity, ?_⟩` and prove the remaining obligations. Introduce `n q f rd g b h hn hf hq hlf hb hrd hg hgb hh`. Establish `hn' : (1:ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hf' : (1:ℝ) ≤ f` using `by exact_mod_cast hf`.

Establish `hqn : (q:ℝ)^2 ≤ n` using `by exact_mod_cast hq`. Establish `hq0 : (0:ℝ) ≤ q` using `Nat.cast_nonneg _`. Establish `hs1 : 1 ≤ Real.sqrt (n:ℝ)` using `Real.one_le_sqrt.mpr hn'`. Establish `hss : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = n` using `Real.mul_self_sqrt (by linarith)`. Establish `hqs : (q:ℝ) ≤ Real.sqrt n` using `Real.le_sqrt_of_sq_le hqn`.

Establish `hlogn : Real.log n ≤ 2 * Real.sqrt n`. Establish `h1 : Real.log n = 2 * Real.log (Real.sqrt n)`. Rewrite using `[Real.log_sqrt (by linarith)]; ring`. Establish `h2` using `Real.log_le_sub_one_of_pos (show 0 < Real.sqrt (n:ℝ) by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hlb : Real.log 2 ≤ Real.log b` using `Real.log_le_log (by norm_num) hb`. Establish `hl2` using `Real.log_two_gt_d9`. Establish `hlrd : 0 ≤ Real.log rd` using `Real.log_nonneg hrd`. Establish `hlbr : Real.log (b * rd) = Real.log b + Real.log rd` using `Real.log_mul (by positivity) (by positivity)`. Establish `hlg : Real.log g ≤ Cg * Real.log b`.

Use `Real.log_le_log (by linarith) hgb` as an intermediate fact. Rewrite `this` using `[Real.log_rpow (by linarith)]`. Then use the resulting hypothesis. Rewrite `hh` using `[hlbr]`. Establish `hY` using `log_ydat hn hf hrd hg hb`. Use `set ℓ := Real.log b + Real.log rd with hℓ`.

Establish `hℓ0 : 0.69 ≤ ℓ` using `by linarith`. Establish `hlY : Real.log (Ydat n f rd g b) ≤ 3 * Real.sqrt n + (Cg + 1) * ℓ`. Rewrite using `[hY]`. Establish `: Cg * Real.log b ≤ Cg * ℓ`. Apply `mul_le_mul_of_nonneg_left _ (by linarith); linarith` to reduce the goal to its premises.

Combine the linear equalities and inequalities to obtain the conclusion. Generalize the expression as in `Real.log (Ydat n f rd g b) = LY at *`. Generalize the expression as in `Real.sqrt (n:ℝ) = s at *`. Establish `k1 : (q:ℝ) * LY ≤ (Cg + 6) * (n * ℓ)`. Combine the equalities or inequalities in the displayed calculation.

Apply `mul_le_mul_of_nonneg_right hqs` to reduce the goal to its premises. Establish `: 0 ≤ (Cg + 1) * ℓ` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = 3 * n + (Cg + 1) * (s * ℓ) := by rw [← hss]; ring`. Use `_ ≤ 3 * n + (Cg + 1) * (n * ℓ) := by`.

Establish `: s ≤ n` using `by nlinarith`. Use `gcongr`. Use `_ ≤ _ := by nlinarith`. Establish `e2 : epsN c n f ^ 2 = c ^ 2 / ((n:ℝ) ^ 16 * (f:ℝ) ^ 4)`. Unfold `epsN`.

Rewrite using `[div_pow]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `he0 : 0 ≤ epsN c n f ^ 2` using `sq_nonneg _`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[e2]`. Clear the denominators using the available nonvanishing facts. Use `_ ≤ h * epsN c n f ^ 2 := by gcongr`.
-/
theorem threshold_far_region : ThreshFar := by
  intro C' c Cg hC' hc hCg
  refine ⟨C' * (Cg + 6) / c ^ 2, by positivity, ?_⟩
  intro n q f rd g b h hn hf hq hlf hb hrd hg hgb hh
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hqn : (q:ℝ)^2 ≤ n := by exact_mod_cast hq
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have hs1 : 1 ≤ Real.sqrt (n:ℝ) := Real.one_le_sqrt.mpr hn'
  have hss : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = n := Real.mul_self_sqrt (by linarith)
  have hqs : (q:ℝ) ≤ Real.sqrt n := Real.le_sqrt_of_sq_le hqn
  have hlogn : Real.log n ≤ 2 * Real.sqrt n := by
    have h1 : Real.log n = 2 * Real.log (Real.sqrt n) := by
      rw [Real.log_sqrt (by linarith)]; ring
    have h2 := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt (n:ℝ) by linarith)
    linarith
  have hlb : Real.log 2 ≤ Real.log b := Real.log_le_log (by norm_num) hb
  have hl2 := Real.log_two_gt_d9
  have hlrd : 0 ≤ Real.log rd := Real.log_nonneg hrd
  have hlbr : Real.log (b * rd) = Real.log b + Real.log rd :=
    Real.log_mul (by positivity) (by positivity)
  have hlg : Real.log g ≤ Cg * Real.log b := by
    have := Real.log_le_log (by linarith) hgb
    rwa [Real.log_rpow (by linarith)] at this
  rw [hlbr] at hh
  have hY := log_ydat hn hf hrd hg hb
  set ℓ := Real.log b + Real.log rd with hℓ
  have hℓ0 : 0.69 ≤ ℓ := by linarith
  have hlY : Real.log (Ydat n f rd g b) ≤ 3 * Real.sqrt n + (Cg + 1) * ℓ := by
    rw [hY]
    have : Cg * Real.log b ≤ Cg * ℓ := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    linarith
  generalize Real.log (Ydat n f rd g b) = LY at *
  generalize Real.sqrt (n:ℝ) = s at *
  have k1 : (q:ℝ) * LY ≤ (Cg + 6) * (n * ℓ) := by
    calc (q:ℝ) * LY ≤ q * (3 * s + (Cg + 1) * ℓ) := by gcongr
      _ ≤ s * (3 * s + (Cg + 1) * ℓ) := by
          apply mul_le_mul_of_nonneg_right hqs
          have : 0 ≤ (Cg + 1) * ℓ := by positivity
          linarith
      _ = 3 * n + (Cg + 1) * (s * ℓ) := by rw [← hss]; ring
      _ ≤ 3 * n + (Cg + 1) * (n * ℓ) := by
          have : s ≤ n := by nlinarith
          gcongr
      _ ≤ _ := by nlinarith
  have e2 : epsN c n f ^ 2 = c ^ 2 / ((n:ℝ) ^ 16 * (f:ℝ) ^ 4) := by
    unfold epsN; rw [div_pow]; congr 1; ring
  have he0 : 0 ≤ epsN c n f ^ 2 := sq_nonneg _
  calc C' * (n:ℝ) ^ 2 * q * f * LY = C' * (n:ℝ) ^ 2 * f * (q * LY) := by ring
    _ ≤ C' * (n:ℝ) ^ 2 * f * ((Cg + 6) * (n * ℓ)) := by gcongr
    _ = (C' * (Cg + 6) / c ^ 2 * (n:ℝ) ^ 19 * (f:ℝ) ^ 5 * ℓ) * epsN c n f ^ 2 := by
        rw [e2]; field_simp
    _ ≤ h * epsN c n f ^ 2 := by gcongr

/- English proof (translation)
Introduce `C C₁ c m hC hC₁ hc`. Use `⟨16 * ((2 * C + C₁) * m + 2 + c), by positivity, ?_⟩` and prove the remaining obligations. Introduce `n q f rd g b x hn hq hf hrd hg hb hx`. Take `⟨hY, hnY, hfY, hrdY, hgY, hbY⟩` from `ydat_facts hn hf hrd hg hb`. Generalize the expression as in `Ydat n f rd g b = Y at *`.

Establish `hY0 : 0 < Y` using `by linarith`. Establish `hn' : (1:ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hf' : (1:ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `hq' : (1:ℝ) ≤ q` using `by exact_mod_cast hq`. Establish `hlog : 1 / 2 ≤ Real.log Y`.

Establish `h1` using `Real.log_two_gt_d9`. Establish `h2 : Real.log 2 ≤ Real.log Y` using `Real.log_le_log (by norm_num) hY`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogn : Real.log n ≤ Real.log Y` using `Real.log_le_log (by linarith) hnY`. Establish `hlogn0 : 0 ≤ Real.log n` using `Real.log_nonneg hn'`.

Establish `h1 : C / Y ^ (-(C₁ * q)) ≤ Real.exp (Real.log Y * (2 * C + C₁ * q))`. Rewrite using `[Real.rpow_neg hY0.le, div_inv_eq_mul, ← Real.rpow_def_of_pos hY0, Real.rpow_add hY0]`. Use `le_rpow_two_mul hY (by linarith : 0 ≤ C)` as an intermediate fact. Use `gcongr`. Establish `h2 : 2 * (f:ℝ) ≤ Real.exp (Real.log Y * 2)`.

Rewrite using `[← Real.rpow_def_of_pos hY0, Real.rpow_two]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h0 : 0 ≤ C / Y ^ (-(C₁ * q))` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]`.

Use `_ ≤ _ := by`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use `push_cast`. Generalize the expression as in `Real.log Y = ℓ at *`. Generalize the expression as in `Real.log (n:ℝ) = ln at *`.

Use `set u := (n:ℝ) ^ 2 * q * f with hu`. Establish `hm0 : (0:ℝ) ≤ m` using `Nat.cast_nonneg _`. Establish `u1 : (n:ℝ) ^ 2 * f ≤ u`. Rewrite using `[hu]`. Combine the equalities or inequalities in the displayed calculation.

Establish `u2 : (n:ℝ) * f ≤ (n:ℝ) ^ 2 * f`. Establish `: (n:ℝ) ≤ (n:ℝ) ^ 2` using `by nlinarith`. Use `gcongr`. Establish `u3 : 1 ≤ (n:ℝ) * f` using `by nlinarith`. Establish `hx' : ((2 * C + C₁) * m + 2 + c) * (u * ℓ) ≤ x / 16`.

Establish `: 16 * ((2 * C + C₁) * m + 2 + c) * (n:ℝ) ^ 2 * q * f * ℓ = 16 * (((2 * C + C₁) * m + 2 + c) * (u * ℓ))` using `by rw [hu]; ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `t1 : (m:ℝ) * (n:ℝ) ^ 2 * f * (ℓ * (2 * C + C₁ * q)) ≤ (2 * C + C₁) * m * (u * ℓ)`. Establish `e : (m:ℝ) * (n:ℝ) ^ 2 * f * (ℓ * (2 * C + C₁ * q)) = m * ℓ * (2 * C * ((n:ℝ) ^ 2 * f) + C₁ * u)` using `by rw [hu]; ring`. Rewrite using `[e]`.

Combine the equalities or inequalities in the displayed calculation. Establish `t2 : ℓ * 2 ≤ 2 * (u * ℓ)`. Establish `: 1 ≤ u` using `by linarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `t3 : c * n * f * ln ≤ c * (u * ℓ)`.

Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem far_region_negligible : FarNegligible := by
  intro C C₁ c m hC hC₁ hc
  refine ⟨16 * ((2 * C + C₁) * m + 2 + c), by positivity, ?_⟩
  intro n q f rd g b x hn hq hf hrd hg hb hx
  obtain ⟨hY, hnY, hfY, hrdY, hgY, hbY⟩ := ydat_facts hn hf hrd hg hb
  generalize Ydat n f rd g b = Y at *
  have hY0 : 0 < Y := by linarith
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hlog : 1 / 2 ≤ Real.log Y := by
    have h1 := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY
    linarith
  have hlogn : Real.log n ≤ Real.log Y := Real.log_le_log (by linarith) hnY
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn'
  have h1 : C / Y ^ (-(C₁ * q)) ≤ Real.exp (Real.log Y * (2 * C + C₁ * q)) := by
    rw [Real.rpow_neg hY0.le, div_inv_eq_mul, ← Real.rpow_def_of_pos hY0, Real.rpow_add hY0]
    have := le_rpow_two_mul hY (by linarith : 0 ≤ C)
    gcongr
  have h2 : 2 * (f:ℝ) ≤ Real.exp (Real.log Y * 2) := by
    rw [← Real.rpow_def_of_pos hY0, Real.rpow_two]
    nlinarith
  have h0 : 0 ≤ C / Y ^ (-(C₁ * q)) := by positivity
  calc (C / Y ^ (-(C₁ * q))) ^ (m * n ^ 2 * f) * (2 * f) * Real.exp (-(x / 16))
      ≤ (Real.exp (Real.log Y * (2 * C + C₁ * q))) ^ (m * n ^ 2 * f) * Real.exp (Real.log Y * 2)
          * Real.exp (-(x / 16)) := by gcongr
    _ = Real.exp (((m * n ^ 2 * f : ℕ) : ℝ) * (Real.log Y * (2 * C + C₁ * q)) + Real.log Y * 2
          + -(x / 16)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        push_cast
        generalize Real.log Y = ℓ at *
        generalize Real.log (n:ℝ) = ln at *
        set u := (n:ℝ) ^ 2 * q * f with hu
        have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg _
        have u1 : (n:ℝ) ^ 2 * f ≤ u := by
          rw [hu]
          calc (n:ℝ) ^ 2 * f = (n:ℝ) ^ 2 * 1 * f := by ring
            _ ≤ _ := by gcongr
        have u2 : (n:ℝ) * f ≤ (n:ℝ) ^ 2 * f := by
          have : (n:ℝ) ≤ (n:ℝ) ^ 2 := by nlinarith
          gcongr
        have u3 : 1 ≤ (n:ℝ) * f := by nlinarith
        have hx' : ((2 * C + C₁) * m + 2 + c) * (u * ℓ) ≤ x / 16 := by
          have : 16 * ((2 * C + C₁) * m + 2 + c) * (n:ℝ) ^ 2 * q * f * ℓ
              = 16 * (((2 * C + C₁) * m + 2 + c) * (u * ℓ)) := by rw [hu]; ring
          linarith
        have t1 : (m:ℝ) * (n:ℝ) ^ 2 * f * (ℓ * (2 * C + C₁ * q)) ≤ (2 * C + C₁) * m * (u * ℓ) := by
          have e : (m:ℝ) * (n:ℝ) ^ 2 * f * (ℓ * (2 * C + C₁ * q))
              = m * ℓ * (2 * C * ((n:ℝ) ^ 2 * f) + C₁ * u) := by rw [hu]; ring
          rw [e]
          calc (m:ℝ) * ℓ * (2 * C * ((n:ℝ) ^ 2 * f) + C₁ * u) ≤ m * ℓ * (2 * C * u + C₁ * u) := by
                gcongr
            _ = _ := by ring
        have t2 : ℓ * 2 ≤ 2 * (u * ℓ) := by
          have : 1 ≤ u := by linarith
          nlinarith
        have t3 : c * n * f * ln ≤ c * (u * ℓ) := by
          calc c * n * f * ln = c * ((n * f) * ln) := by ring
            _ ≤ c * (u * ℓ) := by
              gcongr
              linarith
        nlinarith

/- English proof (translation)
Unfold `Vsph; exact Finset.prod_pos fun l _ => by positivity`.
-/
lemma vsph_pos (i : ℕ) : 0 < Vsph i := by
  unfold Vsph; exact Finset.prod_pos fun l _ => by positivity

/- English proof (translation)
Proceed by induction on `J with`. Consider the case `zero => simp`. Consider the case `succ J ih`. Rewrite using `[Finset.prod_range_succ, ← mul_assoc, ← ih]`. Unfold `Vsph`.

Rewrite using `[← add_assoc, Finset.prod_Icc_succ_top (by omega)]`. Simplify using the standard rewrite rules.
-/
lemma vsph_add (k J : ℕ) : Vsph (k + J)
    = Vsph k * ∏ i ∈ range J, (2 * Real.pi ^ (k + i + 1) / ((k + i).factorial : ℝ)) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih]
    unfold Vsph
    rw [← add_assoc, Finset.prod_Icc_succ_top (by omega)]
    simp

noncomputable def sfac (k : ℕ) : ℝ := ∏ i ∈ range k, (i.factorial : ℝ)

/- English proof (translation)
Unfold `sfac; exact Finset.prod_pos fun l _ => by positivity`.
-/
lemma sfac_pos (k : ℕ) : 0 < sfac k := by
  unfold sfac; exact Finset.prod_pos fun l _ => by positivity

/- English proof (translation)
Unfold `sfac`. Rewrite using `[Finset.prod_range_add]`. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Apply `Finset.prod_le_prod (fun i _ => by positivity)` to reduce the goal to its premises. Introduce `i _`.

Conclude with `Nat.factorial_le (by omega)` after adjusting the coercions.
-/
lemma sfac_mul_le (a b : ℕ) : sfac a * sfac b ≤ sfac (a + b) := by
  unfold sfac
  rw [Finset.prod_range_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.prod_le_prod (fun i _ => by positivity)
  intro i _
  exact_mod_cast Nat.factorial_le (by omega)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [sfac]`. Consider the case `insert x s hx ih`. Rewrite using `[Finset.prod_insert hx, Finset.sum_insert hx]`. Combine the equalities or inequalities in the displayed calculation.

Apply `mul_le_mul_of_nonneg_left ih (sfac_pos _).le` to reduce the goal to its premises. Use `_ ≤ _ := sfac_mul_le _ _`.
-/
lemma sfac_prod_le {ι : Type} (s : Finset ι) (j : ι → ℕ) :
    ∏ x ∈ s, sfac (j x) ≤ sfac (∑ x ∈ s, j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sfac]
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    calc sfac (j x) * ∏ x ∈ s, sfac (j x) ≤ sfac (j x) * sfac (∑ x ∈ s, j x) := by
          apply mul_le_mul_of_nonneg_left ih (sfac_pos _).le
      _ ≤ _ := sfac_mul_le _ _

/- English proof (translation)
Establish `hπ : 3 < Real.pi` using `Real.pi_gt_three`. Establish `: 1 ≤ Real.pi ^ l` using `one_le_pow₀ (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma one_le_two_pi_pow (l : ℕ) : 1 ≤ 2 * Real.pi ^ l := by
  have hπ : 3 < Real.pi := Real.pi_gt_three
  have : 1 ≤ Real.pi ^ l := one_le_pow₀ (by linarith)
  linarith

/- English proof (translation)
Establish `h` using `vsph_add 0 k`. Establish `h0 : Vsph 0 = 1` using `by simp [Vsph]`. Rewrite `h` using `[zero_add, h0, one_mul]`. Rewrite using `[h]`. Unfold `sfac`.

Rewrite using `[← Finset.prod_inv_distrib]`. Apply `Finset.prod_le_prod (fun i _ => by positivity)` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[zero_add, div_eq_mul_inv]`. Use `one_le_two_pi_pow (i + 1)` as an intermediate fact.

Establish `h2 : (0:ℝ) ≤ ((i.factorial : ℝ))⁻¹` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma inv_sfac_le_vsph (k : ℕ) : (sfac k)⁻¹ ≤ Vsph k := by
  have h := vsph_add 0 k
  have h0 : Vsph 0 = 1 := by simp [Vsph]
  rw [zero_add, h0, one_mul] at h
  rw [h]
  unfold sfac
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_le_prod (fun i _ => by positivity)
  intro i _
  rw [zero_add, div_eq_mul_inv]
  have := one_le_two_pi_pow (i + 1)
  have h2 : (0:ℝ) ≤ ((i.factorial : ℝ))⁻¹ := by positivity
  nlinarith

/- English proof (translation)
Establish `hπ : 3 < Real.pi` using `Real.pi_gt_three`. Establish `he : 1 ≤ Real.exp 1` using `Real.one_le_exp (by norm_num)`. Establish `hp0 : (0:ℝ) < p` using `by exact_mod_cast hp`. Establish `hC1 : 1 ≤ 2 * Real.pi * Real.exp 1` using `by nlinarith`. Establish `h1` using `Real.pow_div_factorial_le_exp (p:ℝ) hp0.le k`.

Establish `hk0 : (0:ℝ) < k.factorial` using `by exact_mod_cast k.factorial_pos`. Establish `h2 : 1 / (k.factorial:ℝ) ≤ Real.exp p / (p:ℝ)^k`. Rewrite using `[div_le_div_iff₀ hk0 (by positivity)]`. Rewrite `h1` using `[div_le_iff₀ hk0]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h3 : 1 / (p:ℝ)^k ≤ ((2 * Real.pi * Real.exp 1) / (p:ℝ)) ^ k`. Rewrite using `[div_pow]`. Use `gcongr`. Conclude with `one_le_pow₀ hC1`. Establish `h4 : 4 * Real.pi ^ (p+q) * Real.exp p ≤ (2 * Real.pi * Real.exp 1) ^ (p + q)`.

Rewrite using `[mul_pow, mul_pow]`. Establish `a : (4:ℝ) ≤ 2^(p+q)`. Combine the equalities or inequalities in the displayed calculation. Establish `b : Real.exp p ≤ Real.exp 1 ^ (p+q)`. Rewrite using `[← Real.exp_nat_mul, mul_one]`.

Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use `push_cast`. Combine the linear relations using `[(Nat.cast_nonneg q : (0:ℝ) ≤ q)]`. Use `gcongr`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma vratio_base (p q k : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    2 * Real.pi ^ p / (k.factorial : ℝ) * (2 * Real.pi ^ q)
      ≤ (2 * Real.pi * Real.exp 1) ^ (p + q) * ((2 * Real.pi * Real.exp 1) / (p:ℝ)) ^ k := by
  have hπ : 3 < Real.pi := Real.pi_gt_three
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  have hC1 : 1 ≤ 2 * Real.pi * Real.exp 1 := by nlinarith
  have h1 := Real.pow_div_factorial_le_exp (p:ℝ) hp0.le k
  have hk0 : (0:ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have h2 : 1 / (k.factorial:ℝ) ≤ Real.exp p / (p:ℝ)^k := by
    rw [div_le_div_iff₀ hk0 (by positivity)]
    rw [div_le_iff₀ hk0] at h1
    linarith
  have h3 : 1 / (p:ℝ)^k ≤ ((2 * Real.pi * Real.exp 1) / (p:ℝ)) ^ k := by
    rw [div_pow]
    gcongr
    exact one_le_pow₀ hC1
  have h4 : 4 * Real.pi ^ (p+q) * Real.exp p ≤ (2 * Real.pi * Real.exp 1) ^ (p + q) := by
    rw [mul_pow, mul_pow]
    have a : (4:ℝ) ≤ 2^(p+q) := by
      calc (4:ℝ) = 2^2 := by norm_num
        _ ≤ 2^(p+q) := pow_le_pow_right₀ (by norm_num) (by omega)
    have b : Real.exp p ≤ Real.exp 1 ^ (p+q) := by
      rw [← Real.exp_nat_mul, mul_one]; apply Real.exp_le_exp.mpr; push_cast
      linarith [(Nat.cast_nonneg q : (0:ℝ) ≤ q)]
    gcongr
  calc 2 * Real.pi ^ p / (k.factorial : ℝ) * (2 * Real.pi ^ q)
      = 4 * Real.pi^(p+q) * (1 / (k.factorial:ℝ)) := by rw [pow_add]; ring
    _ ≤ 4 * Real.pi^(p+q) * (Real.exp p / (p:ℝ)^k) := by gcongr
    _ = (4 * Real.pi^(p+q) * Real.exp p) * (1 / (p:ℝ)^k) := by ring
    _ ≤ _ := by gcongr

/- English proof (translation)
Establish `hπ : 3 < Real.pi` using `Real.pi_gt_three`. Establish `he : 1 ≤ Real.exp 1` using `Real.one_le_exp (by norm_num)`. Use `⟨2 * Real.pi * Real.exp 1, by nlinarith, ?_⟩` and prove the remaining obligations. Introduce `p q a j hJq hqp`. Establish `hPi : (sfac (∑ x, j x))⁻¹ ≤ ∏ x, Vsph (j x)`.

Combine the equalities or inequalities in the displayed calculation. Apply `inv_anti₀ (Finset.prod_pos fun x _ => sfac_pos _) (sfac_prod_le _ _)` to reduce the goal to its premises. Use `_ = ∏ x, (sfac (j x))⁻¹ := (Finset.prod_inv_distrib _).symm`. Use `_ ≤ _ := Finset.prod_le_prod (fun x _ => (inv_pos.mpr (sfac_pos _)).le) (fun x _ => inv_sfac_le_vsph _)`. Generalize the expression as in `(∏ x, Vsph (j x)) = Pj at *`.

Generalize the expression as in `(∑ x, j x) = J at *`. Take `⟨k', rfl⟩` from `Nat.exists_eq_add_of_le' hJq`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le' (le_trans (Nat.le_add_left J k') hqp)`. Rewrite using `[Nat.add_sub_cancel, Nat.add_sub_cancel, vsph_add k J, vsph_add k' J]`. Establish `hS` using `sfac_pos J`.

Establish `hPj : 0 < Pj` using `lt_of_lt_of_le (inv_pos.mpr hS) hPi`. Establish `hVk` using `vsph_pos k`. Establish `hVk'` using `vsph_pos k'`. Use `set P1 := ∏ i ∈ range J, (2 * Real.pi ^ (k + i + 1) / ((k + i).factorial : ℝ)) with hP1`. Use `set P2 := ∏ i ∈ range J, (2 * Real.pi ^ (k' + i + 1) / ((k' + i).factorial : ℝ)) with hP2`.

Establish `hP10 : 0 ≤ P1` using `Finset.prod_nonneg fun i _ => by positivity`. Establish `hP20 : 0 ≤ P2` using `Finset.prod_nonneg fun i _ => by positivity`. Establish `e : Vsph k * P1 * (Vsph k' * P2) / (Vsph k * Vsph k' * Pj) = P1 * P2 / Pj`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.

Establish `b1 : P1 ≤ (2 * Real.pi ^ (k + J) / (k.factorial : ℝ)) ^ J`. Rewrite using `[hP1]`. Use `conv_rhs => rw [← Finset.card_range J, ← Finset.prod_const, Finset.card_range]`. Apply `Finset.prod_le_prod (fun i _ => by positivity)` to reduce the goal to its premises. Introduce `i hi`.

Establish `hi'` using `Finset.mem_range.mp hi`. Establish `h1 : Real.pi ^ (k + i + 1) ≤ Real.pi ^ (k + J)` using `pow_le_pow_right₀ (by linarith) (by omega)`. Establish `h2 : (k.factorial : ℝ) ≤ ((k + i).factorial : ℝ)`. Conclude with `Nat.factorial_le (by omega)` after adjusting the coercions. Establish `h3 : (0:ℝ) < k.factorial` using `by exact_mod_cast k.factorial_pos`.

Use `gcongr`. Establish `b2 : P2 ≤ (2 * Real.pi ^ (k' + J)) ^ J * (sfac J)⁻¹`. Rewrite using `[hP2]`. Unfold `sfac`. Rewrite using `[← Finset.prod_inv_distrib]`.

Use `conv_rhs => rw [← Finset.card_range J, ← Finset.prod_const, Finset.card_range]`. Rewrite using `[← Finset.prod_mul_distrib]`. Apply `Finset.prod_le_prod (fun i _ => by positivity)` to reduce the goal to its premises. Introduce `i hi`. Establish `hi'` using `Finset.mem_range.mp hi`.

Establish `h1 : Real.pi ^ (k' + i + 1) ≤ Real.pi ^ (k' + J)` using `pow_le_pow_right₀ (by linarith) (by omega)`. Establish `h2 : (i.factorial : ℝ) ≤ ((k' + i).factorial : ℝ)`. Conclude with `Nat.factorial_le (by omega)` after adjusting the coercions. Establish `h3 : (0:ℝ) < i.factorial` using `by exact_mod_cast i.factorial_pos`. Rewrite using `[← div_eq_mul_inv]`.

Use `gcongr`. Establish `hJJ : 1 ≤ (J:ℝ) ^ ((J:ℝ) ^ 2 / 2)`. Break down `Nat.eq_zero_or_pos J with rfl | hJ` into its components or cases. Simplify using the standard rewrite rules. Conclude with `Real.one_le_rpow (by exact_mod_cast hJ) (by positivity)`.

Establish `b3 : P1 * P2 / Pj ≤ (2 * Real.pi ^ (k + J) / (k.factorial : ℝ) * (2 * Real.pi ^ (k' + J))) ^ J`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc ((2 * Real.pi ^ (k' + J)) ^ J), inv_mul_cancel₀ hS.ne', mul_one, ← mul_pow]`. Establish `b4 : (2 * Real.pi ^ (k + J) / (k.factorial : ℝ) * (2 * Real.pi ^ (k' + J))) ^ J ≤ (2 * Real.pi * Real.exp 1) ^ (J * (k + J + (k' + J))) * ((2 * Real.pi * Real.exp 1) / ((k + J : ℕ):ℝ)) ^ (J * k)`. Break down `Nat.eq_zero_or_pos J with rfl | hJ` into its components or cases.

Simplify using the standard rewrite rules. Rewrite using `[mul_comm J, mul_comm J, pow_mul, pow_mul, ← mul_pow]`. Apply `pow_le_pow_left₀ (by positivity)` to reduce the goal to its premises. Conclude with `vratio_base (k + J) (k' + J) k (by omega) (by omega)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem volume_ratio : VRatio := by
  have hπ : 3 < Real.pi := Real.pi_gt_three
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  refine ⟨2 * Real.pi * Real.exp 1, by nlinarith, ?_⟩
  intro p q a j hJq hqp
  have hPi : (sfac (∑ x, j x))⁻¹ ≤ ∏ x, Vsph (j x) := by
    calc (sfac (∑ x, j x))⁻¹ ≤ (∏ x, sfac (j x))⁻¹ := by
          apply inv_anti₀ (Finset.prod_pos fun x _ => sfac_pos _) (sfac_prod_le _ _)
      _ = ∏ x, (sfac (j x))⁻¹ := (Finset.prod_inv_distrib _).symm
      _ ≤ _ := Finset.prod_le_prod (fun x _ => (inv_pos.mpr (sfac_pos _)).le)
          (fun x _ => inv_sfac_le_vsph _)
  generalize (∏ x, Vsph (j x)) = Pj at *
  generalize (∑ x, j x) = J at *
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hJq
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (le_trans (Nat.le_add_left J k') hqp)
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel, vsph_add k J, vsph_add k' J]
  have hS := sfac_pos J
  have hPj : 0 < Pj := lt_of_lt_of_le (inv_pos.mpr hS) hPi
  have hVk := vsph_pos k
  have hVk' := vsph_pos k'
  set P1 := ∏ i ∈ range J, (2 * Real.pi ^ (k + i + 1) / ((k + i).factorial : ℝ)) with hP1
  set P2 := ∏ i ∈ range J, (2 * Real.pi ^ (k' + i + 1) / ((k' + i).factorial : ℝ)) with hP2
  have hP10 : 0 ≤ P1 := Finset.prod_nonneg fun i _ => by positivity
  have hP20 : 0 ≤ P2 := Finset.prod_nonneg fun i _ => by positivity
  have e : Vsph k * P1 * (Vsph k' * P2) / (Vsph k * Vsph k' * Pj) = P1 * P2 / Pj := by
    field_simp
  rw [e]
  have b1 : P1 ≤ (2 * Real.pi ^ (k + J) / (k.factorial : ℝ)) ^ J := by
    rw [hP1]
    conv_rhs => rw [← Finset.card_range J, ← Finset.prod_const, Finset.card_range]
    apply Finset.prod_le_prod (fun i _ => by positivity)
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have h1 : Real.pi ^ (k + i + 1) ≤ Real.pi ^ (k + J) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have h2 : (k.factorial : ℝ) ≤ ((k + i).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    have h3 : (0:ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
    gcongr
  have b2 : P2 ≤ (2 * Real.pi ^ (k' + J)) ^ J * (sfac J)⁻¹ := by
    rw [hP2]
    unfold sfac
    rw [← Finset.prod_inv_distrib]
    conv_rhs => rw [← Finset.card_range J, ← Finset.prod_const, Finset.card_range]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod (fun i _ => by positivity)
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have h1 : Real.pi ^ (k' + i + 1) ≤ Real.pi ^ (k' + J) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have h2 : (i.factorial : ℝ) ≤ ((k' + i).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    have h3 : (0:ℝ) < i.factorial := by exact_mod_cast i.factorial_pos
    rw [← div_eq_mul_inv]
    gcongr
  have hJJ : 1 ≤ (J:ℝ) ^ ((J:ℝ) ^ 2 / 2) := by
    rcases Nat.eq_zero_or_pos J with rfl | hJ
    · simp
    · exact Real.one_le_rpow (by exact_mod_cast hJ) (by positivity)
  have b3 : P1 * P2 / Pj ≤ (2 * Real.pi ^ (k + J) / (k.factorial : ℝ) * (2 * Real.pi ^ (k' + J))) ^ J := by
    calc P1 * P2 / Pj ≤ P1 * P2 / (sfac J)⁻¹ := by gcongr
      _ = P1 * (P2 * sfac J) := by rw [div_inv_eq_mul]; ring
      _ ≤ (2 * Real.pi ^ (k + J) / (k.factorial : ℝ)) ^ J
            * ((2 * Real.pi ^ (k' + J)) ^ J * (sfac J)⁻¹ * sfac J) := by gcongr
      _ = _ := by
          rw [mul_assoc ((2 * Real.pi ^ (k' + J)) ^ J), inv_mul_cancel₀ hS.ne', mul_one, ← mul_pow]
  have b4 : (2 * Real.pi ^ (k + J) / (k.factorial : ℝ) * (2 * Real.pi ^ (k' + J))) ^ J
      ≤ (2 * Real.pi * Real.exp 1) ^ (J * (k + J + (k' + J)))
        * ((2 * Real.pi * Real.exp 1) / ((k + J : ℕ):ℝ)) ^ (J * k) := by
    rcases Nat.eq_zero_or_pos J with rfl | hJ
    · simp
    · rw [mul_comm J, mul_comm J, pow_mul, pow_mul, ← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      exact vratio_base (k + J) (k' + J) k (by omega) (by omega)
  calc P1 * P2 / Pj ≤ _ := b3
    _ ≤ _ := b4
    _ = (2 * Real.pi * Real.exp 1) ^ (J * (k + J + (k' + J)))
        * ((2 * Real.pi * Real.exp 1) / ((k + J : ℕ):ℝ)) ^ (J * k) * 1 := (mul_one _).symm
    _ ≤ _ := by gcongr

/- English proof (translation)
Introduce `α S r β π c hc h0 hr hstep`. Establish `key : ∀ i, i ≤ r → ((S.image (π i)).card : ℝ) ≤ ∏ k ∈ range i, c k`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`.

Introduce `_`. Simplify using `only [Finset.range_zero, Finset.prod_empty]`. Establish `: (S.image (π 0)).card ≤ 1`. Rewrite using `[Finset.card_le_one]`. Introduce `a ha b hb`.

Take `⟨x, hx, rfl⟩` from `Finset.mem_image.mp ha`. Take `⟨y, hy, rfl⟩` from `Finset.mem_image.mp hb`. Conclude with `h0 x hx y hy`. Conclude with `this` after adjusting the coercions. Consider the case `succ i ih`.

Introduce `hi`. Establish `ih'` using `ih (by omega)`. Establish `hfib : ∀ b ∈ S.image (π i), (((S.filter (fun x => π i x = b)).image (π (i+1))).card : ℝ) ≤ c i`. Introduce `b _`. Take `⟨T, hTF, hinj, himg⟩` from `Finset.exists_subset_injOn_image_eq_of_surjOn (f := π (i+1)) (S.filter (fun x => π i x = b)) ((S.filter (fun x => π i x = b)).image (π (i+1))) (by`.

Introduce `v hv`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.mp hv`. Conclude with `⟨x, hx, rfl⟩)`. Rewrite using `[← himg, Finset.card_image_of_injOn hinj]`. Apply `hstep i (by omega) T` to reduce the goal to its premises.

Introduce `x hx`. Conclude with `(Finset.mem_filter.mp (hTF hx)).1`. Introduce `y hy z hz`. Rewrite using `[(Finset.mem_filter.mp (hTF hy)).2, (Finset.mem_filter.mp (hTF hz)).2]`. Introduce `y hy z hz hyz`.

Conclude with `hinj hy hz hyz`. Establish `hsub : S.image (π (i+1)) ⊆ (S.image (π i)).biUnion (fun b => (S.filter (fun x => π i x = b)).image (π (i+1)))`. Introduce `v hv`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.mp hv`. Conclude with `Finset.mem_biUnion.mpr ⟨π i x, Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hx, rfl⟩)⟩`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `Finset.card_le_card hsub` after adjusting the coercions. Use `_ ≤ ∑ b ∈ S.image (π i), (((S.filter (fun x => π i x = b)).image (π (i+1))).card : ℝ) := by`. Conclude with `Finset.card_biUnion_le` after adjusting the coercions. Use `_ ≤ ∑ b ∈ S.image (π i), c i := Finset.sum_le_sum hfib`.

Use `_ = (S.image (π i)).card * c i := by simp`. Use `_ ≤ (∏ k ∈ range i, c k) * c i := by`. Apply `mul_le_mul_of_nonneg_right ih' (hc i)` to reduce the goal to its premises. Use `_ = _ := (Finset.prod_range_succ _ _).symm`. Use `key r le_rfl` as an intermediate fact.

Rewrite `this` using `[Finset.card_image_of_injOn (fun x hx y hy h => hr x hx y hy h)]`. Then use the resulting hypothesis.
-/
theorem fibre_count_alt : FibreCount := by
  classical
  intro α S r β π c hc h0 hr hstep
  have key : ∀ i, i ≤ r → ((S.image (π i)).card : ℝ) ≤ ∏ k ∈ range i, c k := by
    intro i
    induction i with
    | zero =>
      intro _
      simp only [Finset.range_zero, Finset.prod_empty]
      have : (S.image (π 0)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
        exact h0 x hx y hy
      exact_mod_cast this
    | succ i ih =>
      intro hi
      have ih' := ih (by omega)
      have hfib : ∀ b ∈ S.image (π i),
          (((S.filter (fun x => π i x = b)).image (π (i+1))).card : ℝ) ≤ c i := by
        intro b _
        obtain ⟨T, hTF, hinj, himg⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
          (f := π (i+1)) (S.filter (fun x => π i x = b))
          ((S.filter (fun x => π i x = b)).image (π (i+1)))
          (by
            intro v hv
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
            exact ⟨x, hx, rfl⟩)
        rw [← himg, Finset.card_image_of_injOn hinj]
        apply hstep i (by omega) T
        · intro x hx; exact (Finset.mem_filter.mp (hTF hx)).1
        · intro y hy z hz
          rw [(Finset.mem_filter.mp (hTF hy)).2, (Finset.mem_filter.mp (hTF hz)).2]
        · intro y hy z hz hyz
          exact hinj hy hz hyz
      have hsub : S.image (π (i+1)) ⊆ (S.image (π i)).biUnion
          (fun b => (S.filter (fun x => π i x = b)).image (π (i+1))) := by
        intro v hv
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_biUnion.mpr ⟨π i x, Finset.mem_image_of_mem _ hx,
          Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hx, rfl⟩)⟩
      calc ((S.image (π (i+1))).card : ℝ)
          ≤ (((S.image (π i)).biUnion
              (fun b => (S.filter (fun x => π i x = b)).image (π (i+1)))).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ ∑ b ∈ S.image (π i), (((S.filter (fun x => π i x = b)).image (π (i+1))).card : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ b ∈ S.image (π i), c i := Finset.sum_le_sum hfib
        _ = (S.image (π i)).card * c i := by simp
        _ ≤ (∏ k ∈ range i, c k) * c i := by
            apply mul_le_mul_of_nonneg_right ih' (hc i)
        _ = _ := (Finset.prod_range_succ _ _).symm
  have := key r le_rfl
  rwa [Finset.card_image_of_injOn (fun x hx y hy h => hr x hx y hy h)] at this

def IsW (t : ℤ) : Prop := t = 0 ∨ ∃ k : ℕ, t = 4 ^ k ∨ t = -(4 ^ k)

/- English proof (translation)
Establish `h : ∀ x y : Fin a, j x * j y = (if x < y then j x * j y else 0) + (if y < x then j y * j x else 0) + (if x = y then j x ^ 2 else 0)`. Introduce `x y`. Break down `lt_trichotomy x y with h | h | h` into its components or cases. Simplify using `[h, h.ne, h.le.not_gt]`. Substitute `h` using the available equality.

Simplify using `[sq]`. Simplify using `[h, h.ne', h.le.not_gt, mul_comm]`. Rewrite using `[sq, Finset.sum_mul_sum]`. Repeatedly rewrite using `[Finset.sum_filter]`. Combine the equalities or inequalities in the displayed calculation.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `x _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `y _`. Conclude with `h x y`.

Use `_ = (∑ x, ∑ y, (if x < y then j x * j y else 0)) + (∑ x, ∑ y, (if y < x then j y * j x else 0)) + ∑ x, ∑ y, (if x = y then j x ^ 2 else 0) := by`. Repeatedly rewrite using `[Finset.sum_add_distrib]`. Use `_ = _ := by`. Rewrite using `[Finset.sum_comm (f := fun x y => if y < x then j y * j x else 0)]`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma sq_sum_fin {a : ℕ} (j : Fin a → ℕ) :
    (∑ x, j x) ^ 2 = (∑ x, j x ^ 2)
      + 2 * ∑ x, ∑ y ∈ univ.filter (fun y => x < y), j x * j y := by
  have h : ∀ x y : Fin a, j x * j y = (if x < y then j x * j y else 0)
      + (if y < x then j y * j x else 0) + (if x = y then j x ^ 2 else 0) := by
    intro x y
    rcases lt_trichotomy x y with h | h | h
    · simp [h, h.ne, h.le.not_gt]
    · subst h; simp [sq]
    · simp [h, h.ne', h.le.not_gt, mul_comm]
  rw [sq, Finset.sum_mul_sum]
  simp_rw [Finset.sum_filter]
  calc ∑ x, ∑ y, j x * j y
      = ∑ x, ∑ y, ((if x < y then j x * j y else 0)
      + (if y < x then j y * j x else 0) + (if x = y then j x ^ 2 else 0)) := by
        apply Finset.sum_congr rfl; intro x _
        apply Finset.sum_congr rfl; intro y _
        exact h x y
    _ = (∑ x, ∑ y, (if x < y then j x * j y else 0))
        + (∑ x, ∑ y, (if y < x then j y * j x else 0)) + ∑ x, ∑ y, (if x = y then j x ^ 2 else 0) := by
        simp_rw [Finset.sum_add_distrib]
    _ = _ := by
        rw [Finset.sum_comm (f := fun x y => if y < x then j y * j x else 0)]
        simp
        ring

/- English proof (translation)
Introduce `a j n0`. Establish `hsq` using `sq_sum_fin j`. Establish `hd : dimN j n0 = 4 * (∑ x, ∑ y ∈ univ.filter (fun y => x < y), j x * j y) + (∑ x, j x ^ 2) + 2 * (∑ x, j x) * n0`. Unfold `dimN`. Establish `e1 : (∑ x, ∑ y ∈ univ.filter (fun y => x < y), 2 * j x * j y) = 2 * ∑ x, ∑ y ∈ univ.filter (fun y => x < y), j x * j y`.

Repeatedly rewrite using `[mul_assoc, ← Finset.mul_sum]`. Establish `e2 : (∑ x, 2 * j x * n0) = 2 * (∑ x, j x) * n0`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[e1, e2]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h1 : (n0 + 2 * ∑ x, j x) ^ 2 = n0 ^ 2 + 2 * (∑ x, j x ^ 2) + 2 * dimN j n0`. Rewrite using `[hd]`. Establish `: (n0 + 2 * ∑ x, j x) ^ 2 = n0 ^ 2 + 4 * n0 * (∑ x, j x) + 4 * (∑ x, j x) ^ 2` using `by ring`. Rewrite using `[this, hsq]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨h1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hd]`. Establish `: 2 * (∑ x, j x) * (n0 + 2 * ∑ x, j x) = 2 * (∑ x, j x) * n0 + 4 * (∑ x, j x) ^ 2` using `by ring`. Rewrite using `[this, hsq]`. Generalize the expression as in `(∑ x, ∑ y ∈ univ.filter (fun y => x < y), j x * j y) = T`.

Generalize the expression as in `(∑ x, j x ^ 2) = Q`. Generalize the expression as in `2 * (∑ x, j x) * n0 = R`. Use linear arithmetic over natural numbers and integers. Establish `h1r : ((n0:ℝ) + 2 * ∑ x, (j x : ℝ)) ^ 2 = (n0:ℝ) ^ 2 + 2 * (∑ x, (j x : ℝ) ^ 2) + 2 * (dimN j n0 : ℝ)` using `by exact_mod_cast h1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem dimension_identity : DimIdentity := by
  intro a j n0
  have hsq := sq_sum_fin j
  have hd : dimN j n0 = 4 * (∑ x, ∑ y ∈ univ.filter (fun y => x < y), j x * j y)
      + (∑ x, j x ^ 2) + 2 * (∑ x, j x) * n0 := by
    unfold dimN
    have e1 : (∑ x, ∑ y ∈ univ.filter (fun y => x < y), 2 * j x * j y)
        = 2 * ∑ x, ∑ y ∈ univ.filter (fun y => x < y), j x * j y := by
      simp_rw [mul_assoc, ← Finset.mul_sum]
    have e2 : (∑ x, 2 * j x * n0) = 2 * (∑ x, j x) * n0 := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [e1, e2]; ring
  have h1 : (n0 + 2 * ∑ x, j x) ^ 2 = n0 ^ 2 + 2 * (∑ x, j x ^ 2) + 2 * dimN j n0 := by
    rw [hd]
    have : (n0 + 2 * ∑ x, j x) ^ 2 = n0 ^ 2 + 4 * n0 * (∑ x, j x) + 4 * (∑ x, j x) ^ 2 := by ring
    rw [this, hsq]; ring
  refine ⟨h1, ?_, ?_⟩
  · rw [hd]
    have : 2 * (∑ x, j x) * (n0 + 2 * ∑ x, j x) = 2 * (∑ x, j x) * n0 + 4 * (∑ x, j x) ^ 2 := by ring
    rw [this, hsq]
    generalize (∑ x, ∑ y ∈ univ.filter (fun y => x < y), j x * j y) = T
    generalize (∑ x, j x ^ 2) = Q
    generalize 2 * (∑ x, j x) * n0 = R
    omega
  · have h1r : ((n0:ℝ) + 2 * ∑ x, (j x : ℝ)) ^ 2
        = (n0:ℝ) ^ 2 + 2 * (∑ x, (j x : ℝ) ^ 2) + 2 * (dimN j n0 : ℝ) := by exact_mod_cast h1
    linarith

/- English proof (translation)
Establish `e : ∀ k, inner ℂ x (v k) * inner ℂ (v k) x = ((‖inner ℂ x (v k)‖ ^ 2 : ℝ) : ℂ)`. Introduce `k`. Rewrite using `[← inner_conj_symm (v k) x, Complex.mul_conj']`. Use `push_cast`. Both sides reduce to the same expression.

Establish `h1 : (∫ k, ((‖inner ℂ x (v k)‖ ^ 2 : ℝ) : ℂ) ∂μ) = ((‖x‖ ^ 2 : ℝ) : ℂ)`. Use `hres x x` as an intermediate fact. Simplify using `only [e] at this`. Rewrite using `[this, inner_self_eq_norm_sq_to_K]`. Use `push_cast`.

Both sides reduce to the same expression. Establish `hint : Integrable (fun k => ‖inner ℂ x (v k)‖ ^ 2) μ`. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules.

Assume the negation of the conclusion as `hn`. Establish `h2 : ¬ Integrable (fun k => ((‖inner ℂ x (v k)‖ ^ 2 : ℝ) : ℂ)) μ` using `fun hi => hn (by`. Establish `h4` using `hi.re`. Simplify `h4)` using `[← Complex.ofReal_pow]`. Establish `h3` using `integral_undef h2`.

Rewrite `h3` using `[h1]`. Establish `: ‖x‖ ^ 2 = 0` using `by exact_mod_cast h3`. Conclude with `hx (by simpa using this)`. Use `⟨hint, ?_⟩` and prove the remaining obligations. Rewrite `h1` using `[integral_complex_ofReal]`.

Conclude with `h1` after adjusting the coercions.
-/
lemma resolution_sq {Ω T : Type} [MeasurableSpace Ω] (μ : Measure Ω) [NormedAddCommGroup T]
    [InnerProductSpace ℂ T] (v : Ω → T)
    (hres : ∀ x y : T, (∫ k, inner ℂ x (v k) * inner ℂ (v k) y ∂μ) = inner ℂ x y) (x : T) :
    Integrable (fun k => ‖inner ℂ x (v k)‖ ^ 2) μ ∧ (∫ k, ‖inner ℂ x (v k)‖ ^ 2 ∂μ) = ‖x‖ ^ 2 := by
  have e : ∀ k, inner ℂ x (v k) * inner ℂ (v k) x = ((‖inner ℂ x (v k)‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [← inner_conj_symm (v k) x, Complex.mul_conj']; push_cast; rfl
  have h1 : (∫ k, ((‖inner ℂ x (v k)‖ ^ 2 : ℝ) : ℂ) ∂μ) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    have := hres x x
    simp only [e] at this
    rw [this, inner_self_eq_norm_sq_to_K]; push_cast; rfl
  have hint : Integrable (fun k => ‖inner ℂ x (v k)‖ ^ 2) μ := by
    by_cases hx : x = 0
    · subst hx; simp
    by_contra hn
    have h2 : ¬ Integrable (fun k => ((‖inner ℂ x (v k)‖ ^ 2 : ℝ) : ℂ)) μ := fun hi => hn (by
      have h4 := hi.re
      simpa [← Complex.ofReal_pow] using h4)
    have h3 := integral_undef h2
    rw [h1] at h3
    have : ‖x‖ ^ 2 = 0 := by exact_mod_cast h3
    exact hx (by simpa using this)
  refine ⟨hint, ?_⟩
  rw [integral_complex_ofReal] at h1
  exact_mod_cast h1

/- English proof (translation)
Introduce `Ω T _ μ _ _ v c M A hM hres hc hA`. Establish `key : ∀ (x y : T) (t : ℝ), 0 < t → ‖inner ℂ x (A y)‖ ≤ M * ((t * ‖x‖ ^ 2 + ‖y‖ ^ 2 / t) / 2)`. Introduce `x y t ht`. Take `⟨ix, ex⟩` from `resolution_sq μ v hres x`. Take `⟨iy, ey⟩` from `resolution_sq μ v hres y`.

Rewrite using `[hA x y]`. Establish `hg : Integrable (fun k => M * ((t * ‖inner ℂ x (v k)‖ ^ 2 + ‖inner ℂ y (v k)‖ ^ 2 / t) / 2)) μ` using `(((ix.const_mul t).add (iy.div_const t)).div_const 2).const_mul M`. Use `(norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun k => ?_)).trans ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_inner_symm (v k) y] set p := ‖inner ℂ x (v k)‖ set q := ‖inner ℂ y (v k)‖`. Establish `hp : 0 ≤ p` using `norm_nonneg _`.

Establish `hq : 0 ≤ q` using `norm_nonneg _`. Establish `h1 : p * q ≤ (t * p ^ 2 + q ^ 2 / t) / 2`. Establish `h0 : 0 ≤ (t * p - q) ^ 2 / t` using `by positivity`. Establish `e : (t * p - q) ^ 2 / t = t * p ^ 2 - 2 * (p * q) + q ^ 2 / t` using `by field_simp; ring`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `mul_le_mul (hc k) h1 (by positivity) hM`. Apply `le_of_eq` to reduce the goal to its premises. Rewrite using `[integral_const_mul, integral_div, integral_add (ix.const_mul t) (iy.div_const t), integral_const_mul, integral_div, ex, ey]`. Apply `ContinuousLinearMap.opNorm_le_bound _ hM` to reduce the goal to its premises. Introduce `y`.

Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality. Simplify using the standard rewrite rules. Distinguish the cases in `hAy : A y = 0`. Rewrite using `[hAy, norm_zero]`.

Check the signs of the components of the expression. Establish `ha : 0 < ‖A y‖` using `norm_pos_iff.mpr hAy`. Establish `hb : 0 < ‖y‖` using `norm_pos_iff.mpr hy`. Establish `h` using `key (A y) y (‖y‖ / ‖A y‖) (by positivity)`. Rewrite `h` using `[inner_self_eq_norm_sq_to_K]`.

Establish `e1 : ‖((‖A y‖ : ℂ)) ^ 2‖ = ‖A y‖ ^ 2`. Rewrite using `[norm_pow, Complex.norm_real, norm_norm]`. Establish `e2 : (‖y‖ / ‖A y‖ * ‖A y‖ ^ 2 + ‖y‖ ^ 2 / (‖y‖ / ‖A y‖)) / 2 = ‖A y‖ * ‖y‖` using `by field_simp; ring`. Use `erw [e1] at h`. Rewrite `h` using `[e2]`.

Establish `: ‖A y‖ * ‖A y‖ ≤ ‖A y‖ * (M * ‖y‖)` using `by nlinarith`. Conclude with `le_of_mul_le_mul_left this ha`.
-/
theorem resolution_norm_bound : ResolutionNorm := by
  intro Ω T _ μ _ _ v c M A hM hres hc hA
  have key : ∀ (x y : T) (t : ℝ), 0 < t →
      ‖inner ℂ x (A y)‖ ≤ M * ((t * ‖x‖ ^ 2 + ‖y‖ ^ 2 / t) / 2) := by
    intro x y t ht
    obtain ⟨ix, ex⟩ := resolution_sq μ v hres x
    obtain ⟨iy, ey⟩ := resolution_sq μ v hres y
    rw [hA x y]
    have hg : Integrable (fun k => M * ((t * ‖inner ℂ x (v k)‖ ^ 2 + ‖inner ℂ y (v k)‖ ^ 2 / t) / 2)) μ :=
      (((ix.const_mul t).add (iy.div_const t)).div_const 2).const_mul M
    refine (norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun k => ?_)).trans ?_
    · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_inner_symm (v k) y]
      set p := ‖inner ℂ x (v k)‖
      set q := ‖inner ℂ y (v k)‖
      have hp : 0 ≤ p := norm_nonneg _
      have hq : 0 ≤ q := norm_nonneg _
      have h1 : p * q ≤ (t * p ^ 2 + q ^ 2 / t) / 2 := by
        have h0 : 0 ≤ (t * p - q) ^ 2 / t := by positivity
        have e : (t * p - q) ^ 2 / t = t * p ^ 2 - 2 * (p * q) + q ^ 2 / t := by
          field_simp; ring
        linarith
      exact mul_le_mul (hc k) h1 (by positivity) hM
    · apply le_of_eq
      rw [integral_const_mul, integral_div, integral_add (ix.const_mul t) (iy.div_const t),
        integral_const_mul, integral_div, ex, ey]
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro y
  by_cases hy : y = 0
  · subst hy; simp
  by_cases hAy : A y = 0
  · rw [hAy, norm_zero]; positivity
  have ha : 0 < ‖A y‖ := norm_pos_iff.mpr hAy
  have hb : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have h := key (A y) y (‖y‖ / ‖A y‖) (by positivity)
  rw [inner_self_eq_norm_sq_to_K] at h
  have e1 : ‖((‖A y‖ : ℂ)) ^ 2‖ = ‖A y‖ ^ 2 := by
    rw [norm_pow, Complex.norm_real, norm_norm]
  have e2 : (‖y‖ / ‖A y‖ * ‖A y‖ ^ 2 + ‖y‖ ^ 2 / (‖y‖ / ‖A y‖)) / 2 = ‖A y‖ * ‖y‖ := by
    field_simp; ring
  erw [e1] at h
  rw [e2] at h
  have : ‖A y‖ * ‖A y‖ ≤ ‖A y‖ * (M * ‖y‖) := by nlinarith
  exact le_of_mul_le_mul_left this ha

/- English proof (translation)
Introduce `G _ e he x`. Establish `h1 : 0 ≤ e 1`. Use `he {1} (fun _ => 1)` as an intermediate fact. Simplify using `using this`. Establish `h1re : 0 ≤ (e 1).re` using `(Complex.le_def.mp h1).1`.

Establish `h1im : (e 1).im = 0` using `((Complex.le_def.mp h1).2).symm`. Distinguish the cases in `hx : x = 1`. Substitute `hx` using the available equality. Rewrite using `[← Complex.re_add_im (e 1), h1im]`. Simplify using `[abs_of_nonneg h1re]`.

Establish `hpair : ∀ t : ℂ, 0 ≤ e 1 + t * e x + star t * e x⁻¹ + star t * t * e 1`. Introduce `t`. Use `he {1, x} (fun y => if y = 1 then 1 else t)` as an intermediate fact. Rewrite `this` using `[Finset.sum_pair (Ne.symm hx), Finset.sum_pair (Ne.symm hx), Finset.sum_pair (Ne.symm hx)]`. Simplify using `only [if_true, if_neg hx, inv_one, one_mul, mul_one, star_one, inv_mul_cancel] at this`.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `ha` using `hpair 1`. Establish `hb` using `hpair Complex.I`. Rewrite `ha`, `hb` using `[Complex.le_def]`.

Simplify using `only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, star_one, Complex.star_def, Complex.conj_I, Complex.neg_re, Complex.neg_im] at ha hb`. Establish `him : (e x⁻¹).im = -(e x).im` using `by linarith [ha.2]`. Establish `hre : (e x⁻¹).re = (e x).re` using `by linarith [hb.2]`. Distinguish the cases in `h0 : e x = 0`. Rewrite using `[h0, norm_zero]`.

Conclude with `h1re`. Establish `hn : 0 < ‖e x‖` using `norm_pos_iff.mpr h0`. Establish `hc` using `hpair (-(star (e x)) / (‖e x‖ : ℂ))`. Rewrite `hc` using `[Complex.le_def]`. Establish `hsq : (e x).re * (e x).re + (e x).im * (e x).im = ‖e x‖ * ‖e x‖`.

Rewrite using `[← Complex.normSq_apply, Complex.normSq_eq_norm_sq]`. Expand and normalize the polynomial expressions, which then agree. Establish `hinv : e x⁻¹ = star (e x)`. Apply the tactic sequence `apply Complex.ext <;> simp [hre, him]`. Establish `hval : e 1 + (-(star (e x)) / (‖e x‖ : ℂ)) * e x + star (-(star (e x)) / (‖e x‖ : ℂ)) * e x⁻¹ + star (-(star (e x)) / (‖e x‖ : ℂ)) * (-(star (e x)) / (‖e x‖ : ℂ)) * e 1 = 2 * e 1 - 2 * (‖e x‖ : ℂ)`.

Establish `hne : (‖e x‖ : ℂ) ≠ 0` using `by exact_mod_cast hn.ne'`. Establish `hm : star (e x) * e x = (‖e x‖ : ℂ) * (‖e x‖ : ℂ)`. Rewrite using `[Complex.star_def, Complex.conj_mul']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hinv]`.

Simplify using `only [star_div₀, star_neg, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]`. Simplify using `only [Complex.star_def] at hm`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(-2 * (‖e x‖ : ℂ) + e 1) * hm`. Rewrite `hc` using `[hval]`.

Use `hc.1` as an intermediate fact. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem positive_type_bound : PosTypeBound := by
  classical
  intro G _ e he x
  have h1 : 0 ≤ e 1 := by
    have := he {1} (fun _ => 1)
    simpa using this
  have h1re : 0 ≤ (e 1).re := (Complex.le_def.mp h1).1
  have h1im : (e 1).im = 0 := ((Complex.le_def.mp h1).2).symm
  by_cases hx : x = 1
  · subst hx
    rw [← Complex.re_add_im (e 1), h1im]
    simp [abs_of_nonneg h1re]
  have hpair : ∀ t : ℂ, 0 ≤ e 1 + t * e x + star t * e x⁻¹ + star t * t * e 1 := by
    intro t
    have := he {1, x} (fun y => if y = 1 then 1 else t)
    rw [Finset.sum_pair (Ne.symm hx), Finset.sum_pair (Ne.symm hx), Finset.sum_pair (Ne.symm hx)] at this
    simp only [if_true, if_neg hx, inv_one, one_mul, mul_one, star_one, inv_mul_cancel] at this
    convert this using 1
    ring
  have ha := hpair 1
  have hb := hpair Complex.I
  rw [Complex.le_def] at ha hb
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.zero_re,
    Complex.zero_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, star_one,
    Complex.star_def, Complex.conj_I, Complex.neg_re, Complex.neg_im] at ha hb
  have him : (e x⁻¹).im = -(e x).im := by linarith [ha.2]
  have hre : (e x⁻¹).re = (e x).re := by linarith [hb.2]
  by_cases h0 : e x = 0
  · rw [h0, norm_zero]; exact h1re
  have hn : 0 < ‖e x‖ := norm_pos_iff.mpr h0
  have hc := hpair (-(star (e x)) / (‖e x‖ : ℂ))
  rw [Complex.le_def] at hc
  have hsq : (e x).re * (e x).re + (e x).im * (e x).im = ‖e x‖ * ‖e x‖ := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq]; ring
  have hinv : e x⁻¹ = star (e x) := by
    apply Complex.ext <;> simp [hre, him]
  have hval : e 1 + (-(star (e x)) / (‖e x‖ : ℂ)) * e x
      + star (-(star (e x)) / (‖e x‖ : ℂ)) * e x⁻¹
      + star (-(star (e x)) / (‖e x‖ : ℂ)) * (-(star (e x)) / (‖e x‖ : ℂ)) * e 1
      = 2 * e 1 - 2 * (‖e x‖ : ℂ) := by
    have hne : (‖e x‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hm : star (e x) * e x = (‖e x‖ : ℂ) * (‖e x‖ : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']; ring
    rw [hinv]
    simp only [star_div₀, star_neg, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    simp only [Complex.star_def] at hm
    field_simp
    linear_combination (-2 * (‖e x‖ : ℂ) + e 1) * hm
  rw [hval] at hc
  have := hc.1
  simp at this
  linarith

/- English proof (translation)
Introduce `G H₁ H₂ _ _ _ _ _ _ _ U₁ U₂ hU₁ hU₂ v₁ v₂ hcoef hcyc`. Establish `hin₁ : ∀ g x y, inner ℂ (U₁ g x) (U₁ g y) = inner ℂ x y` using `fun g x y => (LinearIsometry.mk (U₁ g).toLinearMap (hU₁ g)).inner_map_map x y`. Establish `hin₂ : ∀ g x y, inner ℂ (U₂ g x) (U₂ g y) = inner ℂ x y` using `fun g x y => (LinearIsometry.mk (U₂ g).toLinearMap (hU₂ g)).inner_map_map x y`. Establish `hmul₁ : ∀ g h x, U₁ (g * h) x = U₁ g (U₁ h x)`. Introduce `g h x`.

Rewrite using `[map_mul]`. Both sides reduce to the same expression. Establish `hmul₂ : ∀ g h x, U₂ (g * h) x = U₂ g (U₂ h x)`. Introduce `g h x`. Rewrite using `[map_mul]`.

Both sides reduce to the same expression. Establish `hpair₁ : ∀ g h, inner ℂ (U₁ g v₁) (U₁ h v₁) = inner ℂ v₁ (U₁ (g⁻¹ * h) v₁)`. Introduce `g h`. Establish `: U₁ h v₁ = U₁ g (U₁ (g⁻¹ * h) v₁)`. Rewrite using `[← hmul₁]`.

Simplify using the standard rewrite rules. Rewrite using `[this, hin₁]`. Establish `hpair₂ : ∀ g h, inner ℂ (U₂ g v₂) (U₂ h v₂) = inner ℂ v₂ (U₂ (g⁻¹ * h) v₂)`. Introduce `g h`. Establish `: U₂ h v₂ = U₂ g (U₂ (g⁻¹ * h) v₂)`.

Rewrite using `[← hmul₂]`. Simplify using the standard rewrite rules. Rewrite using `[this, hin₂]`. Use `set T₁ : (G →₀ ℂ) →ₗ[ℂ] H₁ := Finsupp.linearCombination ℂ (fun g => U₁ g v₁) with hT₁`. Use `set T₂ : (G →₀ ℂ) →ₗ[ℂ] H₂ := Finsupp.linearCombination ℂ (fun g => U₂ g v₂) with hT₂`.

Establish `hinner : ∀ c d, inner ℂ (T₁ c) (T₁ d) = inner ℂ (T₂ c) (T₂ d)`. Introduce `c d`. Simplify using `only [hT₁, hT₂, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hpair₁, hpair₂, hcoef]`. Establish `hnorm : ∀ c, ‖T₁ c‖ = ‖T₂ c‖`. Introduce `c`.

Use `hinner c c` as an intermediate fact. Rewrite `this` using `[inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]`. Establish `h2 : ‖T₁ c‖ ^ 2 = ‖T₂ c‖ ^ 2` using `by exact_mod_cast this`. Conclude with `(sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2`. Establish `hr₂ : LinearMap.range T₂ = Submodule.span ℂ (Set.range fun g => U₂ g v₂)` using `Finsupp.range_linearCombination _`.

Establish `hr₁ : LinearMap.range T₁ = Submodule.span ℂ (Set.range fun g => U₁ g v₁)` using `Finsupp.range_linearCombination _`. Establish `hdense : DenseRange T₂`. Use `(Submodule.dense_iff_topologicalClosure_eq_top).mpr hcyc` as an intermediate fact. Rewrite `this` using `[← hr₂]`. Conclude with `this`.

Establish `hbd : ∃ C : ℝ, ∀ x, ‖T₁ x‖ ≤ C * ‖T₂ x‖` using `⟨1, fun x => by rw [hnorm, one_mul]⟩`. Use `set J0 := T₁.extendOfNorm T₂ with hJ0def`. Establish `hJ0 : ∀ c, J0 (T₂ c) = T₁ c` using `fun c => LinearMap.extendOfNorm_eq hdense hbd c`. Establish `hJnorm : ∀ x, ‖J0 x‖ = ‖x‖`. Use `hdense.induction ?_ (isClosed_eq (by fun_prop) continuous_norm)` and prove the remaining obligations.

Introduce and unpack `_ ⟨c, rfl⟩`. Rewrite using `[hJ0, hnorm]`. Establish `hs₁ : ∀ g (a : ℂ), T₁ (Finsupp.single g a) = a • U₁ g v₁`. Introduce `g a`. Simplify using `[hT₁]`.

Establish `hs₂ : ∀ g (a : ℂ), T₂ (Finsupp.single g a) = a • U₂ g v₂`. Introduce `g a`. Simplify using `[hT₂]`. Establish `horb : ∀ g, J0 (U₂ g v₂) = U₁ g v₁`. Introduce `g`.

Use `hJ0 (Finsupp.single g 1)` as an intermediate fact. Rewrite `this` using `[hs₁, hs₂, one_smul, one_smul]`. Then use the resulting hypothesis. Use `⟨⟨J0.toLinearMap, hJnorm⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `horb 1` as an intermediate fact. Simplify using `using this`.

Introduce `g show ∀ x, J0 (U₂ g x) = U₁ g (J0 x)`. Use `hdense.induction ?_ (isClosed_eq (by fun_prop) (by fun_prop))` and prove the remaining obligations. Introduce and unpack `_ ⟨c, rfl⟩`. Proceed by induction on `c using Finsupp.induction_linear with`. Consider the case `zero => simp`.

Consider the case `add c d hc hd => simp only [map_add, hc, hd]`. Consider the case `single h a`. Rewrite using `[hs₂, map_smul, map_smul, map_smul, map_smul, ← hmul₂, horb, horb, hmul₁]`. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, rfl⟩ show J0 x ∈ _ revert x`.

Use `hdense.induction ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨c, rfl⟩`. Rewrite using `[hJ0]`. Apply `Submodule.le_topologicalClosure` to reduce the goal to its premises. Rewrite using `[← hr₁]`.

Conclude with `LinearMap.mem_range_self _ _`. Conclude with `(Submodule.isClosed_topologicalClosure _).preimage J0.continuous`. Establish `hcl : IsClosed ((LinearMap.range J0.toLinearMap : Submodule ℂ H₁) : Set H₁)`. Apply the tactic sequence `have hiso : Isometry J0 := AddMonoidHomClass.isometry_of_norm J0 hJnorm`. Conclude with `hiso.isClosedEmbedding.isClosed_range`.

Establish `hle : Submodule.span ℂ (Set.range fun g => U₁ g v₁) ≤ LinearMap.range J0.toLinearMap`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `⟨U₂ g v₂, horb g⟩`. Introduce `y hy`.

Take `⟨x, hx⟩` from `Submodule.topologicalClosure_minimal _ hle hcl hy`. Conclude with `⟨x, hx⟩`.
-/
theorem coefficient_isometry : CoeffIso := by
  intro G H₁ H₂ _ _ _ _ _ _ _ U₁ U₂ hU₁ hU₂ v₁ v₂ hcoef hcyc
  have hin₁ : ∀ g x y, inner ℂ (U₁ g x) (U₁ g y) = inner ℂ x y := fun g x y =>
    (LinearIsometry.mk (U₁ g).toLinearMap (hU₁ g)).inner_map_map x y
  have hin₂ : ∀ g x y, inner ℂ (U₂ g x) (U₂ g y) = inner ℂ x y := fun g x y =>
    (LinearIsometry.mk (U₂ g).toLinearMap (hU₂ g)).inner_map_map x y
  have hmul₁ : ∀ g h x, U₁ (g * h) x = U₁ g (U₁ h x) := by
    intro g h x; rw [map_mul]; rfl
  have hmul₂ : ∀ g h x, U₂ (g * h) x = U₂ g (U₂ h x) := by
    intro g h x; rw [map_mul]; rfl
  have hpair₁ : ∀ g h, inner ℂ (U₁ g v₁) (U₁ h v₁) = inner ℂ v₁ (U₁ (g⁻¹ * h) v₁) := by
    intro g h
    have : U₁ h v₁ = U₁ g (U₁ (g⁻¹ * h) v₁) := by
      rw [← hmul₁]; simp
    rw [this, hin₁]
  have hpair₂ : ∀ g h, inner ℂ (U₂ g v₂) (U₂ h v₂) = inner ℂ v₂ (U₂ (g⁻¹ * h) v₂) := by
    intro g h
    have : U₂ h v₂ = U₂ g (U₂ (g⁻¹ * h) v₂) := by
      rw [← hmul₂]; simp
    rw [this, hin₂]
  set T₁ : (G →₀ ℂ) →ₗ[ℂ] H₁ := Finsupp.linearCombination ℂ (fun g => U₁ g v₁) with hT₁
  set T₂ : (G →₀ ℂ) →ₗ[ℂ] H₂ := Finsupp.linearCombination ℂ (fun g => U₂ g v₂) with hT₂
  have hinner : ∀ c d, inner ℂ (T₁ c) (T₁ d) = inner ℂ (T₂ c) (T₂ d) := by
    intro c d
    simp only [hT₁, hT₂, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, hpair₁, hpair₂, hcoef]
  have hnorm : ∀ c, ‖T₁ c‖ = ‖T₂ c‖ := by
    intro c
    have := hinner c c
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at this
    have h2 : ‖T₁ c‖ ^ 2 = ‖T₂ c‖ ^ 2 := by exact_mod_cast this
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2
  have hr₂ : LinearMap.range T₂ = Submodule.span ℂ (Set.range fun g => U₂ g v₂) :=
    Finsupp.range_linearCombination _
  have hr₁ : LinearMap.range T₁ = Submodule.span ℂ (Set.range fun g => U₁ g v₁) :=
    Finsupp.range_linearCombination _
  have hdense : DenseRange T₂ := by
    have := (Submodule.dense_iff_topologicalClosure_eq_top).mpr hcyc
    rw [← hr₂] at this
    exact this
  have hbd : ∃ C : ℝ, ∀ x, ‖T₁ x‖ ≤ C * ‖T₂ x‖ := ⟨1, fun x => by rw [hnorm, one_mul]⟩
  set J0 := T₁.extendOfNorm T₂ with hJ0def
  have hJ0 : ∀ c, J0 (T₂ c) = T₁ c := fun c => LinearMap.extendOfNorm_eq hdense hbd c
  have hJnorm : ∀ x, ‖J0 x‖ = ‖x‖ := by
    refine hdense.induction ?_ (isClosed_eq (by fun_prop) continuous_norm)
    rintro _ ⟨c, rfl⟩
    rw [hJ0, hnorm]
  have hs₁ : ∀ g (a : ℂ), T₁ (Finsupp.single g a) = a • U₁ g v₁ := by
    intro g a; simp [hT₁]
  have hs₂ : ∀ g (a : ℂ), T₂ (Finsupp.single g a) = a • U₂ g v₂ := by
    intro g a; simp [hT₂]
  have horb : ∀ g, J0 (U₂ g v₂) = U₁ g v₁ := by
    intro g
    have := hJ0 (Finsupp.single g 1)
    rwa [hs₁, hs₂, one_smul, one_smul] at this
  refine ⟨⟨J0.toLinearMap, hJnorm⟩, ?_, ?_, ?_⟩
  · have := horb 1
    simpa using this
  · intro g
    show ∀ x, J0 (U₂ g x) = U₁ g (J0 x)
    refine hdense.induction ?_ (isClosed_eq (by fun_prop) (by fun_prop))
    rintro _ ⟨c, rfl⟩
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | single h a =>
      rw [hs₂, map_smul, map_smul, map_smul, map_smul, ← hmul₂, horb, horb, hmul₁]
  · apply Set.Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      show J0 x ∈ _
      revert x
      refine hdense.induction ?_ ?_
      · rintro _ ⟨c, rfl⟩
        rw [hJ0]
        apply Submodule.le_topologicalClosure
        rw [← hr₁]
        exact LinearMap.mem_range_self _ _
      · exact (Submodule.isClosed_topologicalClosure _).preimage J0.continuous
    · have hcl : IsClosed ((LinearMap.range J0.toLinearMap : Submodule ℂ H₁) : Set H₁) := by
        have hiso : Isometry J0 := AddMonoidHomClass.isometry_of_norm J0 hJnorm
        exact hiso.isClosedEmbedding.isClosed_range
      have hle : Submodule.span ℂ (Set.range fun g => U₁ g v₁) ≤ LinearMap.range J0.toLinearMap := by
        rw [Submodule.span_le]
        rintro _ ⟨g, rfl⟩
        exact ⟨U₂ g v₂, horb g⟩
      intro y hy
      obtain ⟨x, hx⟩ := Submodule.topologicalClosure_minimal _ hle hcl hy
      exact ⟨x, hx⟩

/- English proof (translation)
Introduce `X ι _ μ _ _ F c hF horth y`. Establish `hint : ∀ w w', Integrable (fun x => star (F w x) * F w' x) μ`. Introduce `w w'`. Conclude with `(hF w).star.integrable_mul (hF w')`. Establish `e : ∀ x, ((‖∑ w, c w * F w x‖ ^ 2 : ℝ) : ℂ) = ∑ w, ∑ w', star (c w) * c w' * (star (F w x) * F w' x)`.

Introduce `x`. Establish `: ((‖∑ w, c w * F w x‖ ^ 2 : ℝ) : ℂ) = star (∑ w, c w * F w x) * ∑ w, c w * F w x`. Rewrite using `[Complex.star_def, Complex.conj_mul']`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[this, star_sum, Finset.sum_mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `w _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `w' _`.

Rewrite using `[star_mul']`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : (∫ x, ((‖∑ w, c w * F w x‖ ^ 2 : ℝ) : ℂ) ∂μ) = ((∑ w, ‖c w‖ ^ 2 : ℝ) : ℂ)`. Repeatedly rewrite using `[e]`. Rewrite using `[integral_finsetSum _ (fun w _ => integrable_finsetSum _ (fun w' _ => (hint w w').const_mul _))]`.

Use `push_cast`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `w _`. Rewrite using `[integral_finsetSum _ (fun w' _ => (hint w w').const_mul _)]`. Repeatedly rewrite using `[integral_const_mul, horth]`.

Simplify using `only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[Complex.star_def, Complex.conj_mul']`. Rewrite `h1` using `[integral_complex_ofReal]`. Establish `h2 : (∫ x, ‖∑ w, c w * F w x‖ ^ 2 ∂μ) = ∑ w, ‖c w‖ ^ 2` using `by exact_mod_cast h1`. Rewrite using `[h2]`.

Combine the equalities or inequalities in the displayed calculation. Use `(norm_sum_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Repeatedly rewrite using `[norm_mul]`. Use `_ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _`.
-/
theorem kernel_bound_bis : KernelBound := by
  intro X ι _ μ _ _ F c hF horth y
  have hint : ∀ w w', Integrable (fun x => star (F w x) * F w' x) μ := by
    intro w w'
    exact (hF w).star.integrable_mul (hF w')
  have e : ∀ x, ((‖∑ w, c w * F w x‖ ^ 2 : ℝ) : ℂ)
      = ∑ w, ∑ w', star (c w) * c w' * (star (F w x) * F w' x) := by
    intro x
    have : ((‖∑ w, c w * F w x‖ ^ 2 : ℝ) : ℂ) = star (∑ w, c w * F w x) * ∑ w, c w * F w x := by
      rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
    rw [this, star_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro w _
    apply Finset.sum_congr rfl; intro w' _
    rw [star_mul']; ring
  have h1 : (∫ x, ((‖∑ w, c w * F w x‖ ^ 2 : ℝ) : ℂ) ∂μ) = ((∑ w, ‖c w‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [e]
    rw [integral_finsetSum _ (fun w _ => integrable_finsetSum _ (fun w' _ => (hint w w').const_mul _))]
    push_cast
    apply Finset.sum_congr rfl; intro w _
    rw [integral_finsetSum _ (fun w' _ => (hint w w').const_mul _)]
    simp_rw [integral_const_mul, horth]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Complex.star_def, Complex.conj_mul']
  rw [integral_complex_ofReal] at h1
  have h2 : (∫ x, ‖∑ w, c w * F w x‖ ^ 2 ∂μ) = ∑ w, ‖c w‖ ^ 2 := by exact_mod_cast h1
  rw [h2]
  calc ‖∑ w, c w * F w y‖ ^ 2 ≤ (∑ w, ‖c w‖ * ‖F w y‖) ^ 2 := by
        gcongr
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp_rw [norm_mul]
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

noncomputable def farW (h ε : ℝ) : ℕ → ℝ
  | 0 => 1
  | (k+1) => Real.exp (-(h / 8 * (ε * (2 ^ k * ε))))

noncomputable def farA (B h ε : ℝ) (i : ℕ) : ℝ := Real.exp (B * (2 ^ i * ε)) * farW h ε i

/- English proof (translation)
Consider the cases of `i with`. Consider the case `zero => exact zero_le_one`. Consider the case `succ k => exact (Real.exp_pos _).le`.
-/
lemma farW_nonneg (h ε : ℝ) (i : ℕ) : 0 ≤ farW h ε i := by
  cases i with
  | zero => exact zero_le_one
  | succ k => exact (Real.exp_pos _).le

/- English proof (translation)
The claim follows from `mul_nonneg (Real.exp_pos _).le (farW_nonneg _ _ _)`.
-/
lemma farA_nonneg (B h ε : ℝ) (i : ℕ) : 0 ≤ farA B h ε i :=
  mul_nonneg (Real.exp_pos _).le (farW_nonneg _ _ _)

/- English proof (translation)
Unfold `farA farW`. Rewrite using `[mul_one, pow_zero, one_mul]`. Establish `h1 : Real.exp (B * ε) ≤ Real.exp 1` using `Real.exp_le_exp.mpr hBε`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma farA_zero_le {B h ε : ℝ} (hBε : B * ε ≤ 1) : farA B h ε 0 ≤ 3 := by
  unfold farA farW
  rw [mul_one, pow_zero, one_mul]
  have h1 : Real.exp (B * ε) ≤ Real.exp 1 := Real.exp_le_exp.mpr hBε
  have := Real.exp_one_lt_d9
  linarith

/- English proof (translation)
Rewrite using `[Real.exp_neg, inv_eq_one_div]`. Apply `div_le_div_of_nonneg_left (by norm_num) (by norm_num)` to reduce the goal to its premises. Use `Real.add_one_le_exp (1:ℝ)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma exp_neg_one_le_half : Real.exp (-1) ≤ 1 / 2 := by
  rw [Real.exp_neg, inv_eq_one_div]
  apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
  have := Real.add_one_le_exp (1:ℝ); linarith

/- English proof (translation)
Establish `h1 : Real.exp (-(h * ε ^ 2 / 16)) * Real.exp (-1) ^ k ≤ Real.exp (-(h * ε ^ 2 / 16)) * (1 / 2) ^ k`. Use `exp_neg_one_le_half` as an intermediate fact. Establish `h0` using `(Real.exp_pos (-1)).le`. Use `gcongr`. Use `le_trans ?_ h1` and prove the remaining obligations.

Unfold `farA farW`. Rewrite using `[← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `hP : (k:ℝ) + 1 ≤ 2 ^ k` using `by exact_mod_cast Nat.lt_two_pow_self (n := k)`. Establish `hB : 2 * (B * ε) ≤ h * ε ^ 2 / 16` using `by nlinarith`.

Establish `e : B * (2 ^ (k+1) * ε) + -(h / 8 * (ε * (2 ^ k * ε))) = 2 ^ k * (2 * (B * ε) - 2 * (h * ε ^ 2 / 16))` using `by ring`. Rewrite using `[e]`. Establish `hT : 1 ≤ h * ε ^ 2 / 16` using `by linarith`. Generalize the expression as in `h * ε ^ 2 / 16 = T at *`. Establish `hk0 : (0:ℝ) ≤ k` using `Nat.cast_nonneg _`.

Establish `h2 : (2:ℝ) ^ k * (2 * (B * ε) - 2 * T) ≤ 2 ^ k * (-T)`. Apply `mul_le_mul_of_nonneg_left (by linarith) (by positivity)` to reduce the goal to its premises. Establish `h3 : ((k:ℝ) + 1) * T ≤ 2 ^ k * T` using `by gcongr`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma farA_succ_le {B h ε : ℝ} (hε : 0 < ε) (h32 : 32 * B ≤ h * ε) (h16 : 16 ≤ h * ε ^ 2) (k : ℕ) :
    farA B h ε (k+1) ≤ Real.exp (-(h * ε ^ 2 / 16)) * (1 / 2) ^ k := by
  have h1 : Real.exp (-(h * ε ^ 2 / 16)) * Real.exp (-1) ^ k
      ≤ Real.exp (-(h * ε ^ 2 / 16)) * (1 / 2) ^ k := by
    have := exp_neg_one_le_half
    have h0 := (Real.exp_pos (-1)).le
    gcongr
  refine le_trans ?_ h1
  unfold farA farW
  rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hP : (k:ℝ) + 1 ≤ 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self (n := k)
  have hB : 2 * (B * ε) ≤ h * ε ^ 2 / 16 := by nlinarith
  have e : B * (2 ^ (k+1) * ε) + -(h / 8 * (ε * (2 ^ k * ε)))
      = 2 ^ k * (2 * (B * ε) - 2 * (h * ε ^ 2 / 16)) := by ring
  rw [e]
  have hT : 1 ≤ h * ε ^ 2 / 16 := by linarith
  generalize h * ε ^ 2 / 16 = T at *
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
  have h2 : (2:ℝ) ^ k * (2 * (B * ε) - 2 * T) ≤ 2 ^ k * (-T) := by
    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h3 : ((k:ℝ) + 1) * T ≤ 2 ^ k * T := by gcongr
  nlinarith

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Conclude with `sum_geometric_two_le m`. Use `_ = _ := by ring`.
-/
lemma farA_sum_succ {B h ε : ℝ} (hε : 0 < ε) (h32 : 32 * B ≤ h * ε) (h16 : 16 ≤ h * ε ^ 2) (m : ℕ) :
    ∑ k ∈ range m, farA B h ε (k+1) ≤ 2 * Real.exp (-(h * ε ^ 2 / 16)) := by
  calc ∑ k ∈ range m, farA B h ε (k+1)
      ≤ ∑ k ∈ range m, Real.exp (-(h * ε ^ 2 / 16)) * (1 / 2) ^ k :=
        Finset.sum_le_sum fun k _ => farA_succ_le hε h32 h16 k
    _ = Real.exp (-(h * ε ^ 2 / 16)) * ∑ k ∈ range m, (1 / 2 : ℝ) ^ k := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(h * ε ^ 2 / 16)) * 2 := by
        gcongr
        exact sum_geometric_two_le m
    _ = _ := by ring

open Classical in
/- English proof (translation)
Introduce `ι Γ _ _ S d A B h ε q hq hA hB hε hεq hBε h32 h16 hd0 hdε hcount`. Establish `hε2 : 0 < ε ^ 2` using `by positivity`. Establish `hh : 0 ≤ h`. Assume the negation of the conclusion as `hneg`. Use `push Not at hneg`.

Establish `: h * ε ^ 2 < 0` using `mul_neg_of_neg_of_pos hneg hε2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hex : ∀ x : ℝ, ∃ i : ℕ, x ≤ 2 ^ i * ε`. Introduce `x`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt (x / ε) (one_lt_two : (1:ℝ) < 2)`.

Conclude with `⟨n, by rw [div_lt_iff₀ hε] at hn; exact hn.le⟩`. Choose the witnesses or unpack the hypotheses as in `⟨idx, hidx1, hidx2⟩ : ∃ idx : ℝ → ℕ, (∀ x, x ≤ 2 ^ idx x * ε) ∧ (∀ x k, idx x = k + 1 → 2 ^ k * ε < x) := by`. Use `⟨fun x => Nat.find (hex x), fun x => Nat.find_spec (hex x), ?_⟩` and prove the remaining obligations. Introduce `x k hk`. Use `Nat.find_min (hex x) (m := k) (by simp only at hk; omega)` as an intermediate fact.

Conclude with `not_le.mp this`. Establish `hidx0 : ∀ x, ε < x → 1 ≤ idx x`. Introduce `x hx`. Assume the negation of the conclusion as `hc`. Establish `h0 : idx x = 0` using `by omega`.

Use `hidx1 x` as an intermediate fact. Rewrite `this` using `[h0]`. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hW : ∀ x, 0 ≤ x → Real.exp (-(decExp h q x)) ≤ farW h ε (idx x)`.

Introduce `x hx`. Break down `hk : idx x with _ | k` into its components or cases. Use `show _ ≤ (1:ℝ)`. Rewrite using `[Real.exp_le_one_iff]`. Establish `: 0 ≤ decExp h q x` using `mul_nonneg (by linarith) (le_min (sq_nonneg _) (div_nonneg hx (Real.sqrt_nonneg _)))`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `hidx2 x k hk show _ ≤ Real.exp (-(h / 8 * (ε * (2 ^ k * ε))))`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Apply `neg_le_neg` to reduce the goal to its premises. Establish `hεx : ε ≤ x`.

Establish `: (1:ℝ) ≤ 2 ^ k` using `one_le_pow₀ (by norm_num)`. Use the polynomial consequences of the given equalities and inequalities. Establish `h2` using `minimum_linear_form q ε x hq hε hεq hεx`. Unfold `decExp`. Combine the equalities or inequalities in the displayed calculation.

Establish `hw0 : ∀ γ, 0 ≤ ∏ v, Real.exp (-(decExp h q (d γ v)))` using `fun γ => Finset.prod_nonneg fun v _ => (Real.exp_pos _).le`. Establish `hwW : ∀ γ ∈ S, ∏ v, Real.exp (-(decExp h q (d γ v))) ≤ ∏ v, farW h ε (idx (d γ v))` using `fun γ hγ => Finset.prod_le_prod (fun v _ => (Real.exp_pos _).le) (fun v _ => hW _ (hd0 γ hγ v))`. Generalize the expression as in `hwdef : (fun γ => ∏ v, Real.exp (-(decExp h q (d γ v)))) = w at *`. Establish `hw0' : ∀ γ, 0 ≤ w γ` using `fun γ => by rw [← hwdef]; exact hw0 γ`. Establish `hwW' : ∀ γ ∈ S, w γ ≤ ∏ v, farW h ε (idx (d γ v))` using `fun γ hγ => by`.

Rewrite using `[← hwdef]`. Conclude with `hwW γ hγ`. Use `show ∑ γ ∈ S, w γ ≤ _`. Use `set m := S.sup (fun γ => univ.sup (fun v => idx (d γ v))) with hmdef`. Establish `hm : ∀ γ ∈ S, ∀ v, idx (d γ v) ≤ m`.

Introduce `γ hγ v`. Combine the equalities or inequalities in the displayed calculation. Establish `hT1 : Real.exp (-(h * ε ^ 2 / 16)) ≤ 1 / 2`. Use `le_trans (Real.exp_le_exp.mpr ?_) exp_neg_one_le_half` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hv0 : ∀ v₀, ∑ γ ∈ S.filter (fun γ => ε < d γ v₀), w γ ≤ A * (4 ^ Fintype.card ι * (Real.exp (-(h * ε ^ 2 / 16)) / 2))`. Introduce `v₀`. Use `set t : ι → Finset ℕ := fun v => if v = v₀ then Ico 1 (m+1) else range (m+1) with ht`. Establish `hmaps : ∀ γ ∈ S.filter (fun γ => ε < d γ v₀), (fun v => idx (d γ v)) ∈ Fintype.piFinset t`. Introduce `γ hγ`.

Establish `hγ'` using `Finset.mem_filter.mp hγ`. Rewrite using `[Fintype.mem_piFinset]`. Introduce `v`. Simplify using `only [ht]`. Use `split_ifs with hv`.

Substitute `hv` using the available equality. Conclude with `Finset.mem_Ico.mpr ⟨hidx0 _ hγ'.2, Nat.lt_succ_of_le (hm γ hγ'.1 v)⟩`. Conclude with `Finset.mem_range.mpr (Nat.lt_succ_of_le (hm γ hγ'.1 v))`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to hmaps]`. Combine the equalities or inequalities in the displayed calculation.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `I _`. Establish `hmem : ∀ γ ∈ (S.filter (fun γ => ε < d γ v₀)).filter (fun γ => (fun v => idx (d γ v)) = I), γ ∈ S ∧ ∀ v, idx (d γ v) = I v`. Introduce `γ hγ`. Establish `h1` using `Finset.mem_filter.mp hγ`.

Conclude with `⟨(Finset.mem_filter.mp h1.1).1, fun v => congrFun h1.2 v⟩`. Establish `hPW : 0 ≤ ∏ v, farW h ε (I v)` using `Finset.prod_nonneg fun v _ => farW_nonneg _ _ _`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `γ hγ`.

Take `⟨h1, h2⟩` from `hmem γ hγ`. Use `hwW' γ h1` as an intermediate fact. Simplify using `only [h2] at this`. Conclude with `this`. Use `_ = (((S.filter (fun γ => ε < d γ v₀)).filter (fun γ => (fun v => idx (d γ v)) = I)).card : ℝ) * ∏ v, farW h ε (I v) := by`.

Rewrite using `[Finset.sum_const, nsmul_eq_mul]`. Use `_ ≤ (A * Real.exp (B * ∑ v, 2 ^ (I v) * ε)) * ∏ v, farW h ε (I v) := by`. Apply `mul_le_mul_of_nonneg_right _ hPW` to reduce the goal to its premises. Use `le_trans ?_ (hcount (fun v => 2 ^ (I v) * ε) (fun v => by positivity))` and prove the remaining obligations. Establish `hsub : (S.filter (fun γ => ε < d γ v₀)).filter (fun γ => (fun v => idx (d γ v)) = I) ⊆ S.filter (fun γ => ∀ v, d γ v ≤ 2 ^ (I v) * ε)`.

Introduce `γ hγ`. Take `⟨h1, h2⟩` from `hmem γ hγ`. Use `Finset.mem_filter.mpr ⟨h1, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[← h2 v]`. Conclude with `hidx1 _`.

Conclude with `Finset.card_le_card hsub` after adjusting the coercions. Use `_ = A * ∏ v, farA B h ε (I v) := by`. Unfold `farA`. Rewrite using `[Finset.mul_sum, Real.exp_sum, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = A * ∏ v, ∑ i ∈ t v, farA B h ε i := by`. Rewrite using `[← Finset.mul_sum, Finset.prod_univ_sum]`. Use `_ ≤ A * ∏ v, (4 * if v = v₀ then Real.exp (-(h * ε ^ 2 / 16)) / 2 else 1) := by`. Apply `mul_le_mul_of_nonneg_left _ hA` to reduce the goal to its premises. Apply `Finset.prod_le_prod` to reduce the goal to its premises.

Introduce `v _`. Conclude with `Finset.sum_nonneg fun i _ => farA_nonneg _ _ _ _`. Introduce `v _`. Establish `hs` using `farA_sum_succ (B := B) hε h32 h16 m`. Simplify using `only [ht]`.

Use `split_ifs with hv`. Rewrite using `[Finset.sum_Ico_eq_sum_range]`. Simplify using `only [Nat.add_sub_cancel, add_comm 1]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Finset.sum_range_succ']`.

Use `farA_zero_le (h := h) hBε` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = _ := by`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_ite_eq']`. Simplify using the standard rewrite rules.

Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `γ hγ`. Take `⟨v, hv⟩` from `hdε γ hγ`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `hw0' γ`. Conclude with `le_rfl) (Finset.mem_univ v)`. Use `_ = ∑ v₀, ∑ γ ∈ S, (if ε < d γ v₀ then w γ else 0) := Finset.sum_comm`. Use `_ = ∑ v₀, ∑ γ ∈ S.filter (fun γ => ε < d γ v₀), w γ := by simp_rw [Finset.sum_filter]`. Use `_ ≤ ∑ _v₀ : ι, A * (4 ^ Fintype.card ι * (Real.exp (-(h * ε ^ 2 / 16)) / 2)) := Finset.sum_le_sum fun v₀ _ => hv0 v₀`.

Use `_ = Fintype.card ι * (A * (4 ^ Fintype.card ι * (Real.exp (-(h * ε ^ 2 / 16)) / 2))) := by`. Rewrite using `[Finset.sum_const, nsmul_eq_mul, Finset.card_univ]`. Use `_ ≤ _ := by`. Establish `h0 : 0 ≤ A * 4 ^ Fintype.card ι * Fintype.card ι * Real.exp (-(h * ε ^ 2 / 16))`. Check the signs of the components of the expression.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem far_region_sum : FarSum := by
  intro ι Γ _ _ S d A B h ε q hq hA hB hε hεq hBε h32 h16 hd0 hdε hcount
  have hε2 : 0 < ε ^ 2 := by positivity
  have hh : 0 ≤ h := by
    by_contra hneg
    push Not at hneg
    have : h * ε ^ 2 < 0 := mul_neg_of_neg_of_pos hneg hε2
    linarith
  have hex : ∀ x : ℝ, ∃ i : ℕ, x ≤ 2 ^ i * ε := by
    intro x
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (x / ε) (one_lt_two : (1:ℝ) < 2)
    exact ⟨n, by rw [div_lt_iff₀ hε] at hn; exact hn.le⟩
  obtain ⟨idx, hidx1, hidx2⟩ : ∃ idx : ℝ → ℕ, (∀ x, x ≤ 2 ^ idx x * ε) ∧
      (∀ x k, idx x = k + 1 → 2 ^ k * ε < x) := by
    refine ⟨fun x => Nat.find (hex x), fun x => Nat.find_spec (hex x), ?_⟩
    intro x k hk
    have := Nat.find_min (hex x) (m := k) (by simp only at hk; omega)
    exact not_le.mp this
  have hidx0 : ∀ x, ε < x → 1 ≤ idx x := by
    intro x hx
    by_contra hc
    have h0 : idx x = 0 := by omega
    have := hidx1 x
    rw [h0] at this
    simp at this
    linarith
  have hW : ∀ x, 0 ≤ x → Real.exp (-(decExp h q x)) ≤ farW h ε (idx x) := by
    intro x hx
    rcases hk : idx x with _ | k
    · show _ ≤ (1:ℝ)
      rw [Real.exp_le_one_iff]
      have : 0 ≤ decExp h q x :=
        mul_nonneg (by linarith) (le_min (sq_nonneg _) (div_nonneg hx (Real.sqrt_nonneg _)))
      linarith
    · have h1 := hidx2 x k hk
      show _ ≤ Real.exp (-(h / 8 * (ε * (2 ^ k * ε))))
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      have hεx : ε ≤ x := by
        have : (1:ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        nlinarith
      have h2 := minimum_linear_form q ε x hq hε hεq hεx
      unfold decExp
      calc h / 8 * (ε * (2 ^ k * ε)) ≤ h / 8 * (ε * x) := by gcongr
        _ ≤ _ := by gcongr
  have hw0 : ∀ γ, 0 ≤ ∏ v, Real.exp (-(decExp h q (d γ v))) :=
    fun γ => Finset.prod_nonneg fun v _ => (Real.exp_pos _).le
  have hwW : ∀ γ ∈ S, ∏ v, Real.exp (-(decExp h q (d γ v))) ≤ ∏ v, farW h ε (idx (d γ v)) :=
    fun γ hγ => Finset.prod_le_prod (fun v _ => (Real.exp_pos _).le) (fun v _ => hW _ (hd0 γ hγ v))
  generalize hwdef : (fun γ => ∏ v, Real.exp (-(decExp h q (d γ v)))) = w at *
  have hw0' : ∀ γ, 0 ≤ w γ := fun γ => by rw [← hwdef]; exact hw0 γ
  have hwW' : ∀ γ ∈ S, w γ ≤ ∏ v, farW h ε (idx (d γ v)) := fun γ hγ => by
    rw [← hwdef]; exact hwW γ hγ
  show ∑ γ ∈ S, w γ ≤ _
  set m := S.sup (fun γ => univ.sup (fun v => idx (d γ v))) with hmdef
  have hm : ∀ γ ∈ S, ∀ v, idx (d γ v) ≤ m := by
    intro γ hγ v
    calc idx (d γ v) ≤ univ.sup (fun v => idx (d γ v)) :=
          Finset.le_sup (f := fun v => idx (d γ v)) (Finset.mem_univ v)
      _ ≤ m := Finset.le_sup (f := fun γ => univ.sup (fun v => idx (d γ v))) hγ
  have hT1 : Real.exp (-(h * ε ^ 2 / 16)) ≤ 1 / 2 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) exp_neg_one_le_half
    linarith
  have hv0 : ∀ v₀, ∑ γ ∈ S.filter (fun γ => ε < d γ v₀), w γ
      ≤ A * (4 ^ Fintype.card ι * (Real.exp (-(h * ε ^ 2 / 16)) / 2)) := by
    intro v₀
    set t : ι → Finset ℕ := fun v => if v = v₀ then Ico 1 (m+1) else range (m+1) with ht
    have hmaps : ∀ γ ∈ S.filter (fun γ => ε < d γ v₀),
        (fun v => idx (d γ v)) ∈ Fintype.piFinset t := by
      intro γ hγ
      have hγ' := Finset.mem_filter.mp hγ
      rw [Fintype.mem_piFinset]
      intro v
      simp only [ht]
      split_ifs with hv
      · subst hv
        exact Finset.mem_Ico.mpr ⟨hidx0 _ hγ'.2, Nat.lt_succ_of_le (hm γ hγ'.1 v)⟩
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hm γ hγ'.1 v))
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc ∑ I ∈ Fintype.piFinset t,
          ∑ γ ∈ (S.filter (fun γ => ε < d γ v₀)).filter (fun γ => (fun v => idx (d γ v)) = I), w γ
        ≤ ∑ I ∈ Fintype.piFinset t, A * ∏ v, farA B h ε (I v) := by
          apply Finset.sum_le_sum
          intro I _
          have hmem : ∀ γ ∈ (S.filter (fun γ => ε < d γ v₀)).filter
              (fun γ => (fun v => idx (d γ v)) = I), γ ∈ S ∧ ∀ v, idx (d γ v) = I v := by
            intro γ hγ
            have h1 := Finset.mem_filter.mp hγ
            exact ⟨(Finset.mem_filter.mp h1.1).1, fun v => congrFun h1.2 v⟩
          have hPW : 0 ≤ ∏ v, farW h ε (I v) := Finset.prod_nonneg fun v _ => farW_nonneg _ _ _
          calc ∑ γ ∈ (S.filter (fun γ => ε < d γ v₀)).filter
                (fun γ => (fun v => idx (d γ v)) = I), w γ
              ≤ ∑ γ ∈ (S.filter (fun γ => ε < d γ v₀)).filter
                (fun γ => (fun v => idx (d γ v)) = I), ∏ v, farW h ε (I v) := by
                apply Finset.sum_le_sum
                intro γ hγ
                obtain ⟨h1, h2⟩ := hmem γ hγ
                have := hwW' γ h1
                simp only [h2] at this
                exact this
            _ = (((S.filter (fun γ => ε < d γ v₀)).filter
                (fun γ => (fun v => idx (d γ v)) = I)).card : ℝ) * ∏ v, farW h ε (I v) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (A * Real.exp (B * ∑ v, 2 ^ (I v) * ε)) * ∏ v, farW h ε (I v) := by
                apply mul_le_mul_of_nonneg_right _ hPW
                refine le_trans ?_ (hcount (fun v => 2 ^ (I v) * ε) (fun v => by positivity))
                have hsub : (S.filter (fun γ => ε < d γ v₀)).filter
                    (fun γ => (fun v => idx (d γ v)) = I) ⊆
                    S.filter (fun γ => ∀ v, d γ v ≤ 2 ^ (I v) * ε) := by
                  intro γ hγ
                  obtain ⟨h1, h2⟩ := hmem γ hγ
                  refine Finset.mem_filter.mpr ⟨h1, fun v => ?_⟩
                  rw [← h2 v]; exact hidx1 _
                exact_mod_cast Finset.card_le_card hsub
            _ = A * ∏ v, farA B h ε (I v) := by
                unfold farA
                rw [Finset.mul_sum, Real.exp_sum, Finset.prod_mul_distrib]; ring
      _ = A * ∏ v, ∑ i ∈ t v, farA B h ε i := by
          rw [← Finset.mul_sum, Finset.prod_univ_sum]
      _ ≤ A * ∏ v, (4 * if v = v₀ then Real.exp (-(h * ε ^ 2 / 16)) / 2 else 1) := by
          apply mul_le_mul_of_nonneg_left _ hA
          apply Finset.prod_le_prod
          · intro v _; exact Finset.sum_nonneg fun i _ => farA_nonneg _ _ _ _
          · intro v _
            have hs := farA_sum_succ (B := B) hε h32 h16 m
            simp only [ht]
            split_ifs with hv
            · rw [Finset.sum_Ico_eq_sum_range]
              simp only [Nat.add_sub_cancel, add_comm 1]
              linarith
            · rw [Finset.sum_range_succ']
              have := farA_zero_le (h := h) hBε
              linarith
      _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_ite_eq']
          simp
  calc ∑ γ ∈ S, w γ ≤ ∑ γ ∈ S, ∑ v₀, (if ε < d γ v₀ then w γ else 0) := by
        apply Finset.sum_le_sum
        intro γ hγ
        obtain ⟨v, hv⟩ := hdε γ hγ
        calc w γ = (if ε < d γ v then w γ else 0) := by rw [if_pos hv]
          _ ≤ _ := Finset.single_le_sum (f := fun v₀ => if ε < d γ v₀ then w γ else 0)
              (fun v _ => by
                show 0 ≤ if ε < d γ v then w γ else 0
                split_ifs
                · exact hw0' γ
                · exact le_rfl) (Finset.mem_univ v)
    _ = ∑ v₀, ∑ γ ∈ S, (if ε < d γ v₀ then w γ else 0) := Finset.sum_comm
    _ = ∑ v₀, ∑ γ ∈ S.filter (fun γ => ε < d γ v₀), w γ := by simp_rw [Finset.sum_filter]
    _ ≤ ∑ _v₀ : ι, A * (4 ^ Fintype.card ι * (Real.exp (-(h * ε ^ 2 / 16)) / 2)) :=
        Finset.sum_le_sum fun v₀ _ => hv0 v₀
    _ = Fintype.card ι * (A * (4 ^ Fintype.card ι * (Real.exp (-(h * ε ^ 2 / 16)) / 2))) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ ≤ _ := by
        have h0 : 0 ≤ A * 4 ^ Fintype.card ι * Fintype.card ι * Real.exp (-(h * ε ^ 2 / 16)) := by
          positivity
        nlinarith

end Formalism.HermitianLatticeCounting.P
