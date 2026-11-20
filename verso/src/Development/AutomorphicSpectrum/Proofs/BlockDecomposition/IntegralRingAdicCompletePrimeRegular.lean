import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.TiltCompl

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Rewrite using `[preTilt_norm_def, coe_untilt_pFlat]`. Conclude with `norm_pos_iff.2 natCast_p_ne_zero_cp`.
-/
theorem norm_pFlat_pos : 0 < ‖pFlat l‖ := by
  rw [preTilt_norm_def, coe_untilt_pFlat]
  exact norm_pos_iff.2 natCast_p_ne_zero_cp

/- English proof (translation)
Rewrite using `[preTilt_norm_def, coe_untilt_pFlat]`. Conclude with `IsPerfectoidField.norm_natCast_lt_one`.
-/
theorem norm_pFlat_lt_one : ‖pFlat l‖ < 1 := by
  rw [preTilt_norm_def, coe_untilt_pFlat]
  exact IsPerfectoidField.norm_natCast_lt_one

/- English proof (translation)
Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton, preTilt_dvd_iff_norm_le, norm_pow]`.
-/
theorem smodEq_iff (n : ℕ) (x y : Ob l) :
    x ≡ y [SMOD (Ideal.span {pFlat l} ^ n • ⊤ : Ideal (Ob l))] ↔ ‖x - y‖ ≤ ‖pFlat l‖ ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, preTilt_dvd_iff_norm_le, norm_pow]

/- English proof (translation)
Introduce `l _`. Establish `h0 : 0 < ‖pFlat l‖` using `norm_pFlat_pos`. Establish `h1 : ‖pFlat l‖ < 1` using `norm_pFlat_lt_one`. Establish `hlim : Filter.Tendsto (fun n : ℕ => ‖pFlat l‖ ^ n) Filter.atTop (nhds 0)` using `tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1`. Use `⟨{ haus' := fun x hx => ?_, prec' := fun f hf => ?_ }, ?_⟩` and prove the remaining obligations.

Establish `hb : ∀ n : ℕ, ‖x‖ ≤ ‖pFlat l‖ ^ n` using `fun n => by`. Simplify using `using (smodEq_iff n x 0).1 (hx n)`. Establish `: ‖x‖ ≤ 0` using `ge_of_tendsto' hlim hb`. Conclude with `norm_le_zero_iff.1 this`. Establish `hb : ∀ {m n : ℕ}, m ≤ n → ‖f m - f n‖ ≤ ‖pFlat l‖ ^ m` using `fun h => (smodEq_iff _ _ _).1 (hf h)`.

Establish `hc : CauchySeq f`. Use `cauchySeq_of_le_geometric ‖pFlat l‖ 1 h1 fun n => ?_` and prove the remaining obligations. Rewrite using `[dist_eq_norm, one_mul]`. Conclude with `hb n.le_succ`. Take `⟨L, hL⟩` from `cauchySeq_tendsto_of_complete hc`.

Use `⟨L, fun n => (smodEq_iff _ _ _).2 ?_⟩` and prove the remaining obligations. Establish `ht : Filter.Tendsto (fun m => ‖f n - f m‖) Filter.atTop (nhds ‖f n - L‖)` using `(tendsto_const_nhds.sub hL).norm`. Use `le_of_tendsto ht ?_` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_ge_atTop n] with m hm using hb hm`. Conclude with `mem_nonZeroDivisors_iff_left.2 fun x hx => by`.

Use `congrArg norm hx` as an intermediate fact. Rewrite `this` using `[norm_mul, norm_zero]`. Conclude with `norm_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h0.ne')`.
-/
theorem complete_tf : ∀ {l : ℕ} [Fact l.Prime],
    IsAdicComplete (Ideal.span {pFlat l}) (Ob l) ∧ pFlat l ∈ nonZeroDivisors (Ob l) := by
  intro l _
  have h0 : 0 < ‖pFlat l‖ := norm_pFlat_pos
  have h1 : ‖pFlat l‖ < 1 := norm_pFlat_lt_one
  have hlim : Filter.Tendsto (fun n : ℕ => ‖pFlat l‖ ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1
  refine ⟨{ haus' := fun x hx => ?_, prec' := fun f hf => ?_ }, ?_⟩
  · have hb : ∀ n : ℕ, ‖x‖ ≤ ‖pFlat l‖ ^ n := fun n => by
      simpa using (smodEq_iff n x 0).1 (hx n)
    have : ‖x‖ ≤ 0 := ge_of_tendsto' hlim hb
    exact norm_le_zero_iff.1 this
  · have hb : ∀ {m n : ℕ}, m ≤ n → ‖f m - f n‖ ≤ ‖pFlat l‖ ^ m := fun h =>
      (smodEq_iff _ _ _).1 (hf h)
    have hc : CauchySeq f := by
      refine cauchySeq_of_le_geometric ‖pFlat l‖ 1 h1 fun n => ?_
      rw [dist_eq_norm, one_mul]
      exact hb n.le_succ
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    refine ⟨L, fun n => (smodEq_iff _ _ _).2 ?_⟩
    have ht : Filter.Tendsto (fun m => ‖f n - f m‖) Filter.atTop (nhds ‖f n - L‖) :=
      (tendsto_const_nhds.sub hL).norm
    refine le_of_tendsto ht ?_
    filter_upwards [Filter.eventually_ge_atTop n] with m hm using hb hm
  · exact mem_nonZeroDivisors_iff_left.2 fun x hx => by
      have := congrArg norm hx
      rw [norm_mul, norm_zero] at this
      exact norm_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h0.ne')

end GlobalTheory.CompanionTheory.TiltCompl
