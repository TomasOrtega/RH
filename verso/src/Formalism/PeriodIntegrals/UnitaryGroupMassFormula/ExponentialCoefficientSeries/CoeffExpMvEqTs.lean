import Mathlib
import Formalism.PeriodIntegrals.SimeqPdInt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CubeFormalIdentities.CoeffPowMulPowEqZero

noncomputable section

open MvPowerSeries

namespace PI.UnitaryGroupMassFormula.SimeqPdInt

variable {p : ℕ} [Fact p.Prime] {σ : Type*}

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[coeff_pderiv]`. Express the relevant statement in the definitionally equal form `((n k : ℂ_[p]) + 1) * coeff (n + Finsupp.single k 1) F = _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pd_eq [DecidableEq σ] (k : σ) (F : MvPowerSeries σ ℂ_[p]) :
    PI.SimeqPdInt.pd k F = pderiv ℂ_[p] k F := by
  ext n
  rw [coeff_pderiv]
  change ((n k : ℂ_[p]) + 1) * coeff (n + Finsupp.single k 1) F = _
  ring

def ts (f : MvPowerSeries σ ℂ_[p]) (N : ℕ) : MvPowerSeries σ ℂ_[p] :=
  ∑ n ∈ Finset.range N, ((n.factorial : ℂ_[p])⁻¹) • f ^ n

/- English proof (translation)
Simplify using `only [ts, map_sum, coeff_smul]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[div_eq_inv_mul]`.
-/
theorem coeff_ts (f : MvPowerSeries σ ℂ_[p]) (N : ℕ) (a : σ →₀ ℕ) :
    coeff a (ts f N) = ∑ n ∈ Finset.range N, coeff a (f ^ n) / (n.factorial : ℂ_[p]) := by
  simp only [ts, map_sum, coeff_smul]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [div_eq_inv_mul]

/- English proof (translation)
Rewrite using `[coeff_ts]`. Conclude with `PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.coeff_expMv_of_le hf N h`.
-/
theorem coeff_expMv_eq_ts {f : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0)
    {a : σ →₀ ℕ} {N : ℕ} (h : a.degree ≤ N) :
    coeff a (PI.FglGram.expMv f) = coeff a (ts f (N + 1)) := by
  rw [coeff_ts]
  exact PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.coeff_expMv_of_le hf N h

/- English proof (translation)
Simplify using `only [ts, map_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_range_succ']`. Rewrite using `[pow_zero, Derivation.map_smul, pderiv_one, smul_zero, add_zero]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[Derivation.map_smul, pderiv_pow, Nat.add_sub_cancel, Algebra.smul_def, Algebra.smul_def]`.

Establish `h1 : ((n + 1 : ℕ) : ℂ_[p]) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero n`. Establish `h2 : (n.factorial : ℂ_[p]) ≠ 0` using `by exact_mod_cast n.factorial_ne_zero`. Establish `hc : (n.factorial : ℂ_[p])⁻¹ = ((n + 1).factorial : ℂ_[p])⁻¹ * ((n + 1 : ℕ) : ℂ_[p])`. Rewrite using `[Nat.factorial_succ, Nat.cast_mul]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[hc, map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pderiv_ts (k : σ) (f : MvPowerSeries σ ℂ_[p]) (N : ℕ) :
    pderiv ℂ_[p] k (ts f (N + 1)) = ts f N * pderiv ℂ_[p] k f := by
  simp only [ts, map_sum, Finset.sum_mul]
  rw [Finset.sum_range_succ']
  rw [pow_zero, Derivation.map_smul, pderiv_one, smul_zero, add_zero]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Derivation.map_smul, pderiv_pow, Nat.add_sub_cancel, Algebra.smul_def, Algebra.smul_def]
  have h1 : ((n + 1 : ℕ) : ℂ_[p]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h2 : (n.factorial : ℂ_[p]) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hc : (n.factorial : ℂ_[p])⁻¹ =
      ((n + 1).factorial : ℂ_[p])⁻¹ * ((n + 1 : ℕ) : ℂ_[p]) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
    field_simp
  rw [hc, map_mul, map_natCast]
  ring

/- English proof (translation)
Use extensionality with `α`. Establish `hdeg : (α + Finsupp.single k 1).degree ≤ α.degree + 1`. Rewrite using `[map_add]`. Simplify using the standard rewrite rules. Rewrite using `[coeff_pderiv, coeff_expMv_eq_ts hf hdeg, ← coeff_pderiv, pderiv_ts, coeff_mul, coeff_mul]`.

Use `Finset.sum_congr rfl fun q hq => ?_` and prove the remaining obligations. Establish `hq' : q.1 + q.2 = α` using `by simpa using hq`. Establish `hle : q.1.degree ≤ α.degree`. Rewrite using `[← hq', map_add]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[coeff_expMv_eq_ts hf hle]`.
-/
theorem pderiv_expMv (k : σ) {f : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0) :
    pderiv ℂ_[p] k (PI.FglGram.expMv f) = PI.FglGram.expMv f * pderiv ℂ_[p] k f := by
  classical
  ext α
  have hdeg : (α + Finsupp.single k 1).degree ≤ α.degree + 1 := by
    rw [map_add]
    simp
  rw [coeff_pderiv, coeff_expMv_eq_ts hf hdeg, ← coeff_pderiv, pderiv_ts, coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq' : q.1 + q.2 = α := by simpa using hq
  have hle : q.1.degree ≤ α.degree := by
    rw [← hq', map_add]
    omega
  rw [coeff_expMv_eq_ts hf hle]

/- English proof (translation)
Introduce `n`. Establish `hn` using `hF (n + Finsupp.single k 1)`. Unfold `PI.FglGram.IsIntP at hn ⊢`. Rewrite using `[coeff_pderiv, norm_mul]`. Use `mul_le_one₀ hn (norm_nonneg _) ?_` and prove the remaining obligations.

Use `IsUltrametricDist.norm_natCast_le_one ℂ_[p] (n k + 1)` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`.
-/
theorem int_pderiv (k : σ) {F : MvPowerSeries σ ℂ_[p]} (hF : PI.FglGram.IntegralMv F) :
    PI.FglGram.IntegralMv (pderiv ℂ_[p] k F) := by
  intro n
  have hn := hF (n + Finsupp.single k 1)
  unfold PI.FglGram.IsIntP at hn ⊢
  rw [coeff_pderiv, norm_mul]
  refine mul_le_one₀ hn (norm_nonneg _) ?_
  have := IsUltrametricDist.norm_natCast_le_one ℂ_[p] (n k + 1)
  push_cast at this
  exact this

/- English proof (translation)
Introduce `p _ σ _ f hf k`. Take `⟨h0, hE⟩` from `hf`. Rewrite `h0`, `hE` using `[sub_zero]`. Establish `hE' : PI.FglGram.IntegralMv (PI.FglGram.expMv f)` using `hE`. Establish `hinv` using `PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.int_expMv_neg h0 hE'`.

Establish `hWV : PI.FglGram.expMv (-f) * PI.FglGram.expMv f = 1`. Rewrite using `[← PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.expMv_add (by rw [map_neg, h0, neg_zero]) h0, neg_add_cancel, PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.expMv_zero]`. Establish `key : PI.SimeqPdInt.pd k f = PI.FglGram.expMv (-f) * pderiv ℂ_[p] k (PI.FglGram.expMv f)`. Rewrite using `[pd_eq, pderiv_expMv k h0, ← mul_assoc, hWV, one_mul]`. Rewrite using `[key]`.

Conclude with `PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.int_mul hinv (int_pderiv k hE')`.
-/
theorem target : PI.SimeqPdInt.Target := by
  intro p _ σ _ f hf k
  obtain ⟨h0, hE⟩ := hf
  rw [sub_zero] at h0 hE
  have hE' : PI.FglGram.IntegralMv (PI.FglGram.expMv f) := hE
  have hinv := PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.int_expMv_neg h0 hE'
  have hWV : PI.FglGram.expMv (-f) * PI.FglGram.expMv f = 1 := by
    rw [← PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.expMv_add (by rw [map_neg, h0, neg_zero]) h0, neg_add_cancel,
      PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.expMv_zero]
  have key : PI.SimeqPdInt.pd k f =
      PI.FglGram.expMv (-f) * pderiv ℂ_[p] k (PI.FglGram.expMv f) := by
    rw [pd_eq, pderiv_expMv k h0, ← mul_assoc, hWV, one_mul]
  rw [key]
  exact PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.int_mul hinv (int_pderiv k hE')

end PI.UnitaryGroupMassFormula.SimeqPdInt
