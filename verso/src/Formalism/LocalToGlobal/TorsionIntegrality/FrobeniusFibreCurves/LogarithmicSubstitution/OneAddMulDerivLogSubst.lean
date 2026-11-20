import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementA
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule

noncomputable section

namespace Formalism.L2.Th1.B

open PowerSeries

section One

variable {K : Type} [Field K] [CharZero K]

/- English proof (translation)
Rewrite using `[← coe_substAlgHom ha, map_one]`.
-/
theorem psubst_one {ι : Type} {a : MvPowerSeries ι K} (ha : HasSubst a) :
    (1 : PowerSeries K).subst a = 1 := by
  rw [← coe_substAlgHom ha, map_one]

/- English proof (translation)
Establish `hd : ∀ n : ℕ, coeff n (derivative K (log K)) = (-1 : K) ^ n`. Introduce `n`. Rewrite using `[PowerSeries.coeff_derivative]`. Simplify using `[PowerSeries.log]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Use extensionality with `n`. Rewrite using `[add_mul, one_mul, map_add]`. Break down `n with _ | n` into its components or cases. Simplify using `[hd]`.

Rewrite using `[coeff_succ_X_mul, hd, hd, coeff_one]`. Simplify using `[pow_succ]`.
-/
theorem one_add_X_mul_deriv_log : (1 + X : PowerSeries K) * derivative K (log K) = 1 := by
  have hd : ∀ n : ℕ, coeff n (derivative K (log K)) = (-1 : K) ^ n := by
    intro n
    rw [PowerSeries.coeff_derivative]
    simp [PowerSeries.log]
    field_simp
    ring
  ext n
  rw [add_mul, one_mul, map_add]
  rcases n with _ | n
  · simp [hd]
  · rw [coeff_succ_X_mul, hd, hd, coeff_one]
    simp [pow_succ]

/- English proof (translation)
Rewrite using `[← coe_substAlgHom ha, map_add, map_one, coe_substAlgHom, subst_X ha]`.
-/
theorem one_add_X_subst {ι : Type} {a : MvPowerSeries ι K} (ha : HasSubst a) :
    (1 + X : PowerSeries K).subst a = 1 + a := by
  rw [← coe_substAlgHom ha, map_add, map_one, coe_substAlgHom, subst_X ha]

/- English proof (translation)
Establish `h` using `congrArg (PowerSeries.substAlgHom ha) (one_add_X_mul_deriv_log (K := K))`. Rewrite `h` using `[map_mul, map_one, coe_substAlgHom, one_add_X_subst ha]`. Conclude with `h`.
-/
theorem one_add_mul_deriv_log_subst {ι : Type} {a : MvPowerSeries ι K} (ha : HasSubst a) :
    (1 + a) * (derivative K (log K)).subst a = 1 := by
  have h := congrArg (PowerSeries.substAlgHom ha) (one_add_X_mul_deriv_log (K := K))
  rw [map_mul, map_one, coe_substAlgHom, one_add_X_subst ha] at h
  exact h

/- English proof (translation)
Rewrite using `[PowerSeries.constantCoeff_subst (HasSubst.of_constantCoeff_zero hf), finsum_eq_single _ 0]`. Simplify using the standard rewrite rules. Introduce `d hd`. Simplify using `[hf, zero_pow hd]`.
-/
private theorem constantCoeff_powerSeries_subst_mv_eq {ι : Type} (φ : PowerSeries K) {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (φ.subst f) = constantCoeff φ := by
  rw [PowerSeries.constantCoeff_subst (HasSubst.of_constantCoeff_zero hf), finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [hf, zero_pow hd]

/- English proof (translation)
The claim follows from `constantCoeff_powerSeries_subst_mv_eq φ (f := g) hg`.
-/
private theorem constantCoeff_powerSeries_subst_eq (φ : PowerSeries K) {g : PowerSeries K}
    (hg : constantCoeff g = 0) : constantCoeff (φ.subst g) = constantCoeff φ :=
  constantCoeff_powerSeries_subst_mv_eq φ (f := g) hg

/- English proof (translation)
Rewrite using `[← coeff_zero_eq_constantCoeff_apply]`. Simplify using `[PowerSeries.log]`.
-/
private theorem constantCoeff_log_eq_zero' : constantCoeff (log K) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [PowerSeries.log]

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[PowerSeries.coeff_derivative]`. Simplify using `[coeff_exp, Nat.factorial_succ]`. Clear the denominators using the available nonvanishing facts.
-/
private theorem derivative_exp_eq_exp : derivative K (exp K) = exp K := by
  ext n
  rw [PowerSeries.coeff_derivative]
  simp [coeff_exp, Nat.factorial_succ]
  field_simp

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[PowerSeries.coeff_derivative]`. Express the relevant statement in the definitionally equal form `_ = MvPowerSeries.coeff (Finsupp.single () n) _`. Rewrite using `[MvPowerSeries.coeff_pderiv, ← Finsupp.single_add, Finsupp.single_eq_same]`. Both sides reduce to the same expression.
-/
private theorem derivative_eq_pderiv_unit (f : PowerSeries K) :
    derivative K f = MvPowerSeries.pderiv K () f := by
  ext n
  rw [PowerSeries.coeff_derivative]
  change _ = MvPowerSeries.coeff (Finsupp.single () n) _
  rw [MvPowerSeries.coeff_pderiv, ← Finsupp.single_add, Finsupp.single_eq_same]
  rfl

/- English proof (translation)
Establish `h` using `Formalism.G.LogCR.pderiv_psubst (R := K) (τ := Unit) (a := g) hg φ ()`. Simplify using `only [derivative_eq_pderiv_unit]`. Conclude with `h`.
-/
private theorem derivative_subst_eq_chain_rule {g : PowerSeries K} (hg : constantCoeff g = 0)
    (φ : PowerSeries K) :
    derivative K (φ.subst g) = (derivative K φ).subst g * derivative K g := by
  have h := Formalism.G.LogCR.pderiv_psubst (R := K) (τ := Unit) (a := g) hg φ ()
  simp only [derivative_eq_pderiv_unit]
  exact h

/- English proof (translation)
Establish `hc : constantCoeff (exp K - 1 : PowerSeries K) = 0` using `by simp`. Apply `derivative.ext` to reduce the goal to its premises. Rewrite using `[derivative_subst_eq_chain_rule hc, derivative_X, map_sub, derivative_exp_eq_exp, Derivation.map_one_eq_zero, sub_zero]`. Establish `h` using `one_add_mul_deriv_log_subst (HasSubst.of_constantCoeff_zero' hc)`. Establish `e : (1 : PowerSeries K) + (exp K - 1) = exp K` using `by ring`.

Rewrite `h` using `[e]`. Rewrite using `[mul_comm]`. Conclude with `h`. Rewrite using `[constantCoeff_powerSeries_subst_eq _ hc, constantCoeff_log_eq_zero']`. Simplify using the standard rewrite rules.
-/
theorem log_subst_exp : (log K).subst (exp K - 1) = X := by
  have hc : constantCoeff (exp K - 1 : PowerSeries K) = 0 := by simp
  apply derivative.ext
  · rw [derivative_subst_eq_chain_rule hc, derivative_X, map_sub, derivative_exp_eq_exp, Derivation.map_one_eq_zero,
      sub_zero]
    have h := one_add_mul_deriv_log_subst (HasSubst.of_constantCoeff_zero' hc)
    have e : (1 : PowerSeries K) + (exp K - 1) = exp K := by ring
    rw [e] at h
    rw [mul_comm]
    exact h
  · rw [constantCoeff_powerSeries_subst_eq _ hc, constantCoeff_log_eq_zero']
    simp

/- English proof (translation)
Rewrite using `[constantCoeff_powerSeries_subst_mv_eq _ hf]`. Simplify using the standard rewrite rules.
-/
theorem constantCoeff_exp_subst {ι : Type} {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff ((exp K).subst f) = 1 := by
  rw [constantCoeff_powerSeries_subst_mv_eq _ hf]
  simp

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[map_zero]`. Proceed by induction on `n with`. Consider the case `zero => simpa using h0`. Consider the case `succ n ih`.

Establish `hn` using `congrArg (coeff n) h`. Rewrite `hn` using `[add_mul, one_mul, map_add, PowerSeries.coeff_derivative]`. Break down `n with _ | m` into its components or cases. Rewrite `hn` using `[coeff_zero_X_mul]`. Simplify `hn` using `[ih]`.

Rewrite `hn` using `[coeff_succ_X_mul, PowerSeries.coeff_derivative, ih]`. Establish `hne : ((m : K) + 1 + 1) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero (m + 1)`. Simplify `hn` using `[hne]`.
-/
private theorem eq_zero_of_one_add_X_mul_derivative_eq_self {F : PowerSeries K}
    (h : (1 + X) * derivative K F = F) (h0 : constantCoeff F = 0) : F = 0 := by
  ext n
  rw [map_zero]
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have hn := congrArg (coeff n) h
    rw [add_mul, one_mul, map_add, PowerSeries.coeff_derivative] at hn
    rcases n with _ | m
    · rw [coeff_zero_X_mul] at hn
      simpa [ih] using hn
    · rw [coeff_succ_X_mul, PowerSeries.coeff_derivative, ih] at hn
      have hne : ((m : K) + 1 + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + 1)
      simpa [hne] using hn

/- English proof (translation)
Establish `hl : constantCoeff (log K) = 0` using `constantCoeff_log_eq_zero'`. Establish `hE : derivative K ((exp K).subst (log K)) = (exp K).subst (log K) * derivative K (log K)`. Rewrite using `[derivative_subst_eq_chain_rule hl, derivative_exp_eq_exp]`. Rewrite using `[← sub_eq_zero]`. Apply `eq_zero_of_one_add_X_mul_derivative_eq_self` to reduce the goal to its premises.

Rewrite using `[map_sub, hE, map_add, Derivation.map_one_eq_zero, derivative_X, zero_add, mul_sub, mul_one, mul_left_comm, one_add_X_mul_deriv_log, mul_one]`. Rewrite using `[map_sub, constantCoeff_powerSeries_subst_eq _ hl]`. Simplify using the standard rewrite rules.
-/
theorem exp_subst_log : (exp K).subst (log K) = 1 + X := by
  have hl : constantCoeff (log K) = 0 := constantCoeff_log_eq_zero'
  have hE : derivative K ((exp K).subst (log K)) =
      (exp K).subst (log K) * derivative K (log K) := by
    rw [derivative_subst_eq_chain_rule hl, derivative_exp_eq_exp]
  rw [← sub_eq_zero]
  apply eq_zero_of_one_add_X_mul_derivative_eq_self
  · rw [map_sub, hE, map_add, Derivation.map_one_eq_zero, derivative_X, zero_add, mul_sub, mul_one,
      mul_left_comm, one_add_X_mul_deriv_log, mul_one]
  · rw [map_sub, constantCoeff_powerSeries_subst_eq _ hl]
    simp

/- English proof (translation)
It suffices to establish `H : ∀ N : ℕ, ∀ n : σ →₀ ℕ, n.degree = N → MvPowerSeries.coeff n u = 0 by`. Use extensionality with `n`. Simplify using `using H _ n rfl`. Introduce `N`. Proceed by induction on `N with`.

Consider the case `zero`. Introduce `n hn`. Rewrite `hn` using `[Finsupp.degree_eq_zero_iff]`. Substitute `hn` using the available equality. Simplify using `using h0`.

Consider the case `succ N ih`. Introduce `n hn`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, n i ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Establish `: n = 0`. Use extensionality with `j`. Conclude with `hc j`. Substitute `this` using the available equality. Simplify using `at hn`.

Use `set m := n - Finsupp.single i 1 with hm`. Establish `hnm : n = m + Finsupp.single i 1`. Use extensionality with `j`. Simplify using `only [hm, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]`. Use `split_ifs with hij`.

Substitute `hij` using the available equality. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Establish `hadd : (m + Finsupp.single i 1).degree = m.degree + 1`. Rewrite using `[map_add, Finsupp.degree_single]`.

Establish `hdeg : m.degree = N`. Rewrite `hadd` using `[← hnm]`. Use linear arithmetic over natural numbers and integers. Establish `key` using `congrArg (MvPowerSeries.coeff m) (hu i)`. Rewrite `key` using `[MvPowerSeries.coeff_pderiv, ih m hdeg, ← hnm]`.

Establish `hne : ((m i : K) + 1) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero (m i)`. Simplify `key` using `[hne]`.
-/
private theorem eq_zero_of_forall_pderiv_eq_self {σ : Type} {u : MvPowerSeries σ K}
    (hu : ∀ i, MvPowerSeries.pderiv K i u = u) (h0 : MvPowerSeries.constantCoeff u = 0) :
    u = 0 := by
  classical
  suffices H : ∀ N : ℕ, ∀ n : σ →₀ ℕ, n.degree = N → MvPowerSeries.coeff n u = 0 by
    ext n
    simpa using H _ n rfl
  intro N
  induction N with
  | zero =>
    intro n hn
    rw [Finsupp.degree_eq_zero_iff] at hn
    subst hn
    simpa using h0
  | succ N ih =>
    intro n hn
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      by_contra hc
      push_neg at hc
      have : n = 0 := by
        ext j
        exact hc j
      subst this
      simp at hn
    set m := n - Finsupp.single i 1 with hm
    have hnm : n = m + Finsupp.single i 1 := by
      ext j
      simp only [hm, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
        Finsupp.single_apply]
      split_ifs with hij
      · subst hij
        omega
      · omega
    have hadd : (m + Finsupp.single i 1).degree = m.degree + 1 := by
      rw [map_add, Finsupp.degree_single]
    have hdeg : m.degree = N := by
      rw [← hnm] at hadd
      omega
    have key := congrArg (MvPowerSeries.coeff m) (hu i)
    rw [MvPowerSeries.coeff_pderiv, ih m hdeg, ← hnm] at key
    have hne : ((m i : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m i)
    simpa [hne] using key

/- English proof (translation)
Rewrite using `[Formalism.G.LogCR.pderiv_psubst hf, derivative_exp_eq_exp]`.
-/
private theorem pderiv_exp_subst_eq_mul_pderiv {ι : Type} [Finite ι] (i : ι) {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.pderiv K i ((exp K).subst f) = (exp K).subst f * MvPowerSeries.pderiv K i f := by
  rw [Formalism.G.LogCR.pderiv_psubst hf, derivative_exp_eq_exp]

/- English proof (translation)
Establish `h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Establish `h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Establish `h01 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Rewrite using `[← sub_eq_zero]`. Apply `eq_zero_of_forall_pderiv_eq_self` to reduce the goal to its premises.

Introduce `i`. Rewrite using `[map_sub, Derivation.leibniz, pderiv_exp_subst_eq_mul_pderiv i h01, pderiv_exp_subst_eq_mul_pderiv i h0, pderiv_exp_subst_eq_mul_pderiv i h1, map_add, smul_eq_mul, smul_eq_mul]`. Apply the tactic sequence `fin_cases i <;> simp <;> ring`. Rewrite using `[map_sub, map_mul, constantCoeff_powerSeries_subst_mv_eq _ h01, constantCoeff_powerSeries_subst_mv_eq _ h0, constantCoeff_powerSeries_subst_mv_eq _ h1]`. Simplify using the standard rewrite rules.
-/
theorem exp_biv :
    (exp K).subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) =
      (exp K).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) *
        (exp K).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) := by
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have h01 : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_pderiv_eq_self
  · intro i
    rw [map_sub, Derivation.leibniz, pderiv_exp_subst_eq_mul_pderiv i h01, pderiv_exp_subst_eq_mul_pderiv i h0,
      pderiv_exp_subst_eq_mul_pderiv i h1, map_add, smul_eq_mul, smul_eq_mul]
    fin_cases i <;> simp <;> ring
  · rw [map_sub, map_mul, constantCoeff_powerSeries_subst_mv_eq _ h01, constantCoeff_powerSeries_subst_mv_eq _ h0,
      constantCoeff_powerSeries_subst_mv_eq _ h1]
    simp

/- English proof (translation)
Conclude with `MvPowerSeries.hasSubst_of_constantCoeff_zero h`.
-/
private theorem hasSubst_of_forall_constantCoeff_eq_zero {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ K}
    (h : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) : MvPowerSeries.HasSubst a := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero h

/- English proof (translation)
Establish `hu' : MvPowerSeries.HasSubst (fun _ : Unit => u)` using `hasSubst_of_forall_constantCoeff_eq_zero (fun _ => hu)`. Unfold `PowerSeries.subst`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply hu' hb]`.
-/
theorem psubst_msubst {ι κ : Type} (φ : PowerSeries K) {u : MvPowerSeries ι K}
    (hu : MvPowerSeries.constantCoeff u = 0) {b : ι → MvPowerSeries κ K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (φ.subst u) = φ.subst (MvPowerSeries.subst b u) := by
  have hu' : MvPowerSeries.HasSubst (fun _ : Unit => u) :=
    hasSubst_of_forall_constantCoeff_eq_zero (fun _ => hu)
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply hu' hb]

end One

section Rules

variable {K : Type} [Field K] [CharZero K] {ι : Type}

/- English proof (translation)
Apply the tactic sequence `have hb : MvPowerSeries.HasSubst ![f, g] := hasSubst_of_forall_constantCoeff_eq_zero (fun i => by fin_cases i <;> simpa)`. Establish `h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Establish `h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Establish `h01 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Establish `h` using `congrArg (MvPowerSeries.subst ![f, g]) (exp_biv (K := K))`.

Rewrite `h` using `[psubst_msubst _ h01 hb, MvPowerSeries.subst_mul hb, psubst_msubst _ h0 hb, psubst_msubst _ h1 hb]`. Simplify `h` using `[fExp, MvPowerSeries.subst_add hb, MvPowerSeries.subst_X hb]`.
-/
theorem fExp_add {f g : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) : fExp (f + g) = fExp f * fExp g := by
  have hb : MvPowerSeries.HasSubst ![f, g] :=
    hasSubst_of_forall_constantCoeff_eq_zero (fun i => by fin_cases i <;> simpa)
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have h01 : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have h := congrArg (MvPowerSeries.subst ![f, g]) (exp_biv (K := K))
  rw [psubst_msubst _ h01 hb, MvPowerSeries.subst_mul hb, psubst_msubst _ h0 hb,
    psubst_msubst _ h1 hb] at h
  simpa [fExp, MvPowerSeries.subst_add hb, MvPowerSeries.subst_X hb] using h

/- English proof (translation)
The claim follows from `constantCoeff_exp_subst hf`.
-/
theorem constantCoeff_fExp {f : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (fExp f) = 1 :=
  constantCoeff_exp_subst hf

/- English proof (translation)
Establish `hE : constantCoeff (exp K - 1 : PowerSeries K) = 0` using `by simp`. Establish `hf' : HasSubst f` using `HasSubst.of_constantCoeff_zero hf`. Unfold `fLog fExp`. Establish `e : (exp K).subst f - 1 = (exp K - 1 : PowerSeries K).subst f`. Rewrite using `[← coe_substAlgHom hf', map_sub, map_one]`.

Rewrite using `[e, ← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hE) hf', log_subst_exp, subst_X hf']`.
-/
theorem fLog_fExp {f : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0) :
    fLog (fExp f) = f := by
  have hE : constantCoeff (exp K - 1 : PowerSeries K) = 0 := by simp
  have hf' : HasSubst f := HasSubst.of_constantCoeff_zero hf
  unfold fLog fExp
  have e : (exp K).subst f - 1 = (exp K - 1 : PowerSeries K).subst f := by
    rw [← coe_substAlgHom hf', map_sub, map_one]
  rw [e, ← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hE) hf',
    log_subst_exp, subst_X hf']

/- English proof (translation)
Establish `hg1 : MvPowerSeries.constantCoeff (g - 1) = 0` using `by simp [hg]`. Unfold `fLog`. Rewrite using `[constantCoeff_powerSeries_subst_mv_eq _ hg1]`. Conclude with `constantCoeff_log_eq_zero'`.
-/
theorem constantCoeff_fLog {g : MvPowerSeries ι K} (hg : MvPowerSeries.constantCoeff g = 1) :
    MvPowerSeries.constantCoeff (fLog g) = 0 := by
  have hg1 : MvPowerSeries.constantCoeff (g - 1) = 0 := by simp [hg]
  unfold fLog
  rw [constantCoeff_powerSeries_subst_mv_eq _ hg1]
  exact constantCoeff_log_eq_zero'

/- English proof (translation)
Establish `hg1 : MvPowerSeries.constantCoeff (g - 1) = 0` using `by simp [hg]`. Establish `hl : constantCoeff (log K) = 0` using `constantCoeff_log_eq_zero'`. Unfold `fExp fLog`. Rewrite using `[← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hl) (HasSubst.of_constantCoeff_zero hg1), exp_subst_log, one_add_X_subst (HasSubst.of_constantCoeff_zero hg1)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fExp_fLog {g : MvPowerSeries ι K} (hg : MvPowerSeries.constantCoeff g = 1) :
    fExp (fLog g) = g := by
  have hg1 : MvPowerSeries.constantCoeff (g - 1) = 0 := by simp [hg]
  have hl : constantCoeff (log K) = 0 := constantCoeff_log_eq_zero'
  unfold fExp fLog
  rw [← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hl)
    (HasSubst.of_constantCoeff_zero hg1), exp_subst_log,
    one_add_X_subst (HasSubst.of_constantCoeff_zero hg1)]
  ring

/- English proof (translation)
The claim follows from `pderiv_exp_subst_eq_mul_pderiv i hf`.
-/
theorem pd_fExp [Finite ι] (i : ι) {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) : pd i (fExp f) = fExp f * pd i f :=
  pderiv_exp_subst_eq_mul_pderiv i hf

/- English proof (translation)
Establish `hg1 : MvPowerSeries.constantCoeff (g - 1) = 0` using `by simp [hg]`. Establish `hD` using `Formalism.G.LogCR.pderiv_psubst hg1 (log K) i`. Establish `hL` using `one_add_mul_deriv_log_subst (HasSubst.of_constantCoeff_zero hg1)`. Establish `e : (1 : MvPowerSeries ι K) + (g - 1) = g` using `by ring`. Rewrite `hL` using `[e]`.

Unfold `fLog`. Use `show g * MvPowerSeries.pderiv K i (PowerSeries.subst (g - 1) (log K)) = MvPowerSeries.pderiv K i g`. Rewrite using `[hD, ← mul_assoc, hL, one_mul, map_sub, Derivation.map_one_eq_zero, sub_zero]`.
-/
theorem mul_pd_fLog [Finite ι] (i : ι) {g : MvPowerSeries ι K}
    (hg : MvPowerSeries.constantCoeff g = 1) : g * pd i (fLog g) = pd i g := by
  have hg1 : MvPowerSeries.constantCoeff (g - 1) = 0 := by simp [hg]
  have hD := Formalism.G.LogCR.pderiv_psubst hg1 (log K) i
  have hL := one_add_mul_deriv_log_subst (HasSubst.of_constantCoeff_zero hg1)
  have e : (1 : MvPowerSeries ι K) + (g - 1) = g := by ring
  rw [e] at hL
  unfold fLog
  show g * MvPowerSeries.pderiv K i (PowerSeries.subst (g - 1) (log K)) = MvPowerSeries.pderiv K i g
  rw [hD, ← mul_assoc, hL, one_mul, map_sub, Derivation.map_one_eq_zero, sub_zero]

/- English proof (translation)
The claim follows from `psubst_msubst _ hf (hasSubst_of_forall_constantCoeff_eq_zero hφ)`.
-/
theorem subst_fExp {κ : Type} [Finite ι] {φ : ι → MvPowerSeries κ K}
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst φ (fExp f) = fExp (MvPowerSeries.subst φ f) :=
  psubst_msubst _ hf (hasSubst_of_forall_constantCoeff_eq_zero hφ)

/- English proof (translation)
Establish `hg1 : MvPowerSeries.constantCoeff (g - 1) = 0` using `by simp [hg]`. Establish `hφ' : MvPowerSeries.HasSubst φ` using `hasSubst_of_forall_constantCoeff_eq_zero hφ`. Unfold `fLog`. Rewrite using `[psubst_msubst _ hg1 hφ', ← MvPowerSeries.coe_substAlgHom hφ', map_sub, map_one]`.
-/
theorem subst_fLog {κ : Type} [Finite ι] {φ : ι → MvPowerSeries κ K}
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) {g : MvPowerSeries ι K}
    (hg : MvPowerSeries.constantCoeff g = 1) :
    MvPowerSeries.subst φ (fLog g) = fLog (MvPowerSeries.subst φ g) := by
  have hg1 : MvPowerSeries.constantCoeff (g - 1) = 0 := by simp [hg]
  have hφ' : MvPowerSeries.HasSubst φ := hasSubst_of_forall_constantCoeff_eq_zero hφ
  unfold fLog
  rw [psubst_msubst _ hg1 hφ', ← MvPowerSeries.coe_substAlgHom hφ', map_sub, map_one]

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[dz, PowerSeries.coeff_derivative]`. Simplify using `only [prim, coeff_mk, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]`. Establish `hne : ((n : K) + 1) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero n`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
theorem dz_prim (f : PowerSeries K) : dz (prim f) = f := by
  ext n
  rw [dz, PowerSeries.coeff_derivative]
  simp only [prim, coeff_mk, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
  have hne : ((n : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

/- English proof (translation)
Rewrite using `[← coeff_zero_eq_constantCoeff_apply]`. Simplify using `[prim]`.
-/
theorem constantCoeff_prim (f : PowerSeries K) : constantCoeff (prim f) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [prim]

end Rules

/- English proof (translation)
Introduce `K _ _ ι`. Conclude with `⟨fun f g hf hg => fExp_add hf hg, fun f hf => ⟨constantCoeff_fExp hf, fLog_fExp hf⟩, fun g hg => ⟨constantCoeff_fLog hg, fExp_fLog hg⟩⟩`.
-/
theorem expLogIdentities : ExpLogRules := by
  intro K _ _ ι
  exact ⟨fun f g hf hg => fExp_add hf hg,
    fun f hf => ⟨constantCoeff_fExp hf, fLog_fExp hf⟩,
    fun g hg => ⟨constantCoeff_fLog hg, fExp_fLog hg⟩⟩

end Formalism.L2.Th1.B
