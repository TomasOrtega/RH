import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeGap.HCFdegRGap
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section

namespace PI.UnitaryGroupMassFormula.HCFdegRGap

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S MeasureTheory Matrix

/- English proof (translation)
Establish `hN2 : (2 : ℝ) ≤ N` using `by linarith`. Establish `hlog2` using `Real.log_two_gt_d9`. Establish `hlog : (0.69 : ℝ) < Real.log N` using `lt_of_lt_of_le (by norm_num at hlog2 ⊢; linarith) (Real.log_le_log (by norm_num) hN2)`. Establish `hep : 0 < ep0` using `lt_of_lt_of_le (Real.exp_pos _) he1`. Establish `hmin : 1 ≤ min p q` using `le_min hp hq`.

Establish `hpq : 1 ≤ p * q` using `by nlinarith`. Establish `hpq3 : (p * q) ^ 2 ≤ (p * q) ^ 3` using `by nlinarith`. Establish `hsum : p + q ≤ 2 * (p * q)` using `by nlinarith`. Use `set X := 8192 * min p q * (p * q) ^ 3 * Real.log N with hXdef`. Establish `hX : 8192 * 0.69 * (p * q) ^ 3 ≤ X`.

Establish `h3 : 0 ≤ (p * q) ^ 3` using `by positivity`. Establish `h4 : (1 : ℝ) * 0.69 ≤ min p q * Real.log N` using `mul_le_mul hmin hlog.le (by norm_num) (by linarith)`. Rewrite using `[hXdef]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hdiv : 4 * X ≤ X / ep0 ^ 2`.

Rewrite using `[le_div_iff₀ (by positivity)]`. Establish `h5 : ep0 ^ 2 ≤ 1 / 4` using `by nlinarith`. Establish `hXpos : 0 ≤ X` using `le_trans (by positivity) hX`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hN]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem gap_big {p q N ep0 h0 : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hN : N = p + q)
    (he1 : Real.exp (-N) ≤ ep0) (he2 : ep0 < 1 / 2)
    (hh : 8192 * min p q * (p * q) ^ 3 * Real.log N / ep0 ^ 2 ≤ h0) :
    32 * N * p * q + 2 < h0 := by
  have hN2 : (2 : ℝ) ≤ N := by linarith
  have hlog2 := Real.log_two_gt_d9
  have hlog : (0.69 : ℝ) < Real.log N :=
    lt_of_lt_of_le (by norm_num at hlog2 ⊢; linarith) (Real.log_le_log (by norm_num) hN2)
  have hep : 0 < ep0 := lt_of_lt_of_le (Real.exp_pos _) he1
  have hmin : 1 ≤ min p q := le_min hp hq
  have hpq : 1 ≤ p * q := by nlinarith
  have hpq3 : (p * q) ^ 2 ≤ (p * q) ^ 3 := by nlinarith
  have hsum : p + q ≤ 2 * (p * q) := by nlinarith
  set X := 8192 * min p q * (p * q) ^ 3 * Real.log N with hXdef
  have hX : 8192 * 0.69 * (p * q) ^ 3 ≤ X := by
    have h3 : 0 ≤ (p * q) ^ 3 := by positivity
    have h4 : (1 : ℝ) * 0.69 ≤ min p q * Real.log N := mul_le_mul hmin hlog.le (by norm_num) (by linarith)
    rw [hXdef]
    nlinarith
  have hdiv : 4 * X ≤ X / ep0 ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have h5 : ep0 ^ 2 ≤ 1 / 4 := by nlinarith
    have hXpos : 0 ≤ X := le_trans (by positivity) hX
    nlinarith
  rw [hN]
  nlinarith

/- English proof (translation)
Introduce `N ε lam ep0 h0 H _ _ σ w p q hp hq hlam hgap he1 he2 hh0 hDS hw`. Establish `hNpq : (N : ℝ) = p + q`. Use `Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N))) (fun a => ε a = true)` as an intermediate fact. Establish `h' : (Finset.univ.filter (fun a => ε a = true)).card + (Finset.univ.filter (fun a => ε a = false)).card = N` using `by simpa using this`. Use `show (N : ℝ) = ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) + ((Finset.univ.filter (fun a => ε a = false)).card : ℝ)`.

Establish `h''` using `congrArg (fun x : ℕ => (x : ℝ)) h'`. Move the coercions through the operations in `at h''`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbig : 32 * (N : ℝ) * p * q + 2 < h0` using `gap_big hp hq hNpq he1 he2 hh0`. Establish `hp' : 1 ≤ (Finset.univ.filter (fun a => ε a = true)).card`.

Establish `h : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => ε a = true)).card : ℝ)` using `hp`. Conclude with `h` after adjusting the coercions. Establish `hq' : 1 ≤ (Finset.univ.filter (fun a => ε a = false)).card`. Establish `h : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => ε a = false)).card : ℝ)` using `hq`. Conclude with `h` after adjusting the coercions.

Establish `hfw` using `hf N ε lam h0 hp' hq' hlam hgap hbig H σ w hDS hw`. Establish `hτ` using `Formalism.MainNotions.RT.finrank_lowK_eq hW hL ε lam hlam σ hDS`. Establish `hep : 0 < ep0` using `lt_of_lt_of_le (Real.exp_pos _) he1`. Establish `hnn` using `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.fdegHC_nonneg lam hlam`. Rewrite using `[hfw, hτ]`.

Use `⟨by nlinarith, ?_⟩` and prove the remaining obligations. Establish `hle` using `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.fdegHC_le_dTau ε lam hlam`. Establish `hτ0 : 0 < StandardLattice.dTau ε lam` using `StandardLattice.formalDegreeFactor_pos_of_strictAnti ε lam hlam.1`. Establish `hexp : p * q = ((StandardLattice.nPlus ε * StandardLattice.nMinus ε : ℕ) : ℝ)` using `by push_cast; rfl`. Rewrite using `[hexp, Real.rpow_natCast]`.

Establish `hp1 : 1 ≤ StandardLattice.nPlus ε`. Establish `h : (1 : ℝ) ≤ ((StandardLattice.nPlus ε : ℕ) : ℝ)` using `hp`. Conclude with `h` after adjusting the coercions. Establish `hq1 : 1 ≤ StandardLattice.nMinus ε`. Establish `h : (1 : ℝ) ≤ ((StandardLattice.nMinus ε : ℕ) : ℝ)` using `hq`.

Conclude with `h` after adjusting the coercions. Establish `hN` using `StandardLattice.count_plus_add_count_minus N ε`. Establish `hL1` using `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.lamAbs_ge_one lam hlam (by omega)`. Establish `hpq : (1 : ℝ) ≤ 3 * p * q` using `by nlinarith`. Establish `hX : StandardLattice.lamAbs lam ≤ 3 * p * q * StandardLattice.lamAbs lam` using `by nlinarith`.

Establish `hpow : StandardLattice.lamAbs lam ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) ≤ (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε)` using `pow_le_pow_left₀ (by linarith) hX _`. Establish `hpos : 0 ≤ (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε)` using `pow_nonneg (by nlinarith) _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem dimension_bound_of_gap (s : (n : ℕ) → (Fin n → Bool) → NNReal)
    (hf : ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (h : ℝ),
      1 ≤ (Finset.univ.filter (fun a => ε a = true)).card →
      1 ≤ (Finset.univ.filter (fun a => ε a = false)).card →
      Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.GapAtLeast ε lam h →
      32 * (N : ℝ) * ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) *
        ((Finset.univ.filter (fun a => ε a = false)).card : ℝ) + 2 < h →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H), IsDS ε lam σ → w ≠ 0 →
        fdegOf ((s N ε : ENNReal) • Formalism.REAL.muG ε) σ w = Formalism.QuantumDeterminants.fdegHC lam)
    (hW : DiscreteSeriesWeylDimension.WeylForK) (hL : DiscreteSeriesWeylDimension.LowKMultOne) : Formalism.MainNotions.RT.DiscreteSeriesDegreeBoundsAtScale s := by
  intro N ε lam ep0 h0 H _ _ σ w p q hp hq hlam hgap he1 he2 hh0 hDS hw
  have hNpq : (N : ℝ) = p + q := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N))) (fun a => ε a = true)
    have h' : (Finset.univ.filter (fun a => ε a = true)).card +
        (Finset.univ.filter (fun a => ε a = false)).card = N := by simpa using this
    show (N : ℝ) = ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) +
      ((Finset.univ.filter (fun a => ε a = false)).card : ℝ)
    have h'' := congrArg (fun x : ℕ => (x : ℝ)) h'
    push_cast at h''
    linarith
  have hbig : 32 * (N : ℝ) * p * q + 2 < h0 := gap_big hp hq hNpq he1 he2 hh0
  have hp' : 1 ≤ (Finset.univ.filter (fun a => ε a = true)).card := by
    have h : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) := hp
    exact_mod_cast h
  have hq' : 1 ≤ (Finset.univ.filter (fun a => ε a = false)).card := by
    have h : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => ε a = false)).card : ℝ) := hq
    exact_mod_cast h
  have hfw := hf N ε lam h0 hp' hq' hlam hgap hbig H σ w hDS hw
  have hτ := Formalism.MainNotions.RT.finrank_lowK_eq hW hL ε lam hlam σ hDS
  have hep : 0 < ep0 := lt_of_lt_of_le (Real.exp_pos _) he1
  have hnn := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.fdegHC_nonneg lam hlam
  rw [hfw, hτ]
  refine ⟨by nlinarith, ?_⟩
  have hle := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.fdegHC_le_dTau ε lam hlam
  have hτ0 : 0 < StandardLattice.dTau ε lam := StandardLattice.formalDegreeFactor_pos_of_strictAnti ε lam hlam.1
  have hexp : p * q = ((StandardLattice.nPlus ε * StandardLattice.nMinus ε : ℕ) : ℝ) := by push_cast; rfl
  rw [hexp, Real.rpow_natCast]
  have hp1 : 1 ≤ StandardLattice.nPlus ε := by
    have h : (1 : ℝ) ≤ ((StandardLattice.nPlus ε : ℕ) : ℝ) := hp
    exact_mod_cast h
  have hq1 : 1 ≤ StandardLattice.nMinus ε := by
    have h : (1 : ℝ) ≤ ((StandardLattice.nMinus ε : ℕ) : ℝ) := hq
    exact_mod_cast h
  have hN := StandardLattice.count_plus_add_count_minus N ε
  have hL1 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.lamAbs_ge_one lam hlam (by omega)
  have hpq : (1 : ℝ) ≤ 3 * p * q := by nlinarith
  have hX : StandardLattice.lamAbs lam ≤ 3 * p * q * StandardLattice.lamAbs lam := by nlinarith
  have hpow : StandardLattice.lamAbs lam ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) ≤
      (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) :=
    pow_le_pow_left₀ (by linarith) hX _
  have hpos : 0 ≤ (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) :=
    pow_nonneg (by nlinarith) _
  calc Formalism.QuantumDeterminants.fdegHC lam ≤ StandardLattice.dTau ε lam * StandardLattice.lamAbs lam ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) := hle
    _ ≤ StandardLattice.dTau ε lam * (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) :=
        mul_le_mul_of_nonneg_left hpow hτ0.le
    _ ≤ 4 * StandardLattice.dTau ε lam * (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) := by nlinarith

/- English proof (translation)
Introduce `cd s hc` and use `dimension_bound_of_gap s (hG cd s hc) hW hL`.
-/
theorem dimension_bound_of_gap_uniform (hG : HCFdegRGap) (hW : DiscreteSeriesWeylDimension.WeylForK) (hL : DiscreteSeriesWeylDimension.LowKMultOne) :
    Formalism.MainNotions.RT.DiscreteSeriesDegreeBoundsAllScales :=
  fun cd s hc => dimension_bound_of_gap s (hG cd s hc) hW hL

end PI.UnitaryGroupMassFormula.HCFdegRGap
