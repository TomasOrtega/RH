import Formalism.HermitianCurvature.StatementLE

namespace Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

/- English proof (translation)
Use function extensionality and compare the values at `ω a`. Simplify using `[mulF]`.
-/
theorem mulF_rpow_zero (B : Base) {A : Type} (u : Fn B A) : mulF B (fun x => x ^ (0:ℝ)) u = u := by
  funext ω a; simp [mulF]

/- English proof (translation)
Use function extensionality and compare the values at `ω a`. Establish `h1 : mulF B (fun _ => (1:ℝ)) u = u` using `by funext ω a; simp [mulF]`. Simplify using `[dS, conjS, h1]`.
-/
theorem dS_zero (B : Base) {A A' : Type} (T : Fn B A → Fn B A') (u : Fn B A) : dS B T u 0 = T u := by
  funext ω a
  have h1 : mulF B (fun _ => (1:ℝ)) u = u := by funext ω a; simp [mulF]
  simp [dS, conjS, h1]

/- English proof (translation)
Simplify using `only [pr, LE.sq, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Simplify using the standard rewrite rules.
-/
theorem pr_self (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (v : Fn B A) (ω : B.Ω) :
    pr B wt v v ω = ((LE.sq B wt v ω : ℝ) : ℂ) := by
  simp only [pr, LE.sq, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]; simp

/- English proof (translation)
Repeatedly rewrite using `[pr_self]`. Conclude with `integral_ofReal`.
-/
theorem int_pr_self (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (v : Fn B A) :
    ∫ ω, pr B wt v v ω ∂B.μ = ((∫ ω, LE.sq B wt v ω ∂B.μ : ℝ) : ℂ) := by
  simp_rw [pr_self]; exact integral_ofReal

/- English proof (translation)
Unfold `SmoothLog Cut.sc`. Conclude with `(c.smooth.comp (Real.contDiff_exp.div_const ε)).pow m`.
-/
theorem smoothLog_sc (c : Cut) (ε : ℝ) (m : ℕ) : SmoothLog (c.sc ε m) := by
  unfold SmoothLog Cut.sc
  exact (c.smooth.comp (Real.contDiff_exp.div_const ε)).pow m

/- English proof (translation)
Unfold `ld`. Establish `: Continuous (iteratedDeriv p (fun u : ℝ => φ (Real.exp u)))` using `h.continuous_iteratedDeriv p (by exact_mod_cast le_top)`. Conclude with `this.measurable.comp Real.measurable_log`.
-/
theorem meas_ld (p : ℕ) (φ : ℝ → ℝ) (h : SmoothLog φ) : Measurable (ld p φ) := by
  unfold ld
  have : Continuous (iteratedDeriv p (fun u : ℝ => φ (Real.exp u))) :=
    h.continuous_iteratedDeriv p (by exact_mod_cast le_top)
  exact this.measurable.comp Real.measurable_log

/- English proof (translation)
Use `hLeib B A A' T u M hJ hP φ hφ` as an intermediate fact. Repeatedly rewrite using `[this]`. Use `Finset.measurable_sum _ fun p _ => ?_` and prove the remaining obligations. Use `Measurable.div_const (Measurable.mul ?_ (hm p a)) _` and prove the remaining obligations. Conclude with `Complex.measurable_ofReal.comp ((meas_ld p φ hφ).comp B.G_meas)`.
-/
theorem measurable_apply_mulF_of_jetLocal (hLeib : Leibniz) (B : Base) {A A' : Type} (T : Fn B A → Fn B A') (u : Fn B A) (M : ℕ)
    (hJ : JetLocal B T u) (hP : PolyS B T u M) (hm : ∀ p a, Measurable fun ω => dS B T u p ω a)
    (φ : ℝ → ℝ) (hφ : SmoothLog φ) (a : A') : Measurable fun ω => T (mulF B φ u) ω a := by
  have := hLeib B A A' T u M hJ hP φ hφ
  simp_rw [this]
  refine Finset.measurable_sum _ fun p _ => ?_
  refine Measurable.div_const (Measurable.mul ?_ (hm p a)) _
  exact Complex.measurable_ofReal.comp ((meas_ld p φ hφ).comp B.G_meas)

/- English proof (translation)
Introduce `hLeib hCut hL2 hPair h5 h6 B X c M hpos hMeas hJet hPoly hCoef hPol hLoc hBeta`. Take `⟨hmu, hmC, hmd, hmS⟩` from `hMeas`. Establish `hI0 : Integrable (LE.sq B X.dw (X.gw X.u)) B.μ`. Use `hCoef 0` as an intermediate fact. Rewrite `this` using `[dS_zero]`. Then use the resulting hypothesis.

Establish `hmg : ∀ a, Measurable fun ω => X.gw X.u ω a`. Introduce `a`. Use `hmS 0 a` as an intermediate fact. Rewrite `this` using `[dS_zero]`. Then use the resulting hypothesis. Establish `L1` using `hL2 hLeib hCut B X.R X.ι X.gw X.u X.dw c M 1 le_rfl hpos hmd hJet hPoly hmS hCoef`.

Establish `L2` using `hL2 hLeib hCut B X.R X.ι X.gw X.u X.dw c M 2 (by norm_num) hpos hmd hJet hPoly hmS hCoef`. Establish `hmT : ∀ (m : ℕ) (ε : ℝ) (a : X.ι), Measurable fun ω => X.gw (mulF B (c.sc ε m) X.u) ω a` using `fun m ε a => measurable_apply_mulF_of_jetLocal hLeib B X.gw X.u M hJet hPoly hmS _ (smoothLog_sc c ε m) a`. Establish `hzero : Tendsto (fun ε : ℝ => ∫ ω, LE.sq B X.dw (fun ω a => X.gw X.u ω a - X.gw X.u ω a) ω ∂B.μ) (𝓝[>] 0) (𝓝 0)`. Simplify using `[LE.sq]`. Establish `P2` using `hPair B X.ι X.dw (X.gw X.u) (X.gw X.u) (fun _ => X.gw X.u) (fun ε => X.gw (mulF B (c.sc ε 2) X.u)) hpos hmd hmg hmg (fun _ a _ => hmg a) (fun ε a _ => hmT 2 ε a) hI0 hI0 (fun _ _ => hI0) L2.1 hzero L2.2`.

Establish `T5` using `h5 B X c ⟨hmu, hmC, hmd, hmS⟩ hBeta`. Establish `hev : (fun ε : ℝ => X.beta (X.Cw X.u) (mulF B (c.sc ε 2) X.u)) =ᶠ[𝓝[>] 0] fun ε : ℝ => ∫ ω, pr B X.dw (X.gw X.u) (X.gw (mulF B (c.sc ε 2) X.u)) ω ∂B.μ` using `by filter_upwards [self_mem_nhdsWithin] with ε hε`. Conclude with `h6 hCut B X c hJet hPol hLoc ε hε`. Establish `heq : ∫ ω, pr B X.dw (X.gw X.u) (X.gw X.u) ω ∂B.μ = X.beta (X.Cw X.u) X.u` using `tendsto_nhds_unique P2 (T5.congr' hev)`. Use `⟨hI0, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← int_pr_self]`. Conclude with `heq`. Establish `P1` using `hPair B X.ι X.dw (X.gw X.u) (X.gw X.u) (fun ε => X.gw (mulF B (c.sc ε 1) X.u)) (fun ε => X.gw (mulF B (c.sc ε 1) X.u)) hpos hmd hmg hmg (fun ε a _ => hmT 1 ε a) (fun ε a _ => hmT 1 ε a) hI0 hI0 L1.1 L1.1 L1.2 L1.2`. Rewrite `P1` using `[heq]`. Use `P1.congr' ?_` and prove the remaining obligations.

Use `filter_upwards [self_mem_nhdsWithin] with ε hε`. Conclude with `(hPol ε ε 1 1 hε hε le_rfl le_rfl).symm`.
-/
theorem lemmaEprimeFromSteps : LemmaEprimeFromSteps := by
  intro hLeib hCut hL2 hPair h5 h6 B X c M hpos hMeas hJet hPoly hCoef hPol hLoc hBeta
  obtain ⟨hmu, hmC, hmd, hmS⟩ := hMeas
  have hI0 : Integrable (LE.sq B X.dw (X.gw X.u)) B.μ := by
    have := hCoef 0; rwa [dS_zero] at this
  have hmg : ∀ a, Measurable fun ω => X.gw X.u ω a := by
    intro a; have := hmS 0 a; rwa [dS_zero] at this
  have L1 := hL2 hLeib hCut B X.R X.ι X.gw X.u X.dw c M 1 le_rfl hpos hmd hJet hPoly hmS hCoef
  have L2 := hL2 hLeib hCut B X.R X.ι X.gw X.u X.dw c M 2 (by norm_num) hpos hmd hJet hPoly hmS hCoef
  have hmT : ∀ (m : ℕ) (ε : ℝ) (a : X.ι), Measurable fun ω => X.gw (mulF B (c.sc ε m) X.u) ω a :=
    fun m ε a => measurable_apply_mulF_of_jetLocal hLeib B X.gw X.u M hJet hPoly hmS _ (smoothLog_sc c ε m) a
  have hzero : Tendsto (fun ε : ℝ => ∫ ω, LE.sq B X.dw (fun ω a => X.gw X.u ω a - X.gw X.u ω a) ω ∂B.μ)
      (𝓝[>] 0) (𝓝 0) := by
    simp [LE.sq]

  have P2 := hPair B X.ι X.dw (X.gw X.u) (X.gw X.u) (fun _ => X.gw X.u) (fun ε => X.gw (mulF B (c.sc ε 2) X.u))
    hpos hmd hmg hmg (fun _ a _ => hmg a) (fun ε a _ => hmT 2 ε a) hI0 hI0 (fun _ _ => hI0) L2.1 hzero L2.2
  have T5 := h5 B X c ⟨hmu, hmC, hmd, hmS⟩ hBeta
  have hev : (fun ε : ℝ => X.beta (X.Cw X.u) (mulF B (c.sc ε 2) X.u)) =ᶠ[𝓝[>] 0]
      fun ε : ℝ => ∫ ω, pr B X.dw (X.gw X.u) (X.gw (mulF B (c.sc ε 2) X.u)) ω ∂B.μ := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact h6 hCut B X c hJet hPol hLoc ε hε
  have heq : ∫ ω, pr B X.dw (X.gw X.u) (X.gw X.u) ω ∂B.μ = X.beta (X.Cw X.u) X.u :=
    tendsto_nhds_unique P2 (T5.congr' hev)
  refine ⟨hI0, ?_, ?_⟩
  · rw [← int_pr_self]; exact heq
  · have P1 := hPair B X.ι X.dw (X.gw X.u) (X.gw X.u) (fun ε => X.gw (mulF B (c.sc ε 1) X.u))
      (fun ε => X.gw (mulF B (c.sc ε 1) X.u))
      hpos hmd hmg hmg (fun ε a _ => hmT 1 ε a) (fun ε a _ => hmT 1 ε a) hI0 hI0 L1.1 L1.1 L1.2 L1.2
    rw [heq] at P1
    refine P1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hPol ε ε 1 1 hε hε le_rfl le_rfl).symm

/- English proof (translation)
Unfold `ld`. Consider the cases of `q with`. Consider the case `zero => simp`. Consider the case `succ n => simp [iteratedDeriv_succ']`.
-/
theorem ld_one (q : ℕ) (x : ℝ) : ld q (fun _ => (1:ℝ)) x = if q = 0 then 1 else 0 := by
  unfold ld
  cases q with
  | zero => simp
  | succ n => simp [iteratedDeriv_succ']

/- English proof (translation)
Introduce `hCut B X c hJet hPol hLoc ε hε`. Take `⟨m, cc, hc⟩` from `hJet`. Establish `hε1 : 0 < ε / 8` using `by positivity`. Establish `h1u : mulF B (fun _ => (1:ℝ)) X.u = X.u` using `by funext ω a; simp [mulF]`. Establish `hbig : ∀ ω, ε / 8 < B.G ω → ∀ a, X.gw (mulF B (c.sc (ε/8) 1) X.u) ω a = X.gw X.u ω a`.

Introduce `ω hω a`. Establish `e1` using `hc (c.sc (ε/8) 1) (smoothLog_sc c _ 1) ω a`. Establish `e2` using `hc (fun _ => (1:ℝ)) (by unfold SmoothLog; exact contDiff_const) ω a`. Rewrite `e2` using `[h1u]`. Rewrite using `[e1, e2]`.

Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Take `⟨C, hC⟩` from `hCut c 1 q le_rfl`. Rewrite using `[(hC (ε/8) (B.G ω) hε1 (B.G_pos ω)).2.2 hω, ld_one]`. Establish `hsmall : ∀ ω, B.G ω ≤ ε / 8 → ∀ a, X.gw (mulF B (c.sc ε 2) X.u) ω a = 0`. Introduce `ω hω a`.

Rewrite using `[hc (c.sc ε 2) (smoothLog_sc c _ 2) ω a]`. Use `Finset.sum_eq_zero fun q _ => ?_` and prove the remaining obligations. Take `⟨C, hC⟩` from `hCut c 2 q (by norm_num)`. Rewrite using `[(hC ε (B.G ω) hε (B.G_pos ω)).2.1 (by linarith)]; simp`. Establish `hsc : ∀ ω, B.G ω ≤ ε / 8 → c.sc ε 2 (B.G ω) = 0`.

Introduce `ω hω`. Establish `: B.G ω / ε ≤ 1 / 2` using `by rw [div_le_iff₀ hε]; linarith`. Simplify using `[Cut.sc, c.zero _ this]`. Combine the equalities or inequalities in the displayed calculation. Unfold `EP.beta`.

Use `integral_congr_ae (Eventually.of_forall fun ω => ?_)` and prove the remaining obligations. Simplify using `only [pr]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Break down `lt_or_ge (ε/8) (B.G ω) with h | h` into its components or cases. Rewrite using `[hLoc (ε/8) ω hε1 h a]`.

Simplify using `[mulF, hsc ω h]`. Use `_ = ∫ ω, pr B X.dw (X.gw (mulF B (c.sc (ε/8) 1) X.u)) (X.gw (mulF B (c.sc ε 2) X.u)) ω ∂B.μ := hPol (ε/8) ε 1 2 hε1 hε le_rfl (by norm_num)`. Use `_ = _ := by`. Use `integral_congr_ae (Eventually.of_forall fun ω => ?_)` and prove the remaining obligations. Simplify using `only [pr]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Break down `lt_or_ge (ε/8) (B.G ω) with h | h` into its components or cases. Rewrite using `[hbig ω h a]`. Simplify using `[hsmall ω h a]`.
-/
theorem epStep6 : EpStep6 := by
  intro hCut B X c hJet hPol hLoc ε hε
  obtain ⟨m, cc, hc⟩ := hJet
  have hε1 : 0 < ε / 8 := by positivity
  have h1u : mulF B (fun _ => (1:ℝ)) X.u = X.u := by funext ω a; simp [mulF]
  have hbig : ∀ ω, ε / 8 < B.G ω → ∀ a, X.gw (mulF B (c.sc (ε/8) 1) X.u) ω a = X.gw X.u ω a := by
    intro ω hω a
    have e1 := hc (c.sc (ε/8) 1) (smoothLog_sc c _ 1) ω a
    have e2 := hc (fun _ => (1:ℝ)) (by unfold SmoothLog; exact contDiff_const) ω a
    rw [h1u] at e2
    rw [e1, e2]
    refine Finset.sum_congr rfl fun q _ => ?_
    obtain ⟨C, hC⟩ := hCut c 1 q le_rfl
    rw [(hC (ε/8) (B.G ω) hε1 (B.G_pos ω)).2.2 hω, ld_one]
  have hsmall : ∀ ω, B.G ω ≤ ε / 8 → ∀ a, X.gw (mulF B (c.sc ε 2) X.u) ω a = 0 := by
    intro ω hω a
    rw [hc (c.sc ε 2) (smoothLog_sc c _ 2) ω a]
    refine Finset.sum_eq_zero fun q _ => ?_
    obtain ⟨C, hC⟩ := hCut c 2 q (by norm_num)
    rw [(hC ε (B.G ω) hε (B.G_pos ω)).2.1 (by linarith)]; simp
  have hsc : ∀ ω, B.G ω ≤ ε / 8 → c.sc ε 2 (B.G ω) = 0 := by
    intro ω hω
    have : B.G ω / ε ≤ 1 / 2 := by rw [div_le_iff₀ hε]; linarith
    simp [Cut.sc, c.zero _ this]
  calc X.beta (X.Cw X.u) (mulF B (c.sc ε 2) X.u)
      = X.beta (X.Cw (mulF B (c.sc (ε/8) 1) X.u)) (mulF B (c.sc ε 2) X.u) := by
        unfold EP.beta
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [pr]
        refine Finset.sum_congr rfl fun a _ => ?_
        rcases lt_or_ge (ε/8) (B.G ω) with h | h
        · rw [hLoc (ε/8) ω hε1 h a]
        · simp [mulF, hsc ω h]
    _ = ∫ ω, pr B X.dw (X.gw (mulF B (c.sc (ε/8) 1) X.u)) (X.gw (mulF B (c.sc ε 2) X.u)) ω ∂B.μ :=
        hPol (ε/8) ε 1 2 hε1 hε le_rfl (by norm_num)
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [pr]
        refine Finset.sum_congr rfl fun a _ => ?_
        rcases lt_or_ge (ε/8) (B.G ω) with h | h
        · rw [hbig ω h a]
        · simp [hsmall ω h a]

/- English proof (translation)
Introduce `h B X p N hpN hpos hMeas hNF q`. Take `⟨n, v, C, h1, h2, h3⟩` from `hNF q`. Take `⟨hmu, hmC, hmd, hmS⟩` from `hMeas`. Use `h B (Fin n) _ v C p N hpN ?_ ?_ h1 h2 h3` and prove the remaining obligations. Unfold `LE.sq`.

Use `Finset.measurable_sum _ fun a _ => ?_` and prove the remaining obligations. Conclude with `(hmd a).mul ((hmS q a).norm.pow_const 2)`. Introduce `ω`. Unfold `LE.sq`. Conclude with `Finset.sum_nonneg fun a _ => mul_nonneg (hpos ω a) (by positivity)`.
-/
theorem epCoefInt : EpCoefInt := by
  intro h B X p N hpN hpos hMeas hNF q
  obtain ⟨n, v, C, h1, h2, h3⟩ := hNF q
  obtain ⟨hmu, hmC, hmd, hmS⟩ := hMeas
  refine h B (Fin n) _ v C p N hpN ?_ ?_ h1 h2 h3
  · unfold LE.sq
    refine Finset.measurable_sum _ fun a _ => ?_
    exact (hmd a).mul ((hmS q a).norm.pow_const 2)
  · intro ω; unfold LE.sq
    exact Finset.sum_nonneg fun a _ => mul_nonneg (hpos ω a) (by positivity)

open Polynomial in
/- English proof (translation)
Proceed by induction on `p generalizing P with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[iteratedDeriv_succ']`. Establish `: deriv (fun s : ℝ => P.eval (s : ℂ)) = fun s : ℝ => (derivative P).eval (s : ℂ)`.

Use function extensionality and compare the values at `s`. Conclude with `((P.hasDerivAt (s : ℂ)).comp_ofReal).deriv`. Rewrite using `[this, ih]`. Simplify using `[Function.iterate_succ]`.
-/
theorem iterDeriv_poly (P : ℂ[X]) (p : ℕ) :
    iteratedDeriv p (fun s : ℝ => P.eval (s : ℂ)) = fun s : ℝ => ((derivative^[p]) P).eval (s : ℂ) := by
  induction p generalizing P with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have : deriv (fun s : ℝ => P.eval (s : ℂ)) = fun s : ℝ => (derivative P).eval (s : ℂ) := by
      funext s
      exact ((P.hasDerivAt (s : ℂ)).comp_ofReal).deriv
    rw [this, ih]
    simp [Function.iterate_succ]

open Polynomial in
noncomputable def mkP (m : ℕ) (c : ℕ → ℂ) : ℂ[X] := ∑ q ∈ range (m + 1), C (c q) * X ^ q

open Polynomial in
/- English proof (translation)
Unfold `mkP`. Rewrite using `[eval_finsetSum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[eval_mul, eval_C, eval_pow, eval_X, mul_comm]`.
-/
theorem mkP_eval (m : ℕ) (c : ℕ → ℂ) (z : ℂ) : (mkP m c).eval z = ∑ q ∈ range (m + 1), z ^ q * c q := by
  unfold mkP
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, mul_comm]

open Polynomial in
/- English proof (translation)
Simplify using `[mkP, finsetSum_coeff, coeff_C_mul, coeff_X_pow]`.
-/
theorem mkP_coeff (m : ℕ) (c : ℕ → ℂ) (k : ℕ) : (mkP m c).coeff k = if k < m + 1 then c k else 0 := by
  simp [mkP, finsetSum_coeff, coeff_C_mul, coeff_X_pow]

/- English proof (translation)
Unfold `ld`. Establish `: (fun u : ℝ => (Real.exp u) ^ s) = fun u : ℝ => Real.exp (s * u)`. Use function extensionality and compare the values at `u`. Rewrite using `[mul_comm, Real.exp_mul]`. Rewrite using `[this, iteratedDeriv_exp_const_mul]`.

Use `show s ^ q * Real.exp (s * Real.log x) = _`. Rewrite using `[mul_comm s, Real.exp_mul, Real.exp_log hx]`.
-/
theorem ld_rpow (q : ℕ) (s x : ℝ) (hx : 0 < x) : ld q (fun y => y ^ s) x = s ^ q * x ^ s := by
  unfold ld
  have : (fun u : ℝ => (Real.exp u) ^ s) = fun u : ℝ => Real.exp (s * u) := by
    funext u; rw [mul_comm, Real.exp_mul]
  rw [this, iteratedDeriv_exp_const_mul]
  show s ^ q * Real.exp (s * Real.log x) = _
  rw [mul_comm s, Real.exp_mul, Real.exp_log hx]

/- English proof (translation)
Unfold `SmoothLog`. Establish `: (fun u : ℝ => (Real.exp u) ^ s) = fun u : ℝ => Real.exp (s * u)`. Use function extensionality and compare the values at `u`. Rewrite using `[mul_comm, Real.exp_mul]`. Rewrite using `[this]`.

Conclude with `Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)`.
-/
theorem smoothLog_rpow (s : ℝ) : SmoothLog (fun y => y ^ s) := by
  unfold SmoothLog
  have : (fun u : ℝ => (Real.exp u) ^ s) = fun u : ℝ => Real.exp (s * u) := by
    funext u; rw [mul_comm, Real.exp_mul]
  rw [this]
  exact Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)

open Polynomial in
/- English proof (translation)
Introduce `B A A' T u d hJ hP φ hφ ω a`. Take `⟨m, c, hc⟩` from `hJ`. Take `⟨c', hc'⟩` from `hP`. Establish `hconj : ∀ s : ℝ, conjS B T u s ω a = (mkP m (fun q => c q ω a)).eval (s : ℂ)`. Introduce `s`.

Rewrite using `[mkP_eval]`. Unfold `conjS`. Rewrite using `[hc _ (smoothLog_rpow s) ω a, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[ld_rpow q s _ (B.G_pos ω)]`.

Establish `h1 : (B.G ω) ^ (-s) * (B.G ω) ^ s = 1`. Rewrite using `[← Real.rpow_add (B.G_pos ω)]`. Simplify using the standard rewrite rules. Establish `h2 : (((B.G ω) ^ (-s) : ℝ) : ℂ) * (((B.G ω) ^ s : ℝ) : ℂ) = 1`. Rewrite using `[← Complex.ofReal_mul, h1]`.

Simplify using the standard rewrite rules. Use `push_cast`. Take the linear combination `((s:ℂ) ^ q * c q ω a) * h2`. Establish `hPP : mkP m (fun q => c q ω a) = mkP d (fun q => c' q ω a)`. Use `Polynomial.eq_of_infinite_eval_eq _ _ ?_` and prove the remaining obligations.

Use `Set.Infinite.mono (s := Set.range (fun s : ℝ => (s : ℂ))) ?_ (Set.infinite_range_of_injective Complex.ofReal_injective)` and prove the remaining obligations. Introduce and unpack `_ ⟨s, rfl⟩`. Use `show _ = _`. Rewrite using `[← hconj s, hc' s ω a, mkP_eval]`. Establish `hdS : ∀ p, dS B T u p ω a = p.factorial * (mkP m (fun q => c q ω a)).coeff p`.

Introduce `p`. Unfold `dS`. Repeatedly rewrite using `[hconj]`. Rewrite using `[iterDeriv_poly]`. Simplify using `only [Complex.ofReal_zero]`.

Rewrite using `[← coeff_zero_eq_eval_zero, coeff_iterate_derivative]`. Simplify using `[Nat.descFactorial_self]`. Rewrite using `[hc φ hφ ω a]`. Establish `e1 : ∑ q ∈ range (m + 1), (ld q φ (B.G ω) : ℂ) * c q ω a = ∑ q ∈ range (max m d + 1), (ld q φ (B.G ω) : ℂ) * (mkP m (fun q => c q ω a)).coeff q`. Establish `hs` using `Finset.sum_subset (s₁ := range (m+1)) (s₂ := range (max m d + 1)) (f := fun q => (ld q φ (B.G ω) : ℂ) * (mkP m (fun q => c q ω a)).coeff q) (by intro q hq; simp only [Finset.mem_range] at *; omega) (by intro q _ hq; rw [mkP_coeff, if_neg (by simpa using hq)]; simp)`.

Rewrite using `[← hs]`. Use `Finset.sum_congr rfl fun q hq => ?_` and prove the remaining obligations. Rewrite using `[mkP_coeff, if_pos (Finset.mem_range.mp hq)]`. Establish `e2 : ∑ p ∈ range (d + 1), (ld p φ (B.G ω) : ℂ) * dS B T u p ω a / p.factorial = ∑ q ∈ range (max m d + 1), (ld q φ (B.G ω) : ℂ) * (mkP m (fun q => c q ω a)).coeff q`. Establish `hs` using `Finset.sum_subset (s₁ := range (d+1)) (s₂ := range (max m d + 1)) (f := fun q => (ld q φ (B.G ω) : ℂ) * (mkP m (fun q => c q ω a)).coeff q) (by intro q hq; simp only [Finset.mem_range] at *; omega) (by intro q _ hq; rw [hPP, mkP_coeff, if_neg (by simpa using hq)]; simp)`.

Rewrite using `[← hs]`. Use `Finset.sum_congr rfl fun q hq => ?_` and prove the remaining obligations. Rewrite using `[hdS]`. Establish `: (q.factorial : ℂ) ≠ 0` using `by exact_mod_cast q.factorial_ne_zero`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e1, e2]`.
-/
theorem leibniz : Leibniz := by
  intro B A A' T u d hJ hP φ hφ ω a
  obtain ⟨m, c, hc⟩ := hJ
  obtain ⟨c', hc'⟩ := hP
  have hconj : ∀ s : ℝ, conjS B T u s ω a = (mkP m (fun q => c q ω a)).eval (s : ℂ) := by
    intro s
    rw [mkP_eval]
    unfold conjS
    rw [hc _ (smoothLog_rpow s) ω a, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [ld_rpow q s _ (B.G_pos ω)]
    have h1 : (B.G ω) ^ (-s) * (B.G ω) ^ s = 1 := by
      rw [← Real.rpow_add (B.G_pos ω)]; simp
    have h2 : (((B.G ω) ^ (-s) : ℝ) : ℂ) * (((B.G ω) ^ s : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, h1]; simp
    push_cast
    linear_combination ((s:ℂ) ^ q * c q ω a) * h2
  have hPP : mkP m (fun q => c q ω a) = mkP d (fun q => c' q ω a) := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
    refine Set.Infinite.mono (s := Set.range (fun s : ℝ => (s : ℂ))) ?_
      (Set.infinite_range_of_injective Complex.ofReal_injective)
    rintro _ ⟨s, rfl⟩
    show _ = _
    rw [← hconj s, hc' s ω a, mkP_eval]
  have hdS : ∀ p, dS B T u p ω a = p.factorial * (mkP m (fun q => c q ω a)).coeff p := by
    intro p
    unfold dS
    simp_rw [hconj]
    rw [iterDeriv_poly]
    simp only [Complex.ofReal_zero]
    rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative]
    simp [Nat.descFactorial_self]
  rw [hc φ hφ ω a]
  have e1 : ∑ q ∈ range (m + 1), (ld q φ (B.G ω) : ℂ) * c q ω a =
      ∑ q ∈ range (max m d + 1), (ld q φ (B.G ω) : ℂ) * (mkP m (fun q => c q ω a)).coeff q := by
    have hs := Finset.sum_subset (s₁ := range (m+1)) (s₂ := range (max m d + 1))
      (f := fun q => (ld q φ (B.G ω) : ℂ) * (mkP m (fun q => c q ω a)).coeff q)
      (by intro q hq; simp only [Finset.mem_range] at *; omega)
      (by intro q _ hq; rw [mkP_coeff, if_neg (by simpa using hq)]; simp)
    rw [← hs]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [mkP_coeff, if_pos (Finset.mem_range.mp hq)]
  have e2 : ∑ p ∈ range (d + 1), (ld p φ (B.G ω) : ℂ) * dS B T u p ω a / p.factorial =
      ∑ q ∈ range (max m d + 1), (ld q φ (B.G ω) : ℂ) * (mkP m (fun q => c q ω a)).coeff q := by
    have hs := Finset.sum_subset (s₁ := range (d+1)) (s₂ := range (max m d + 1))
      (f := fun q => (ld q φ (B.G ω) : ℂ) * (mkP m (fun q => c q ω a)).coeff q)
      (by intro q hq; simp only [Finset.mem_range] at *; omega)
      (by intro q _ hq; rw [hPP, mkP_coeff, if_neg (by simpa using hq)]; simp)
    rw [← hs]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [hdS]
    have : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast q.factorial_ne_zero
    field_simp
  rw [e1, e2]

/- English proof (translation)
Introduce `ε σ hε v`. Unfold `th`. Establish `h1 : Real.exp v / (Real.exp v + ε) = (1 + ε * Real.exp (-v))⁻¹`. Rewrite using `[Real.exp_neg]`. Use `Real.exp_pos v` as an intermediate fact.

Clear the denominators using the available nonvanishing facts. Establish `h2 : 0 ≤ 1 + ε * Real.exp (-v)` using `by positivity`. Rewrite using `[h1, Real.inv_rpow h2, Real.rpow_neg h2]`.
-/
theorem thetaForm : ThetaForm := by
  intro ε σ hε v
  unfold th
  have h1 : Real.exp v / (Real.exp v + ε) = (1 + ε * Real.exp (-v))⁻¹ := by
    rw [Real.exp_neg]; have := Real.exp_pos v; field_simp
  have h2 : 0 ≤ 1 + ε * Real.exp (-v) := by positivity
  rw [h1, Real.inv_rpow h2, Real.rpow_neg h2]

/- English proof (translation)
Introduce `ε σ x hε hσ hx`. Unfold `th`. Establish `h0 : 0 < x / (x + ε)` using `by positivity`. Establish `h1 : x / (x + ε) ≤ 1` using `by rw [div_le_one (by positivity)]; linarith`. Conclude with `⟨Real.rpow_pos_of_pos h0 σ, Real.rpow_le_one h0.le h1 hσ⟩`.
-/
theorem thetaRange : ThetaRange := by
  intro ε σ x hε hσ hx
  unfold th
  have h0 : 0 < x / (x + ε) := by positivity
  have h1 : x / (x + ε) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  exact ⟨Real.rpow_pos_of_pos h0 σ, Real.rpow_le_one h0.le h1 hσ⟩

/- English proof (translation)
Simplify using `only [pr, mulF, Finset.mul_sum, map_mul, Complex.conj_ofReal]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pr_mulF (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (h u : Fn B A) (φ : ℝ → ℝ) (ω : B.Ω) :
    pr B wt h (mulF B φ u) ω = (φ (B.G ω) : ℂ) * pr B wt h u ω := by
  simp only [pr, mulF, Finset.mul_sum, map_mul, Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/- English proof (translation)
Introduce `B X c hMeas hBeta`. Take `⟨hmu, hmC, hmd, hmS⟩` from `hMeas`. Take `⟨hIu, hIh⟩` from `hBeta`. Unfold `EP.beta`. Repeatedly rewrite using `[pr_mulF]`.

Establish `hmpr : Measurable fun ω => pr B (fun _ _ => (1:ℝ)) (X.Cw X.u) X.u ω`. Unfold `pr`. Use `Finset.measurable_sum _ fun a _ => ?_` and prove the remaining obligations. Conclude with `(measurable_const.mul (hmC a)).mul (Complex.continuous_conj.measurable.comp (hmu a))`. Establish `hbd : ∀ ω, ‖pr B (fun _ _ => (1:ℝ)) (X.Cw X.u) X.u ω‖ ≤ LE.sq B (fun _ _ => 1) (X.Cw X.u) ω + LE.sq B (fun _ _ => 1) X.u ω`.

Introduce `ω`. Unfold `pr LE.sq`. Rewrite using `[← Finset.sum_add_distrib]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)` and prove the remaining obligations. Simplify using `only [Complex.ofReal_one, one_mul, norm_mul, RCLike.norm_conj]`.

Use polynomial arithmetic with `[sq_nonneg (‖X.Cw X.u ω a‖ - ‖X.u ω a‖), norm_nonneg (X.Cw X.u ω a), norm_nonneg (X.u ω a)]`. Use `tendsto_integral_filter_of_dominated_convergence (fun ω => LE.sq B (fun _ _ => 1) (X.Cw X.u) ω + LE.sq B (fun _ _ => 1) X.u ω) ?_ ?_ (hIh.add hIu) ?_` and prove the remaining obligations. Use `Eventually.of_forall fun ε => ?_` and prove the remaining obligations. Use `Measurable.aestronglyMeasurable (Measurable.mul ?_ hmpr)` and prove the remaining obligations. Use `Complex.measurable_ofReal.comp ?_` and prove the remaining obligations.

Unfold `Cut.sc`. Conclude with `((c.smooth.continuous.measurable.comp (B.G_meas.div_const ε)).pow_const 2)`. Use `Eventually.of_forall fun ε => Eventually.of_forall fun ω => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Establish `h1 : ‖((c.sc ε 2 (B.G ω) : ℝ) : ℂ)‖ ≤ 1`.

Rewrite using `[Complex.norm_real, Real.norm_eq_abs]`. Unfold `Cut.sc`. Rewrite using `[abs_of_nonneg (by positivity)]`. Conclude with `pow_le_one₀ (c.nonneg _) (c.le_one _)`. Combine the equalities or inequalities in the displayed calculation.

Use `Eventually.of_forall fun ω => ?_` and prove the remaining obligations. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Establish `: ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Set.Ioo 0 (B.G ω)` using `Ioo_mem_nhdsGT (B.G_pos ω)`. Use `filter_upwards [this] with ε hε`. Establish `h1 : 1 ≤ B.G ω / ε` using `by rw [le_div_iff₀ hε.1]; linarith [hε.2]`.

Simplify using `[Cut.sc, c.one _ h1]`.
-/
theorem epStep5 : EpStep5 := by
  intro B X c hMeas hBeta
  obtain ⟨hmu, hmC, hmd, hmS⟩ := hMeas
  obtain ⟨hIu, hIh⟩ := hBeta
  unfold EP.beta
  simp_rw [pr_mulF]
  have hmpr : Measurable fun ω => pr B (fun _ _ => (1:ℝ)) (X.Cw X.u) X.u ω := by
    unfold pr
    refine Finset.measurable_sum _ fun a _ => ?_
    exact (measurable_const.mul (hmC a)).mul (Complex.continuous_conj.measurable.comp (hmu a))
  have hbd : ∀ ω, ‖pr B (fun _ _ => (1:ℝ)) (X.Cw X.u) X.u ω‖ ≤
      LE.sq B (fun _ _ => 1) (X.Cw X.u) ω + LE.sq B (fun _ _ => 1) X.u ω := by
    intro ω
    unfold pr LE.sq
    rw [← Finset.sum_add_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    simp only [Complex.ofReal_one, one_mul, norm_mul, RCLike.norm_conj]
    nlinarith [sq_nonneg (‖X.Cw X.u ω a‖ - ‖X.u ω a‖), norm_nonneg (X.Cw X.u ω a), norm_nonneg (X.u ω a)]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ω => LE.sq B (fun _ _ => 1) (X.Cw X.u) ω + LE.sq B (fun _ _ => 1) X.u ω) ?_ ?_ (hIh.add hIu) ?_
  · refine Eventually.of_forall fun ε => ?_
    refine Measurable.aestronglyMeasurable (Measurable.mul ?_ hmpr)
    refine Complex.measurable_ofReal.comp ?_
    unfold Cut.sc
    exact ((c.smooth.continuous.measurable.comp (B.G_meas.div_const ε)).pow_const 2)
  · refine Eventually.of_forall fun ε => Eventually.of_forall fun ω => ?_
    rw [norm_mul]
    have h1 : ‖((c.sc ε 2 (B.G ω) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      unfold Cut.sc
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_one₀ (c.nonneg _) (c.le_one _)
    calc _ ≤ 1 * ‖pr B (fun _ _ => (1:ℝ)) (X.Cw X.u) X.u ω‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hbd ω
  · refine Eventually.of_forall fun ω => ?_
    refine tendsto_const_nhds.congr' ?_
    have : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Set.Ioo 0 (B.G ω) := Ioo_mem_nhdsGT (B.G_pos ω)
    filter_upwards [this] with ε hε
    have h1 : 1 ≤ B.G ω / ε := by rw [le_div_iff₀ hε.1]; linarith [hε.2]
    simp [Cut.sc, c.one _ h1]

/- English proof (translation)
Introduce `B T _ f v C p N hpN hmf hf0 hfb h1 h2`. Establish `hg : Integrable (fun ω => |C| * ∑ t, (‖v t ω‖ ^ 2 + (B.G ω) ^ (2 * p) * ‖v t ω‖ ^ 2)) B.μ` using `(integrable_finset_sum _ fun t _ => (h1 t).add (h2 t)).const_mul _`. Use `hg.mono' hmf.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (hf0 ω)]`. Use `(hfb ω).trans ?_` and prove the remaining obligations.

Establish `hG` using `B.G_pos ω`. Establish `hexp : (0:ℝ) ≤ (2 * p : ℝ) - N`. Establish `: (N:ℝ) ≤ 2 * p` using `by exact_mod_cast hpN`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpow : (B.G ω) ^ ((2 * p : ℝ) - N) ≤ 1 + (B.G ω) ^ (2 * p)`.

Break down `le_total (B.G ω) 1 with h | h` into its components or cases. Use `Real.rpow_le_one hG.le h hexp` as an intermediate fact. Establish `h' : 0 ≤ (B.G ω) ^ (2 * p)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Use `Real.rpow_le_rpow_of_exponent_le h (show (2 * p : ℝ) - N ≤ ((2 * p : ℕ) : ℝ) by push_cast; linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])` as an intermediate fact.

Rewrite `this` using `[Real.rpow_natCast]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hS : 0 ≤ ∑ t, ‖v t ω‖ ^ 2` using `Finset.sum_nonneg fun t _ => by positivity`. Establish `hr : 0 ≤ (B.G ω) ^ ((2 * p : ℝ) - N)` using `Real.rpow_nonneg hG.le _`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_assoc, Finset.mul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem derived_energy_L2 : WeightedIntegrable := by
  intro B T _ f v C p N hpN hmf hf0 hfb h1 h2
  have hg : Integrable (fun ω => |C| * ∑ t, (‖v t ω‖ ^ 2 + (B.G ω) ^ (2 * p) * ‖v t ω‖ ^ 2)) B.μ :=
    (integrable_finset_sum _ fun t _ => (h1 t).add (h2 t)).const_mul _
  refine hg.mono' hmf.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ω)]
  refine (hfb ω).trans ?_
  have hG := B.G_pos ω
  have hexp : (0:ℝ) ≤ (2 * p : ℝ) - N := by
    have : (N:ℝ) ≤ 2 * p := by exact_mod_cast hpN
    linarith
  have hpow : (B.G ω) ^ ((2 * p : ℝ) - N) ≤ 1 + (B.G ω) ^ (2 * p) := by
    rcases le_total (B.G ω) 1 with h | h
    · have := Real.rpow_le_one hG.le h hexp
      have h' : 0 ≤ (B.G ω) ^ (2 * p) := by positivity
      linarith
    · have := Real.rpow_le_rpow_of_exponent_le h (show (2 * p : ℝ) - N ≤ ((2 * p : ℕ) : ℝ) by push_cast; linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])
      rw [Real.rpow_natCast] at this
      linarith
  have hS : 0 ≤ ∑ t, ‖v t ω‖ ^ 2 := Finset.sum_nonneg fun t _ => by positivity
  have hr : 0 ≤ (B.G ω) ^ ((2 * p : ℝ) - N) := Real.rpow_nonneg hG.le _
  calc C * (B.G ω) ^ ((2 * p : ℝ) - N) * ∑ t, ‖v t ω‖ ^ 2
      ≤ |C| * (B.G ω) ^ ((2 * p : ℝ) - N) * ∑ t, ‖v t ω‖ ^ 2 := by
        gcongr; exact le_abs_self C
    _ ≤ |C| * (1 + (B.G ω) ^ (2 * p)) * ∑ t, ‖v t ω‖ ^ 2 := by gcongr
    _ = _ := by
        rw [mul_assoc, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun t _ => ?_
        ring

/- English proof (translation)
Introduce `ε σ hε`. Unfold `SmoothLog`. Establish `: (fun u : ℝ => th ε σ (Real.exp u)) = fun u : ℝ => (1 + ε * Real.exp (-u)) ^ (-σ)`. Use function extensionality and compare the values at `u`. Conclude with `thetaForm ε σ hε u`.

Rewrite using `[this]`. Use `ContDiff.rpow_const_of_ne ?_ ?_` and prove the remaining obligations. Conclude with `contDiff_const.add (contDiff_const.mul (Real.contDiff_exp.comp contDiff_neg))`. Introduce `u`. Check the signs of the components of the expression.
-/
theorem thetaSmooth : ThetaSmooth := by
  intro ε σ hε
  unfold SmoothLog
  have : (fun u : ℝ => th ε σ (Real.exp u)) = fun u : ℝ => (1 + ε * Real.exp (-u)) ^ (-σ) := by
    funext u; exact thetaForm ε σ hε u
  rw [this]
  refine ContDiff.rpow_const_of_ne ?_ ?_
  · exact contDiff_const.add (contDiff_const.mul (Real.contDiff_exp.comp contDiff_neg))
  · intro u; positivity

/- English proof (translation)
Introduce `σ ε ε' x hσ hε hεε hx`. Unfold `th`. Establish `h1 : 0 < x + ε` using `by linarith`. Establish `h2 : 0 < x + ε'` using `by linarith`. Use `Real.rpow_le_rpow (div_nonneg hx.le h2.le) ?_ hσ` and prove the remaining obligations.

Conclude with `div_le_div_of_nonneg_left hx.le h1 (by linarith)`.
-/
theorem thetaMono : ThetaMono := by
  intro σ ε ε' x hσ hε hεε hx
  unfold th
  have h1 : 0 < x + ε := by linarith
  have h2 : 0 < x + ε' := by linarith
  refine Real.rpow_le_rpow (div_nonneg hx.le h2.le) ?_ hσ
  exact div_le_div_of_nonneg_left hx.le h1 (by linarith)

/- English proof (translation)
Introduce `hC σ ε hσ hε p x hx`. Unfold `ld`. Establish `: (fun u : ℝ => th ε σ (Real.exp u)) = fun u : ℝ => (1 + ε * Real.exp (-u)) ^ (-σ)`. Use function extensionality and compare the values at `u`. Conclude with `thetaForm ε σ hε u`.

Rewrite using `[this]`. Establish `h` using `hC σ ε hσ hε p (Real.log x)`. Rewrite `h` using `[← thetaForm ε σ hε (Real.log x), Real.exp_log hx]`. Then use the resulting hypothesis.
-/
theorem thetaBound : ThetaBound := by
  intro hC σ ε hσ hε p x hx
  unfold ld
  have : (fun u : ℝ => th ε σ (Real.exp u)) = fun u : ℝ => (1 + ε * Real.exp (-u)) ^ (-σ) := by
    funext u; exact thetaForm ε σ hε u
  rw [this]
  have h := hC σ ε hσ hε p (Real.log x)
  rwa [← thetaForm ε σ hε (Real.log x), Real.exp_log hx] at h

/- English proof (translation)
Consider the cases of `p with`. Consider the case `zero => simp`. Consider the case `succ n => simp [iteratedDeriv_succ']`.
-/
theorem iterDeriv_const' (p : ℕ) (k t : ℝ) : iteratedDeriv p (fun _ : ℝ => k) t = if p = 0 then k else 0 := by
  cases p with
  | zero => simp
  | succ n => simp [iteratedDeriv_succ']

/- English proof (translation)
Introduce `c m p hm`. Use `set h : ℝ → ℝ := fun t => c.χ (Real.exp t) ^ m with hh`. Establish `hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h` using `(c.smooth.comp Real.contDiff_exp).pow m`. Establish `hcont : Continuous (iteratedDeriv p h)` using `hsm.continuous_iteratedDeriv p (by exact_mod_cast le_top)`. Establish `hlow : ∀ t, t < Real.log (1/2) → iteratedDeriv p h t = 0`.

Introduce `t ht`. Establish `: h =ᶠ[𝓝 t] fun _ => (0:ℝ)` using `by filter_upwards [Iio_mem_nhds ht] with s hs`. Establish `: Real.exp s ≤ 1/2`. Use `Real.exp_lt_exp.mpr hs` as an intermediate fact. Rewrite using `[Real.exp_log (by norm_num)] at this; exact this.le`.

Simplify using `only [hh, c.zero _ this]`. Conclude with `zero_pow (by omega)`. Rewrite using `[this.iteratedDeriv_eq p, iterDeriv_const']`. Simplify using the standard rewrite rules. Establish `hhigh : ∀ t, 0 < t → iteratedDeriv p h t = if p = 0 then 1 else 0`.

Introduce `t ht`. Establish `: h =ᶠ[𝓝 t] fun _ => (1:ℝ)` using `by filter_upwards [Ioi_mem_nhds ht] with s hs`. Establish `: 1 ≤ Real.exp s` using `Real.one_le_exp (le_of_lt hs)`. Simplify using `[hh, c.one _ this]`. Rewrite using `[this.iteratedDeriv_eq p, iterDeriv_const']`.

Take `⟨C0, hC0⟩` from `(isCompact_Icc (a := Real.log (1/2)) (b := 0)).exists_bound_of_continuousOn hcont.continuousOn`. Establish `hbd : ∀ t, |iteratedDeriv p h t| ≤ max C0 1`. Introduce `t`. Break down `lt_or_ge t (Real.log (1/2)) with h1 | h1` into its components or cases. Rewrite using `[hlow t h1]`.

Simplify using the standard rewrite rules. Break down `lt_or_ge 0 t with h2 | h2` into its components or cases. Apply the tactic sequence `rw [hhigh t h2]; split_ifs <;> simp`. Conclude with `(hC0 t ⟨h1, h2⟩).trans (le_max_left _ _)`. Establish `key : ∀ ε x : ℝ, 0 < ε → ld p (c.sc ε m) x = iteratedDeriv p h (Real.log x - Real.log ε)`.

Introduce `ε x hε`. Unfold `ld`. Establish `: (fun u : ℝ => c.sc ε m (Real.exp u)) = fun u : ℝ => h (u - Real.log ε)`. Use function extensionality and compare the values at `u`. Simplify using `only [hh, Cut.sc]`.

Rewrite using `[Real.exp_sub, Real.exp_log hε]`. Rewrite using `[this, iteratedDeriv_comp_sub_const]`. Use `⟨max C0 1, fun ε x hε hx => ?_⟩` and prove the remaining obligations. Rewrite using `[key ε x hε]`. Use `⟨hbd _, fun hlt => hlow _ ?_, fun hlt => hhigh _ ?_⟩` and prove the remaining obligations.

Rewrite using `[← Real.log_div hx.ne' hε.ne']`. Use `Real.log_lt_log (by positivity) ?_` and prove the remaining obligations. Rewrite using `[div_lt_iff₀ hε]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `Real.log_lt_log hε hlt` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cutBound : CutBound := by
  intro c m p hm
  set h : ℝ → ℝ := fun t => c.χ (Real.exp t) ^ m with hh
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := (c.smooth.comp Real.contDiff_exp).pow m
  have hcont : Continuous (iteratedDeriv p h) := hsm.continuous_iteratedDeriv p (by exact_mod_cast le_top)
  have hlow : ∀ t, t < Real.log (1/2) → iteratedDeriv p h t = 0 := by
    intro t ht
    have : h =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      have : Real.exp s ≤ 1/2 := by
        have := Real.exp_lt_exp.mpr hs
        rw [Real.exp_log (by norm_num)] at this; exact this.le
      simp only [hh, c.zero _ this]
      exact zero_pow (by omega)
    rw [this.iteratedDeriv_eq p, iterDeriv_const']; simp
  have hhigh : ∀ t, 0 < t → iteratedDeriv p h t = if p = 0 then 1 else 0 := by
    intro t ht
    have : h =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      have : 1 ≤ Real.exp s := Real.one_le_exp (le_of_lt hs)
      simp [hh, c.one _ this]
    rw [this.iteratedDeriv_eq p, iterDeriv_const']
  obtain ⟨C0, hC0⟩ := (isCompact_Icc (a := Real.log (1/2)) (b := 0)).exists_bound_of_continuousOn hcont.continuousOn
  have hbd : ∀ t, |iteratedDeriv p h t| ≤ max C0 1 := by
    intro t
    rcases lt_or_ge t (Real.log (1/2)) with h1 | h1
    · rw [hlow t h1]; simp
    · rcases lt_or_ge 0 t with h2 | h2
      · rw [hhigh t h2]; split_ifs <;> simp
      · exact (hC0 t ⟨h1, h2⟩).trans (le_max_left _ _)
  have key : ∀ ε x : ℝ, 0 < ε → ld p (c.sc ε m) x = iteratedDeriv p h (Real.log x - Real.log ε) := by
    intro ε x hε
    unfold ld
    have : (fun u : ℝ => c.sc ε m (Real.exp u)) = fun u : ℝ => h (u - Real.log ε) := by
      funext u; simp only [hh, Cut.sc]; rw [Real.exp_sub, Real.exp_log hε]
    rw [this, iteratedDeriv_comp_sub_const]
  refine ⟨max C0 1, fun ε x hε hx => ?_⟩
  rw [key ε x hε]
  refine ⟨hbd _, fun hlt => hlow _ ?_, fun hlt => hhigh _ ?_⟩
  · rw [← Real.log_div hx.ne' hε.ne']
    refine Real.log_lt_log (by positivity) ?_
    rw [div_lt_iff₀ hε]; linarith
  · have := Real.log_lt_log hε hlt; linarith

/- English proof (translation)
Unfold `LE.sq`. Rewrite using `[Finset.sum_comm, Finset.mul_sum]`. Use `Finset.sum_le_sum fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum]`. Establish `h1 : ‖∑ p ∈ range (M + 1), (k p ω : ℂ) * D p ω a / p.factorial‖ ≤ ∑ p ∈ range (M+1), K * ‖D p ω a‖`.

Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)` and prove the remaining obligations. Rewrite using `[norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]`. Establish `hf : (1:ℝ) ≤ p.factorial` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr p.factorial_ne_zero`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : (∑ p ∈ range (M+1), K * ‖D p ω a‖) ^ 2 ≤ (M + 1) * ∑ p ∈ range (M+1), (K * ‖D p ω a‖) ^ 2`.

Use `sq_sum_le_card_mul_sum_sq (s := range (M+1)) (f := fun p => K * ‖D p ω a‖)` as an intermediate fact. Simplify using `using this`. Establish `h3 : ‖∑ p ∈ range (M + 1), (k p ω : ℂ) * D p ω a / p.factorial‖ ^ 2 ≤ (M + 1) * K ^ 2 * ∑ p ∈ range (M+1), ‖D p ω a‖ ^ 2`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sq_comb_le (B : Base) {A' : Type} [Fintype A'] (wt : B.Ω → A' → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a)
    (D : ℕ → Fn B A') (M : ℕ) (k : ℕ → B.Ω → ℝ) (K : ℝ) (hK : ∀ p ∈ range (M+1), ∀ ω, |k p ω| ≤ K) (ω : B.Ω) :
    LE.sq B wt (fun ω a => ∑ p ∈ range (M + 1), (k p ω : ℂ) * D p ω a / p.factorial) ω ≤
      (M + 1) * K ^ 2 * ∑ p ∈ range (M + 1), LE.sq B wt (D p) ω := by
  unfold LE.sq
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.mul_sum]
  have h1 : ‖∑ p ∈ range (M + 1), (k p ω : ℂ) * D p ω a / p.factorial‖ ≤ ∑ p ∈ range (M+1), K * ‖D p ω a‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
    have hf : (1:ℝ) ≤ p.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr p.factorial_ne_zero
    calc |k p ω| * ‖D p ω a‖ / p.factorial ≤ |k p ω| * ‖D p ω a‖ := div_le_self (by positivity) hf
      _ ≤ K * ‖D p ω a‖ := mul_le_mul_of_nonneg_right (hK p hp ω) (norm_nonneg _)
  have h2 : (∑ p ∈ range (M+1), K * ‖D p ω a‖) ^ 2 ≤ (M + 1) * ∑ p ∈ range (M+1), (K * ‖D p ω a‖) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := range (M+1)) (f := fun p => K * ‖D p ω a‖)
    simpa using this
  have h3 : ‖∑ p ∈ range (M + 1), (k p ω : ℂ) * D p ω a / p.factorial‖ ^ 2 ≤
      (M + 1) * K ^ 2 * ∑ p ∈ range (M+1), ‖D p ω a‖ ^ 2 := by
    calc _ ≤ (∑ p ∈ range (M+1), K * ‖D p ω a‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
      _ = _ := by simp_rw [mul_pow]; rw [← Finset.mul_sum]; ring
  calc wt ω a * _ ≤ wt ω a * ((M + 1) * K ^ 2 * ∑ p ∈ range (M+1), ‖D p ω a‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (hpos ω a)
    _ = _ := by ring

/- English proof (translation)
Unfold `LE.sq`. Conclude with `Finset.measurable_sum _ fun a _ => (h1 a).mul ((h2 a).norm.pow_const 2)`.
-/
theorem meas_sq (B : Base) {A' : Type} [Fintype A'] (wt : B.Ω → A' → ℝ) (v : Fn B A')
    (h1 : ∀ a, Measurable fun ω => wt ω a) (h2 : ∀ a, Measurable fun ω => v ω a) : Measurable (LE.sq B wt v) := by
  unfold LE.sq
  exact Finset.measurable_sum _ fun a _ => (h1 a).mul ((h2 a).norm.pow_const 2)

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun a _ => mul_nonneg (hpos ω a) (by positivity)`.
-/
theorem sq_nonneg' (B : Base) {A' : Type} [Fintype A'] (wt : B.Ω → A' → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a) (v : Fn B A') (ω) :
    0 ≤ LE.sq B wt v ω := Finset.sum_nonneg fun a _ => mul_nonneg (hpos ω a) (by positivity)

/- English proof (translation)
Introduce `hLeib hCut B A A' _ T u wt c M m hm hpos hmw hJ hP hmS hI`. Use `choose Cf hCf using fun p => hCut c m p hm`. Use `set K : ℝ := (∑ p ∈ range (M+1), |Cf p|) + 1 with hKdef`. Establish `hCK : ∀ p ∈ range (M+1), |Cf p| ≤ K - 1`. Introduce `p hp`.

Use `Finset.single_le_sum (f := fun p => |Cf p|) (fun i _ => abs_nonneg _) hp` as an intermediate fact. Simplify using `only [hKdef]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hg : Integrable (fun ω => ((M:ℝ) + 1) * K ^ 2 * ∑ p ∈ range (M + 1), LE.sq B wt (dS B T u p) ω) B.μ` using `(integrable_finsetSum _ fun p _ => hI p).const_mul _`. Establish `hform : ∀ ε : ℝ, T (mulF B (c.sc ε m) u) = fun ω a => ∑ p ∈ range (M + 1), ((ld p (c.sc ε m) (B.G ω) : ℝ) : ℂ) * dS B T u p ω a / p.factorial`.

Introduce `ε`. Use function extensionality and compare the values at `ω a`. Conclude with `hLeib B A A' T u M hJ hP _ (smoothLog_sc c ε m) ω a`. Establish `hmT : ∀ (ε : ℝ) a, Measurable fun ω => T (mulF B (c.sc ε m) u) ω a`. Introduce `ε a`.

Rewrite using `[hform]`. Use `Finset.measurable_sum _ fun p _ => ?_` and prove the remaining obligations. Use `Measurable.div_const (Measurable.mul ?_ (hmS p a)) _` and prove the remaining obligations. Conclude with `Complex.measurable_ofReal.comp ((meas_ld p _ (smoothLog_sc c ε m)).comp B.G_meas)`. Establish `hmTu : ∀ a, Measurable fun ω => T u ω a`.

Introduce `a`. Use `hmS 0 a` as an intermediate fact. Rewrite `this` using `[dS_zero]`. Then use the resulting hypothesis. Prove the components needed by the constructor for the conclusion. Introduce `ε hε`.

Use `hg.mono' (meas_sq B wt _ hmw (hmT ε)).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (sq_nonneg' B wt hpos _ ω), hform]`. Use `sq_comb_le B wt hpos (dS B T u) M (fun p ω => ld p (c.sc ε m) (B.G ω)) K ?_ ω` and prove the remaining obligations. Introduce `p hp ω`. Use `(hCf p ε (B.G ω) hε (B.G_pos ω)).1` as an intermediate fact.

Establish `h2` using `hCK p hp`. Combine the linear relations using `[le_abs_self (Cf p)]`. Establish `hdiff : ∀ ε : ℝ, (fun ω a => T (mulF B (c.sc ε m) u) ω a - T u ω a) = fun ω a => ∑ p ∈ range (M + 1), ((ld p (c.sc ε m) (B.G ω) - (if p = 0 then 1 else 0) : ℝ) : ℂ) * dS B T u p ω a / p.factorial`. Introduce `ε`. Use function extensionality and compare the values at `ω a`.

Rewrite using `[hform]`. Establish `: T u ω a = ∑ p ∈ range (M+1), (((if p = 0 then 1 else 0 : ℝ)) : ℂ) * dS B T u p ω a / p.factorial`. Rewrite using `[Finset.sum_eq_single 0]`. Simplify using `[dS_zero]`. Introduce `p _ hp`.

Simplify using `[hp]`. Introduce `h`. Simplify using `at h`. Rewrite using `[this, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. It suffices to establish `key : Tendsto (fun ε : ℝ => ∫ ω, LE.sq B wt (fun ω a => T (mulF B (c.sc ε m) u) ω a - T u ω a) ω ∂B.μ) (𝓝[>] 0) (𝓝 (∫ _ω, (0:ℝ) ∂B.μ)) by simpa using key`. Use `tendsto_integral_filter_of_dominated_convergence (fun ω => ((M:ℝ) + 1) * K ^ 2 * ∑ p ∈ range (M + 1), LE.sq B wt (dS B T u p) ω) ?_ ?_ hg ?_` and prove the remaining obligations. Use `Eventually.of_forall fun ε => ?_` and prove the remaining obligations.

Conclude with `(meas_sq B wt _ hmw (fun a => (hmT ε a).sub (hmTu a))).aestronglyMeasurable`. Use `filter_upwards [self_mem_nhdsWithin] with ε hε`. Use `Eventually.of_forall fun ω => ?_` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (sq_nonneg' B wt hpos _ ω), hdiff]`. Use `sq_comb_le B wt hpos (dS B T u) M (fun p ω => ld p (c.sc ε m) (B.G ω) - (if p = 0 then 1 else 0)) K ?_ ω` and prove the remaining obligations.

Introduce `p hp ω`. Establish `h1` using `(hCf p ε (B.G ω) hε (B.G_pos ω)).1`. Establish `h2` using `hCK p hp`. Apply the tactic sequence `have h3 : |(if p = 0 then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> simp`. Combine the equalities or inequalities in the displayed calculation.

Use `Eventually.of_forall fun ω => ?_` and prove the remaining obligations. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Establish `: ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Set.Ioo 0 (B.G ω)` using `Ioo_mem_nhdsGT (B.G_pos ω)`. Use `filter_upwards [this] with ε hε`. Rewrite using `[hdiff]`.

Unfold `LE.sq`. Use `symm`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Establish `: ∑ p ∈ range (M + 1), ((ld p (c.sc ε m) (B.G ω) - (if p = 0 then 1 else 0) : ℝ) : ℂ) * dS B T u p ω a / p.factorial = 0`. Use `Finset.sum_eq_zero fun p _ => ?_` and prove the remaining obligations.

Rewrite using `[(hCf p ε (B.G ω) hε.1 (B.G_pos ω)).2.2 hε.2]`. Simplify using the standard rewrite rules. Use `beta_reduce`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem limit_L2 : CutoffLimitInL2 := by
  intro hLeib hCut B A A' _ T u wt c M m hm hpos hmw hJ hP hmS hI
  choose Cf hCf using fun p => hCut c m p hm
  set K : ℝ := (∑ p ∈ range (M+1), |Cf p|) + 1 with hKdef
  have hCK : ∀ p ∈ range (M+1), |Cf p| ≤ K - 1 := by
    intro p hp
    have := Finset.single_le_sum (f := fun p => |Cf p|) (fun i _ => abs_nonneg _) hp
    simp only [hKdef]; linarith
  have hg : Integrable (fun ω => ((M:ℝ) + 1) * K ^ 2 * ∑ p ∈ range (M + 1), LE.sq B wt (dS B T u p) ω) B.μ :=
    (integrable_finsetSum _ fun p _ => hI p).const_mul _
  have hform : ∀ ε : ℝ, T (mulF B (c.sc ε m) u) =
      fun ω a => ∑ p ∈ range (M + 1), ((ld p (c.sc ε m) (B.G ω) : ℝ) : ℂ) * dS B T u p ω a / p.factorial := by
    intro ε; funext ω a; exact hLeib B A A' T u M hJ hP _ (smoothLog_sc c ε m) ω a
  have hmT : ∀ (ε : ℝ) a, Measurable fun ω => T (mulF B (c.sc ε m) u) ω a := by
    intro ε a
    rw [hform]
    refine Finset.measurable_sum _ fun p _ => ?_
    refine Measurable.div_const (Measurable.mul ?_ (hmS p a)) _
    exact Complex.measurable_ofReal.comp ((meas_ld p _ (smoothLog_sc c ε m)).comp B.G_meas)
  have hmTu : ∀ a, Measurable fun ω => T u ω a := by
    intro a; have := hmS 0 a; rwa [dS_zero] at this
  constructor
  · intro ε hε
    refine hg.mono' (meas_sq B wt _ hmw (hmT ε)).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg' B wt hpos _ ω), hform]
    refine sq_comb_le B wt hpos (dS B T u) M (fun p ω => ld p (c.sc ε m) (B.G ω)) K ?_ ω
    intro p hp ω
    have := (hCf p ε (B.G ω) hε (B.G_pos ω)).1
    have h2 := hCK p hp
    linarith [le_abs_self (Cf p)]
  · have hdiff : ∀ ε : ℝ, (fun ω a => T (mulF B (c.sc ε m) u) ω a - T u ω a) =
        fun ω a => ∑ p ∈ range (M + 1),
          ((ld p (c.sc ε m) (B.G ω) - (if p = 0 then 1 else 0) : ℝ) : ℂ) * dS B T u p ω a / p.factorial := by
      intro ε; funext ω a
      rw [hform]
      have : T u ω a = ∑ p ∈ range (M+1), (((if p = 0 then 1 else 0 : ℝ)) : ℂ) * dS B T u p ω a / p.factorial := by
        rw [Finset.sum_eq_single 0]
        · simp [dS_zero]
        · intro p _ hp; simp [hp]
        · intro h; simp at h
      rw [this, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      push_cast; ring
    suffices key : Tendsto (fun ε : ℝ => ∫ ω, LE.sq B wt (fun ω a => T (mulF B (c.sc ε m) u) ω a - T u ω a) ω ∂B.μ)
        (𝓝[>] 0) (𝓝 (∫ _ω, (0:ℝ) ∂B.μ)) by simpa using key
    refine tendsto_integral_filter_of_dominated_convergence
      (fun ω => ((M:ℝ) + 1) * K ^ 2 * ∑ p ∈ range (M + 1), LE.sq B wt (dS B T u p) ω) ?_ ?_ hg ?_
    · refine Eventually.of_forall fun ε => ?_
      exact (meas_sq B wt _ hmw (fun a => (hmT ε a).sub (hmTu a))).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg' B wt hpos _ ω), hdiff]
      refine sq_comb_le B wt hpos (dS B T u) M
        (fun p ω => ld p (c.sc ε m) (B.G ω) - (if p = 0 then 1 else 0)) K ?_ ω
      intro p hp ω
      have h1 := (hCf p ε (B.G ω) hε (B.G_pos ω)).1
      have h2 := hCK p hp
      have h3 : |(if p = 0 then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
      calc _ ≤ |ld p (c.sc ε m) (B.G ω)| + |(if p = 0 then (1:ℝ) else 0)| := abs_sub _ _
        _ ≤ K := by linarith [le_abs_self (Cf p)]
    · refine Eventually.of_forall fun ω => ?_
      refine tendsto_const_nhds.congr' ?_
      have : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Set.Ioo 0 (B.G ω) := Ioo_mem_nhdsGT (B.G_pos ω)
      filter_upwards [this] with ε hε
      rw [hdiff]
      unfold LE.sq
      symm
      refine Finset.sum_eq_zero fun a _ => ?_
      have : ∑ p ∈ range (M + 1),
          ((ld p (c.sc ε m) (B.G ω) - (if p = 0 then 1 else 0) : ℝ) : ℂ) * dS B T u p ω a / p.factorial = 0 := by
        refine Finset.sum_eq_zero fun p _ => ?_
        rw [(hCf p ε (B.G ω) hε.1 (B.G_pos ω)).2.2 hε.2]; simp
      beta_reduce
      rw [this]; simp

/- English proof (translation)
Establish `h` using `sq_nonneg (a - δ * b)`. Establish `: a ^ 2 / δ + δ * b ^ 2 - 2 * (a * b) = (a - δ * b) ^ 2 / δ` using `by field_simp; ring`. Establish `h2 : 0 ≤ (a - δ * b) ^ 2 / δ` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem amgm (a b δ : ℝ) (hδ : 0 < δ) : a * b ≤ (a ^ 2 / δ + δ * b ^ 2) / 2 := by
  have h := sq_nonneg (a - δ * b)
  have : a ^ 2 / δ + δ * b ^ 2 - 2 * (a * b) = (a - δ * b) ^ 2 / δ := by field_simp; ring
  have h2 : 0 ≤ (a - δ * b) ^ 2 / δ := by positivity
  linarith

/- English proof (translation)
Unfold `pr LE.sq`. Rewrite using `[Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos ω i)]`. Use `mul_le_mul_of_nonneg_left (amgm ‖a ω i‖ ‖b ω i‖ δ hδ) (hpos ω i)` as an intermediate fact.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem pr_bound (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a) (a b : Fn B A)
    (δ : ℝ) (hδ : 0 < δ) (ω : B.Ω) : ‖pr B wt a b ω‖ ≤ (LE.sq B wt a ω / δ + δ * LE.sq B wt b ω) / 2 := by
  unfold pr LE.sq
  rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos ω i)]
  have := mul_le_mul_of_nonneg_left (amgm ‖a ω i‖ ‖b ω i‖ δ hδ) (hpos ω i)
  calc _ = wt ω i * (‖a ω i‖ * ‖b ω i‖) := by ring
    _ ≤ _ := this
    _ = _ := by ring

/- English proof (translation)
Unfold `pr`. Use `Finset.measurable_sum _ fun i _ => ?_` and prove the remaining obligations. Conclude with `((Complex.measurable_ofReal.comp (h0 i)).mul (h1 i)).mul (Complex.continuous_conj.measurable.comp (h2 i))`.
-/
theorem meas_pr (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (a b : Fn B A)
    (h0 : ∀ i, Measurable fun ω => wt ω i) (h1 : ∀ i, Measurable fun ω => a ω i) (h2 : ∀ i, Measurable fun ω => b ω i) :
    Measurable (pr B wt a b) := by
  unfold pr
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((Complex.measurable_ofReal.comp (h0 i)).mul (h1 i)).mul (Complex.continuous_conj.measurable.comp (h2 i))

/- English proof (translation)
Use `Integrable.mono' (((ha.div_const 1).add (hb.const_mul 1)).div_const 2) (meas_pr B wt a b h0 h1 h2).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)` and prove the remaining obligations. Conclude with `pr_bound B wt hpos a b 1 one_pos ω`.
-/
theorem int_pr (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a) (a b : Fn B A)
    (h0 : ∀ i, Measurable fun ω => wt ω i) (h1 : ∀ i, Measurable fun ω => a ω i) (h2 : ∀ i, Measurable fun ω => b ω i)
    (ha : Integrable (LE.sq B wt a) B.μ) (hb : Integrable (LE.sq B wt b) B.μ) : Integrable (pr B wt a b) B.μ := by
  refine Integrable.mono' (((ha.div_const 1).add (hb.const_mul 1)).div_const 2)
    (meas_pr B wt a b h0 h1 h2).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  exact pr_bound B wt hpos a b 1 one_pos ω

/- English proof (translation)
Use `(norm_integral_le_of_norm_le (((ha.div_const δ).add (hb.const_mul δ)).div_const 2) (Eventually.of_forall fun ω => pr_bound B wt hpos a b δ hδ ω)).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[integral_div, integral_add' (ha.div_const δ) (hb.const_mul δ), integral_div, integral_const_mul]`.
-/
theorem norm_int_pr_le (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a) (a b : Fn B A)
    (ha : Integrable (LE.sq B wt a) B.μ) (hb : Integrable (LE.sq B wt b) B.μ) (δ : ℝ) (hδ : 0 < δ) :
    ‖∫ ω, pr B wt a b ω ∂B.μ‖ ≤ ((∫ ω, LE.sq B wt a ω ∂B.μ) / δ + δ * ∫ ω, LE.sq B wt b ω ∂B.μ) / 2 := by
  refine (norm_integral_le_of_norm_le (((ha.div_const δ).add (hb.const_mul δ)).div_const 2)
    (Eventually.of_forall fun ω => pr_bound B wt hpos a b δ hδ ω)).trans (le_of_eq ?_)
  rw [integral_div, integral_add' (ha.div_const δ) (hb.const_mul δ), integral_div, integral_const_mul]

/- English proof (translation)
Introduce `B A _ wt v v' f f' hpos hmw hmv hmv' hmf hmf' hIv hIv' hIf hIf' hT hT'`. Use `set V : ℝ := ∫ ω, LE.sq B wt v ω ∂B.μ`. Use `set V' : ℝ := ∫ ω, LE.sq B wt v' ω ∂B.μ`. Establish `hV : 0 ≤ V` using `integral_nonneg fun ω => sq_nonneg' B wt hpos _ ω`. Establish `hV' : 0 ≤ V'` using `integral_nonneg fun ω => sq_nonneg' B wt hpos _ ω`.

Establish `hIsub : ∀ (g w : Fn B A), (∀ a, Measurable fun ω => g ω a) → (∀ a, Measurable fun ω => w ω a) → Integrable (LE.sq B wt g) B.μ → Integrable (LE.sq B wt w) B.μ → Integrable (LE.sq B wt (fun ω a => g ω a - w ω a)) B.μ`. Introduce `g w hg hw hIg hIw`. Use `Integrable.mono' ((hIg.const_mul 2).add (hIw.const_mul 2)) (meas_sq B wt _ hmw fun a => (hg a).sub (hw a)).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (sq_nonneg' B wt hpos _ ω)]`. Simplify using `only [LE.sq, Pi.add_apply, Finset.mul_sum]`.

Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum fun a _ => ?_` and prove the remaining obligations. Establish `h1 : ‖g ω a - w ω a‖ ≤ ‖g ω a‖ + ‖w ω a‖` using `norm_sub_le _ _`. Establish `h2 : ‖g ω a - w ω a‖ ^ 2 ≤ 2 * ‖g ω a‖ ^ 2 + 2 * ‖w ω a‖ ^ 2`. Use polynomial arithmetic with `[norm_nonneg (g ω a - w ω a), sq_nonneg (‖g ω a‖ - ‖w ω a‖), norm_nonneg (g ω a), norm_nonneg (w ω a)]`.

Use polynomial arithmetic with `[hpos ω a]`. Rewrite using `[Metric.tendsto_nhds]`. Introduce `η hη`. Use `set δ : ℝ := η / (V + V' + 1) with hδdef`. Establish `hδ : 0 < δ` using `by positivity`.

Establish `hsum : Tendsto (fun ε : ℝ => ((∫ ω, LE.sq B wt (fun ω a => f ε ω a - v ω a) ω ∂B.μ) + ∫ ω, LE.sq B wt (fun ω a => f' ε ω a - v' ω a) ω ∂B.μ) * (1 / 2 + 1 / (2 * δ))) (𝓝[>] 0) (𝓝 0)`. Use `(hT.add hT').mul_const (1 / 2 + 1 / (2 * δ))` as an intermediate fact. Simplify using `using this`. Establish `hev` using `(tendsto_order.mp hsum).2 (η / 2) (by positivity)`. Use `filter_upwards [hev, self_mem_nhdsWithin] with ε hε hpos'`.

Establish `hε0 : 0 < ε` using `hpos'`. Use `set a1 : Fn B A := fun ω a => f ε ω a - v ω a`. Use `set a2 : Fn B A := fun ω a => f' ε ω a - v' ω a`. Establish `hI1 : Integrable (LE.sq B wt a1) B.μ` using `hIsub _ _ (fun a => hmf ε a hε0) hmv (hIf ε hε0) hIv`. Establish `hI2 : Integrable (LE.sq B wt a2) B.μ` using `hIsub _ _ (fun a => hmf' ε a hε0) hmv' (hIf' ε hε0) hIv'`.

Establish `hm1 : ∀ a, Measurable fun ω => a1 ω a` using `fun a => (hmf ε a hε0).sub (hmv a)`. Establish `hm2 : ∀ a, Measurable fun ω => a2 ω a` using `fun a => (hmf' ε a hε0).sub (hmv' a)`. Establish `hdec : ∀ ω, pr B wt (f ε) (f' ε) ω - pr B wt v v' ω = pr B wt a1 a2 ω + pr B wt a1 v' ω + pr B wt v a2 ω`. Introduce `ω`. Simplify using `only [pr, a1, a2, map_sub]`.

Rewrite using `[← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `i1` using `int_pr B wt hpos a1 a2 hmw hm1 hm2 hI1 hI2`. Establish `i2` using `int_pr B wt hpos a1 v' hmw hm1 hmv' hI1 hIv'`.

Establish `i3` using `int_pr B wt hpos v a2 hmw hmv hm2 hIv hI2`. Establish `i4` using `int_pr B wt hpos (f ε) (f' ε) hmw (fun a => hmf ε a hε0) (fun a => hmf' ε a hε0) (hIf ε hε0) (hIf' ε hε0)`. Establish `i5` using `int_pr B wt hpos v v' hmw hmv hmv' hIv hIv'`. Rewrite using `[dist_eq_norm, ← integral_sub i4 i5]`. Repeatedly rewrite using `[hdec]`.

Establish `h12 : Integrable (fun ω => pr B wt a1 a2 ω + pr B wt a1 v' ω) B.μ` using `i1.add i2`. Rewrite using `[integral_add h12 i3, integral_add i1 i2]`. Establish `b1` using `norm_int_pr_le B wt hpos a1 a2 hI1 hI2 1 one_pos`. Establish `b2` using `norm_int_pr_le B wt hpos a1 v' hI1 hIv' δ hδ`. Establish `b3` using `norm_int_pr_le B wt hpos v a2 hIv hI2 (1/δ) (by positivity)`.

Establish `hδV : δ * (V + V') < η`. Rewrite using `[hδdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Use `set E1 : ℝ := ∫ ω, LE.sq B wt a1 ω ∂B.μ`. Use `set E2 : ℝ := ∫ ω, LE.sq B wt a2 ω ∂B.μ`.

Establish `e3 : V / (1/δ) = δ * V` using `by field_simp`. Establish `e4 : (E1 + E2) * (1 / 2 + 1 / (2 * δ)) = (E1 / 1 + 1 * E2) / 2 + E1 / δ / 2 + 1 / δ * E2 / 2` using `by field_simp; ring`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem pairLimit : PairLimit := by
  intro B A _ wt v v' f f' hpos hmw hmv hmv' hmf hmf' hIv hIv' hIf hIf' hT hT'
  set V : ℝ := ∫ ω, LE.sq B wt v ω ∂B.μ
  set V' : ℝ := ∫ ω, LE.sq B wt v' ω ∂B.μ
  have hV : 0 ≤ V := integral_nonneg fun ω => sq_nonneg' B wt hpos _ ω
  have hV' : 0 ≤ V' := integral_nonneg fun ω => sq_nonneg' B wt hpos _ ω
  have hIsub : ∀ (g w : Fn B A), (∀ a, Measurable fun ω => g ω a) → (∀ a, Measurable fun ω => w ω a) →
      Integrable (LE.sq B wt g) B.μ → Integrable (LE.sq B wt w) B.μ →
      Integrable (LE.sq B wt (fun ω a => g ω a - w ω a)) B.μ := by
    intro g w hg hw hIg hIw
    refine Integrable.mono' ((hIg.const_mul 2).add (hIw.const_mul 2))
      (meas_sq B wt _ hmw fun a => (hg a).sub (hw a)).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg' B wt hpos _ ω)]
    simp only [LE.sq, Pi.add_apply, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    have h1 : ‖g ω a - w ω a‖ ≤ ‖g ω a‖ + ‖w ω a‖ := norm_sub_le _ _
    have h2 : ‖g ω a - w ω a‖ ^ 2 ≤ 2 * ‖g ω a‖ ^ 2 + 2 * ‖w ω a‖ ^ 2 := by
      nlinarith [norm_nonneg (g ω a - w ω a), sq_nonneg (‖g ω a‖ - ‖w ω a‖), norm_nonneg (g ω a), norm_nonneg (w ω a)]
    nlinarith [hpos ω a]
  rw [Metric.tendsto_nhds]
  intro η hη
  set δ : ℝ := η / (V + V' + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have hsum : Tendsto (fun ε : ℝ => ((∫ ω, LE.sq B wt (fun ω a => f ε ω a - v ω a) ω ∂B.μ) +
      ∫ ω, LE.sq B wt (fun ω a => f' ε ω a - v' ω a) ω ∂B.μ) * (1 / 2 + 1 / (2 * δ))) (𝓝[>] 0) (𝓝 0) := by
    have := (hT.add hT').mul_const (1 / 2 + 1 / (2 * δ))
    simpa using this
  have hev := (tendsto_order.mp hsum).2 (η / 2) (by positivity)
  filter_upwards [hev, self_mem_nhdsWithin] with ε hε hpos'
  have hε0 : 0 < ε := hpos'
  set a1 : Fn B A := fun ω a => f ε ω a - v ω a
  set a2 : Fn B A := fun ω a => f' ε ω a - v' ω a
  have hI1 : Integrable (LE.sq B wt a1) B.μ := hIsub _ _ (fun a => hmf ε a hε0) hmv (hIf ε hε0) hIv
  have hI2 : Integrable (LE.sq B wt a2) B.μ := hIsub _ _ (fun a => hmf' ε a hε0) hmv' (hIf' ε hε0) hIv'
  have hm1 : ∀ a, Measurable fun ω => a1 ω a := fun a => (hmf ε a hε0).sub (hmv a)
  have hm2 : ∀ a, Measurable fun ω => a2 ω a := fun a => (hmf' ε a hε0).sub (hmv' a)
  have hdec : ∀ ω, pr B wt (f ε) (f' ε) ω - pr B wt v v' ω =
      pr B wt a1 a2 ω + pr B wt a1 v' ω + pr B wt v a2 ω := by
    intro ω
    simp only [pr, a1, a2, map_sub]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have i1 := int_pr B wt hpos a1 a2 hmw hm1 hm2 hI1 hI2
  have i2 := int_pr B wt hpos a1 v' hmw hm1 hmv' hI1 hIv'
  have i3 := int_pr B wt hpos v a2 hmw hmv hm2 hIv hI2
  have i4 := int_pr B wt hpos (f ε) (f' ε) hmw (fun a => hmf ε a hε0) (fun a => hmf' ε a hε0) (hIf ε hε0) (hIf' ε hε0)
  have i5 := int_pr B wt hpos v v' hmw hmv hmv' hIv hIv'
  rw [dist_eq_norm, ← integral_sub i4 i5]
  simp_rw [hdec]
  have h12 : Integrable (fun ω => pr B wt a1 a2 ω + pr B wt a1 v' ω) B.μ := i1.add i2
  rw [integral_add h12 i3, integral_add i1 i2]
  have b1 := norm_int_pr_le B wt hpos a1 a2 hI1 hI2 1 one_pos
  have b2 := norm_int_pr_le B wt hpos a1 v' hI1 hIv' δ hδ
  have b3 := norm_int_pr_le B wt hpos v a2 hIv hI2 (1/δ) (by positivity)
  have hδV : δ * (V + V') < η := by
    rw [hδdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  set E1 : ℝ := ∫ ω, LE.sq B wt a1 ω ∂B.μ
  set E2 : ℝ := ∫ ω, LE.sq B wt a2 ω ∂B.μ
  have e3 : V / (1/δ) = δ * V := by field_simp
  have e4 : (E1 + E2) * (1 / 2 + 1 / (2 * δ)) = (E1 / 1 + 1 * E2) / 2 + E1 / δ / 2 + 1 / δ * E2 / 2 := by
    field_simp; ring
  calc _ ≤ ‖∫ ω, pr B wt a1 a2 ω ∂B.μ‖ + ‖∫ ω, pr B wt a1 v' ω ∂B.μ‖ + ‖∫ ω, pr B wt v a2 ω ∂B.μ‖ :=
        norm_add₃_le
    _ ≤ (E1 / 1 + 1 * E2) / 2 + (E1 / δ + δ * V') / 2 + (V / (1/δ) + 1/δ * E2) / 2 := by
        gcongr
    _ = (E1 + E2) * (1 / 2 + 1 / (2 * δ)) + δ * (V + V') / 2 := by rw [e4, e3]; ring
    _ < η := by linarith

/- English proof (translation)
Introduce `hA hL2 hPair hCoef hLeib hCut B N F c hInf hImp hCl Y hY`. Take `⟨hM, hPos, hFac, hBN, hMon, hJet⟩` from `hImp`. Take `⟨hPoly, hp⟩` from `hA hCoef B N F hInf hM hPos hFac hBN hMon hCl Y hY`. Establish `hpos : ∀ ω a, 0 ≤ F.dw Y ω a` using `fun ω a => mul_nonneg (pow_nonneg (hPos.1 ω).le N) (hPos.2 Y hY a).le`. Establish `hmw : ∀ a, Measurable fun ω => F.dw Y ω a` using `fun a => (hM.1.pow_const N).mul_const _`.

Establish `hmS : ∀ p a, Measurable fun ω => dS B (F.gw Y) F.u p ω a` using `fun p a => (hp p).1 a`. Establish `L` using `hL2 hLeib hCut B F.R F.ι (F.gw Y) F.u (F.dw Y) c (N * (F.r + 1)) 1 le_rfl hpos hmw (hJet Y hY) hPoly hmS (fun p => (hp p).2)`. Establish `hmg : ∀ a, Measurable fun ω => F.gw Y F.u ω a`. Introduce `a`. Use `hmS 0 a` as an intermediate fact.

Rewrite `this` using `[dS_zero]`. Then use the resulting hypothesis. Establish `hmT : ∀ (ε : ℝ) a, Measurable fun ω => F.gw Y (mulF B (c.sc ε 1) F.u) ω a` using `fun ε a => measurable_apply_mulF_of_jetLocal hLeib B (F.gw Y) F.u _ (hJet Y hY) hPoly hmS _ (smoothLog_sc c ε 1) a`. Establish `P` using `hPair B F.ι (F.dw Y) (F.gw Y F.u) (F.gw Y F.u) (fun ε => F.gw Y (mulF B (c.sc ε 1) F.u)) (fun ε => F.gw Y (mulF B (c.sc ε 1) F.u)) hpos hmw hmg hmg (fun ε a _ => hmT ε a) (fun ε a _ => hmT ε a) (hCl Y hY) (hCl Y hY) L.1 L.1 L.2 L.2`. Rewrite `P` using `[int_pr_self]`. Use `(Complex.continuous_re.tendsto _).comp P` as an intermediate fact.

Simplify `this` using `[Function.comp_def]`.
-/
theorem limitB : LimitB := by
  intro hA hL2 hPair hCoef hLeib hCut B N F c hInf hImp hCl Y hY
  obtain ⟨hM, hPos, hFac, hBN, hMon, hJet⟩ := hImp
  obtain ⟨hPoly, hp⟩ := hA hCoef B N F hInf hM hPos hFac hBN hMon hCl Y hY
  have hpos : ∀ ω a, 0 ≤ F.dw Y ω a := fun ω a =>
    mul_nonneg (pow_nonneg (hPos.1 ω).le N) (hPos.2 Y hY a).le
  have hmw : ∀ a, Measurable fun ω => F.dw Y ω a := fun a => (hM.1.pow_const N).mul_const _
  have hmS : ∀ p a, Measurable fun ω => dS B (F.gw Y) F.u p ω a := fun p a => (hp p).1 a
  have L := hL2 hLeib hCut B F.R F.ι (F.gw Y) F.u (F.dw Y) c (N * (F.r + 1)) 1 le_rfl hpos hmw (hJet Y hY) hPoly
    hmS (fun p => (hp p).2)
  have hmg : ∀ a, Measurable fun ω => F.gw Y F.u ω a := by
    intro a; have := hmS 0 a; rwa [dS_zero] at this
  have hmT : ∀ (ε : ℝ) a, Measurable fun ω => F.gw Y (mulF B (c.sc ε 1) F.u) ω a :=
    fun ε a => measurable_apply_mulF_of_jetLocal hLeib B (F.gw Y) F.u _ (hJet Y hY) hPoly hmS _ (smoothLog_sc c ε 1) a
  have P := hPair B F.ι (F.dw Y) (F.gw Y F.u) (F.gw Y F.u) (fun ε => F.gw Y (mulF B (c.sc ε 1) F.u))
    (fun ε => F.gw Y (mulF B (c.sc ε 1) F.u)) hpos hmw hmg hmg (fun ε a _ => hmT ε a) (fun ε a _ => hmT ε a)
    (hCl Y hY) (hCl Y hY) L.1 L.1 L.2 L.2
  simp_rw [int_pr_self] at P
  have := (Complex.continuous_re.tendsto _).comp P
  simpa [Function.comp_def] using this

/- English proof (translation)
The claim follows from `lemmaEprimeFromSteps leibniz cutBound limit_L2 pairLimit epStep5 epStep6`.
-/
theorem lemmaEprime : LemmaEprime :=
  lemmaEprimeFromSteps leibniz cutBound limit_L2 pairLimit epStep5 epStep6

/- English proof (translation)
Simplify using `[ld, Real.exp_log hx]`.
-/
theorem ld_zero' (φ : ℝ → ℝ) (x : ℝ) (hx : 0 < x) : ld 0 φ x = φ x := by
  simp [ld, Real.exp_log hx]

/- English proof (translation)
Introduce `hRange hLim B A _ wt v σ K hσ hpos hmw hmv hInt hBd`. Establish `hsqm : Measurable (LE.sq B wt v)` using `meas_sq B wt v hmw hmv`. Establish `hsq0 : ∀ ω, 0 ≤ LE.sq B wt v ω` using `sq_nonneg' B wt hpos v`. Use `set e : ℕ → ℝ := fun n => 1 / ((n:ℝ) + 1) with he`. Establish `he0 : ∀ n, 0 < e n` using `fun n => by simp only [he]; positivity`.

Establish `hte : Tendsto e atTop (𝓝[>] 0)` using `tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall he0⟩`. Establish `hmth : ∀ ε : ℝ, Measurable fun ω => th ε σ (B.G ω)` using `fun ε => by`. Unfold `th`. Conclude with `(B.G_meas.div (B.G_meas.add_const ε)).pow_const σ`. Establish `hlim : ∀ ω, Tendsto (fun n => th (e n) σ (B.G ω) * LE.sq B wt v ω) atTop (𝓝 (LE.sq B wt v ω))`.

Introduce `ω`. Establish `h` using `(hLim σ 0 (B.G ω) (B.G_pos ω)).comp hte`. Simplify using `only [Function.comp_def, ld_zero' _ _ (B.G_pos ω), if_true] at h`. Simplify using `using h.mul_const (LE.sq B wt v ω)`. Establish `hK0 : 0 ≤ K`.

Use `le_trans (integral_nonneg fun ω => ?_) (hBd 1 one_pos)` and prove the remaining obligations. Conclude with `mul_nonneg (hRange 1 σ _ one_pos hσ (B.G_pos ω)).1.le (hsq0 ω)`. Establish `hle : ∫⁻ ω, ENNReal.ofReal (LE.sq B wt v ω) ∂B.μ ≤ ENNReal.ofReal K`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr fun ω => ?_` and prove the remaining obligations.

Conclude with `((ENNReal.tendsto_ofReal (hlim ω)).liminf_eq).symm`. Use `_ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (th (e n) σ (B.G ω) * LE.sq B wt v ω) ∂B.μ) atTop := lintegral_liminf_le fun n => ((hmth (e n)).mul hsqm).ennreal_ofReal`. Use `_ ≤ liminf (fun _ : ℕ => ENNReal.ofReal K) atTop := by`. Use `liminf_le_liminf (Eventually.of_forall fun n => ?_)` and prove the remaining obligations. Rewrite using `[← ofReal_integral_eq_lintegral_ofReal (hInt (e n) (he0 n)) (Eventually.of_forall fun ω => mul_nonneg (hRange (e n) σ _ (he0 n) hσ (B.G_pos ω)).1.le (hsq0 ω))]`.

Conclude with `ENNReal.ofReal_le_ofReal (hBd (e n) (he0 n))`. Use `_ = ENNReal.ofReal K := by simp`. Use `⟨⟨hsqm.aestronglyMeasurable, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hasFiniteIntegral_iff_ofReal (Eventually.of_forall hsq0)]`. Conclude with `lt_of_le_of_lt hle ENNReal.ofReal_lt_top`.

Rewrite using `[integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hsq0) hsqm.aestronglyMeasurable]`. Conclude with `ENNReal.toReal_le_of_le_ofReal hK0 hle`.
-/
theorem fatouStep : FatouStep := by
  intro hRange hLim B A _ wt v σ K hσ hpos hmw hmv hInt hBd
  have hsqm : Measurable (LE.sq B wt v) := meas_sq B wt v hmw hmv
  have hsq0 : ∀ ω, 0 ≤ LE.sq B wt v ω := sq_nonneg' B wt hpos v
  set e : ℕ → ℝ := fun n => 1 / ((n:ℝ) + 1) with he
  have he0 : ∀ n, 0 < e n := fun n => by simp only [he]; positivity
  have hte : Tendsto e atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall he0⟩
  have hmth : ∀ ε : ℝ, Measurable fun ω => th ε σ (B.G ω) := fun ε => by
    unfold th; exact (B.G_meas.div (B.G_meas.add_const ε)).pow_const σ
  have hlim : ∀ ω, Tendsto (fun n => th (e n) σ (B.G ω) * LE.sq B wt v ω) atTop (𝓝 (LE.sq B wt v ω)) := by
    intro ω
    have h := (hLim σ 0 (B.G ω) (B.G_pos ω)).comp hte
    simp only [Function.comp_def, ld_zero' _ _ (B.G_pos ω), if_true] at h
    simpa using h.mul_const (LE.sq B wt v ω)
  have hK0 : 0 ≤ K := by
    refine le_trans (integral_nonneg fun ω => ?_) (hBd 1 one_pos)
    exact mul_nonneg (hRange 1 σ _ one_pos hσ (B.G_pos ω)).1.le (hsq0 ω)
  have hle : ∫⁻ ω, ENNReal.ofReal (LE.sq B wt v ω) ∂B.μ ≤ ENNReal.ofReal K := by
    calc ∫⁻ ω, ENNReal.ofReal (LE.sq B wt v ω) ∂B.μ
        = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (th (e n) σ (B.G ω) * LE.sq B wt v ω)) atTop ∂B.μ := by
          refine lintegral_congr fun ω => ?_
          exact ((ENNReal.tendsto_ofReal (hlim ω)).liminf_eq).symm
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (th (e n) σ (B.G ω) * LE.sq B wt v ω) ∂B.μ) atTop :=
          lintegral_liminf_le fun n => ((hmth (e n)).mul hsqm).ennreal_ofReal
      _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal K) atTop := by
          refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
          rw [← ofReal_integral_eq_lintegral_ofReal (hInt (e n) (he0 n))
            (Eventually.of_forall fun ω => mul_nonneg (hRange (e n) σ _ (he0 n) hσ (B.G_pos ω)).1.le (hsq0 ω))]
          exact ENNReal.ofReal_le_ofReal (hBd (e n) (he0 n))
      _ = ENNReal.ofReal K := by simp
  refine ⟨⟨hsqm.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hsq0)]
    exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hsq0) hsqm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hK0 hle

noncomputable def Fk (k : ℕ) (s : ℝ) (t : ℝ) : ℝ := Real.exp (-(k:ℝ) * t) * (1 + Real.exp (-t)) ^ (-s)

/- English proof (translation)
Unfold `Fk`. Use `(Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul ?_` and prove the remaining obligations. Use `ContDiff.rpow_const_of_ne ?_ ?_` and prove the remaining obligations. Conclude with `contDiff_const.add (Real.contDiff_exp.comp contDiff_neg)`. Introduce `u`.

Check the signs of the components of the expression.
-/
theorem Fk_contDiff (k : ℕ) (s : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Fk k s) := by
  unfold Fk
  refine (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul ?_
  refine ContDiff.rpow_const_of_ne ?_ ?_
  · exact contDiff_const.add (Real.contDiff_exp.comp contDiff_neg)
  · intro u; positivity

/- English proof (translation)
Use function extensionality and compare the values at `t`. Establish `hp : 0 < 1 + Real.exp (-t)` using `by positivity`. Establish `h1 : HasDerivAt (fun t : ℝ => Real.exp (-(k:ℝ) * t)) (Real.exp (-(k:ℝ) * t) * (-(k:ℝ) * 1)) t` using `((hasDerivAt_id t).const_mul (-(k:ℝ))).exp`. Establish `h2 : HasDerivAt (fun t : ℝ => 1 + Real.exp (-t)) (Real.exp (-t) * (-1)) t` using `((hasDerivAt_id t).neg.exp).const_add 1`. Establish `h3` using `h2.rpow_const (p := -s) (Or.inl hp.ne')`.

Establish `h4` using `h1.mul h3`. Establish `h5 : deriv (Fk k s) t = _` using `h4.deriv`. Rewrite using `[h5]`. Unfold `Fk`. Establish `e1 : Real.exp (-((k+1 : ℕ):ℝ) * t) = Real.exp (-(k:ℝ) * t) * Real.exp (-t)`.

Rewrite using `[← Real.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : -s - 1 = -(s+1)` using `by ring`.

Rewrite using `[e1, e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Fk_deriv (k : ℕ) (s : ℝ) : deriv (Fk k s) = fun t => -(k:ℝ) * Fk k s t + s * Fk (k+1) (s+1) t := by
  funext t
  have hp : 0 < 1 + Real.exp (-t) := by positivity
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-(k:ℝ) * t)) (Real.exp (-(k:ℝ) * t) * (-(k:ℝ) * 1)) t :=
    ((hasDerivAt_id t).const_mul (-(k:ℝ))).exp
  have h2 : HasDerivAt (fun t : ℝ => 1 + Real.exp (-t)) (Real.exp (-t) * (-1)) t :=
    ((hasDerivAt_id t).neg.exp).const_add 1
  have h3 := h2.rpow_const (p := -s) (Or.inl hp.ne')
  have h4 := h1.mul h3
  have h5 : deriv (Fk k s) t = _ := h4.deriv
  rw [h5]
  unfold Fk
  have e1 : Real.exp (-((k+1 : ℕ):ℝ) * t) = Real.exp (-(k:ℝ) * t) * Real.exp (-t) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  have e2 : -s - 1 = -(s+1) := by ring
  rw [e1, e2]; ring

/- English proof (translation)
Establish `h0 : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0)` using `Real.tendsto_exp_neg_atTop_nhds_zero`. Establish `h1 : Tendsto (fun t : ℝ => (1 + Real.exp (-t)) ^ (-s)) atTop (𝓝 1)`. Use `(h0.const_add 1).rpow_const (p := -s) (Or.inl (by norm_num))` as an intermediate fact. Simplify using `using this`. Unfold `Fk`.

Use `split_ifs with hk`. Substitute `hk` using the available equality. Simplify using `using h1`. Establish `h2 : Tendsto (fun t : ℝ => Real.exp (-(k:ℝ) * t)) atTop (𝓝 0)`. Establish `hk' : (0:ℝ) < k` using `by exact_mod_cast Nat.pos_of_ne_zero hk`.

Establish `: Tendsto (fun t : ℝ => (k:ℝ) * t) atTop atTop` using `tendsto_id.const_mul_atTop hk'`. Use `h0.comp this` as an intermediate fact. Simplify `this` using `[Function.comp_def]`. Simplify using `using h2.mul h1`.
-/
theorem Fk_lim (k : ℕ) (s : ℝ) : Tendsto (Fk k s) atTop (𝓝 (if k = 0 then 1 else 0)) := by
  have h0 : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have h1 : Tendsto (fun t : ℝ => (1 + Real.exp (-t)) ^ (-s)) atTop (𝓝 1) := by
    have := (h0.const_add 1).rpow_const (p := -s) (Or.inl (by norm_num))
    simpa using this
  unfold Fk
  split_ifs with hk
  · subst hk; simpa using h1
  · have h2 : Tendsto (fun t : ℝ => Real.exp (-(k:ℝ) * t)) atTop (𝓝 0) := by
      have hk' : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
      have : Tendsto (fun t : ℝ => (k:ℝ) * t) atTop atTop := tendsto_id.const_mul_atTop hk'
      have := h0.comp this
      simpa [Function.comp_def] using this
    simpa using h2.mul h1

/- English proof (translation)
Proceed by induction on `p with`. Consider the case `zero => intro k s`. Simplify using `using Fk_lim k s`. Consider the case `succ n ih`. Introduce `k s`.

Rewrite using `[iteratedDeriv_succ', Fk_deriv]`. Establish `hadd : iteratedDeriv n (fun t => -(k:ℝ) * Fk k s t + s * Fk (k+1) (s+1) t) = fun t => -(k:ℝ) * iteratedDeriv n (Fk k s) t + s * iteratedDeriv n (Fk (k+1) (s+1)) t`. Use function extensionality and compare the values at `t`. Establish `c1 : ContDiffAt ℝ n (fun t => -(k:ℝ) * Fk k s t) t` using `(contDiff_const.mul ((Fk_contDiff k s).of_le (by exact_mod_cast le_top))).contDiffAt`. Establish `c2 : ContDiffAt ℝ n (fun t => s * Fk (k+1) (s+1) t) t` using `(contDiff_const.mul ((Fk_contDiff (k+1) (s+1)).of_le (by exact_mod_cast le_top))).contDiffAt`.

Rewrite using `[iteratedDeriv_fun_add c1 c2, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]`. Rewrite using `[hadd]`. Establish `t1` using `(ih k s).const_mul (-(k:ℝ))`. Establish `t2` using `(ih (k+1) (s+1)).const_mul s`. Use `t1.add t2` as an intermediate fact.

Establish `hval : -(k:ℝ) * (if n = 0 ∧ k = 0 then 1 else 0) + s * (if n = 0 ∧ k + 1 = 0 then 1 else 0) = (if n + 1 = 0 ∧ k = 0 then (1:ℝ) else 0)`. Apply the tactic sequence `by_cases hk : k = 0 <;> simp [hk]`. Rewrite `this` using `[hval]`. Conclude with `this`.
-/
theorem Fk_iter_lim (p : ℕ) : ∀ (k : ℕ) (s : ℝ),
    Tendsto (iteratedDeriv p (Fk k s)) atTop (𝓝 (if p = 0 ∧ k = 0 then 1 else 0)) := by
  induction p with
  | zero => intro k s; simpa using Fk_lim k s
  | succ n ih =>
    intro k s
    rw [iteratedDeriv_succ', Fk_deriv]
    have hadd : iteratedDeriv n (fun t => -(k:ℝ) * Fk k s t + s * Fk (k+1) (s+1) t) =
        fun t => -(k:ℝ) * iteratedDeriv n (Fk k s) t + s * iteratedDeriv n (Fk (k+1) (s+1)) t := by
      funext t
      have c1 : ContDiffAt ℝ n (fun t => -(k:ℝ) * Fk k s t) t :=
        (contDiff_const.mul ((Fk_contDiff k s).of_le (by exact_mod_cast le_top))).contDiffAt
      have c2 : ContDiffAt ℝ n (fun t => s * Fk (k+1) (s+1) t) t :=
        (contDiff_const.mul ((Fk_contDiff (k+1) (s+1)).of_le (by exact_mod_cast le_top))).contDiffAt
      rw [iteratedDeriv_fun_add c1 c2, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
    rw [hadd]
    have t1 := (ih k s).const_mul (-(k:ℝ))
    have t2 := (ih (k+1) (s+1)).const_mul s
    have := t1.add t2
    have hval : -(k:ℝ) * (if n = 0 ∧ k = 0 then 1 else 0) + s * (if n = 0 ∧ k + 1 = 0 then 1 else 0) =
        (if n + 1 = 0 ∧ k = 0 then (1:ℝ) else 0) := by
      by_cases hk : k = 0 <;> simp [hk]
    rw [hval] at this
    exact this

/- English proof (translation)
Introduce `σ p x hx`. Establish `hlog : Tendsto (fun ε : ℝ => Real.log x - Real.log ε) (𝓝[>] 0) atTop`. Use `Real.tendsto_log_nhdsGT_zero` as an intermediate fact. Establish `h2 : Tendsto (fun ε : ℝ => -Real.log ε) (𝓝[>] 0) atTop` using `tendsto_neg_atBot_atTop.comp this`. Simplify `tendsto_atTop_add_const_left _ (Real.log x) h2` using `[sub_eq_add_neg]`.

Establish `h` using `(Fk_iter_lim p 0 σ).comp hlog`. Simplify using `only [and_true] at h`. Use `h.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with ε hε`. Establish `hε0 : 0 < ε` using `hε`.

Unfold `ld`. Establish `: (fun u : ℝ => th ε σ (Real.exp u)) = fun u : ℝ => Fk 0 σ (u - Real.log ε)`. Use function extensionality and compare the values at `u`. Rewrite using `[thetaForm ε σ hε0 u]`. Unfold `Fk`.

Establish `: Real.exp (-(u - Real.log ε)) = ε * Real.exp (-u)`. Rewrite using `[neg_sub, Real.exp_sub, Real.exp_log hε0, Real.exp_neg]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Rewrite using `[this, iteratedDeriv_comp_sub_const]`. Both sides reduce to the same expression.
-/
theorem thetaLimit : ThetaLimit := by
  intro σ p x hx
  have hlog : Tendsto (fun ε : ℝ => Real.log x - Real.log ε) (𝓝[>] 0) atTop := by
    have := Real.tendsto_log_nhdsGT_zero
    have h2 : Tendsto (fun ε : ℝ => -Real.log ε) (𝓝[>] 0) atTop := tendsto_neg_atBot_atTop.comp this
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_left _ (Real.log x) h2
  have h := (Fk_iter_lim p 0 σ).comp hlog
  simp only [and_true] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : 0 < ε := hε
  unfold ld
  have : (fun u : ℝ => th ε σ (Real.exp u)) = fun u : ℝ => Fk 0 σ (u - Real.log ε) := by
    funext u
    rw [thetaForm ε σ hε0 u]
    unfold Fk
    have : Real.exp (-(u - Real.log ε)) = ε * Real.exp (-u) := by
      rw [neg_sub, Real.exp_sub, Real.exp_log hε0, Real.exp_neg]; ring
    rw [this]; simp
  rw [this, iteratedDeriv_comp_sub_const]
  rfl

end Formalism.FourierDecayAlt.P.LEx1
