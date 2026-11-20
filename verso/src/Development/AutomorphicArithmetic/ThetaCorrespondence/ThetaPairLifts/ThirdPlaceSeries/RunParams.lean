import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaBoundLengthUnit
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
noncomputable section
namespace GlobalTheory.ThetaSizeBounds
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `_`. Use `(Formalism.MainNotions.Closed.and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 6) _root_.GlobalTheory.CovTop.WtShape.wtN_z).imp fun Fm CH _ hh => ?_` and prove the remaining obligations. Take `⟨⟨A, -, a, ha⟩, ⟨C2, -, b0, hb0⟩⟩` from `hh`. Use `⟨200000, by norm_num, max a b0, fun x hx hle ι p hp i hi Y hY => ?_⟩` and prove the remaining obligations. Establish `hN : HostNum (Fm.D x ι) (Fm.L x ι) (Fm.parT x hx ι).PP A 6` using `ha x hx ((le_max_left _ _).trans hle) ι p hp i`.

Establish `hW : WtNum p i (Fm.parT x hx ι).PP` using `hb0 x hx ((le_max_right _ _).trans hle) ι p hp i`. Establish `S` using `Fm.sizes x hx ι`. Establish `P` using `Fm.params x hx ι`. Establish `hm4` using `Formalism.L2.Pj.host_m_pow_four_le_f S`. Establish `hf2` using `Formalism.L2.Pj.host_f_sq_le_rd P`.

Establish `hrd16` using `Formalism.L2.Pj.host_rd_ge_sixteen P`. Take `⟨-, -, -, -, -, sC, sQD, -, -, -, -, -, -, -, -, -, -, -, -, -, sG, -⟩` from `S`. Take `⟨-, -, -, -, -, -, h1, h2⟩` from `sQD`. Establish `ef` using `Formalism.L2.Pj.hostSize_f (Fm.D x ι)`. Establish `erd` using `Formalism.L2.Pj.hostSize_rd (Fm.D x ι)`.

Establish `a1` using `(Fm.D x ι).R.two_le_m`. Establish `a2` using `(Fm.D x ι).R.m_add_three_le_k`. Establish `a3 : (Fm.D x ι).R.r + 5 ≤ (Fm.D x ι).R.t` using `(Fm.D x ι).R.rank_add_five_le`. Establish `a4 : (Fm.D x ι).R.f ≤ (Fm.D x ι).R.k` using `(Fm.D x ι).R.f_le_k`. Establish `a5 : (Fm.D x ι).R.k ≤ (Fm.D x ι).R.r ∧ (Fm.D x ι).R.m ≤ (Fm.D x ι).R.r ∧ 6 ≤ (Fm.D x ι).R.r`.

Unfold `Formalism.BasicNotions.Ranks.r`. Use linear arithmetic over natural numbers and integers. Establish `hf8` using `hN.f8`. Establish `hL10 : 10 ≤ (Fm.L x ι).sc.L` using `hN.big.2.1`. Establish `hLL` using `hN.big.2.2.2`.

Establish `hfR : (8 : ℝ) ≤ (Fm.D x ι).R.f` using `by exact_mod_cast hf8`. Establish `hrR : (6 : ℝ) ≤ (Fm.D x ι).R.r` using `by exact_mod_cast a5.2.2`. Establish `hmR : (2 : ℝ) ≤ (Fm.D x ι).R.m` using `by exact_mod_cast a1`. Establish `ht : (11 : ℝ) ≤ (Fm.D x ι).R.t` using `by exact_mod_cast (by omega : 11 ≤ (Fm.D x ι).R.t)`. Establish `hft : ((Fm.D x ι).R.f : ℝ) ≤ (Fm.D x ι).R.t` using `by exact_mod_cast (by omega : (Fm.D x ι).R.f ≤ (Fm.D x ι).R.t)`.

Establish `hrt : ((Fm.D x ι).R.r : ℝ) ≤ (Fm.D x ι).R.t` using `by exact_mod_cast (by omega : (Fm.D x ι).R.r ≤ (Fm.D x ι).R.t)`. Establish `hb1 : 1 ≤ (Fm.L x ι).sc.b` using `Real.one_le_exp (by linarith)`. Establish `hb0' : 0 < (Fm.L x ι).sc.b` using `Real.exp_pos _`. Establish `hq : (1 : ℝ) ≤ (Fm.D x ι).host.q` using `by exact_mod_cast (Fm.D x ι).host.hyp.1.one_lt.le`. Establish `hd' : (1 : ℝ) ≤ (Fm.D x ι).host.d` using `by exact_mod_cast (Fm.D x ι).host.hyp.2.1.one_lt.le`.

Establish `hn : (1 : ℝ) ≤ (Fm.D x ι).R.n` using `by exact_mod_cast (Fm.D x ι).R.ord_pos`. Establish `hqd : (1 : ℝ) ≤ ((Fm.D x ι).host.q : ℝ) * (Fm.D x ι).host.d` using `by nlinarith`. Establish `hs : Real.sqrt (((Fm.D x ι).host.q : ℝ) * (Fm.D x ι).host.d) ≤ ((Fm.D x ι).host.q : ℝ) * (Fm.D x ι).host.d`. Rewrite using `[Real.sqrt_le_left (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hc : (Fm.D x ι).host.rdE ≤ szCond (Fm.L x ι)`. Unfold `szCond`. Conclude with `UpperTheory.Ram.Rd.rdE_le_cond _`. Establish `hc1 : (1 : ℝ) ≤ szCond (Fm.L x ι)` using `h1.trans hc`. Establish `hsb : Real.sqrt (Fm.L x ι).sc.b ≤ (Fm.L x ι).sc.b` using `Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩`.

Establish `hrdb : (Fm.D x ι).host.rdE ≤ (Fm.L x ι).sc.b`. Establish `e1 : (Fm.D x ι).host.rdE ≤ szCond (Fm.L x ι) ^ 36 * ((Fm.D x ι).R.t : ℝ) ^ 150` using `hc.trans ((le_self_pow₀ hc1 (by norm_num)).trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith))))`. Conclude with `(e1.trans sC).trans hsb`. Establish `hlogrd : Real.log (ReciprocityTheory.ChartRestriction.G.I2.PT.rd (Fm.D x ι).host.E) ≤ 2 * (Fm.L x ι).sc.L`. Rewrite using `[erd]`.

Use `Real.log_le_log (by linarith) hrdb` as an intermediate fact. Unfold `Formalism.BasicNotions.Scale.b at this`. Rewrite `this` using `[Real.log_exp]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlfr` using `hN.logfr.1`.

Establish `hlf : Real.log (ReciprocityTheory.ChartRestriction.G.I2.PT.f (Fm.D x ι).host.E : ℝ) ≤ 2 * (Fm.L x ι).sc.L`. Rewrite using `[ef]`. Establish `hf0 : (0 : ℝ) < (Fm.D x ι).R.f` using `by linarith`. Use `Real.log_le_log hf0 (le_mul_of_one_le_right hf0.le (by linarith : (1 : ℝ) ≤ (Fm.D x ι).R.r))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hlr : Real.log ((Fm.D x ι).R.r : ℝ) ≤ (Fm.L x ι).sc.L`. Establish `hr0 : (0 : ℝ) < (Fm.D x ι).R.r` using `by linarith`. Use `Real.log_le_log hr0 (le_mul_of_one_le_left hr0.le (by linarith : (1 : ℝ) ≤ (Fm.D x ι).R.f))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hg0 : ∀ k, (0 : ℝ) < (Fm.D x ι).host.g k` using `fun k => by exact_mod_cast ((Fm.D x ι).host.g_prime k).pos`.

Establish `hq1 : 1 ≤ (Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1` using `Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero ((Fm.D x ι).host.g_prime 0).ne_zero ((Fm.D x ι).host.g_prime 1).ne_zero)`. Establish `hlq : Real.log (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) ≤ 70 * (Fm.L x ι).sc.L`. Use `push_cast`. Rewrite using `[Real.log_mul (hg0 0).ne' (hg0 1).ne']`. Combine the linear relations using `[hN.logg 0, hN.logg 1]`.

Establish `hP` using `archimedeanBoundTotalConstant_nonneg_le_bound (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m (Fm.L x ι).sc.L (by linarith) (by rw [ef]; omega) (by omega) (by omega) a5.2.1 hq1 (by rw [erd]; exact h1) hlogrd hlf hlr hlq`. Rewrite `hP` using `[ef]`. Use `⟨?_, hP.1, ?_, fun DF hDF hDFb => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hW.sig.2.1]`. Unfold `Formalism.BasicNotions.Ranks.sigW`.

Use linear arithmetic over natural numbers and integers. Establish `hZ1 : (1 : ℝ) ≤ zBase (Fm.L x ι)`. Unfold `zBase`. Use `mul_le_mul hfR hrR (by norm_num) (by linarith)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `hZ : zBase (Fm.L x ι) ^ 2 ≤ (Fm.parT x hx ι).PP` using `(pow_le_pow_right₀ hZ1 (by norm_num)).trans hN.ppLow`. Establish `hD1 : (1 : ℝ) ≤ (dimFlag (dat p i) : ℝ)`. Rewrite using `[hW.dim]`. Establish `: 1 ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2` using `Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (Nat.choose_pos (by omega)).ne')`. Conclude with `this` after adjusting the coercions.

Establish `hT0 : (0 : ℝ) ≤ lenT p i (Fm.parT x hx ι).PP` using `Nat.cast_nonneg _`. Establish `hPP0 : 0 ≤ (Fm.parT x hx ι).PP` using `le_trans (by positivity) hZ`. Establish `hrow` using `hW.what₂.2`. Establish `hTP : (lenT p i (Fm.parT x hx ι).PP : ℝ) * (Fm.parT x hx ι).PP ≤ (Fm.L x ι).sc.b` using `by revert hrow hD1 hT0 hPP0 hL10`. Generalize the expression as in `(lenT p i (Fm.parT x hx ι).PP : ℝ) = T`.

Generalize the expression as in `(Fm.parT x hx ι).PP = PP`. Generalize the expression as in `(dimFlag (dat p i) : ℝ) = Dd`. Generalize the expression as in `(Fm.L x ι).sc.L = L`. Generalize the expression as in `(Fm.L x ι).sc.b = b`. Introduce `hrow hD1 hT0 hPP0 hL10`.

Establish `e0 : 0 ≤ PP * T` using `mul_nonneg hPP0 hT0`. Establish `e1 : PP * T * 1 ≤ PP * T * Dd ^ 2` using `mul_le_mul_of_nonneg_left (one_le_pow₀ hD1) e0`. Establish `e2 : PP * T * Dd ^ 2 * 1 ≤ PP * T * Dd ^ 2 * L` using `mul_le_mul_of_nonneg_left (by linarith) (by positivity)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hU : (Fm.L x ι).sc.b ≤ unitE p`.

Rewrite using `[hW.unit]`. Establish `e1 : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.m` using `by nlinarith`. Establish `e2 : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.m * (Fm.L x ι).sc.L * Real.log (Real.log (Fm.L x ι).sc.x)`. Use `mul_le_mul e1 (by linarith : (1 : ℝ) ≤ (Fm.L x ι).sc.L) zero_le_one (by linarith)` as an intermediate fact. Use `mul_le_mul this hLL zero_le_one (by linarith)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `: (Fm.L x ι).sc.b * 1 ≤ (Fm.L x ι).sc.b * ((Fm.D x ι).R.f * (Fm.D x ι).R.m * (Fm.L x ι).sc.L * Real.log (Real.log (Fm.L x ι).sc.x))` using `mul_le_mul_of_nonneg_left e2 (by linarith)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hPz : GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m 5 1 ≤ 200000 * zBase (Fm.L x ι) ^ 2` using `hP.2`. Combine the equalities or inequalities in the displayed calculation.

Establish `hDF1 : (1 : ℝ) ≤ DF` using `by exact_mod_cast hDF`. Establish `hk : (1 : ℝ) ≤ (Fm.D x ι).R.k` using `by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.k)`. Establish `hg : ∀ k, (Fm.L x ι).sc.b ^ 8 ≤ ((Fm.D x ι).host.g k : ℝ)` using `fun k => (pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_left (by linarith) hk) 8).trans (sG k k).1`. Establish `key` using `size_inequality_real (Fm.D x ι).host.rdE (szCond (Fm.L x ι)) (Fm.D x ι).R.t (Fm.L x ι).sc.b (Fm.D x ι).R.f (Fm.D x ι).R.r DF ((Fm.D x ι).host.g 0) ((Fm.D x ι).host.g 1) h1 hc sC ht (by linarith) hft (by linarith) hrt hDF1 hDFb (hg 0) (hg 1)`. Establish `hrun` using `GlobalTheory.RunParametersOfLower.runOK_of_le (Fm.D x ι).host.E (Fm.D x ι).R.r DF ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m hDF (by rw [ef]; nlinarith) (by omega) hm4 hf2 hrd16 (by unfold ReciprocityTheory.ChartRestriction.G.I2.RR; rw [ef, erd]; push_cast; exact …`.

Rewrite `hrun` using `[ef]`. Conclude with `hrun`. Introduce `s hs`. Establish `hR0 : (1 : ℝ) ≤ Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF)) ^ 2`. Rewrite using `[Real.sq_sqrt (by positivity)]`.

Establish `: (0 : ℝ) ≤ DF` using `Nat.cast_nonneg _`. Use the polynomial consequences of the given equalities and inequalities. Establish `hRR : (1 : ℝ) ≤ ReciprocityTheory.ChartRestriction.G.I2.RR (E` using `(Fm.D x ι).host.E) := by`. Unfold `ReciprocityTheory.ChartRestriction.G.I2.RR; exact one_le_pow₀ (by linarith)`. Use `sqrt_lt_th_real ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Y.d.l₂.M : ℝ) (ReciprocityTheory.ChartRestriction.G.I2.PT.f (Fm.D x ι).host.E : ℝ) (Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF))) (ReciprocityTheory.ChartRestriction.G.I2.RR (E := (Fm.D x ι).host.E)) (Fm.L x …` as an intermediate fact.

Unfold `ReciprocityTheory.ChartRestriction.G.I2.th`. Conclude with `this`.
-/
theorem run_params_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP C => (dat p i).q ≤ (Fm.D x ι).R.m ∧ 0 ≤ GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m 5 1 ∧ lenT p i PP * GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m 5 1 ≤ C * unitE p ∧ ∀ DF : ℕ, 1 ≤ DF → (DF : ℝ) ≤ (Fm.L x ι).sc.b ^ 2 → GlobalTheory.EtaAn.RunOK (Fm.D x ι).host.E (Fm.D x ι).R.r DF ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF))) (Fm.D x ι).R.m ∧ ∀ s : ℝ, (Y.d.l₂.M : ℝ) * s < (Fm.L x ι).sc.b → Real.sqrt s < ReciprocityTheory.ChartRestriction.G.I2.th (E := (Fm.D x ι).host.E) ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF))) := by
  intro _
  refine (Formalism.MainNotions.Closed.and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 6) _root_.GlobalTheory.CovTop.WtShape.wtN_z).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨A, -, a, ha⟩, ⟨C2, -, b0, hb0⟩⟩ := hh
  refine ⟨200000, by norm_num, max a b0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  have hN : HostNum (Fm.D x ι) (Fm.L x ι) (Fm.parT x hx ι).PP A 6 := ha x hx ((le_max_left _ _).trans hle) ι p hp i
  have hW : WtNum p i (Fm.parT x hx ι).PP := hb0 x hx ((le_max_right _ _).trans hle) ι p hp i
  have S := Fm.sizes x hx ι
  have P := Fm.params x hx ι
  have hm4 := Formalism.L2.Pj.host_m_pow_four_le_f S
  have hf2 := Formalism.L2.Pj.host_f_sq_le_rd P
  have hrd16 := Formalism.L2.Pj.host_rd_ge_sixteen P
  obtain ⟨-, -, -, -, -, sC, sQD, -, -, -, -, -, -, -, -, -, -, -, -, -, sG, -⟩ := S
  obtain ⟨-, -, -, -, -, -, h1, h2⟩ := sQD
  have ef := Formalism.L2.Pj.hostSize_f (Fm.D x ι)
  have erd := Formalism.L2.Pj.hostSize_rd (Fm.D x ι)
  have a1 := (Fm.D x ι).R.two_le_m
  have a2 := (Fm.D x ι).R.m_add_three_le_k
  have a3 : (Fm.D x ι).R.r + 5 ≤ (Fm.D x ι).R.t := (Fm.D x ι).R.rank_add_five_le
  have a4 : (Fm.D x ι).R.f ≤ (Fm.D x ι).R.k := (Fm.D x ι).R.f_le_k
  have a5 : (Fm.D x ι).R.k ≤ (Fm.D x ι).R.r ∧ (Fm.D x ι).R.m ≤ (Fm.D x ι).R.r ∧ 6 ≤ (Fm.D x ι).R.r := by
    unfold Formalism.BasicNotions.Ranks.r; omega
  have hf8 := hN.f8
  have hL10 : 10 ≤ (Fm.L x ι).sc.L := hN.big.2.1
  have hLL := hN.big.2.2.2
  have hfR : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
  have hrR : (6 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast a5.2.2
  have hmR : (2 : ℝ) ≤ (Fm.D x ι).R.m := by exact_mod_cast a1
  have ht : (11 : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : 11 ≤ (Fm.D x ι).R.t)
  have hft : ((Fm.D x ι).R.f : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : (Fm.D x ι).R.f ≤ (Fm.D x ι).R.t)
  have hrt : ((Fm.D x ι).R.r : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : (Fm.D x ι).R.r ≤ (Fm.D x ι).R.t)
  have hb1 : 1 ≤ (Fm.L x ι).sc.b := Real.one_le_exp (by linarith)
  have hb0' : 0 < (Fm.L x ι).sc.b := Real.exp_pos _
  have hq : (1 : ℝ) ≤ (Fm.D x ι).host.q := by exact_mod_cast (Fm.D x ι).host.hyp.1.one_lt.le
  have hd' : (1 : ℝ) ≤ (Fm.D x ι).host.d := by exact_mod_cast (Fm.D x ι).host.hyp.2.1.one_lt.le
  have hn : (1 : ℝ) ≤ (Fm.D x ι).R.n := by exact_mod_cast (Fm.D x ι).R.ord_pos
  have hqd : (1 : ℝ) ≤ ((Fm.D x ι).host.q : ℝ) * (Fm.D x ι).host.d := by nlinarith
  have hs : Real.sqrt (((Fm.D x ι).host.q : ℝ) * (Fm.D x ι).host.d) ≤ ((Fm.D x ι).host.q : ℝ) * (Fm.D x ι).host.d := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hc : (Fm.D x ι).host.rdE ≤ szCond (Fm.L x ι) := by
    unfold szCond
    exact UpperTheory.Ram.Rd.rdE_le_cond _
  have hc1 : (1 : ℝ) ≤ szCond (Fm.L x ι) := h1.trans hc
  have hsb : Real.sqrt (Fm.L x ι).sc.b ≤ (Fm.L x ι).sc.b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hrdb : (Fm.D x ι).host.rdE ≤ (Fm.L x ι).sc.b := by
    have e1 : (Fm.D x ι).host.rdE ≤ szCond (Fm.L x ι) ^ 36 * ((Fm.D x ι).R.t : ℝ) ^ 150 :=
      hc.trans ((le_self_pow₀ hc1 (by norm_num)).trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith))))
    exact (e1.trans sC).trans hsb
  have hlogrd : Real.log (ReciprocityTheory.ChartRestriction.G.I2.PT.rd (Fm.D x ι).host.E) ≤ 2 * (Fm.L x ι).sc.L := by
    rw [erd]
    have := Real.log_le_log (by linarith) hrdb
    unfold Formalism.BasicNotions.Scale.b at this
    rw [Real.log_exp] at this
    linarith
  have hlfr := hN.logfr.1
  have hlf : Real.log (ReciprocityTheory.ChartRestriction.G.I2.PT.f (Fm.D x ι).host.E : ℝ) ≤ 2 * (Fm.L x ι).sc.L := by
    rw [ef]
    have hf0 : (0 : ℝ) < (Fm.D x ι).R.f := by linarith
    have := Real.log_le_log hf0 (le_mul_of_one_le_right hf0.le (by linarith : (1 : ℝ) ≤ (Fm.D x ι).R.r))
    linarith
  have hlr : Real.log ((Fm.D x ι).R.r : ℝ) ≤ (Fm.L x ι).sc.L := by
    have hr0 : (0 : ℝ) < (Fm.D x ι).R.r := by linarith
    have := Real.log_le_log hr0 (le_mul_of_one_le_left hr0.le (by linarith : (1 : ℝ) ≤ (Fm.D x ι).R.f))
    linarith
  have hg0 : ∀ k, (0 : ℝ) < (Fm.D x ι).host.g k := fun k => by exact_mod_cast ((Fm.D x ι).host.g_prime k).pos
  have hq1 : 1 ≤ (Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero ((Fm.D x ι).host.g_prime 0).ne_zero ((Fm.D x ι).host.g_prime 1).ne_zero)
  have hlq : Real.log (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) ≤ 70 * (Fm.L x ι).sc.L := by
    push_cast
    rw [Real.log_mul (hg0 0).ne' (hg0 1).ne']
    linarith [hN.logg 0, hN.logg 1]
  have hP := archimedeanBoundTotalConstant_nonneg_le_bound (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m
    (Fm.L x ι).sc.L (by linarith) (by rw [ef]; omega) (by omega) (by omega) a5.2.1 hq1 (by rw [erd]; exact h1)
    hlogrd hlf hlr hlq
  rw [ef] at hP
  refine ⟨?_, hP.1, ?_, fun DF hDF hDFb => ⟨?_, ?_⟩⟩
  · rw [hW.sig.2.1]; unfold Formalism.BasicNotions.Ranks.sigW; omega
  ·
    have hZ1 : (1 : ℝ) ≤ zBase (Fm.L x ι) := by
      unfold zBase
      have := mul_le_mul hfR hrR (by norm_num) (by linarith)
      nlinarith
    have hZ : zBase (Fm.L x ι) ^ 2 ≤ (Fm.parT x hx ι).PP :=
      (pow_le_pow_right₀ hZ1 (by norm_num)).trans hN.ppLow
    have hD1 : (1 : ℝ) ≤ (dimFlag (dat p i) : ℝ) := by
      rw [hW.dim]
      have : 1 ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 :=
        Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (Nat.choose_pos (by omega)).ne')
      exact_mod_cast this
    have hT0 : (0 : ℝ) ≤ lenT p i (Fm.parT x hx ι).PP := Nat.cast_nonneg _
    have hPP0 : 0 ≤ (Fm.parT x hx ι).PP := le_trans (by positivity) hZ
    have hrow := hW.what₂.2
    have hTP : (lenT p i (Fm.parT x hx ι).PP : ℝ) * (Fm.parT x hx ι).PP ≤ (Fm.L x ι).sc.b := by
      revert hrow hD1 hT0 hPP0 hL10
      generalize (lenT p i (Fm.parT x hx ι).PP : ℝ) = T
      generalize (Fm.parT x hx ι).PP = PP
      generalize (dimFlag (dat p i) : ℝ) = Dd
      generalize (Fm.L x ι).sc.L = L
      generalize (Fm.L x ι).sc.b = b
      intro hrow hD1 hT0 hPP0 hL10
      have e0 : 0 ≤ PP * T := mul_nonneg hPP0 hT0
      have e1 : PP * T * 1 ≤ PP * T * Dd ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hD1) e0
      have e2 : PP * T * Dd ^ 2 * 1 ≤ PP * T * Dd ^ 2 * L := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith
    have hU : (Fm.L x ι).sc.b ≤ unitE p := by
      rw [hW.unit]
      have e1 : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.m := by nlinarith
      have e2 : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.m * (Fm.L x ι).sc.L * Real.log (Real.log (Fm.L x ι).sc.x) := by
        have := mul_le_mul e1 (by linarith : (1 : ℝ) ≤ (Fm.L x ι).sc.L) zero_le_one (by linarith)
        have := mul_le_mul this hLL zero_le_one (by linarith)
        linarith
      have : (Fm.L x ι).sc.b * 1 ≤ (Fm.L x ι).sc.b *
          ((Fm.D x ι).R.f * (Fm.D x ι).R.m * (Fm.L x ι).sc.L * Real.log (Real.log (Fm.L x ι).sc.x)) :=
        mul_le_mul_of_nonneg_left e2 (by linarith)
      nlinarith
    have hPz : GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1)
        (Fm.D x ι).R.m 5 1 ≤ 200000 * zBase (Fm.L x ι) ^ 2 := hP.2
    calc (lenT p i (Fm.parT x hx ι).PP : ℝ) * GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r
          ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m 5 1
        ≤ (lenT p i (Fm.parT x hx ι).PP : ℝ) * (200000 * (Fm.parT x hx ι).PP) :=
          mul_le_mul_of_nonneg_left (hPz.trans (by linarith)) hT0
      _ = 200000 * ((lenT p i (Fm.parT x hx ι).PP : ℝ) * (Fm.parT x hx ι).PP) := by ring
      _ ≤ 200000 * unitE p := by linarith
  ·
    have hDF1 : (1 : ℝ) ≤ DF := by exact_mod_cast hDF
    have hk : (1 : ℝ) ≤ (Fm.D x ι).R.k := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.k)
    have hg : ∀ k, (Fm.L x ι).sc.b ^ 8 ≤ ((Fm.D x ι).host.g k : ℝ) := fun k =>
      (pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_left (by linarith) hk) 8).trans (sG k k).1
    have key := size_inequality_real (Fm.D x ι).host.rdE (szCond (Fm.L x ι)) (Fm.D x ι).R.t (Fm.L x ι).sc.b (Fm.D x ι).R.f
      (Fm.D x ι).R.r DF ((Fm.D x ι).host.g 0) ((Fm.D x ι).host.g 1) h1 hc sC ht (by linarith) hft (by linarith) hrt
      hDF1 hDFb (hg 0) (hg 1)
    have hrun := GlobalTheory.RunParametersOfLower.runOK_of_le (Fm.D x ι).host.E (Fm.D x ι).R.r DF
      ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m hDF (by rw [ef]; nlinarith) (by omega) hm4 hf2 hrd16
      (by unfold ReciprocityTheory.ChartRestriction.G.I2.RR; rw [ef, erd]; push_cast; exact key)
    rw [ef] at hrun
    exact hrun
  ·
    intro s hs
    have hR0 : (1 : ℝ) ≤ Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF)) ^ 2 := by
      rw [Real.sq_sqrt (by positivity)]
      have : (0 : ℝ) ≤ DF := Nat.cast_nonneg _
      nlinarith
    have hRR : (1 : ℝ) ≤ ReciprocityTheory.ChartRestriction.G.I2.RR (E := (Fm.D x ι).host.E) := by
      unfold ReciprocityTheory.ChartRestriction.G.I2.RR; exact one_le_pow₀ (by linarith)
    have := sqrt_lt_th_real ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Y.d.l₂.M : ℝ)
      (ReciprocityTheory.ChartRestriction.G.I2.PT.f (Fm.D x ι).host.E : ℝ) (Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF)))
      (ReciprocityTheory.ChartRestriction.G.I2.RR (E := (Fm.D x ι).host.E)) (Fm.L x ι).sc.b s hq1 hb0' (level_ge p i Y hY (by linarith))
      (by rw [ef]; linarith) hR0 hRR hs
    unfold ReciprocityTheory.ChartRestriction.G.I2.th
    exact this
end GlobalTheory.ThetaSizeBounds
end
end
