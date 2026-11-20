import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.RowsFinC
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.PointwiseKernelBound
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.NearNonzeroTerms
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FarTermSum
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.RareFlags
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DeepSetBound
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DefiniteFiniteCount
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.LatticeCountingTheorem
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeRightTranslateLowerBoun
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsSubLeExpNegSixteenthMul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientIntegrableMajorant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountHypPAtAddQAt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NearAbsMeasurableAndSplit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsIntegralSubConstMulLeOfSplit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphicKernelConvergencePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrablePhStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnitaryGroupCountEqMainTermStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CountSum

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1, h.2.1, hn.trans h.2.2.1, h.2.2.2⟩`.
-/
theorem countHyp_mono {B : RowsAut} {Cg : ℝ} {n₀ n₁ : ℕ} {d : InfinitePlace B.I.F → ℝ} {p q : ℕ} {b : ℝ}
    (h : CountHyp B Cg n₀ d p q b) (hn : n₁ ≤ n₀) : CountHyp B Cg n₁ d p q b :=
  ⟨h.1, h.2.1, hn.trans h.2.2.1, h.2.2.2⟩

/- English proof (translation)
Introduce `hfinC hflag hpt hnear hfar hrare hdeep Cg`. Distinguish the cases in `hC : 0 ≤ Cg`. Use `swap`. Conclude with `⟨8, fun B d p q b h => absurd (GlobalTheory.Dec.countHyp_numerics B Cg 8 d p q b le_rfl h).1 hC⟩`. Take `⟨n₁, hn₁⟩` from `hnear Cg hC`.

Take `⟨n₂, hn₂⟩` from `hfar Cg hC`. Take `⟨n₃, hn₃⟩` from `hrare`. Take `⟨n₄, hn₄⟩` from `hdeep Cg hC`. Use `⟨8 + n₁ + n₂ + n₃ + n₄ + ⌈Real.exp 15⌉₊, fun B d p q b H => ?_⟩` and prove the remaining obligations. Establish `hfin` using `hfinC B Cg _ d p q b (by omega) H`.

Use `⟨hfin, ?_⟩` and prove the remaining obligations. Take `⟨-, -, hf1, -, hpq, h2q, hrk, hmin, hd, -, -, hts, h, -, hgap, -, h32, -, h120, -⟩` from `GlobalTheory.Dec.countHyp_numerics B Cg _ d p q b (by omega) H`. Establish `H1` using `countHyp_mono H (n₁ := n₁) (by omega)`. Establish `H2` using `countHyp_mono H (n₁ := n₂) (by omega)`. Establish `H4` using `countHyp_mono H (n₁ := n₄) (by omega)`.

Take `⟨hDS, hsig, hn, hq2, hrd, hlf, -, -, -, hg, -, hpr, h4, hsp, -⟩` from `H`. Break down `Nat.eq_zero_or_pos q with rfl | hq` into its components or cases. Establish `e` using `GlobalTheory.T.definiteUnitaryGroup_count_eq_mainTerm B d p ⟨hDS, hsig, by omega, hg, hpr, h4, hsp⟩ hfin`. Rewrite using `[← e, sub_self, abs_zero]`. Check the signs of the components of the expression.

Establish `hn1 : 1 ≤ B.I.n` using `by omega`. Take `⟨hT, hL, hS, -⟩` from `GlobalTheory.CongTop.adelic_topology B.I`. Establish `: BorelSpace B.I.GA` using `inferInstance`. Take `⟨-, -, hphe1, him, hre, -, hloc⟩` from `hpt B d p q h hDS hsig hgap (by rw [hmin]; exact h120)`. Take `⟨-, hv0, hvT, -⟩` from `hflag B.I B.μf B.fund B.fund_spec p q hsig h2q 1 (fun _ => 1) le_rfl (fun _ => le_rfl) (by simpa using Nat.succ_le_of_lt hq) ∅ MeasurableSet.empty (Set.empty_subset _)`.

Take `⟨hc, hle, hint⟩` from `GlobalTheory.Dec.PhMajProof.phMaj B d h hDS hloc`. Establish `hI : Integrable (ph B d) (muInf B.I)`. Establish `h0` using `hint 0 le_rfl (fun v => Or.inr (by`. Establish `h1` using `h32 v`. Rewrite `h1`, the goal using `[hrk v]`.

Establish `hs : 0 < Real.sqrt q` using `Real.sqrt_pos.2 (by exact_mod_cast hq)`. Establish `hqn : (q : ℝ) < B.I.n` using `by exact_mod_cast (by omega : q < B.I.n)`. Establish `hn0 : (0 : ℝ) < B.I.n` using `by exact_mod_cast hn1`. Use `mul_lt_mul_of_pos_left hqn (mul_pos hs hn0)` as an intermediate fact. Use the proof step `nlinarith))`.

Simplify using `only [zero_mul, Real.exp_zero, mul_one] at h0`. Conclude with `h0.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hle)`. Take `⟨-, -, ⟨T, hT⟩, -⟩` from `GlobalTheory.GlobProj.globalProj_holds B d hDS hI`. Take `⟨-, Fc, -, -, -, hexp, hKi, hD, -⟩` from `GlobalTheory.T.kernelB' B d h hDS hn1 hloc h32 hfin T hT`. Take `⟨hsum, -⟩` from `GlobalTheory.T.automorphicKernel_convergence_properties B d h hDS hn1 hloc h32`.

Take `⟨hmeas, hsplit⟩` from `GlobalTheory.NearMeas.nearAbs_measurable_and_split B d hDS`. Establish `hcl : Continuous (least B.I)` using `(GlobalTheory.LeastVar.least_variation_continuity B.I hn1).2.1`. Use `set μ := (B.I.muA B.μf).restrict B.fund with hμ`. Establish `: IsFiniteMeasure μ` using `⟨by rw [hμ, Measure.restrict_apply_univ]; exact hvT⟩`. Establish `hM : MeasurableSet {x | tauStar B q b ≤ least B.I x}` using `(isClosed_le continuous_const hcl).measurableSet`.

Establish `hvol : 0 < B.I.vol B.μf B.fund` using `ENNReal.toReal_pos hv0.ne' hvT.ne`. Establish `hc0 : 0 ≤ (∏ v, d v) * (B.e 1).re` using `mul_nonneg hd.le hre`. Establish `hmain : mainTerm B d = (∏ v, d v) * (B.e 1).re * B.I.vol B.μf B.fund`. Unfold `mainTerm AutInst.Dstar`. Expand and normalize the polynomial expressions, which then agree.

Establish `hm0 : 0 ≤ mainTerm B d` using `hmain ▸ mul_nonneg hc0 hvol.le`. Establish `e1 : {x | tauStar B q b ≤ least B.I x} ∩ B.fund = {x | x ∈ B.fund ∧ tauStar B q b ≤ least B.I x}` using `Set.inter_comm _ _`. Establish `e2 : {x | tauStar B q b ≤ least B.I x}ᶜ ∩ B.fund = GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet B q b`. Use extensionality with `x`. Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet, and_comm]`.

Establish `key` using `GlobalTheory.abs_integral_sub_const_mul_le_of_split B.I.GA μ {x | tauStar B q b ≤ least B.I x} (fun x => (kern B.I (phe B d) x x).re) (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d) ((∏ v …`. Simplify using `only [hexp, Complex.re_sum]`. Use `Finset.sum_nonneg fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.ofReal_re]`. Conclude with `Complex.normSq_nonneg _)`.

Use `hmeas hc0 (mul_nonneg (Real.exp_pos _).le hm0) (mul_nonneg (Real.exp_pos _).le hm0) (by positivity)`. Use the proof step `(fun x _ => by`. Use `le_trans (ENNReal.ofReal_le_ofReal ?_) (hsplit x (hsum x x).1)` and prove the remaining obligations. Use `le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)` and prove the remaining obligations. Rewrite using `[Complex.sub_re, hphe1, Complex.re_ofReal_mul])`.

Use the proof step `(by rw [hμ, Measure.restrict_restrict hM, e1]; exact hn₁ B d p q b hq H1)`. Use the proof step `(by rw [hμ, Measure.restrict_restrict hM, e1]; exact hn₂ B d p q b hq H2)`. Use the proof step `(by rw [hμ, Measure.restrict_restrict hM.compl, e2]; exact hn₄ B d p q b hq H4)`. Establish `hKD : ∫ x, (kern B.I (phe B d) x x).re ∂μ = (B.D : ℝ)`. Use `integral_re hKi` as an intermediate fact.

Rewrite `this` using `[hD]`. Simplify using `using this`. Establish `hU : (μ Set.univ).toReal = B.I.vol B.μf B.fund`. Rewrite using `[hμ, Measure.restrict_apply_univ]`. Both sides reduce to the same expression.

Establish `hP : (μ {x | tauStar B q b ≤ least B.I x}ᶜ).toReal ≤ Real.exp (-(1 / 4 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log B.I.n)) * B.I.vol B.μf B.fund`. Establish `h1` using `hn₃ B p q hsig (by omega) hq2 hrd hlf`. Unfold `prob at h1`. Rewrite `h1` using `[div_le_iff₀ hvol]`. Use `le_trans ?_ h1` and prove the remaining obligations.

Rewrite using `[hμ, Measure.restrict_apply hM.compl]`. Use `ENNReal.toReal_mono ((measure_mono Set.inter_subset_right).trans_lt hvT).ne (measure_mono (Set.inter_subset_inter_left _ fun x hx => ?_))` and prove the remaining obligations. Establish `hx' : ¬ tauStar B q b ≤ least B.I x` using `hx`. Conclude with `lt_trans (not_le.1 hx') (hts hq).1`. Rewrite `key` using `[hKD, hU, ← hmain]`.

Establish `hP'` using `mul_le_mul_of_nonneg_left hP hc0`. Establish `hne : Real.exp 15 ≤ (B.I.n : ℝ)` using `Nat.ceil_le.1 (by omega)`. Establish `fin` using `GlobalTheory.abs_sub_le_exp_neg_sixteenth_mul (B.D : ℝ) (mainTerm B d) B.I.n B.I.f (by positivity) hm0 hne (by exact_mod_cast hf1) (by`. Use `key.trans ?_` and prove the remaining obligations. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound`.

Simplify using `only [neg_mul]`. Rewrite `*` using `[hmain]`. Use polynomial arithmetic with `[hP'])`. Simplify `fin` using `only [neg_mul]`.
-/
theorem countingTheorem_of_finite_of_bounds :
    (∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ →
      CountHyp B Cg n₀ d p q b → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re)) →
    GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Deep.PtBound →
    GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.NearModerate → GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.FarModerate → GlobalTheory.IndefiniteRowSideFullHecke.RareFlags.FlagRare →
    GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.DeepBound → GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem := by
  intro hfinC hflag hpt hnear hfar hrare hdeep Cg
  by_cases hC : 0 ≤ Cg
  swap
  · exact ⟨8, fun B d p q b h => absurd (GlobalTheory.Dec.countHyp_numerics B Cg 8 d p q b le_rfl h).1 hC⟩
  obtain ⟨n₁, hn₁⟩ := hnear Cg hC
  obtain ⟨n₂, hn₂⟩ := hfar Cg hC
  obtain ⟨n₃, hn₃⟩ := hrare
  obtain ⟨n₄, hn₄⟩ := hdeep Cg hC
  refine ⟨8 + n₁ + n₂ + n₃ + n₄ + ⌈Real.exp 15⌉₊, fun B d p q b H => ?_⟩
  have hfin := hfinC B Cg _ d p q b (by omega) H
  refine ⟨hfin, ?_⟩
  obtain ⟨-, -, hf1, -, hpq, h2q, hrk, hmin, hd, -, -, hts, h, -, hgap, -, h32, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg _ d p q b (by omega) H
  have H1 := countHyp_mono H (n₁ := n₁) (by omega)
  have H2 := countHyp_mono H (n₁ := n₂) (by omega)
  have H4 := countHyp_mono H (n₁ := n₄) (by omega)
  obtain ⟨hDS, hsig, hn, hq2, hrd, hlf, -, -, -, hg, -, hpr, h4, hsp, -⟩ := H
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have e := GlobalTheory.T.definiteUnitaryGroup_count_eq_mainTerm B d p ⟨hDS, hsig, by omega, hg, hpr, h4, hsp⟩ hfin
    rw [← e, sub_self, abs_zero]
    positivity
  have hn1 : 1 ≤ B.I.n := by omega
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  have : BorelSpace B.I.GA := inferInstance
  obtain ⟨-, -, hphe1, him, hre, -, hloc⟩ := hpt B d p q h hDS hsig hgap (by rw [hmin]; exact h120)
  obtain ⟨-, hv0, hvT, -⟩ := hflag B.I B.μf B.fund B.fund_spec p q hsig h2q 1 (fun _ => 1) le_rfl
    (fun _ => le_rfl) (by simpa using Nat.succ_le_of_lt hq) ∅ MeasurableSet.empty (Set.empty_subset _)
  obtain ⟨hc, hle, hint⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hDS hloc
  have hI : Integrable (ph B d) (muInf B.I) := by
    have h0 := hint 0 le_rfl (fun v => Or.inr (by
      have h1 := h32 v
      rw [hrk v] at h1 ⊢
      have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 (by exact_mod_cast hq)
      have hqn : (q : ℝ) < B.I.n := by exact_mod_cast (by omega : q < B.I.n)
      have hn0 : (0 : ℝ) < B.I.n := by exact_mod_cast hn1
      have := mul_lt_mul_of_pos_left hqn (mul_pos hs hn0)
      nlinarith))
    simp only [zero_mul, Real.exp_zero, mul_one] at h0
    exact h0.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hle)
  obtain ⟨-, -, ⟨T, hT⟩, -⟩ := GlobalTheory.GlobProj.globalProj_holds B d hDS hI
  obtain ⟨-, Fc, -, -, -, hexp, hKi, hD, -⟩ := GlobalTheory.T.kernelB' B d h hDS hn1 hloc h32 hfin T hT
  obtain ⟨hsum, -⟩ := GlobalTheory.T.automorphicKernel_convergence_properties B d h hDS hn1 hloc h32
  obtain ⟨hmeas, hsplit⟩ := GlobalTheory.NearMeas.nearAbs_measurable_and_split B d hDS
  have hcl : Continuous (least B.I) := (GlobalTheory.LeastVar.least_variation_continuity B.I hn1).2.1
  set μ := (B.I.muA B.μf).restrict B.fund with hμ
  have : IsFiniteMeasure μ := ⟨by rw [hμ, Measure.restrict_apply_univ]; exact hvT⟩
  have hM : MeasurableSet {x | tauStar B q b ≤ least B.I x} :=
    (isClosed_le continuous_const hcl).measurableSet
  have hvol : 0 < B.I.vol B.μf B.fund := ENNReal.toReal_pos hv0.ne' hvT.ne
  have hc0 : 0 ≤ (∏ v, d v) * (B.e 1).re := mul_nonneg hd.le hre
  have hmain : mainTerm B d = (∏ v, d v) * (B.e 1).re * B.I.vol B.μf B.fund := by
    unfold mainTerm AutInst.Dstar; ring
  have hm0 : 0 ≤ mainTerm B d := hmain ▸ mul_nonneg hc0 hvol.le
  have e1 : {x | tauStar B q b ≤ least B.I x} ∩ B.fund = {x | x ∈ B.fund ∧ tauStar B q b ≤ least B.I x} :=
    Set.inter_comm _ _
  have e2 : {x | tauStar B q b ≤ least B.I x}ᶜ ∩ B.fund = GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet B q b := by
    ext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet, and_comm]
  have key := GlobalTheory.abs_integral_sub_const_mul_le_of_split B.I.GA μ {x | tauStar B q b ≤ least B.I x}
    (fun x => (kern B.I (phe B d) x x).re) (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d)
    ((∏ v, d v) * (B.e 1).re) (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound B d)
    (Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) * mainTerm B d)
    ((B.D : ℝ) * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) hM hKi.re
    (fun x => by
      simp only [hexp, Complex.re_sum]
      refine Finset.sum_nonneg fun i _ => ?_
      rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
      exact Complex.normSq_nonneg _)
    hmeas hc0 (mul_nonneg (Real.exp_pos _).le hm0) (mul_nonneg (Real.exp_pos _).le hm0) (by positivity)
    (fun x _ => by
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hsplit x (hsum x x).1)
      refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
      rw [Complex.sub_re, hphe1, Complex.re_ofReal_mul])
    (by rw [hμ, Measure.restrict_restrict hM, e1]; exact hn₁ B d p q b hq H1)
    (by rw [hμ, Measure.restrict_restrict hM, e1]; exact hn₂ B d p q b hq H2)
    (by rw [hμ, Measure.restrict_restrict hM.compl, e2]; exact hn₄ B d p q b hq H4)
  have hKD : ∫ x, (kern B.I (phe B d) x x).re ∂μ = (B.D : ℝ) := by
    have := integral_re hKi
    rw [hD] at this
    simpa using this
  have hU : (μ Set.univ).toReal = B.I.vol B.μf B.fund := by
    rw [hμ, Measure.restrict_apply_univ]; rfl
  have hP : (μ {x | tauStar B q b ≤ least B.I x}ᶜ).toReal ≤
      Real.exp (-(1 / 4 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log B.I.n)) * B.I.vol B.μf B.fund := by
    have h1 := hn₃ B p q hsig (by omega) hq2 hrd hlf
    unfold prob at h1
    rw [div_le_iff₀ hvol] at h1
    refine le_trans ?_ h1
    rw [hμ, Measure.restrict_apply hM.compl]
    refine ENNReal.toReal_mono ((measure_mono Set.inter_subset_right).trans_lt hvT).ne
      (measure_mono (Set.inter_subset_inter_left _ fun x hx => ?_))
    have hx' : ¬ tauStar B q b ≤ least B.I x := hx
    exact lt_trans (not_le.1 hx') (hts hq).1
  rw [hKD, hU, ← hmain] at key
  have hP' := mul_le_mul_of_nonneg_left hP hc0
  have hne : Real.exp 15 ≤ (B.I.n : ℝ) := Nat.ceil_le.1 (by omega)
  have fin := GlobalTheory.abs_sub_le_exp_neg_sixteenth_mul (B.D : ℝ) (mainTerm B d) B.I.n B.I.f (by positivity) hm0 hne
    (by exact_mod_cast hf1) (by
      refine key.trans ?_
      unfold GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound
      simp only [neg_mul]
      rw [hmain] at *
      nlinarith [hP'])
  simpa only [neg_mul] using fin

end GlobalTheory.CountSum
