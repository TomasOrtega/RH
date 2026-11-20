import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeHsNormLeDegreeBoundRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeArithmetic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolPos
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSigmaFiniteQuot
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentCovolumeFiniteBoundedStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralStabiliserCovolumeLeIndexWeightStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermAmplitudeLeCovolumeLocalAmplitudesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdaptedNormalFormGivesRealNormalFormStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrictFundamentalSetIntegralStabilizerExistsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapHypothesisOfLargenessConstantGeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointGramMinorsAgreeProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdaptedNormalFormNormsMinorsEqLabelProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedNormalFormRelevantTermProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalBoundProductOverPlacesLabelStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeSizeConsequencesOfWordIndependentHyps
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsIdentityOfEqualFlags
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWin

noncomputable section
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints GlobalTheory.TypeAsm

namespace GlobalTheory.TypeAsm.AmpTerms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `h0 : 0 ≤ ∏ i, Real.sqrt (f i)` using `Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _`. Establish `h2 : (∏ i, Real.sqrt (f i)) ^ 2 = ∏ i, f i`. Rewrite using `[← Finset.prod_pow]`. Conclude with `Finset.prod_congr rfl fun i _ => Real.sq_sqrt (hf i)`. Rewrite using `[← h2, Real.sqrt_sq h0]`.
-/
theorem prod_sqrt {ι : Type} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∏ i, Real.sqrt (f i) = Real.sqrt (∏ i, f i) := by
  have h0 : 0 ≤ ∏ i, Real.sqrt (f i) := Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _
  have h2 : (∏ i, Real.sqrt (f i)) ^ 2 = ∏ i, f i := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => Real.sq_sqrt (hf i)
  rw [← h2, Real.sqrt_sq h0]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, div_one]`. Use `_ ≤ (∏ i, Real.sqrt (d i)) * (A ^ Fintype.card ι * PB) := by`. Apply `mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _)` to reduce the goal to its premises. Conclude with `mul_le_mul_of_nonneg_left hg (pow_nonneg hA _)`.
-/
theorem prod_bound {ι : Type} [Fintype ι] (x d g : ι → ℝ) (A PB : ℝ) (hA : 0 ≤ A)
    (hx : ∀ i, 0 ≤ x i) (h : ∀ i, x i ≤ Real.sqrt (d i) * (A / 1 * g i)) (hg : ∏ i, g i ≤ PB) :
    ∏ i, x i ≤ (∏ i, Real.sqrt (d i)) * (A ^ Fintype.card ι * PB) := by
  calc ∏ i, x i ≤ ∏ i, (Real.sqrt (d i) * (A / 1 * g i)) :=
        Finset.prod_le_prod (fun i _ => hx i) (fun i _ => h i)
    _ = (∏ i, Real.sqrt (d i)) * (A ^ Fintype.card ι * ∏ i, g i) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, div_one]
    _ ≤ (∏ i, Real.sqrt (d i)) * (A ^ Fintype.card ι * PB) := by
        apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left hg (pow_nonneg hA _)

/- English proof (translation)
Establish `s1 : a ≤ a * V * L` using `by nlinarith`. Establish `s2 : a * V * L ≤ w * (vol * Pr) * L` using `mul_le_mul_of_nonneg_right hfact hL`. Establish `s3 : vol * Pr ≤ om * (vk * L) * Pr` using `mul_le_mul_of_nonneg_right hvol hPr0`. Establish `s4 : om * (vk * L) * Pr ≤ om * (vk * L) * (sd * (A0f * PB))` using `mul_le_mul_of_nonneg_left hPr (by positivity)`. Establish `s5 : w * (vol * Pr) * L ≤ w * (om * (vk * L) * (sd * (A0f * PB))) * L`.

Apply `mul_le_mul_of_nonneg_right _ hL` to reduce the goal to its premises. Conclude with `mul_le_mul_of_nonneg_left (s3.trans s4) hw`. Establish `s6 : w * (om * (vk * L) * (sd * (A0f * PB))) * L = w * sd * om * (vk * L * L * A0f * PB)` using `by ring`. Establish `s7 : w * sd * om * (vk * L * L * A0f * PB) ≤ w * sd * om * G` using `mul_le_mul_of_nonneg_left hG (by positivity)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem chain {a V L w vol Pr om vk sd A0f PB G : ℝ} (ha : 0 ≤ a) (hV : 1 ≤ V * L) (hL : 0 ≤ L) (hw : 0 ≤ w)
    (hPr0 : 0 ≤ Pr) (hom : 0 ≤ om) (hvk : 0 ≤ vk)
    (hfact : a * V ≤ w * (vol * Pr)) (hvol : vol ≤ om * (vk * L)) (hPr : Pr ≤ sd * (A0f * PB))
    (hG : vk * L * L * A0f * PB ≤ G) (hsd : 0 ≤ sd) : a ≤ w * sd * G * om := by
  have s1 : a ≤ a * V * L := by nlinarith
  have s2 : a * V * L ≤ w * (vol * Pr) * L := mul_le_mul_of_nonneg_right hfact hL
  have s3 : vol * Pr ≤ om * (vk * L) * Pr := mul_le_mul_of_nonneg_right hvol hPr0
  have s4 : om * (vk * L) * Pr ≤ om * (vk * L) * (sd * (A0f * PB)) :=
    mul_le_mul_of_nonneg_left hPr (by positivity)
  have s5 : w * (vol * Pr) * L ≤ w * (om * (vk * L) * (sd * (A0f * PB))) * L := by
    apply mul_le_mul_of_nonneg_right _ hL
    exact mul_le_mul_of_nonneg_left (s3.trans s4) hw
  have s6 : w * (om * (vk * L) * (sd * (A0f * PB))) * L = w * sd * om * (vk * L * L * A0f * PB) := by ring
  have s7 : w * sd * om * (vk * L * L * A0f * PB) ≤ w * sd * om * G :=
    mul_le_mul_of_nonneg_left hG (by positivity)
  nlinarith

/- English proof (translation)
Take `⟨⟨-, hCk, hmf, -, -, -, -, -, -, -, hrd, -, -, -, -, -, -, -, hv, -, -, -, hT, -, hCl0⟩, -, -⟩` from `hH.1`. Establish `hm : D.R.m = 2 * D.R.rS + 2` using `D.R.rS_two.symm`. Establish `hL : 1 < large₂.sc.L` using `Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos`. Establish `hrdv : D.host.rdE = 2 * D.host.v` using `by unfold Host.v; ring`. Establish `hb : large₂.sc.b = Real.exp large₂.sc.L` using `rfl`.

Establish `hf : 1 ≤ D.R.f`. Establish `: 1 ≤ D.R.m ^ 4` using `Nat.one_le_pow _ _ (by omega)`. Use linear arithmetic over natural numbers and integers. Establish `h2v : 2 * D.host.v ≤ large₂.sc.b`. Rewrite using `[← hrdv, hb]`.

Establish `hpos : 0 < D.host.rdE` using `by rw [hrdv]; linarith`. Establish `hrd' : Real.log D.host.rdE ≤ large₂.sc.L` using `hrd.trans (div_le_self (by linarith) hCl)`. Conclude with `(Real.log_le_iff_le_exp hpos).1 hrd'`. Establish `hk40 : 40 * D.R.rS ^ 4 ≤ D.R.k`. Establish `hmr : (D.R.rS : ℝ) ≤ D.R.m` using `by rw [hm]; push_cast; linarith`.

Establish `hm1 : (1 : ℝ) ≤ D.R.m` using `by rw [hm]; push_cast; linarith`. Establish `hr0 : (0 : ℝ) ≤ D.R.rS` using `Nat.cast_nonneg _`. Establish `h4 : (D.R.rS : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 5`. Combine the equalities or inequalities in the displayed calculation. Establish `hf1 : (1 : ℝ) ≤ D.R.f` using `by exact_mod_cast hf`.

Establish `hm5 : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 5` using `by positivity`. Establish `hx : (D.R.m : ℝ) ^ 5 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L`. Establish `h1 : (D.R.m : ℝ) ^ 5 ≤ (D.R.m : ℝ) ^ 5 * D.R.f` using `le_mul_of_one_le_right hm5 hf1`. Conclude with `h1.trans (le_mul_of_one_le_right (by positivity) hL.le)`. Establish `hreal : ((40 * D.R.rS ^ 4 : ℕ) : ℝ) ≤ D.R.k`.

Use `push_cast`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_right hC'` to reduce the goal to its premises. Check the signs of the components of the expression. Use `_ = C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by ring`.

Use `_ ≤ D.R.k := hCk`. Conclude with `hreal` after adjusting the coercions. Use `⟨hm, hv, h2v, hf, hk40, ?_, fun w => ?_⟩` and prove the remaining obligations. Establish `: D.R.rS ≤ D.R.rS ^ 4`. Break down `Nat.eq_zero_or_pos D.R.rS with h | h` into its components or cases.

Rewrite using `[h]`. Evaluate the numerical expressions. Conclude with `Nat.le_self_pow (by norm_num) _`. Use linear arithmetic over natural numbers and integers. Establish `hb0 : 0 < large₂.sc.b` using `Real.exp_pos _`.

Conclude with `lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) (hT w).1`.
-/
theorem sizes {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cw cT CT C0 : ℝ}
    (hH : Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0) (hC' : 40 ≤ C') (hCl : 1 ≤ Cl) :
    D.R.m = 2 * D.R.rS + 2 ∧ 1 ≤ D.host.v ∧ 2 * D.host.v ≤ large₂.sc.b ∧ 1 ≤ D.R.f ∧
      40 * D.R.rS ^ 4 ≤ D.R.k ∧ 5 * D.R.rS ≤ D.R.k ∧ (∀ w, 0 < Tr D w) := by
  obtain ⟨⟨-, hCk, hmf, -, -, -, -, -, -, -, hrd, -, -, -, -, -, -, -, hv, -, -, -, hT, -, hCl0⟩, -, -⟩ := hH.1
  have hm : D.R.m = 2 * D.R.rS + 2 := D.R.rS_two.symm
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hrdv : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
  have hb : large₂.sc.b = Real.exp large₂.sc.L := rfl
  have hf : 1 ≤ D.R.f := by
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have h2v : 2 * D.host.v ≤ large₂.sc.b := by
    rw [← hrdv, hb]
    have hpos : 0 < D.host.rdE := by rw [hrdv]; linarith
    have hrd' : Real.log D.host.rdE ≤ large₂.sc.L :=
      hrd.trans (div_le_self (by linarith) hCl)
    exact (Real.log_le_iff_le_exp hpos).1 hrd'
  have hk40 : 40 * D.R.rS ^ 4 ≤ D.R.k := by
    have hmr : (D.R.rS : ℝ) ≤ D.R.m := by rw [hm]; push_cast; linarith
    have hm1 : (1 : ℝ) ≤ D.R.m := by rw [hm]; push_cast; linarith
    have hr0 : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
    have h4 : (D.R.rS : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 5 := by
      calc (D.R.rS : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 4 := pow_le_pow_left₀ hr0 hmr 4
        _ ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_right₀ hm1 (by norm_num)
    have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
    have hm5 : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := by positivity
    have hx : (D.R.m : ℝ) ^ 5 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
      have h1 : (D.R.m : ℝ) ^ 5 ≤ (D.R.m : ℝ) ^ 5 * D.R.f := le_mul_of_one_le_right hm5 hf1
      exact h1.trans (le_mul_of_one_le_right (by positivity) hL.le)
    have hreal : ((40 * D.R.rS ^ 4 : ℕ) : ℝ) ≤ D.R.k := by
      push_cast
      calc 40 * (D.R.rS : ℝ) ^ 4 ≤ 40 * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by linarith
        _ ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by
          apply mul_le_mul_of_nonneg_right hC'; positivity
        _ = C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by ring
        _ ≤ D.R.k := hCk
    exact_mod_cast hreal
  refine ⟨hm, hv, h2v, hf, hk40, ?_, fun w => ?_⟩
  · have : D.R.rS ≤ D.R.rS ^ 4 := by
      rcases Nat.eq_zero_or_pos D.R.rS with h | h
      · rw [h]; norm_num
      · exact Nat.le_self_pow (by norm_num) _
    omega
  · have hb0 : 0 < large₂.sc.b := Real.exp_pos _
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) (hT w).1

/- English proof (translation)
Introduce `hLoc hTailP Cg cb Cw cT CT C0 hcb hcT`. Take `⟨CH, hCH, hT⟩` from `hTailP Cg cb Cw cT CT C0 hcb hcT`. Use `⟨CH, hCH, fun Cs hCs => ?_⟩` and prove the remaining obligations. Take `⟨C₁, hC₁, hProd⟩` from `GlobalTheory.T.localBound_productOverPlaces_label Cs hCs`. Take `⟨Ca, hCa⟩` from `GlobalTheory.amplitude_arithmetic CH hCH`.

Use `⟨max Ca 0, le_max_right _ _, fun C hC => ?_⟩` and prove the remaining obligations. Establish `hC0 : 0 ≤ C` using `(le_max_right _ _).trans hC`. Establish `hCaC : Ca ≤ C` using `(le_max_left _ _).trans hC`. Take `⟨C'₁, Cl₁, hT1⟩` from `hT C₁`. Take `⟨Clg, hGap⟩` from `GlobalTheory.T.gapC_holds`.

Use `⟨max C'₁ 40, max (max Cl₁ Clg) 1, fun C' Cl hC' hCl => ?_⟩` and prove the remaining obligations. Introduce `D large₂ X Y u hTies hH hConc`. Establish `hCl1 : 1 ≤ Cl` using `(le_max_right _ _).trans hCl`. Take `⟨hm, hv, h2v, hf, hk40, hk5, hTr⟩` from `GlobalTheory.TypeAsm.AmpTerms.sizes hH ((le_max_right _ _).trans hC') hCl1`. Establish `hStd : Std D large₂` using `⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hH⟩`.

Establish `hCM : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E` using `hH.2.2.2.2.2.2.2`. Establish `hgap` using `hGap C' Cl Cg cb Cw cT CT C0 D large₂ ((le_max_right _ _).trans ((le_max_left _ _).trans hCl)) hH`. Take `⟨Ch, hBs, hGood⟩` from `hLoc D X ⟨u⟩ hgap hTies.dsig_tie`. Establish `hTail` using `hT1 C' Cl ((le_max_left _ _).trans hC') ((le_max_left _ _).trans ((le_max_left _ _).trans hCl)) D large₂ hTies hH hConc.2.2.2.2.2.2.2`. Take `⟨hcovTop, hcov1⟩` from `GlobalTheory.T.integralUnipotent_covolume_finite_bounded D large₂ X Y u Ch hStd`.

Establish `hb2 : 2 ≤ large₂.sc.b` using `by linarith`. Introduce `t ht`. Establish `hj1 : 1 ≤ jT t` using `Formalism.L2.SG.KappaOffDiagonal.JPosC_holds Cg cb Cw cT CT C0 C' Cl D large₂ X Y u hH hConc t ht`. Establish `hjr : jT t ≤ D.R.rS` using `Nat.sub_le _ _`. Take `⟨De, P, hP, hDel, hDeOK, hprod⟩` from `hProd D large₂ X Y u Ch CH hStd hCH hk40 hk5 t ht hjr hj1`.

Use `set c : ℝ := Formalism.L2.SG.TermOp.wt t * Real.sqrt (dpiC X u) * k2a large₂ CH Cs C (jT t) (labT t) with hc`. Establish `hc0 : 0 ≤ c` using `mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (amplitude_label_nonneg large₂ hC0 _ _)`. Establish `hinf` using `(GlobalTheory.DegAsm.WeightInf.main _ _ (HV D) hCM D.R.rS).2 (F0 X u) (Ft t) (dI D) t.lam`. Establish `hex : ∃ N, GlobalTheory.DegAsm.Adapt (F0 X u) (Ft t) (dI D) N`. Take `⟨N, hN, -⟩` from `GlobalTheory.T.exists_adaptedNormalForm_relevantTerm D large₂ X Y u hStd t ht`.

Conclude with `⟨N, hN⟩`. Establish `key : ∀ N : GlobalTheory.DegCnt.NF (HV D) D.R.rS, GlobalTheory.DegAsm.Adapt (F0 X u) (Ft t) (dI D) N → ‖(Y.tO u u).vec t‖ ≤ c * N.om t.lam`. Introduce `N hN`. Establish `hNj : N.j = jT t` using `(GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label D large₂ X Y u hStd t N hN).1`. Take `⟨β, n₁, g, n₂, hfr⟩` from `GlobalTheory.T.adaptedNormalForm_gives_real_normal_form D large₂ X Y u Ch hStd t N hN`.

Take `⟨K, hK⟩` from `GlobalTheory.T.strict_fundamentalSet_integralStabilizer_exists D X Y u t`. Use `set μ : D.what₂.Tau → Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) := fun τ => (ENNReal.ofReal 1 • GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β).map (Formalism.QuantumDeterminants.conjM (n₂ τ)⁻¹) with hμ`. Establish `hμN : ∀ τ, GlobalTheory.Amp.IsNormalFormStabilizerMeasure D.R.k D.R.rS N.j_le (zB X (Ch.Qi τ) u τ) (zB X (Ch.Qi τ) u τ) (gamT Ch t τ)⁻¹ 1 (μ τ)`. Introduce `τ`. Take `⟨h1, h2, h3, hfo⟩` from `hfr τ`.

Take `⟨-, hz, hz', hTz, ⟨cc, hnorm⟩, -⟩` from `hfo`. Conclude with `⟨hz, hz', hTz, n₁ τ, h1, n₂ τ, h2, g τ, β, cc, hnorm, h3, rfl⟩`. Establish `hvol` using `GlobalTheory.T.integralStabiliser_covolume_le_indexWeight D large₂ X Y u Ch hStd t N hN μ K hμN hK`. Establish `htr : ∀ (a b : ℕ) (e : a = b) (ha : a ≤ D.R.rS) (hb : b ≤ D.R.rS) (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (γ : GlobalTheory.SgInf.Mat D.R.k D.R.rS) (s : ℝ) (μ' : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)), GlobalTheory.Amp.IsNormalFormStabilizerMeasure D.R.k D.R.r …`. Introduce and unpack `a b rfl _ _ _ _ _ _ _ h`.

Conclude with `h`. Establish `hμJ : ∀ τ, GlobalTheory.Amp.IsNormalFormStabilizerMeasure D.R.k D.R.rS hjr (zB X (Ch.Qi τ) u τ) (zB X (Ch.Qi τ) u τ) (gamT Ch t τ)⁻¹ 1 (μ τ)` using `fun τ => htr _ _ hNj _ _ _ _ _ _ _ (hμN τ)`. Establish `hq : ∀ τ, _` using `fun τ => GlobalTheory.DegVol.StabQuot.exists_sigmaFinite_quot D.R.k D.R.rS (jT t) hjr (zB X (Ch.Qi τ) u τ) (zB X (Ch.Qi τ) u τ) (gamT Ch t τ) (muGB X (Ch.Q τ) (Ch.Qi τ) τ) (μ τ) ((hGood.2 u τ).1.2.2.2.2.2.2.1) (hμJ τ) (((GlobalTheory.T.realPointGramMinorsAgree_proof D X Y u Ch τ) …`. Use `choose hσμ hHaarμ hNR ν hσν hνnull hνq using hq`. Establish `hfact` using `GlobalTheory.T.termAmplitude_le_covolume_localAmplitudes D X Y u Ch hBs hGood hcovTop t ht.2 μ ν K (fun τ => ⟨hσμ τ, hHaarμ τ, hσν τ, hνnull τ, hνq τ⟩) hK`.

Establish `hr1 : 1 ≤ D.R.rS` using `hj1.trans hjr`. Establish `hjk : jT t + 2 ≤ D.R.k`. Establish `: D.R.rS ≤ D.R.rS ^ 4` using `Nat.le_self_pow (by norm_num) _`. Use linear arithmetic over natural numbers and integers. Establish `hqq : 16 * D.R.rS ^ 3 + 4 * D.R.rS + 2 ≤ C₁ * D.R.k * D.R.rS`.

Establish `a1 : D.R.rS ^ 3 ≤ D.R.rS ^ 5` using `Nat.pow_le_pow_right hr1 (by norm_num)`. Establish `a2 : D.R.rS ≤ D.R.rS ^ 5` using `Nat.le_self_pow (by norm_num) _`. Establish `a3 : 1 ≤ D.R.rS ^ 5` using `Nat.one_le_pow _ _ hr1`. Establish `a4 : 40 * D.R.rS ^ 4 * D.R.rS ≤ D.R.k * D.R.rS` using `Nat.mul_le_mul_right _ hk40`. Establish `a5 : D.R.k * D.R.rS ≤ C₁ * (D.R.k * D.R.rS)` using `Nat.le_mul_of_pos_left _ hC₁`.

Establish `a6 : 40 * D.R.rS ^ 4 * D.R.rS = 40 * D.R.rS ^ 5` using `by ring`. Rewrite using `[mul_assoc]`. Use linear arithmetic over natural numbers and integers. Establish `hH1 : 1 ≤ H1C large₂ CH`. Unfold `H1C`.

Conclude with `Real.one_le_rpow (by linarith) (by positivity)`. Establish `hloc` using `fun τ => GlobalTheory.T.amplitude_hsNorm_le_degreeBound_realPlace D τ u u 1 (locW Ch u u τ) _ (locS hBs u u τ) (by linarith) one_pos (hTr u) (hTr u) (hGood.2 u τ).1 (hGood.2 u τ).2 (jT t) hjr (C₁ * D.R.k * D.R.rS) (gamT Ch t τ) 1 (H1C large₂ CH) (De τ) _ (ν τ) hj1 hjk hqq one_pos …`. Establish `hom0 : 0 ≤ N.om t.lam` using `hinf.1.trans (hinf.2.1 N hN)`. Establish `hL0 : 0 ≤ lossV D` using `by unfold lossV; have := hv; positivity`. Establish `hvol' : (Measure.pi μ (trI Ch '' K)).toReal ≤ N.om t.lam * (D.host.v ^ (D.R.k * (D.R.rS - jT t) * D.R.f) * lossV D)`.

Rewrite using `[← hNj]`. Conclude with `ENNReal.toReal_le_of_le_ofReal (by have := hv; positivity) hvol`. Establish `hcard : Fintype.card D.what₂.Tau = D.R.f` using `D.what₂.card_Tau`. Establish `hsd : ∏ τ, Real.sqrt (Module.finrank ℂ (Formalism.L2.SG.LocWSOf.locW Ch u u τ).Wp : ℝ) = Real.sqrt (dpiC X u)`. Rewrite using `[prod_sqrt _ (fun τ => Nat.cast_nonneg _)]`.

Unfold `dpiC`. Rewrite using `[Formalism.L2.SG.Pf.AmpWin.finrank_tau]`. Both sides reduce to the same expression. Establish `hA0 : (0 : ℝ) ≤ (2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1 * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))` using `by have := hv; positivity`. Establish `hPr` using `prod_bound _ _ _ _ _ hA0 (fun τ => Real.sqrt_nonneg _) hloc hprod`.

Rewrite `hPr` using `[hsd, hcard]`. Establish `hG` using `hCa C hCaC D.R.k D.R.rS D.R.m D.R.f (jT t) large₂.sc.b D.host.v (k2Del D (jT t) (labT t)) (k2S D (H1C large₂ CH) (jT t) (labT t)) Cs P hm hj1 hjr (by omega) hf hb2 hv h2v hP hDel (one_le_sigma_product _ _ _)`. Establish `hfinal` using `chain (norm_nonneg _) hcov1 hL0 (Real.sqrt_nonneg _) (Finset.prod_nonneg fun τ _ => Real.sqrt_nonneg _) hom0 (by have := hv; positivity) hfact hvol' hPr hG (Real.sqrt_nonneg _)`. Use `hfinal.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[hc]`.

Unfold `k2a H1C`. Both sides reduce to the same expression. Establish `hfin` using `hinf.2.2 _ c hc0 hex key`. Use `show ‖(Y.tO u u).vec t‖ ≤ Formalism.L2.SG.TermOp.wt t * Real.sqrt (dpiC X u) * (omT t * k2a large₂ CH Cs C (jT t) (labT t))`. Establish `e : Formalism.L2.SG.TermOp.wt t * Real.sqrt (dpiC X u) * (omT t * k2a large₂ CH Cs C (jT t) (labT t)) = c * GlobalTheory.DegAsm.omI (F0 X u) (Ft t) (dI D) t.lam`.

Rewrite using `[hc]`. Unfold `omT`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hfin`.
-/
theorem amplitudeBound_of_localData_of_tailBound : GlobalTheory.TypeAsm.LocDatC → GlobalTheory.TypeAsm.TailP → GlobalTheory.TypeAsm.AmpP := by
  intro hLoc hTailP Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨CH, hCH, hT⟩ := hTailP Cg cb Cw cT CT C0 hcb hcT
  refine ⟨CH, hCH, fun Cs hCs => ?_⟩
  obtain ⟨C₁, hC₁, hProd⟩ := GlobalTheory.T.localBound_productOverPlaces_label Cs hCs
  obtain ⟨Ca, hCa⟩ := GlobalTheory.amplitude_arithmetic CH hCH
  refine ⟨max Ca 0, le_max_right _ _, fun C hC => ?_⟩
  have hC0 : 0 ≤ C := (le_max_right _ _).trans hC
  have hCaC : Ca ≤ C := (le_max_left _ _).trans hC
  obtain ⟨C'₁, Cl₁, hT1⟩ := hT C₁
  obtain ⟨Clg, hGap⟩ := GlobalTheory.T.gapC_holds
  refine ⟨max C'₁ 40, max (max Cl₁ Clg) 1, fun C' Cl hC' hCl => ?_⟩
  intro D large₂ X Y u hTies hH hConc
  have hCl1 : 1 ≤ Cl := (le_max_right _ _).trans hCl
  obtain ⟨hm, hv, h2v, hf, hk40, hk5, hTr⟩ :=
    GlobalTheory.TypeAsm.AmpTerms.sizes hH ((le_max_right _ _).trans hC') hCl1
  have hStd : Std D large₂ := ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hH⟩
  have hCM : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := hH.2.2.2.2.2.2.2
  have hgap := hGap C' Cl Cg cb Cw cT CT C0 D large₂ ((le_max_right _ _).trans ((le_max_left _ _).trans hCl)) hH
  obtain ⟨Ch, hBs, hGood⟩ := hLoc D X ⟨u⟩ hgap hTies.dsig_tie
  have hTail := hT1 C' Cl ((le_max_left _ _).trans hC') ((le_max_left _ _).trans ((le_max_left _ _).trans hCl))
    D large₂ hTies hH hConc.2.2.2.2.2.2.2
  obtain ⟨hcovTop, hcov1⟩ := GlobalTheory.T.integralUnipotent_covolume_finite_bounded D large₂ X Y u Ch hStd
  have hb2 : 2 ≤ large₂.sc.b := by linarith
  intro t ht
  have hj1 : 1 ≤ jT t := Formalism.L2.SG.KappaOffDiagonal.JPosC_holds Cg cb Cw cT CT C0 C' Cl D large₂ X Y u hH hConc t ht
  have hjr : jT t ≤ D.R.rS := Nat.sub_le _ _
  obtain ⟨De, P, hP, hDel, hDeOK, hprod⟩ := hProd D large₂ X Y u Ch CH hStd hCH hk40 hk5 t ht hjr hj1
  set c : ℝ := Formalism.L2.SG.TermOp.wt t * Real.sqrt (dpiC X u) * k2a large₂ CH Cs C (jT t) (labT t) with hc
  have hc0 : 0 ≤ c := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (amplitude_label_nonneg large₂ hC0 _ _)
  have hinf := (GlobalTheory.DegAsm.WeightInf.main _ _ (HV D) hCM D.R.rS).2 (F0 X u) (Ft t) (dI D) t.lam
  have hex : ∃ N, GlobalTheory.DegAsm.Adapt (F0 X u) (Ft t) (dI D) N := by
    obtain ⟨N, hN, -⟩ := GlobalTheory.T.exists_adaptedNormalForm_relevantTerm D large₂ X Y u hStd t ht
    exact ⟨N, hN⟩
  have key : ∀ N : GlobalTheory.DegCnt.NF (HV D) D.R.rS, GlobalTheory.DegAsm.Adapt (F0 X u) (Ft t) (dI D) N →
      ‖(Y.tO u u).vec t‖ ≤ c * N.om t.lam := by
    intro N hN
    have hNj : N.j = jT t := (GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label D large₂ X Y u hStd t N hN).1
    obtain ⟨β, n₁, g, n₂, hfr⟩ := GlobalTheory.T.adaptedNormalForm_gives_real_normal_form D large₂ X Y u Ch hStd t N hN
    obtain ⟨K, hK⟩ := GlobalTheory.T.strict_fundamentalSet_integralStabilizer_exists D X Y u t
    set μ : D.what₂.Tau → Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) := fun τ =>
      (ENNReal.ofReal 1 • GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β).map (Formalism.QuantumDeterminants.conjM (n₂ τ)⁻¹) with hμ
    have hμN : ∀ τ, GlobalTheory.Amp.IsNormalFormStabilizerMeasure D.R.k D.R.rS N.j_le (zB X (Ch.Qi τ) u τ) (zB X (Ch.Qi τ) u τ)
        (gamT Ch t τ)⁻¹ 1 (μ τ) := by
      intro τ
      obtain ⟨h1, h2, h3, hfo⟩ := hfr τ
      obtain ⟨-, hz, hz', hTz, ⟨cc, hnorm⟩, -⟩ := hfo
      exact ⟨hz, hz', hTz, n₁ τ, h1, n₂ τ, h2, g τ, β, cc, hnorm, h3, rfl⟩
    have hvol := GlobalTheory.T.integralStabiliser_covolume_le_indexWeight D large₂ X Y u Ch hStd t N hN μ K hμN hK
    have htr : ∀ (a b : ℕ) (e : a = b) (ha : a ≤ D.R.rS) (hb : b ≤ D.R.rS) (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
        (γ : GlobalTheory.SgInf.Mat D.R.k D.R.rS) (s : ℝ) (μ' : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)),
        GlobalTheory.Amp.IsNormalFormStabilizerMeasure D.R.k D.R.rS ha z z' γ s μ' → GlobalTheory.Amp.IsNormalFormStabilizerMeasure D.R.k D.R.rS hb z z' γ s μ' := by
      rintro a b rfl _ _ _ _ _ _ _ h; exact h
    have hμJ : ∀ τ, GlobalTheory.Amp.IsNormalFormStabilizerMeasure D.R.k D.R.rS hjr (zB X (Ch.Qi τ) u τ) (zB X (Ch.Qi τ) u τ)
        (gamT Ch t τ)⁻¹ 1 (μ τ) := fun τ => htr _ _ hNj _ _ _ _ _ _ _ (hμN τ)
    have hq : ∀ τ, _ := fun τ => GlobalTheory.DegVol.StabQuot.exists_sigmaFinite_quot D.R.k D.R.rS (jT t) hjr
      (zB X (Ch.Qi τ) u τ) (zB X (Ch.Qi τ) u τ) (gamT Ch t τ) (muGB X (Ch.Q τ) (Ch.Qi τ) τ) (μ τ)
      ((hGood.2 u τ).1.2.2.2.2.2.2.1) (hμJ τ) (((GlobalTheory.T.realPointGramMinorsAgree_proof D X Y u Ch τ).2 t).1)
    choose hσμ hHaarμ hNR ν hσν hνnull hνq using hq
    have hfact := GlobalTheory.T.termAmplitude_le_covolume_localAmplitudes D X Y u Ch hBs hGood hcovTop t ht.2 μ ν K
      (fun τ => ⟨hσμ τ, hHaarμ τ, hσν τ, hνnull τ, hνq τ⟩) hK
    have hr1 : 1 ≤ D.R.rS := hj1.trans hjr
    have hjk : jT t + 2 ≤ D.R.k := by
      have : D.R.rS ≤ D.R.rS ^ 4 := Nat.le_self_pow (by norm_num) _
      omega
    have hqq : 16 * D.R.rS ^ 3 + 4 * D.R.rS + 2 ≤ C₁ * D.R.k * D.R.rS := by
      have a1 : D.R.rS ^ 3 ≤ D.R.rS ^ 5 := Nat.pow_le_pow_right hr1 (by norm_num)
      have a2 : D.R.rS ≤ D.R.rS ^ 5 := Nat.le_self_pow (by norm_num) _
      have a3 : 1 ≤ D.R.rS ^ 5 := Nat.one_le_pow _ _ hr1
      have a4 : 40 * D.R.rS ^ 4 * D.R.rS ≤ D.R.k * D.R.rS := Nat.mul_le_mul_right _ hk40
      have a5 : D.R.k * D.R.rS ≤ C₁ * (D.R.k * D.R.rS) := Nat.le_mul_of_pos_left _ hC₁
      have a6 : 40 * D.R.rS ^ 4 * D.R.rS = 40 * D.R.rS ^ 5 := by ring
      rw [mul_assoc]
      omega
    have hH1 : 1 ≤ H1C large₂ CH := by
      unfold H1C
      exact Real.one_le_rpow (by linarith) (by positivity)
    have hloc := fun τ => GlobalTheory.T.amplitude_hsNorm_le_degreeBound_realPlace D τ u u 1 (locW Ch u u τ) _ (locS hBs u u τ) (by linarith) one_pos (hTr u)
      (hTr u) (hGood.2 u τ).1 (hGood.2 u τ).2 (jT t) hjr (C₁ * D.R.k * D.R.rS) (gamT Ch t τ) 1 (H1C large₂ CH) (De τ) _
      (ν τ) hj1 hjk hqq one_pos hH1 (hTail τ u _ (hGood.2 u τ).1 _ (hGood.2 u τ).2).1
      (hTail τ u _ (hGood.2 u τ).1 _ (hGood.2 u τ).2).2 (hDeOK τ) (hNR τ) (hνq τ)
    have hom0 : 0 ≤ N.om t.lam := hinf.1.trans (hinf.2.1 N hN)
    have hL0 : 0 ≤ lossV D := by unfold lossV; have := hv; positivity
    have hvol' : (Measure.pi μ (trI Ch '' K)).toReal ≤
        N.om t.lam * (D.host.v ^ (D.R.k * (D.R.rS - jT t) * D.R.f) * lossV D) := by
      rw [← hNj]
      exact ENNReal.toReal_le_of_le_ofReal (by have := hv; positivity) hvol
    have hcard : Fintype.card D.what₂.Tau = D.R.f := D.what₂.card_Tau
    have hsd : ∏ τ, Real.sqrt (Module.finrank ℂ (Formalism.L2.SG.LocWSOf.locW Ch u u τ).Wp : ℝ) =
        Real.sqrt (dpiC X u) := by
      rw [prod_sqrt _ (fun τ => Nat.cast_nonneg _)]
      unfold dpiC
      rw [Formalism.L2.SG.Pf.AmpWin.finrank_tau]
      rfl
    have hA0 : (0 : ℝ) ≤ (2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1 *
        2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1)) := by have := hv; positivity
    have hPr := prod_bound _ _ _ _ _ hA0 (fun τ => Real.sqrt_nonneg _) hloc hprod
    rw [hsd, hcard] at hPr
    have hG := hCa C hCaC D.R.k D.R.rS D.R.m D.R.f (jT t) large₂.sc.b D.host.v (k2Del D (jT t) (labT t))
      (k2S D (H1C large₂ CH) (jT t) (labT t)) Cs P hm hj1 hjr (by omega) hf hb2 hv h2v hP hDel (one_le_sigma_product _ _ _)
    have hfinal := chain (norm_nonneg _) hcov1 hL0 (Real.sqrt_nonneg _)
      (Finset.prod_nonneg fun τ _ => Real.sqrt_nonneg _) hom0 (by have := hv; positivity) hfact hvol' hPr hG
      (Real.sqrt_nonneg _)
    refine hfinal.trans (le_of_eq ?_)
    rw [hc]
    unfold k2a H1C
    rfl
  have hfin := hinf.2.2 _ c hc0 hex key
  show ‖(Y.tO u u).vec t‖ ≤ Formalism.L2.SG.TermOp.wt t * Real.sqrt (dpiC X u) * (omT t * k2a large₂ CH Cs C (jT t) (labT t))
  have e : Formalism.L2.SG.TermOp.wt t * Real.sqrt (dpiC X u) * (omT t * k2a large₂ CH Cs C (jT t) (labT t)) =
      c * GlobalTheory.DegAsm.omI (F0 X u) (Ft t) (dI D) t.lam := by
    rw [hc]; unfold omT; ring
  rw [e]; exact hfin

end GlobalTheory.TypeAsm.AmpTerms
