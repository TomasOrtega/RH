import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.PointwiseKernelBound
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.NearNonzeroTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ModerateLogFactorAbsorbed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizeIntegralsAndCardCompositions
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeRightTranslateLowerBoun
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountHypPAtAddQAt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralLeSumTypes
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NearTermsModeratePointsOneTypeBoundStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.NearMod

/- English proof (translation)
Establish `hE : IsTotallyComplex I.E` using `I.cm.cmUnram.1`. Establish `hdeg : Module.finrank ℚ I.E = Module.finrank ℚ I.F * 2`. Rewrite using `[← I.cm.deg2, Module.finrank_mul_finrank]`. Establish `hc` using `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank I.E`. Establish `hr : NumberField.InfinitePlace.nrRealPlaces I.E = 0` using `NumberField.nrRealPlaces_eq_zero_iff.mpr hE`.

Unfold `Formalism.HermitianLatticesTheory.fDeg AutInst.f`. Rewrite using `[NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]`. Use linear arithmetic over natural numbers and integers.
-/
theorem fDeg_eq (I : AutInst) : Formalism.HermitianLatticesTheory.fDeg I.E = I.f := by

  have hE : IsTotallyComplex I.E := I.cm.cmUnram.1
  have hdeg : Module.finrank ℚ I.E = Module.finrank ℚ I.F * 2 := by
    rw [← I.cm.deg2, Module.finrank_mul_finrank]
  have hc := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank I.E
  have hr : NumberField.InfinitePlace.nrRealPlaces I.E = 0 :=
    NumberField.nrRealPlaces_eq_zero_iff.mpr hE
  unfold Formalism.HermitianLatticesTheory.fDeg AutInst.f
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  omega

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.vInv AutInst.rd`. Rewrite using `[fDeg_eq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem two_vInv_eq (I : AutInst) : 2 * Formalism.HermitianLatticesTheory.vInv I.E = I.rd := by
  unfold Formalism.HermitianLatticesTheory.vInv AutInst.rd
  rw [fDeg_eq]
  ring

/- English proof (translation)
Establish `hYa : Y ^ a ≤ Real.exp (a * (1 / 8 * L))`. Rewrite using `[Real.exp_nat_mul]`. Conclude with `pow_le_pow_left₀ hY0 hY a`. Establish `hYa0 : 0 ≤ Y ^ a` using `pow_nonneg hY0 a`. Break down `lt_or_ge κ 0 with hκ0 | hκ0` into its components or cases.

Establish `: κ * Y ^ a ≤ 0` using `mul_nonpos_of_nonpos_of_nonneg hκ0.le hYa0`. Use polynomial arithmetic with `[Real.exp_pos (-(3 / 8) * L)]`. Establish `h1 : κ * Y ^ a ≤ Real.exp (-(1 / 2 * J * L)) * Real.exp (a * (1 / 8 * L))` using `mul_le_mul hκ hYa hYa0 (Real.exp_pos _).le`. Rewrite `h1` using `[← Real.exp_add]`. Establish `hJ' : (1 : ℝ) ≤ J` using `by exact_mod_cast hJ`.

Establish `ha' : (a : ℝ) ≤ J` using `by exact_mod_cast haJ`. Establish `h2 : -(1 / 2 * J * L) + a * (1 / 8 * L) ≤ -(3 / 8) * L`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 ha') hL, mul_nonneg (sub_nonneg.2 hJ') hL]`. Establish `h3` using `Real.exp_le_exp.2 h2`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem one_type_arith (L κ Y : ℝ) (a J : ℕ) (hL : 0 ≤ L) (hJ : 1 ≤ J) (haJ : a ≤ J)
    (hκ : κ ≤ Real.exp (-(1 / 2 * J * L))) (hY0 : 0 ≤ Y) (hY : Y ≤ Real.exp (1 / 8 * L)) :
    2 * κ * Y ^ a ≤ 2 * Real.exp (-(3 / 8) * L) := by

  have hYa : Y ^ a ≤ Real.exp (a * (1 / 8 * L)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hY0 hY a
  have hYa0 : 0 ≤ Y ^ a := pow_nonneg hY0 a
  rcases lt_or_ge κ 0 with hκ0 | hκ0
  · have : κ * Y ^ a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hκ0.le hYa0
    nlinarith [Real.exp_pos (-(3 / 8) * L)]
  · have h1 : κ * Y ^ a ≤ Real.exp (-(1 / 2 * J * L)) * Real.exp (a * (1 / 8 * L)) :=
      mul_le_mul hκ hYa hYa0 (Real.exp_pos _).le
    rw [← Real.exp_add] at h1
    have hJ' : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    have ha' : (a : ℝ) ≤ J := by exact_mod_cast haJ
    have h2 : -(1 / 2 * J * L) + a * (1 / 8 * L) ≤ -(3 / 8) * L := by
      nlinarith [mul_nonneg (sub_nonneg.2 ha') hL, mul_nonneg (sub_nonneg.2 hJ') hL]
    have h3 := Real.exp_le_exp.2 h2
    nlinarith

/- English proof (translation)
Introduce `hFM hCB hNU hPB`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.NearModerate`. Introduce `Cg hCg`. Take `⟨n₁, hn₁⟩` from `GlobalTheory.moderate_log_factor_absorbed Cg`. Use `⟨max n₁ (3 ^ 15), ?_⟩` and prove the remaining obligations.

Introduce `B d p q b hq hC`. Establish `h8 : 8 ≤ max n₁ (3 ^ 15)` using `le_trans (by norm_num) (le_max_right _ _)`. Take `⟨-, hrd, hf, -, hpq, -, -, hmin, hd, hX, -, -, h, -, hgap, -, -, -, h120, -⟩` from `GlobalTheory.Dec.countHyp_numerics B Cg _ d p q b h8 hC`. Take `⟨hDS, hSig, hn₀, hq2, hlrd, hlf, hb, hlb, -, hg1, hgb, -⟩` from `id hC`. Establish `hPt` using `hPB B d p q h hDS hSig hgap (by rw [hmin]; exact h120)`.

Establish `hm : 0 ≤ mainTerm B d` using `by show 0 ≤ (∏ v, d v) * B.I.vol B.μf B.fund * (B.e 1).re`. Conclude with `mul_nonneg (mul_nonneg hd.le ENNReal.toReal_nonneg) hPt.2.2.2.2.1`. Establish `hn3 : 3 ^ 15 ≤ B.I.n` using `(le_max_right _ _).trans hn₀`. Establish `hn1 : 1 ≤ B.I.n` using `le_trans (by norm_num) hn3`. Establish `hlogn : 15 ≤ Real.log B.I.n`.

Establish `h3 : Real.exp 15 ≤ (B.I.n : ℝ)`. Establish `e1 : Real.exp 1 ≤ 3` using `by linarith [Real.exp_one_lt_d9]`. Combine the equalities or inequalities in the displayed calculation. Use `Real.log_le_log (Real.exp_pos 15) h3` as an intermediate fact. Rewrite `this` using `[Real.log_exp]`. Then use the resulting hypothesis.

Establish `hL : 0 ≤ (B.I.n : ℝ) * B.I.f * Real.log B.I.n`. Establish `: (0 : ℝ) ≤ Real.log B.I.n` using `by linarith`. Check the signs of the components of the expression. Establish `hY` using `hn₁ B.I.n B.I.f q B.I.rd (B.g : ℝ) b ((le_max_left _ _).trans hn₀) hf hq hq2 hrd hlrd hlf hb hlb (by exact_mod_cast hg1) hgb`. Establish `hlX : 0 ≤ Real.log (bigX B b)` using `Real.log_nonneg (by linarith)`.

Establish `hY0 : 0 ≤ 2 * (B.I.f : ℝ) * q * (11 * q * Real.log (bigX B b))` using `mul_nonneg (by positivity) (mul_nonneg (by positivity) hlX)`. Establish `hY1 : 2 * (B.I.f : ℝ) * q * (11 * q * Real.log (bigX B b)) ≤ Real.exp (1 / 8 * ((B.I.n : ℝ) * B.I.f * Real.log B.I.n))` using `hY.1.trans_eq (by congr 1; ring)`. Establish `hA` using `GlobalTheory.T.nearTerms_moderate_points_one_type_bound hFM hNU hPB B Cg _ d p q b h8 hq hC`. Establish `hper : ∀ J ∈ Finset.Icc 1 q, ∀ c : Composition J, ∫⁻ x in {x | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund, {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) ≤ ENNReal.ofReal (mainTerm B d * (2 * Re …`. Introduce `J hJmem c`.

Establish `hJ` using `Finset.mem_Icc.1 hJmem`. Establish `hsum : ∑ i, c.blocksFun i = J` using `c.sum_blocksFun`. Establish `ha : 1 ≤ c.length` using `c.length_pos_of_pos (by omega)`. Establish `hj1 : ∀ i, 1 ≤ c.blocksFun i` using `fun i => c.one_le_blocksFun i`. Use `(hA.2 c.length c.blocksFun ha hj1 (by rw [hsum]; exact hJ.2)).trans ?_` and prove the remaining obligations.

Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Apply `mul_le_mul_of_nonneg_left _ hm` to reduce the goal to its premises. Establish `hκ` using `hCB B.I.E B.I.cm.cmUnram p q c.length c.blocksFun hj1 (by rw [hsum]; exact hJ.2) (by rw [hpq]; exact hlogn) (by rw [hpq]; exact hq2) (by rw [two_vInv_eq, hpq]; exact hlrd) (by rw [fDeg_eq, hpq]; exact hlf)`. Rewrite `hκ` using `[hsum, hpq, fDeg_eq]`. Conclude with `one_type_arith _ _ _ c.length J hL hJ.1 c.length_le (hκ.trans_eq (by congr 1; ring)) hY0 hY1`.

Establish `hSm : MeasurableSet {x : B.I.GA | tauStar B q b ≤ least B.I x}` using `measurableSet_le measurable_const (GlobalTheory.LeastVar.continuous_least B.I hn1).measurable`. Establish `hΦ0 : ∀ x, 1 / 2 ≤ least B.I x → {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x = 0` using `fun x hx => Set.indicator_apply_eq_zero.2 (fun _ => hA.1 x hx)`. Use `set M : ℝ := mainTerm B d * (2 * Real.exp (-(3 / 8) * ((B.I.n : ℝ) * B.I.f * Real.log B.I.n))) with hM`. Establish `h2q : (2 : ENNReal) ^ q = ENNReal.ofReal (2 ^ q)`. Rewrite using `[ENNReal.ofReal_pow (by norm_num)]; simp`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_indicator hSm, Measure.restrict_restrict hSm, Set.inter_comm]`. Both sides reduce to the same expression. Use `_ ≤ ∑ J ∈ Finset.Icc 1 q, ∑ c : Composition J, ∫⁻ x in {x | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund, {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) := GlobalTheory.TypeDecomp.lintegral_le_sum …`. Use `_ ≤ ∑ J ∈ Finset.Icc 1 q, ∑ _c : Composition J, ENNReal.ofReal M := Finset.sum_le_sum fun J hJ => Finset.sum_le_sum fun c _ => hper J hJ c`.

Use `_ = ((∑ J ∈ Finset.Icc 1 q, Fintype.card (Composition J) : ℕ) : ENNReal) * ENNReal.ofReal M := by`. Rewrite using `[Nat.cast_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun J _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Use `_ ≤ (2 : ENNReal) ^ q * ENNReal.ofReal M := by gcongr`.

Conclude with `(GlobalTheory.sum_card_composition_lt q).le` after adjusting the coercions. Use `_ = ENNReal.ofReal (2 ^ q * M) := by`. Rewrite using `[h2q]; exact (ENNReal.ofReal_mul (by positivity)).symm`. Use `_ ≤ ENNReal.ofReal (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound B d) := by`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises.

Establish `e2 : Real.exp (-(1 / 4 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log (B.I.n : ℝ))) = Real.exp (-(1 / 4) * B.I.n * B.I.f * Real.log B.I.n)` using `by congr 1; ring`. Establish `e1 : Real.exp (-(3 / 8) * ((B.I.n : ℝ) * B.I.f * Real.log B.I.n)) = Real.exp (-(3 / 8) * B.I.n * B.I.f * Real.log B.I.n)` using `by congr 1; ring`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound`. Rewrite using `[e2, hM, e1]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem nearModerate : GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.FlagMeas.ConstantBound → GlobalTheory.Dec.NearUnip →
    GlobalTheory.Deep.PtBound → GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.NearModerate := by
  intro hFM hCB hNU hPB
  unfold GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.NearModerate
  intro Cg hCg
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.moderate_log_factor_absorbed Cg
  refine ⟨max n₁ (3 ^ 15), ?_⟩
  intro B d p q b hq hC
  have h8 : 8 ≤ max n₁ (3 ^ 15) := le_trans (by norm_num) (le_max_right _ _)
  obtain ⟨-, hrd, hf, -, hpq, -, -, hmin, hd, hX, -, -, h, -, hgap, -, -, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg _ d p q b h8 hC
  obtain ⟨hDS, hSig, hn₀, hq2, hlrd, hlf, hb, hlb, -, hg1, hgb, -⟩ := id hC

  have hPt := hPB B d p q h hDS hSig hgap (by rw [hmin]; exact h120)
  have hm : 0 ≤ mainTerm B d := by
    show 0 ≤ (∏ v, d v) * B.I.vol B.μf B.fund * (B.e 1).re
    exact mul_nonneg (mul_nonneg hd.le ENNReal.toReal_nonneg) hPt.2.2.2.2.1

  have hn3 : 3 ^ 15 ≤ B.I.n := (le_max_right _ _).trans hn₀
  have hn1 : 1 ≤ B.I.n := le_trans (by norm_num) hn3
  have hlogn : 15 ≤ Real.log B.I.n := by
    have h3 : Real.exp 15 ≤ (B.I.n : ℝ) := by
      have e1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      calc Real.exp 15 = Real.exp 1 ^ 15 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 3 ^ 15 := pow_le_pow_left₀ (Real.exp_pos 1).le e1 15
        _ ≤ (B.I.n : ℝ) := by exact_mod_cast hn3
    have := Real.log_le_log (Real.exp_pos 15) h3
    rwa [Real.log_exp] at this
  have hL : 0 ≤ (B.I.n : ℝ) * B.I.f * Real.log B.I.n := by
    have : (0 : ℝ) ≤ Real.log B.I.n := by linarith
    positivity

  have hY := hn₁ B.I.n B.I.f q B.I.rd (B.g : ℝ) b ((le_max_left _ _).trans hn₀) hf hq hq2 hrd hlrd hlf
    hb hlb (by exact_mod_cast hg1) hgb
  have hlX : 0 ≤ Real.log (bigX B b) := Real.log_nonneg (by linarith)
  have hY0 : 0 ≤ 2 * (B.I.f : ℝ) * q * (11 * q * Real.log (bigX B b)) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) hlX)
  have hY1 : 2 * (B.I.f : ℝ) * q * (11 * q * Real.log (bigX B b)) ≤
      Real.exp (1 / 8 * ((B.I.n : ℝ) * B.I.f * Real.log B.I.n)) :=
    hY.1.trans_eq (by congr 1; ring)

  have hA := GlobalTheory.T.nearTerms_moderate_points_one_type_bound hFM hNU hPB B Cg _ d p q b h8 hq hC
  have hper : ∀ J ∈ Finset.Icc 1 q, ∀ c : Composition J,
      ∫⁻ x in {x | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund,
          {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) ≤
        ENNReal.ofReal (mainTerm B d *
          (2 * Real.exp (-(3 / 8) * ((B.I.n : ℝ) * B.I.f * Real.log B.I.n)))) := by
    intro J hJmem c
    have hJ := Finset.mem_Icc.1 hJmem
    have hsum : ∑ i, c.blocksFun i = J := c.sum_blocksFun
    have ha : 1 ≤ c.length := c.length_pos_of_pos (by omega)
    have hj1 : ∀ i, 1 ≤ c.blocksFun i := fun i => c.one_le_blocksFun i
    refine (hA.2 c.length c.blocksFun ha hj1 (by rw [hsum]; exact hJ.2)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hm
    have hκ := hCB B.I.E B.I.cm.cmUnram p q c.length c.blocksFun hj1 (by rw [hsum]; exact hJ.2)
      (by rw [hpq]; exact hlogn) (by rw [hpq]; exact hq2) (by rw [two_vInv_eq, hpq]; exact hlrd)
      (by rw [fDeg_eq, hpq]; exact hlf)
    rw [hsum, hpq, fDeg_eq] at hκ
    exact one_type_arith _ _ _ c.length J hL hJ.1 c.length_le (hκ.trans_eq (by congr 1; ring)) hY0 hY1

  have hSm : MeasurableSet {x : B.I.GA | tauStar B q b ≤ least B.I x} :=
    measurableSet_le measurable_const (GlobalTheory.LeastVar.continuous_least B.I hn1).measurable
  have hΦ0 : ∀ x, 1 / 2 ≤ least B.I x →
      {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x = 0 :=
    fun x hx => Set.indicator_apply_eq_zero.2 (fun _ => hA.1 x hx)
  set M : ℝ := mainTerm B d * (2 * Real.exp (-(3 / 8) * ((B.I.n : ℝ) * B.I.f * Real.log B.I.n))) with hM
  have h2q : (2 : ENNReal) ^ q = ENNReal.ofReal (2 ^ q) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  calc ∫⁻ x in GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.moderate B q b, GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x ∂(B.I.muA B.μf)
      = ∫⁻ x in B.fund, {x | tauStar B q b ≤ least B.I x}.indicator
          (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) := by
        rw [lintegral_indicator hSm, Measure.restrict_restrict hSm, Set.inter_comm]; rfl
    _ ≤ ∑ J ∈ Finset.Icc 1 q, ∑ c : Composition J,
          ∫⁻ x in {x | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund,
            {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) :=
        GlobalTheory.TypeDecomp.lintegral_le_sum_types B p q hSig hn1 _ hΦ0
    _ ≤ ∑ J ∈ Finset.Icc 1 q, ∑ _c : Composition J, ENNReal.ofReal M :=
        Finset.sum_le_sum fun J hJ => Finset.sum_le_sum fun c _ => hper J hJ c
    _ = ((∑ J ∈ Finset.Icc 1 q, Fintype.card (Composition J) : ℕ) : ENNReal) * ENNReal.ofReal M := by
        rw [Nat.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (2 : ENNReal) ^ q * ENNReal.ofReal M := by
        gcongr
        exact_mod_cast (GlobalTheory.sum_card_composition_lt q).le
    _ = ENNReal.ofReal (2 ^ q * M) := by
        rw [h2q]; exact (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound B d) := by
        apply ENNReal.ofReal_le_ofReal
        have e2 : Real.exp (-(1 / 4 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log (B.I.n : ℝ))) =
            Real.exp (-(1 / 4) * B.I.n * B.I.f * Real.log B.I.n) := by congr 1; ring
        have e1 : Real.exp (-(3 / 8) * ((B.I.n : ℝ) * B.I.f * Real.log B.I.n)) =
            Real.exp (-(3 / 8) * B.I.n * B.I.f * Real.log B.I.n) := by congr 1; ring
        unfold GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound
        rw [e2, hM, e1]
        calc (2 : ℝ) ^ q * (mainTerm B d * (2 * Real.exp (-(3 / 8) * B.I.n * B.I.f * Real.log B.I.n)))
            = mainTerm B d * (2 * 2 ^ q * Real.exp (-(3 / 8) * B.I.n * B.I.f * Real.log B.I.n)) := by ring
          _ ≤ mainTerm B d * Real.exp (-(1 / 4) * B.I.n * B.I.f * Real.log B.I.n) :=
            mul_le_mul_of_nonneg_left hY.2 hm
          _ = _ := mul_comm _ _

end GlobalTheory.NearMod
