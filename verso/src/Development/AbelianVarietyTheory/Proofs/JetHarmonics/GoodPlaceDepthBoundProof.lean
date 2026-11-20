import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InertPrimeDepthContentBoundProofStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ComplexConjFrobeniusDepthContentBoundProofStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitPrimeDepthContentBoundProofStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LargePrimePackagesDepthNonposStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ErealLeMulOfForallLe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ForcedContentBoundsProgrammeValueGoodPrime
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelLe
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal
import Development.AutomorphicArithmetic.OrbitLabellings.PkgZeroCsNuNonposOfMonSupply
import Development.AutomorphicArithmetic.OrbitLabellings.RowBoundLeFnumSumAddError
import Development.AutomorphicArithmetic.OrbitLabellings.FMulLeastAdmissibleLevelRowsLe
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.OddLevelBlockBoundAttainedStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MonomialBlockSupplyBothTypingsStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterBlocksAttainBoundStatement
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

namespace GlobalTheory.GoodDepth

/- English proof (translation)
Unfold `DF`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem le_DF_of_mult_pos {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (τ : E →+* ℂ) (h : 0 < Dw.mult τ) : a (τ, 0) ≤ DF Dw a := by
  unfold DF
  calc a (τ, 0) = a (τ, ((⟨0, h⟩ : Fin (Dw.mult τ)) : ℕ)) := rfl
    _ ≤ ∑ i : Fin (Dw.mult τ), a (τ, i) :=
        Finset.single_le_sum (f := fun i : Fin (Dw.mult τ) => a (τ, i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    _ ≤ _ := Finset.single_le_sum (f := fun τ => ∑ i : Fin (Dw.mult τ), a (τ, i)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ τ)

/- English proof (translation)
Unfold `thl`. Apply `Real.sSup_nonneg` to reduce the goal to its premises. Introduce and unpack `t ⟨i, -, -, -, rfl⟩`. Check the signs of the components of the expression.
-/
theorem thl_nonneg' (k l : ℕ) : 0 ≤ thl k l := by
  unfold thl
  apply Real.sSup_nonneg
  rintro t ⟨i, -, -, -, rfl⟩
  positivity

/- English proof (translation)
Establish `h5 : (5 : ℝ) ≤ k` using `by exact_mod_cast hk`. Rewrite using `[Real.le_log_iff_exp_le (by linarith)]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_le_log_of_five_le {k : ℕ} (hk : 5 ≤ k) : 1 ≤ Real.log k := by
  have h5 : (5 : ℝ) ≤ k := by exact_mod_cast hk
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.card, h.m_pos, h.mk_le, h.r_eq, h.SE_nonneg⟩`.
-/
theorem parOK_parAt {N : NumDatum} {j l : ℕ} (h : ParOK (parOf N j l)) (d : ℕ) [NeZero d] (pos : RPl N.R → ℕ → RPl N.R) :
    ParOK (parAt N j d pos) := ⟨h.card, h.m_pos, h.mk_le, h.r_eq, h.SE_nonneg⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.T_one, h.w_pos, h.TW_lo, h.TW_hi, h.th_rng, h.th_m, h.rest_nonneg, h.rest_le⟩`.
-/
theorem degHyp2_parOf {N : NumDatum} {j : ℕ} {W : RPl N.R → ℕ} {T θ0 rest C1 : ℝ}
    (h : RF.DegHyp2 (parAt N j 1 fun z _ => z) W T θ0 rest C1) (l : ℕ) : RF.DegHyp2 (parOf N j l) W T θ0 rest C1 :=
  ⟨h.T_one, h.w_pos, h.TW_lo, h.TW_hi, h.th_rng, h.th_m, h.rest_nonneg, h.rest_le⟩

/- English proof (translation)
Unfold `NumDatum.ordP`. Rewrite using `[if_neg (by rw [h.1]; simp)]`. Conclude with `h.2`.
-/
private theorem odd_ordP_of_conjIn {N : NumDatum} {l : ℕ} (h : ConjIn N l) : Odd (N.ordP l) := by
  unfold NumDatum.ordP
  rw [if_neg (by rw [h.1]; simp)]
  exact h.2

/- English proof (translation)
Introduce `C1 hC1`. Take `⟨CI, hCI, HI⟩` from `GlobalTheory.T.inertPrimeDepthContentBound_proof C1 hC1`. Take `⟨CP, hCP, HP⟩` from `GlobalTheory.T.complexConjFrobeniusDepthContentBound_proof C1 hC1`. Take `⟨CS, hCS, HS⟩` from `GlobalTheory.T.splitPrimeDepthContentBound_proof C1 hC1`. Take `⟨CC, hCC, HC⟩` from `UpperTheory.rowBound_le_Fnum_sum_add_error GlobalTheory.T.oddLevelBlock_bound_attained.2 GlobalTheory.T.characterBlocks_attain_bound.2 GlobalTheory.T.monomialBlock_supply_both_typings.2 C1 hC1`.

Take `⟨HZ, -⟩` from `GlobalTheory.T.largePrime_packages_depth_nonpos`. Use `⟨2 * CI + 2 * CP + 2 * CC + CS + 2, by positivity, ?_⟩` and prove the remaining obligations. Introduce `E _ _ _ H Dw lv Xo c _ hstar hIC hPk N j pl a nW T b L w hj1 hjm hpl hp hq hdom hG hw hb la h2 hq' hd hg0 hg1 hM`. Take `⟨PI, PP, PS, PZ, -, PC, PZC⟩` from `hPk`. Establish `hl : (resCharOf la).Prime` using `Crude.resCharOf_prime la`.

Establish `hin` using `hG.inert_ge _ hl`. Establish `red` using `GlobalTheory.GoodDepth.nuW_bound_of_charts E H Dw lv Xo c hIC la lv.M a nW`. Establish `PI'` using `PI hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin`. Establish `PP'` using `PP hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin`. Establish `PS'` using `PS hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin`.

Establish `PZ'` using `PZ hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin`. Establish `PZC'` using `PZC hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin`. Establish `PC'` using `PC hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin`. Use `clear PI PP PS PZ PZC PC`. Generalize the expression as in `resCharOf la = l at *`.

Take `⟨θ0, hdeg⟩` from `hG.deg`. Establish `hT1 : (1 : ℝ) ≤ T` using `hdeg.T_one`. Establish `hT1' : 1 ≤ T` using `by exact_mod_cast hT1`. Establish `hwpos : ∀ z, 0 ≤ N.w j z` using `fun z => (hdeg.w_pos z).le`. Establish `hsum : 0 ≤ ∑ z, N.w j z` using `Finset.sum_nonneg fun z _ => hwpos z`.

Establish `hw0 : 0 ≤ w` using `hsum.trans hw`. Take `⟨hF0, htri, hOK, hFC, hFI⟩` from `GlobalTheory.ContentValue.main N j l hl h2 hq' hd hg0 hg1 hwpos hG.ratio`. Establish `hm2` using `N.R.two_le_m`. Establish `hmk` using `N.R.m_add_three_le_k`. Establish `hf2 : 2 ≤ N.R.f` using `hm2.trans N.R.m_le_f`.

Establish `hr : N.R.r = N.R.k + N.R.m - 1` using `rfl`. Establish `hn : ((N.R.k - 1 : ℕ) : ℝ) = (N.R.k : ℝ) - 1`. Rewrite using `[Nat.cast_sub (by omega)]; simp`. Establish `hl3 : 3 ≤ l`. Use `hl.two_le` as an intermediate fact.

Use `ne_two_of_not_small h2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hlpos : (0 : ℝ) < l` using `by exact_mod_cast (by omega : 0 < l)`. Take `⟨R1, R2, R3, R4⟩` from `GlobalTheory.RowBudgets.main N.R.r N.R.f (N.R.k - 1) N.R.m nW T l N.R.k b L w (by omega) (by omega) (by omega) hf2 hT1' (by omega) hG.L_ge hG.log_le (by rw [hn]; exact hG.what₂)`. Establish `R5` using `UpperTheory.f_mul_leastAdmissibleLevel_rows_le N.R.r N.R.f (N.R.k - 1) N.R.m nW l N.R.k L (by omega) (by omega) (by omega) hf2 (by omega) hG.L_ge hG.log_le (by rw [hn]; exact hG.what₂)`.

Rewrite `R3`, `R4` using `[hn]`. Establish `hzero : ∀ s : ℕ, (∀ τ, 0 < Dw.mult τ → a (τ, 0) ≤ s * (l - 1)) → 4 * N.R.r * s * N.R.f ≤ nW → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ y : IntFr Xo c T io, y.IsAlg → ∀ (C : IntChart T io y) (ν : ℝ), (((ramOverZ la : ℝ) * ν : ℝ) : EReal) ≤ nuLocC C e lv.M a …`. Introduce `s hs hrow V io e ho y hy C ν hν`. Distinguish the cases in `hc : ConjIn N l`. Take `⟨Pk, rfl⟩` from `PZC' V io e ho y hy C nW ν hν hc.1 (odd_ordP_of_conjIn hc) hwpos s hs hrow`.

Conclude with `UpperTheory.pkgZeroCs_nu_nonpos_of_monSupply GlobalTheory.T.monomialBlock_supply_both_typings.2 _ _ Pk`. Take `⟨d, _, pos, Pk, rfl⟩` from `PZ' V io e ho y hy C nW ν hν hc hwpos s hs (le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num)))) hrow)`. Conclude with `HZ _ _ Pk`. Establish `hSE : 0 ≤ N.Sc + N.eta` using `hOK.SE_nonneg`. Establish `hlog : 1 ≤ Real.log N.R.k` using `one_le_log_of_five_le (by omega)`.

Establish `hth` using `thl_nonneg' N.R.k l`. Use `set A1 : ℝ := Real.log N.R.k * N.R.m * w / l with hA1`. Use `set A2 : ℝ := N.R.f * N.R.k * (N.Sc + N.eta) / l with hA2`. Use `set A3 : ℝ := N.R.k * thl N.R.k l * w with hA3`. Use `set A4 : ℝ := if N.sc.X'' N.R.n < (l : ℝ) then N.R.k * w / (l : ℝ) ^ 2 else 0 with hA4`.

Establish `a1 : 0 ≤ A1` using `by positivity`. Establish `a2 : 0 ≤ A2` using `by positivity`. Establish `a3 : 0 ≤ A3` using `by positivity`. Apply the tactic sequence `have a4 : 0 ≤ A4 := by rw [hA4]; split_ifs <;> positivity`. Establish `hA4' : (if N.sc.X'' N.R.n < (l : ℝ) then 2 * (N.R.k * (∑ z, N.w j z) / (l : ℝ) ^ 2) else 0) ≤ 2 * A4`.

Rewrite using `[hA4]`. Use `split_ifs`. Use `gcongr`. Simplify using the standard rewrite rules. Use `set B : ℝ := N.FjP j l + (2 * CI + 2 * CP + 2 * CC + CS + 2) * (A1 + A2 + A3 + A4) with hB`.

Establish `hB0 : 0 ≤ B` using `by positivity`. Establish `hTpos : (0 : ℝ) < T` using `by linarith`. Establish `hmain : ∀ (V : CDVR) (io : c.F →+* V.Fr) (e : ℕ), OverLa la V.V io e → ∀ y : IntFr Xo c V io, y.IsAlg → ∀ (C : IntChart V io y) (ν : ℝ), (((ramOverZ la : ℝ) * ν : ℝ) : EReal) ≤ nuLocC C e lv.M a nW → ν ≤ B / T`. Introduce `V io e ho y hy C ν hν`. Establish `hBT : 0 ≤ B / T` using `by positivity`.

Distinguish the cases in `hb0 : b < 0`. Use `le_trans (hzero 0 (fun τ hτ => ?_) (by simp) V io e ho y hy C ν hν) hBT` and prove the remaining obligations. Establish `h1` using `hG.first τ hτ`. Establish `h2 : (0 : ℝ) ≤ (T : ℝ) * a (τ, 0)` using `by positivity`. It suffices to derive a contradiction.

Combine the linear equalities and inequalities to obtain the conclusion. Use `push Not at hb0`. Distinguish the cases in `hl2 : N.R.m * b / (T * N.R.f * ((N.R.k : ℝ) - 1) ^ 3 * L) ≤ l`. Take `⟨s, hs1, hs2⟩` from `R3 hl3 hb0 hl2`. Conclude with `le_trans (hzero s (fun τ hτ => hs2 _ (hG.first τ hτ)) hs1 V io e ho y hy C ν hν) hBT`.

Use `push Not at hl2`. Establish `hadd` using `R4 (by omega) hl2 hb`. Establish `herr : errB (parOf N j l) l T ≤ 2 * (A1 + A2 + A3)`. Establish `e1 : Real.log N.R.k * N.R.m * (∑ z, N.w j z) / l ≤ A1` using `by rw [hA1]; gcongr`. Establish `e3 : N.R.k * thl N.R.k l * (∑ z, N.w j z) ≤ A3` using `by rw [hA3]; gcongr`.

Establish `: errB (parOf N j l) l T = Real.log N.R.k * N.R.m * (∑ z, N.w j z) / l + A2 + N.R.k * thl N.R.k l * (∑ z, N.w j z) + T * N.R.f * ((N.R.k : ℝ) - 1) ^ 3 * Real.log N.R.k ^ 2` using `rfl`. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[le_div_iff₀ hTpos, mul_comm]`. Establish `p1` using `mul_nonneg hCI.le a1`.

Establish `p2` using `mul_nonneg hCI.le a2`. Establish `p3` using `mul_nonneg hCI.le a3`. Establish `p4` using `mul_nonneg hCI.le a4`. Establish `q1` using `mul_nonneg hCP.le a1`. Establish `q2` using `mul_nonneg hCP.le a2`.

Establish `q3` using `mul_nonneg hCP.le a3`. Establish `q4` using `mul_nonneg hCP.le a4`. Establish `s1` using `mul_nonneg hCS.le a1`. Establish `s2` using `mul_nonneg hCS.le a2`. Establish `s3` using `mul_nonneg hCS.le a3`.

Establish `s4` using `mul_nonneg hCS.le a4`. Establish `c1` using `mul_nonneg hCC.le a1`. Establish `c2` using `mul_nonneg hCC.le a2`. Establish `c3` using `mul_nonneg hCC.le a3`. Establish `c4` using `mul_nonneg hCC.le a4`.

Break down `htri with hI | hS` into its components or cases. Establish `h5` using `hin hI`. Distinguish the cases in `hc : PhiC N l`. Take `⟨Pk, hT, hν'⟩` from `PP' V io e ho y hy C nW ν hν hc T θ0 C1 (degHyp2_parOf hdeg l) R1`. Establish `h1` using `HP _ l hOK hl h5 Pk`.

Rewrite `h1` using `[hT, hν']`. Establish `h2` using `hFC hc`. Establish `h3` using `mul_le_mul_of_nonneg_left herr hCP.le`. Establish `h1' : (T : ℝ) * ν ≤ ((N.R.k : ℝ) - 1) * (∑ z, N.w j z) / ((l : ℝ) ^ 2 - 1) + CP * errB (parOf N j l) l T` using `h1`. Rewrite using `[hB]`.

Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `hcs : ConjIn N l`. Take `⟨Pk, hT, hν'⟩` from `PC' V io e ho y hy C nW ν hν hcs.1 (odd_ordP_of_conjIn hcs) T θ0 C1 (degHyp2_parOf hdeg l) (R5 h5)`. Establish `h1` using `HC _ l hOK.card hOK.m_pos hOK.mk_le hOK.r_eq hOK.SE_nonneg hl h5 Pk`. Rewrite `h1` using `[hT, hν']`.

Establish `h2` using `hFI hI hc Pk.Z Pk.hZ`. Establish `h3` using `mul_le_mul_of_nonneg_left herr hCC.le`. Establish `h1'` using `le_trans h1 (add_le_add h2 h3)`. Rewrite using `[hB]`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨Pk, hT, hν'⟩` from `PI' V io e ho y hy C nW ν hν hI hcs T θ0 C1 (degHyp2_parOf hdeg l) (R2 h5)`. Establish `h1` using `HI _ l hOK hl h5 Pk`. Rewrite `h1` using `[hT, hν']`. Establish `h2` using `hFI hI hc Pk.Z Pk.hZ`. Establish `h3` using `mul_le_mul_of_nonneg_left herr hCI.le`.

Establish `h1'` using `le_trans h1 (add_le_add h2 h3)`. Rewrite using `[hB]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨d, _, pos, Pk, hT, hν'⟩` from `PS' V io e ho y hy C nW ν hν hS T θ0 C1 hdeg (le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))) R1)`. Establish `h1` using `HS _ l (parOK_parAt hOK d pos) hl Pk`.

Rewrite `h1` using `[hT, hν']`. Establish `h1' : (T : ℝ) * ν ≤ CS * ((N.R.m * (∑ z, N.w j z) + N.R.f * N.R.k * (N.Sc + N.eta)) / l)` using `h1`. Establish `e1 : (N.R.m * (∑ z, N.w j z) + N.R.f * N.R.k * (N.Sc + N.eta)) / l ≤ A1 + A2`. Rewrite using `[hA1, hA2, add_div]`. Establish `: (N.R.m : ℝ) * (∑ z, N.w j z) ≤ Real.log N.R.k * N.R.m * w`.

Combine the equalities or inequalities in the displayed calculation. Use `gcongr`. Establish `h3` using `mul_le_mul_of_nonneg_left e1 hCS.le`. Rewrite using `[hB]`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨r1, r2, -⟩` from `red (B / T) (by positivity) hmain`. Use `⟨r1, ?_, fun hDF => ?_⟩` and prove the remaining obligations. Rewrite `r2` using `[le_div_iff₀ hTpos, mul_comm]`. Conclude with `r2`. Use `(red 0 le_rfl (hzero 1 (fun τ hτ => ?_) ?_)).2.2 rfl` and prove the remaining obligations.

Use `le_DF_of_mult_pos Dw a τ hτ` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[mul_one]`. Conclude with `le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))) R1`.
-/
theorem nuGood : NuGoodSt := by
  intro C1 hC1
  obtain ⟨CI, hCI, HI⟩ := GlobalTheory.T.inertPrimeDepthContentBound_proof C1 hC1
  obtain ⟨CP, hCP, HP⟩ := GlobalTheory.T.complexConjFrobeniusDepthContentBound_proof C1 hC1
  obtain ⟨CS, hCS, HS⟩ := GlobalTheory.T.splitPrimeDepthContentBound_proof C1 hC1
  obtain ⟨CC, hCC, HC⟩ := UpperTheory.rowBound_le_Fnum_sum_add_error GlobalTheory.T.oddLevelBlock_bound_attained.2 GlobalTheory.T.characterBlocks_attain_bound.2 GlobalTheory.T.monomialBlock_supply_both_typings.2 C1 hC1
  obtain ⟨HZ, -⟩ := GlobalTheory.T.largePrime_packages_depth_nonpos
  refine ⟨2 * CI + 2 * CP + 2 * CC + CS + 2, by positivity, ?_⟩
  intro E _ _ _ H Dw lv Xo c _ hstar hIC hPk N j pl a nW T b L w hj1 hjm hpl hp hq hdom hG hw hb la h2 hq' hd hg0 hg1 hM
  obtain ⟨PI, PP, PS, PZ, -, PC, PZC⟩ := hPk
  have hl : (resCharOf la).Prime := Crude.resCharOf_prime la
  have hin := hG.inert_ge _ hl
  have red := GlobalTheory.GoodDepth.nuW_bound_of_charts E H Dw lv Xo c hIC la lv.M a nW
  have PI' := PI hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  have PP' := PP hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  have PS' := PS hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  have PZ' := PZ hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  have PZC' := PZC hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  have PC' := PC hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  clear PI PP PS PZ PZC PC
  generalize resCharOf la = l at *
  obtain ⟨θ0, hdeg⟩ := hG.deg
  have hT1 : (1 : ℝ) ≤ T := hdeg.T_one
  have hT1' : 1 ≤ T := by exact_mod_cast hT1
  have hwpos : ∀ z, 0 ≤ N.w j z := fun z => (hdeg.w_pos z).le
  have hsum : 0 ≤ ∑ z, N.w j z := Finset.sum_nonneg fun z _ => hwpos z
  have hw0 : 0 ≤ w := hsum.trans hw
  obtain ⟨hF0, htri, hOK, hFC, hFI⟩ := GlobalTheory.ContentValue.main N j l hl h2 hq' hd hg0 hg1 hwpos hG.ratio
  have hm2 := N.R.two_le_m
  have hmk := N.R.m_add_three_le_k
  have hf2 : 2 ≤ N.R.f := hm2.trans N.R.m_le_f
  have hr : N.R.r = N.R.k + N.R.m - 1 := rfl
  have hn : ((N.R.k - 1 : ℕ) : ℝ) = (N.R.k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hl3 : 3 ≤ l := by
    have := hl.two_le
    have := ne_two_of_not_small h2
    omega
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  obtain ⟨R1, R2, R3, R4⟩ := GlobalTheory.RowBudgets.main N.R.r N.R.f (N.R.k - 1) N.R.m nW T l N.R.k b L w (by omega) (by omega) (by omega)
    hf2 hT1' (by omega) hG.L_ge hG.log_le (by rw [hn]; exact hG.what₂)
  have R5 := UpperTheory.f_mul_leastAdmissibleLevel_rows_le N.R.r N.R.f (N.R.k - 1) N.R.m nW l N.R.k L (by omega) (by omega) (by omega)
    hf2 (by omega) hG.L_ge hG.log_le (by rw [hn]; exact hG.what₂)
  rw [hn] at R3 R4
  have hzero : ∀ s : ℕ, (∀ τ, 0 < Dw.mult τ → a (τ, 0) ≤ s * (l - 1)) → 4 * N.R.r * s * N.R.f ≤ nW →
      ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ y : IntFr Xo c T io, y.IsAlg →
      ∀ (C : IntChart T io y) (ν : ℝ), (((ramOverZ la : ℝ) * ν : ℝ) : EReal) ≤ nuLocC C e lv.M a nW → ν ≤ 0 := by
    intro s hs hrow V io e ho y hy C ν hν
    by_cases hc : ConjIn N l
    · obtain ⟨Pk, rfl⟩ := PZC' V io e ho y hy C nW ν hν hc.1 (odd_ordP_of_conjIn hc) hwpos s hs hrow
      exact UpperTheory.pkgZeroCs_nu_nonpos_of_monSupply GlobalTheory.T.monomialBlock_supply_both_typings.2 _ _ Pk
    · obtain ⟨d, _, pos, Pk, rfl⟩ := PZ' V io e ho y hy C nW ν hν hc hwpos s hs
        (le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num)))) hrow)
      exact HZ _ _ Pk
  have hSE : 0 ≤ N.Sc + N.eta := hOK.SE_nonneg
  have hlog : 1 ≤ Real.log N.R.k := one_le_log_of_five_le (by omega)
  have hth := thl_nonneg' N.R.k l
  set A1 : ℝ := Real.log N.R.k * N.R.m * w / l with hA1
  set A2 : ℝ := N.R.f * N.R.k * (N.Sc + N.eta) / l with hA2
  set A3 : ℝ := N.R.k * thl N.R.k l * w with hA3
  set A4 : ℝ := if N.sc.X'' N.R.n < (l : ℝ) then N.R.k * w / (l : ℝ) ^ 2 else 0 with hA4
  have a1 : 0 ≤ A1 := by positivity
  have a2 : 0 ≤ A2 := by positivity
  have a3 : 0 ≤ A3 := by positivity
  have a4 : 0 ≤ A4 := by rw [hA4]; split_ifs <;> positivity
  have hA4' : (if N.sc.X'' N.R.n < (l : ℝ) then 2 * (N.R.k * (∑ z, N.w j z) / (l : ℝ) ^ 2) else 0) ≤ 2 * A4 := by
    rw [hA4]
    split_ifs
    · gcongr
    · simp
  set B : ℝ := N.FjP j l + (2 * CI + 2 * CP + 2 * CC + CS + 2) * (A1 + A2 + A3 + A4) with hB
  have hB0 : 0 ≤ B := by positivity
  have hTpos : (0 : ℝ) < T := by linarith
  have hmain : ∀ (V : CDVR) (io : c.F →+* V.Fr) (e : ℕ), OverLa la V.V io e → ∀ y : IntFr Xo c V io, y.IsAlg →
      ∀ (C : IntChart V io y) (ν : ℝ), (((ramOverZ la : ℝ) * ν : ℝ) : EReal) ≤ nuLocC C e lv.M a nW → ν ≤ B / T := by
    intro V io e ho y hy C ν hν
    have hBT : 0 ≤ B / T := by positivity
    by_cases hb0 : b < 0
    · refine le_trans (hzero 0 (fun τ hτ => ?_) (by simp) V io e ho y hy C ν hν) hBT
      have h1 := hG.first τ hτ
      have h2 : (0 : ℝ) ≤ (T : ℝ) * a (τ, 0) := by positivity
      exfalso; linarith
    push Not at hb0
    by_cases hl2 : N.R.m * b / (T * N.R.f * ((N.R.k : ℝ) - 1) ^ 3 * L) ≤ l
    · obtain ⟨s, hs1, hs2⟩ := R3 hl3 hb0 hl2
      exact le_trans (hzero s (fun τ hτ => hs2 _ (hG.first τ hτ)) hs1 V io e ho y hy C ν hν) hBT
    push Not at hl2
    have hadd := R4 (by omega) hl2 hb
    have herr : errB (parOf N j l) l T ≤ 2 * (A1 + A2 + A3) := by
      have e1 : Real.log N.R.k * N.R.m * (∑ z, N.w j z) / l ≤ A1 := by rw [hA1]; gcongr
      have e3 : N.R.k * thl N.R.k l * (∑ z, N.w j z) ≤ A3 := by rw [hA3]; gcongr
      have : errB (parOf N j l) l T = Real.log N.R.k * N.R.m * (∑ z, N.w j z) / l + A2 +
        N.R.k * thl N.R.k l * (∑ z, N.w j z) + T * N.R.f * ((N.R.k : ℝ) - 1) ^ 3 * Real.log N.R.k ^ 2 := rfl
      rw [this]; linarith
    rw [le_div_iff₀ hTpos, mul_comm]
    have p1 := mul_nonneg hCI.le a1
    have p2 := mul_nonneg hCI.le a2
    have p3 := mul_nonneg hCI.le a3
    have p4 := mul_nonneg hCI.le a4
    have q1 := mul_nonneg hCP.le a1
    have q2 := mul_nonneg hCP.le a2
    have q3 := mul_nonneg hCP.le a3
    have q4 := mul_nonneg hCP.le a4
    have s1 := mul_nonneg hCS.le a1
    have s2 := mul_nonneg hCS.le a2
    have s3 := mul_nonneg hCS.le a3
    have s4 := mul_nonneg hCS.le a4
    have c1 := mul_nonneg hCC.le a1
    have c2 := mul_nonneg hCC.le a2
    have c3 := mul_nonneg hCC.le a3
    have c4 := mul_nonneg hCC.le a4
    rcases htri with hI | hS
    · have h5 := hin hI
      by_cases hc : PhiC N l
      · obtain ⟨Pk, hT, hν'⟩ := PP' V io e ho y hy C nW ν hν hc T θ0 C1 (degHyp2_parOf hdeg l) R1
        have h1 := HP _ l hOK hl h5 Pk
        rw [hT, hν'] at h1
        have h2 := hFC hc
        have h3 := mul_le_mul_of_nonneg_left herr hCP.le
        have h1' : (T : ℝ) * ν ≤ ((N.R.k : ℝ) - 1) * (∑ z, N.w j z) / ((l : ℝ) ^ 2 - 1) + CP * errB (parOf N j l) l T := h1
        rw [hB]; linarith
      by_cases hcs : ConjIn N l
      · obtain ⟨Pk, hT, hν'⟩ := PC' V io e ho y hy C nW ν hν hcs.1 (odd_ordP_of_conjIn hcs) T θ0 C1
          (degHyp2_parOf hdeg l) (R5 h5)
        have h1 := HC _ l hOK.card hOK.m_pos hOK.mk_le hOK.r_eq hOK.SE_nonneg hl h5 Pk
        rw [hT, hν'] at h1
        have h2 := hFI hI hc Pk.Z Pk.hZ
        have h3 := mul_le_mul_of_nonneg_left herr hCC.le
        have h1' := le_trans h1 (add_le_add h2 h3)
        rw [hB]; linarith
      · obtain ⟨Pk, hT, hν'⟩ := PI' V io e ho y hy C nW ν hν hI hcs T θ0 C1 (degHyp2_parOf hdeg l) (R2 h5)
        have h1 := HI _ l hOK hl h5 Pk
        rw [hT, hν'] at h1
        have h2 := hFI hI hc Pk.Z Pk.hZ
        have h3 := mul_le_mul_of_nonneg_left herr hCI.le
        have h1' := le_trans h1 (add_le_add h2 h3)
        rw [hB]; linarith
    · obtain ⟨d, _, pos, Pk, hT, hν'⟩ := PS' V io e ho y hy C nW ν hν hS T θ0 C1 hdeg
        (le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))) R1)
      have h1 := HS _ l (parOK_parAt hOK d pos) hl Pk
      rw [hT, hν'] at h1
      have h1' : (T : ℝ) * ν ≤ CS * ((N.R.m * (∑ z, N.w j z) + N.R.f * N.R.k * (N.Sc + N.eta)) / l) := h1
      have e1 : (N.R.m * (∑ z, N.w j z) + N.R.f * N.R.k * (N.Sc + N.eta)) / l ≤ A1 + A2 := by
        rw [hA1, hA2, add_div]
        have : (N.R.m : ℝ) * (∑ z, N.w j z) ≤ Real.log N.R.k * N.R.m * w := by
          calc (N.R.m : ℝ) * (∑ z, N.w j z) = 1 * N.R.m * (∑ z, N.w j z) := by ring
            _ ≤ _ := by gcongr
        gcongr
      have h3 := mul_le_mul_of_nonneg_left e1 hCS.le
      rw [hB]; linarith
  obtain ⟨r1, r2, -⟩ := red (B / T) (by positivity) hmain
  refine ⟨r1, ?_, fun hDF => ?_⟩
  · rw [le_div_iff₀ hTpos, mul_comm] at r2
    exact r2
  · refine (red 0 le_rfl (hzero 1 (fun τ hτ => ?_) ?_)).2.2 rfl
    · have := le_DF_of_mult_pos Dw a τ hτ
      omega
    · rw [mul_one]
      exact le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))) R1

end GlobalTheory.GoodDepth
