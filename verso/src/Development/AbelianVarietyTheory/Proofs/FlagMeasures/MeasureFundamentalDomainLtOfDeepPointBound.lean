import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DeepKernelBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepRegionExponents
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureLeCardMul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizeProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeEqFundamentalDomainInterStatement

open MeasureTheory NumberField Formalism.MainNotions.S GlobalTheory.Count

namespace GlobalTheory.DeepArith

/- English proof (translation)
The claim follows from `Module.finrank_pos`.
-/
theorem one_le_f (I : AutInst) : 1 ≤ I.f := Module.finrank_pos

/- English proof (translation)
Unfold `AutInst.rd`. Use `Real.one_le_rpow ?_ (by positivity)` and prove the remaining obligations. Establish `h` using `Int.one_le_abs (discr_ne_zero I.E)`. Conclude with `h` after adjusting the coercions.
-/
theorem one_le_rd (I : AutInst) : 1 ≤ I.rd := by
  unfold AutInst.rd
  refine Real.one_le_rpow ?_ (by positivity)
  have h := Int.one_le_abs (discr_ne_zero I.E)
  exact_mod_cast h

/- English proof (translation)
Take `⟨-, hsig, hn', hq2, -, -, hb, -, -, hg, -⟩` from `hC`. Establish `hn : 8 ≤ B.I.n` using `hn₀.trans hn'`. Establish `hc0 : ∀ v, 0 < c v` using `fun v => by`. Take `⟨c', h0, -, hu⟩` from `GlobalTheory.GaugeConst.exists_unique_isGauge B.I.n (B.I.ε v)`. Rewrite using `[hu _ (hc v)]`.

Conclude with `h0`. Establish `hf` using `one_le_f B.I`. Establish `hrd` using `one_le_rd B.I`. Establish `hnR : (8 : ℝ) ≤ B.I.n` using `by exact_mod_cast hn`. Establish `hfR : (1 : ℝ) ≤ B.I.f` using `by exact_mod_cast hf`.

Establish `hgR : (1 : ℝ) ≤ B.g` using `by exact_mod_cast hg`. Establish `hfr : B.I.rd ≤ B.I.f * B.I.rd` using `by nlinarith`. Establish `hX : 2 * (B.I.f * B.I.rd) ≤ bigX B b`. Establish `h1 : (2 : ℝ) ≤ B.g * b` using `by nlinarith`. Establish `h2 : (2 : ℝ) ≤ B.I.n * (B.g * b)` using `by nlinarith`.

Establish `: bigX B b = (B.I.n * (B.g * b)) * (B.I.f * B.I.rd)` using `by unfold bigX; ring`. Rewrite using `[this]`. Conclude with `mul_le_mul_of_nonneg_right h2 (by linarith)`. Establish `hX2 : 2 ≤ bigX B b` using `by linarith`. Establish `hvol` using `hV B.I p q hsig hq2 hn (bigX B b) hX2 (by linarith) (by nlinarith) c B.μf hc`.

Take `⟨hcov, -⟩` from `GlobalTheory.T.leftQuotientCovolume_eq_fundamentalDomain_inter B.I B.μf B.fund Set.univ B.fund_spec MeasurableSet.univ (fun _ _ _ _ => Set.mem_univ _)`. Take `⟨hidx, hKg0, hKfin⟩` from `GlobalTheory.CongIndex.measure_Kset_le B.I B.μf B.g hg`. Establish `hKgfin : B.μf (B.I.Kg B.g) ≠ ⊤` using `ne_top_of_le_ne_top hKfin.ne (measure_mono fun _ h => h.1)`. Unfold `GlobalTheory.FlagMeas.gaugeVol at hvol`. Rewrite `hvol` using `[hcov, Set.univ_inter, ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top) (Or.inl hKfin.ne)]`.

Use `set N : ℕ := B.I.n ^ 2 * B.I.f with hN`. Use `set m : ℝ := (B.μf (B.I.Kg B.g)).toReal with hm`. Establish `hm0 : 0 < m` using `ENNReal.toReal_pos hKg0.ne' hKgfin`. Establish `hcp : 0 < ∏ v, c v` using `Finset.prod_pos fun v _ => hc0 v`. Establish `hXp : 0 < bigX B b` using `by linarith`.

Establish `hgp : (0 : ℝ) < B.g` using `by linarith`. Use `set Y : ℝ := (B.g : ℝ) ^ (2 * N) * bigX B b ^ N with hY`. Establish `hY0 : 0 < Y` using `by positivity`. Establish `hv2 : ENNReal.ofReal (∏ v, c v) * B.I.muA B.μf B.fund ≤ ENNReal.ofReal (Y * m)`. Use `(hvol.trans (mul_le_mul' le_rfl hidx)).trans_eq ?_` and prove the remaining obligations.

Rewrite using `[show Y * m = bigX B b ^ N * ((B.g : ℝ) ^ (2 * N) * m) by rw [hY]; ring, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), hm, ENNReal.ofReal_toReal hKgfin, ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]`. Establish `hfin : B.I.muA B.μf B.fund < ⊤`. Rewrite using `[lt_top_iff_ne_top]`. Introduce `h`. Rewrite `hv2` using `[h, ENNReal.mul_top (ENNReal.ofReal_pos.2 hcp).ne']`.

Conclude with `ENNReal.ofReal_ne_top (top_le_iff.1 hv2)`. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Establish `hv3 : (∏ v, c v) * (B.I.muA B.μf B.fund).toReal ≤ Y * m`. Use `ENNReal.toReal_mono ENNReal.ofReal_ne_top hv2` as an intermediate fact. Rewrite `this` using `[ENNReal.toReal_mul, ENNReal.toReal_ofReal hcp.le, ENNReal.toReal_ofReal (by positivity)]`. Then use the resulting hypothesis.

Establish `hl : 0 < least B.I x` using `((GlobalTheory.CountSteps.steps B.I x 1 one_pos).2.2.2.2.2.2.2.2 (by omega)).1`. Establish `ha` using `(GlobalTheory.deep_region_exponents B.I.n B.I.f q B.I.rd B.g b (least B.I x) hn hf hq hq2 hrd hb hgR hl hx.le).2`. Establish `hbe : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * N + N) = Real.sqrt B.I.n * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) + 3 * ((8 * q * N + N : ℕ) : ℝ)`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe`. Establish `: (B.I.n : ℝ) ^ ((3 : ℝ) / 2) = B.I.n * Real.sqrt B.I.n`.

Rewrite using `[show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one, Real.sqrt_eq_rpow]`. Rewrite using `[this]`. Evaluate the numerical expressions. Establish `hd : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B = N` using `rfl`. Rewrite using `[hd, hbe, show 16 * q * N = 2 * (8 * q * N) by ring]`.

Unfold `GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh`. Rewrite `ha` using `[← hN]`. Generalize the expression as in `(2 * ((B.I.n : ℝ) ^ 2 * Real.sqrt B.I.f * B.g * B.I.rd * (2 * least B.I x) ^ ((1 : ℝ) / q) / 4) * Real.sqrt B.I.f * (Real.sqrt B.I.n * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) + 3 * ((8 * q * N + N : ℕ) : ℝ))) ^ (2 * (8 * q * N)) = u at ha ⊢`. Generalize the expression as in `(6 * (Real.sqrt B.I.n * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) + 3 * ((8 * q * N + N : ℕ) : ℝ))) ^ N = v at ha ⊢`. Generalize the expression as in `(17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * N) = w at ha ⊢`.

Establish `h1 : u * v * Real.exp B.I.f * w ≤ Real.exp (-(N : ℝ)) / Y`. Rewrite using `[le_div_iff₀ hY0]`. Use `le_of_eq_of_le ?_ ha` and prove the remaining obligations. Rewrite using `[hY]`. Unfold `bigX`.

Expand and normalize the polynomial expressions, which then agree. Establish `hNc : (N : ℝ) = (B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)` using `by rw [hN]; push_cast; ring`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hNc]`. Clear the denominators using the available nonvanishing facts.
-/
theorem deep_mul_volume_le (hV : GlobalTheory.FlagMeas.AbsoluteVolume) (B : RowsAut) (Cg : ℝ) (n₀ : ℕ)
    (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ) (c : InfinitePlace B.I.F → ℝ) (x : B.I.GA)
    (hn₀ : 8 ≤ n₀) (hq : 1 ≤ q) (hC : CountHyp B Cg n₀ d p q b) (hc : ∀ v, IsGauge (B.I.ε v) (c v))
    (hx : least B.I x < tauStar B q b) :
    B.I.muA B.μf B.fund < ⊤ ∧
    (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) * Real.sqrt B.I.f * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b
        (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ (16 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) *
      (6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^
        GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f *
      (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (∏ v, c v) /
      (B.μf (B.I.Kg B.g)).toReal * (B.I.muA B.μf B.fund).toReal ≤
      Real.exp (-((B.I.n : ℝ) ^ 2 * B.I.f)) := by
  obtain ⟨-, hsig, hn', hq2, -, -, hb, -, -, hg, -⟩ := hC
  have hn : 8 ≤ B.I.n := hn₀.trans hn'
  have hc0 : ∀ v, 0 < c v := fun v => by
    obtain ⟨c', h0, -, hu⟩ := GlobalTheory.GaugeConst.exists_unique_isGauge B.I.n (B.I.ε v)
    rw [hu _ (hc v)]; exact h0
  have hf := one_le_f B.I
  have hrd := one_le_rd B.I
  have hnR : (8 : ℝ) ≤ B.I.n := by exact_mod_cast hn
  have hfR : (1 : ℝ) ≤ B.I.f := by exact_mod_cast hf
  have hgR : (1 : ℝ) ≤ B.g := by exact_mod_cast hg
  have hfr : B.I.rd ≤ B.I.f * B.I.rd := by nlinarith
  have hX : 2 * (B.I.f * B.I.rd) ≤ bigX B b := by
    have h1 : (2 : ℝ) ≤ B.g * b := by nlinarith
    have h2 : (2 : ℝ) ≤ B.I.n * (B.g * b) := by nlinarith
    have : bigX B b = (B.I.n * (B.g * b)) * (B.I.f * B.I.rd) := by unfold bigX; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right h2 (by linarith)
  have hX2 : 2 ≤ bigX B b := by linarith
  have hvol := hV B.I p q hsig hq2 hn (bigX B b) hX2 (by linarith) (by nlinarith) c B.μf hc
  obtain ⟨hcov, -⟩ := GlobalTheory.T.leftQuotientCovolume_eq_fundamentalDomain_inter B.I B.μf B.fund Set.univ B.fund_spec MeasurableSet.univ
    (fun _ _ _ _ => Set.mem_univ _)
  obtain ⟨hidx, hKg0, hKfin⟩ := GlobalTheory.CongIndex.measure_Kset_le B.I B.μf B.g hg
  have hKgfin : B.μf (B.I.Kg B.g) ≠ ⊤ :=
    ne_top_of_le_ne_top hKfin.ne (measure_mono fun _ h => h.1)
  unfold GlobalTheory.FlagMeas.gaugeVol at hvol
  rw [hcov, Set.univ_inter, ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top) (Or.inl hKfin.ne)] at hvol
  set N : ℕ := B.I.n ^ 2 * B.I.f with hN
  set m : ℝ := (B.μf (B.I.Kg B.g)).toReal with hm
  have hm0 : 0 < m := ENNReal.toReal_pos hKg0.ne' hKgfin
  have hcp : 0 < ∏ v, c v := Finset.prod_pos fun v _ => hc0 v
  have hXp : 0 < bigX B b := by linarith
  have hgp : (0 : ℝ) < B.g := by linarith
  set Y : ℝ := (B.g : ℝ) ^ (2 * N) * bigX B b ^ N with hY
  have hY0 : 0 < Y := by positivity
  have hv2 : ENNReal.ofReal (∏ v, c v) * B.I.muA B.μf B.fund ≤ ENNReal.ofReal (Y * m) := by
    refine (hvol.trans (mul_le_mul' le_rfl hidx)).trans_eq ?_
    rw [show Y * m = bigX B b ^ N * ((B.g : ℝ) ^ (2 * N) * m) by rw [hY]; ring,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      hm, ENNReal.ofReal_toReal hKgfin, ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hfin : B.I.muA B.μf B.fund < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 hcp).ne'] at hv2
    exact ENNReal.ofReal_ne_top (top_le_iff.1 hv2)
  refine ⟨hfin, ?_⟩
  have hv3 : (∏ v, c v) * (B.I.muA B.μf B.fund).toReal ≤ Y * m := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hv2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcp.le, ENNReal.toReal_ofReal (by positivity)] at this
  have hl : 0 < least B.I x := ((GlobalTheory.CountSteps.steps B.I x 1 one_pos).2.2.2.2.2.2.2.2 (by omega)).1
  have ha := (GlobalTheory.deep_region_exponents B.I.n B.I.f q B.I.rd B.g b (least B.I x) hn hf hq hq2 hrd hb hgR hl
    hx.le).2
  have hbe : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * N + N) =
      Real.sqrt B.I.n * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) + 3 * ((8 * q * N + N : ℕ) : ℝ) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe
    have : (B.I.n : ℝ) ^ ((3 : ℝ) / 2) = B.I.n * Real.sqrt B.I.n := by
      rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one,
        Real.sqrt_eq_rpow]
    rw [this]; norm_num
  have hd : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B = N := rfl
  rw [hd, hbe, show 16 * q * N = 2 * (8 * q * N) by ring]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh
  rw [← hN] at ha
  generalize (2 * ((B.I.n : ℝ) ^ 2 * Real.sqrt B.I.f * B.g * B.I.rd * (2 * least B.I x) ^ ((1 : ℝ) / q) / 4) *
    Real.sqrt B.I.f * (Real.sqrt B.I.n * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) +
      3 * ((8 * q * N + N : ℕ) : ℝ))) ^ (2 * (8 * q * N)) = u at ha ⊢
  generalize (6 * (Real.sqrt B.I.n * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) +
      3 * ((8 * q * N + N : ℕ) : ℝ))) ^ N = v at ha ⊢
  generalize (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * N) = w at ha ⊢
  have h1 : u * v * Real.exp B.I.f * w ≤ Real.exp (-(N : ℝ)) / Y := by
    rw [le_div_iff₀ hY0]
    refine le_of_eq_of_le ?_ ha
    rw [hY]; unfold bigX; ring
  have hNc : (N : ℝ) = (B.I.n : ℝ) ^ 2 * (B.I.f : ℝ) := by rw [hN]; push_cast; ring
  calc u * v * Real.exp B.I.f * w * (∏ v, c v) / m * (B.I.muA B.μf B.fund).toReal
      ≤ Real.exp (-(N : ℝ)) / Y * (∏ v, c v) / m * (B.I.muA B.μf B.fund).toReal := by gcongr
    _ = Real.exp (-(N : ℝ)) / Y / m * ((∏ v, c v) * (B.I.muA B.μf B.fund).toReal) := by ring
    _ ≤ Real.exp (-(N : ℝ)) / Y / m * (Y * m) := by gcongr
    _ = Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) := by
        rw [hNc]; field_simp

end GlobalTheory.DeepArith
