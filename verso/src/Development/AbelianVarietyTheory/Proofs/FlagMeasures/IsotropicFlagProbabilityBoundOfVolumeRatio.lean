import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermVolumeRatioSameKindOfVolumeRatioInductionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenLinTamagawaVolumeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnfoldingBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeEqFundamentalDomainInterStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAdelicQuotientVolumePosLtTopStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeExistsPosUniqueStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutInstDegreeRootDiscriminantRankStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PointsOfFlagTypeSetMeasurableAndInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdFiveFactorsHermitianVolumeStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.FlagMeas.Bound

open scoped ComplexOrder in

/- English proof (translation)
Unfold `zetaE dedekindZeta LSeries`. Establish `h : (0 : ℂ) ≤ ∑' n : ℕ, LSeries.term (fun n => (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℂ)) ((l : ℝ) : ℂ) n` using `tsum_nonneg fun n => LSeries.term_nonneg (by exact Nat.cast_nonneg _) _`. Establish `h2` using `(Complex.le_def.1 h).1`. Simplify using `using h2`.
-/
theorem zetaE_nonneg (E : Type) [Field E] [NumberField E] (l : ℕ) : 0 ≤ zetaE E l := by
  unfold zetaE dedekindZeta LSeries
  have h : (0 : ℂ) ≤ ∑' n : ℕ, LSeries.term
      (fun n => (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℂ)) ((l : ℝ) : ℂ) n :=
    tsum_nonneg fun n => LSeries.term_nonneg (by exact Nat.cast_nonneg _) _
  have h2 := (Complex.le_def.1 h).1
  simpa using h2

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.vInv`. Check the signs of the components of the expression.
-/
theorem vInv_nonneg (E : Type) [Field E] [NumberField E] : 0 ≤ Formalism.HermitianLatticesTheory.vInv E := by
  unfold Formalism.HermitianLatticesTheory.vInv
  positivity

/- English proof (translation)
Unfold `volU sphV`. Check the signs of the components of the expression.
-/
theorem volU_nonneg (i : ℕ) : 0 ≤ volU i := by
  unfold volU sphV
  positivity

/- English proof (translation)
Unfold `cIw`. Establish `h` using `volU_nonneg`. Use `div_nonneg (mul_nonneg (by positivity) (mul_nonneg (h _) (h _))) (mul_nonneg (mul_nonneg (Finset.prod_nonneg fun i _ => mul_nonneg (h _) (by positivity)) (h _)) (h _))` and prove the remaining obligations.
-/
theorem cIw_nonneg (p q : ℕ) {a : ℕ} (j : Fin a → ℕ) : 0 ≤ cIw p q j := by
  unfold cIw
  have h := volU_nonneg
  refine div_nonneg (mul_nonneg (by positivity) (mul_nonneg (h _) (h _)))
    (mul_nonneg (mul_nonneg (Finset.prod_nonneg fun i _ => mul_nonneg (h _) (by positivity)) (h _)) (h _))

/- English proof (translation)
Establish `hD0 : C / K ≠ 0` using `(ENNReal.div_pos hC0 hK).ne'`. Establish `hD : C / K ≠ ⊤` using `ENNReal.div_ne_top hC hK0`. Establish `e1 : ∀ y, C * y / K = C / K * y` using `fun y => by`. Rewrite using `[div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]`. Rewrite `h1`, `h2` using `[e1]`.

Establish `hp0 : V * ENNReal.ofReal R ≠ 0` using `h2 ▸ mul_ne_zero hD0 hm0`. Establish `hp : V * ENNReal.ofReal R ≠ ⊤` using `h2 ▸ ENNReal.mul_ne_top hD hm`. Establish `hV0 : V ≠ 0` using `left_ne_zero_of_mul hp0`. Establish `hR0 : ENNReal.ofReal R ≠ 0` using `right_ne_zero_of_mul hp0`. Establish `hV : V ≠ ⊤` using `fun h => hp (by rw [h, ENNReal.top_mul hR0])`.

Use `⟨by simpa using hR0, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem div_le_of_scaled {C K x m T V J : ENNReal} {R : ℝ} (hC0 : C ≠ 0) (hC : C ≠ ⊤) (hK0 : K ≠ 0) (hK : K ≠ ⊤)
    (hm0 : m ≠ 0) (hm : m ≠ ⊤) (h1 : C * x / K ≤ T * V * J) (h2 : C * m / K = V * ENNReal.ofReal R) :
    0 < R ∧ x / m ≤ T / ENNReal.ofReal R * J := by
  have hD0 : C / K ≠ 0 := (ENNReal.div_pos hC0 hK).ne'
  have hD : C / K ≠ ⊤ := ENNReal.div_ne_top hC hK0
  have e1 : ∀ y, C * y / K = C / K * y := fun y => by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
  rw [e1] at h1 h2
  have hp0 : V * ENNReal.ofReal R ≠ 0 := h2 ▸ mul_ne_zero hD0 hm0
  have hp : V * ENNReal.ofReal R ≠ ⊤ := h2 ▸ ENNReal.mul_ne_top hD hm
  have hV0 : V ≠ 0 := left_ne_zero_of_mul hp0
  have hR0 : ENNReal.ofReal R ≠ 0 := right_ne_zero_of_mul hp0
  have hV : V ≠ ⊤ := fun h => hp (by rw [h, ENNReal.top_mul hR0])
  refine ⟨by simpa using hR0, ?_⟩
  calc x / m = (C / K * x) / (C / K * m) := (ENNReal.mul_div_mul_left _ _ hD0 hD).symm
    _ ≤ (T * V * J) / (V * ENNReal.ofReal R) := by rw [h2]; gcongr
    _ = (V * (T * J)) / (V * ENNReal.ofReal R) := by ring_nf
    _ = T * J / ENNReal.ofReal R := ENNReal.mul_div_mul_left _ _ hV0 hV
    _ = T / ENNReal.ofReal R * J := by rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]

/- English proof (translation)
Introduce `hstep I μf _ _ fund hfund p q hsig hn a j ha hj hjq B hB hBs`. Take `⟨hf, -, -, -, -, hpq⟩` from `GlobalTheory.T.autInst_degree_rootDiscriminant_rank I`. Establish `hpq` using `hpq p q hsig`. Take `⟨hmeas, hinv, -⟩` from `GlobalTheory.T.pointsOfFlagTypeSet_measurable_and_invariant I a j B hB`. Take `⟨hpos, hfin⟩` from `GlobalTheory.T.unitary_adelic_quotient_volume_pos_lt_top hstep I μf fund hfund p q hsig (by omega)`.

Use `⟨hmeas, hpos, hfin, ?_⟩` and prove the remaining obligations. Take `⟨⟨I₀, hsame, hsig₀⟩, hratio⟩` from `GlobalTheory.T.hermVolumeRatioSameKind_of_volumeRatioInduction hstep I p q (p - ∑ i, j i) (q - ∑ i, j i) hsig (Nat.sub_le _ _) (Nat.sub_le _ _) (by omega)`. Take `⟨t₀, lc₀, sc₀, -⟩` from `GlobalTheory.CongTop.adelic_topology I₀`. Take `⟨-, -, -, hKc, hKo, ⟨Ks, hKs⟩, -⟩` from `GlobalTheory.CongTop.adelic_topology I`. Use `choose c hc0 hc _ using fun v => GlobalTheory.T.riemannianHaarGauge_exists_pos_unique I.n (I.ε v)`.

Use `choose c₀ _ hc₀ _ using fun v => GlobalTheory.T.riemannianHaarGauge_exists_pos_unique I₀.n (I₀.ε v)`. Set `μ₀ : Measure I₀.Gf` to `Measure.haar`. Establish `hU` using `GlobalTheory.T.isotropicFlag_unfolding_bound I I₀ p q a j ha hj hjq (by omega) hsame hsig hsig₀ c μf c₀ μ₀ hc hc₀ B hB hBs`. Establish `hR` using `hratio I₀ hsame hsig₀ c μf c₀ μ₀ hc hc₀`. Rewrite `hU` using `[(GlobalTheory.T.leftQuotientCovolume_eq_fundamentalDomain_inter I μf fund _ hfund hmeas hinv).1]`.

Establish `hR' : ENNReal.ofReal (∏ v, c v) * I.muA μf fund / μf I.Kset = gaugeVol I₀ c₀ μ₀ * ENNReal.ofReal (∏ M ∈ Finset.Ioc (p + q - 2 * ∑ i, j i) (p + q), rankFac I.E M)`. Establish `e : p - ∑ i, j i + (q - ∑ i, j i) = p + q - 2 * ∑ i, j i` using `by omega`. Rewrite using `[← e, ← hR, gaugeVol, (GlobalTheory.T.leftQuotientCovolume_eq_fundamentalDomain_inter I μf fund Set.univ hfund MeasurableSet.univ (fun _ _ _ _ => Set.mem_univ _)).1, Set.univ_inter]`. Establish `hK0 : μf I.Kset ≠ 0` using `(hKo.measure_pos μf ⟨1, by rw [← hKs]; exact Ks.one_mem⟩).ne'`. Establish `hK : μf I.Kset ≠ ⊤` using `hKc.measure_lt_top.ne`.

Establish `hC0 : ENNReal.ofReal (∏ v, c v) ≠ 0`. Simplify using `using Finset.prod_pos fun v _ => hc0 v`. Take `⟨hRpos, hle⟩` from `div_le_of_scaled hC0 ENNReal.ofReal_ne_top hK0 hK hpos.ne' hfin.ne hU hR'`. Use `hle.trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`.

Establish `hv` using `vInv_nonneg I.E`. Establish `hres` using `(dedekindZeta_residue_pos I.E).le`. Rewrite using `[← GlobalTheory.T.prod_five_factors_hermitian_volume I.E I.cm.cmUnram p q a j hjq (by omega), ENNReal.ofReal_div_of_pos hRpos, hf, hpq, ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (cIw_nonneg p q j) _) (by positivity)), ENNReal.ofReal_prod_of_nonneg (fun i _ => mul_nonneg (by posi …`. Use `congr 2`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[GlobalTheory.T.genLin_tamagawa_volume I.E I.cm.cmUnram.1 (j i) (hj i), hf]`. Conclude with `(ENNReal.ofReal_mul (by positivity)).symm`.
-/
theorem flagMeasureBound : VolumeStep → FlagMeasureBound := by
  intro hstep I μf _ _ fund hfund p q hsig hn a j ha hj hjq B hB hBs
  obtain ⟨hf, -, -, -, -, hpq⟩ := GlobalTheory.T.autInst_degree_rootDiscriminant_rank I
  have hpq := hpq p q hsig
  obtain ⟨hmeas, hinv, -⟩ := GlobalTheory.T.pointsOfFlagTypeSet_measurable_and_invariant I a j B hB
  obtain ⟨hpos, hfin⟩ := GlobalTheory.T.unitary_adelic_quotient_volume_pos_lt_top hstep I μf fund hfund p q hsig (by omega)
  refine ⟨hmeas, hpos, hfin, ?_⟩
  obtain ⟨⟨I₀, hsame, hsig₀⟩, hratio⟩ := GlobalTheory.T.hermVolumeRatioSameKind_of_volumeRatioInduction hstep I p q (p - ∑ i, j i) (q - ∑ i, j i) hsig
    (Nat.sub_le _ _) (Nat.sub_le _ _) (by omega)
  obtain ⟨t₀, lc₀, sc₀, -⟩ := GlobalTheory.CongTop.adelic_topology I₀
  obtain ⟨-, -, -, hKc, hKo, ⟨Ks, hKs⟩, -⟩ := GlobalTheory.CongTop.adelic_topology I
  choose c hc0 hc _ using fun v => GlobalTheory.T.riemannianHaarGauge_exists_pos_unique I.n (I.ε v)
  choose c₀ _ hc₀ _ using fun v => GlobalTheory.T.riemannianHaarGauge_exists_pos_unique I₀.n (I₀.ε v)
  let μ₀ : Measure I₀.Gf := Measure.haar
  have hU := GlobalTheory.T.isotropicFlag_unfolding_bound I I₀ p q a j ha hj hjq (by omega) hsame hsig hsig₀ c μf c₀ μ₀ hc hc₀ B hB hBs
  have hR := hratio I₀ hsame hsig₀ c μf c₀ μ₀ hc hc₀
  rw [(GlobalTheory.T.leftQuotientCovolume_eq_fundamentalDomain_inter I μf fund _ hfund hmeas hinv).1] at hU
  have hR' : ENNReal.ofReal (∏ v, c v) * I.muA μf fund / μf I.Kset = gaugeVol I₀ c₀ μ₀ *
      ENNReal.ofReal (∏ M ∈ Finset.Ioc (p + q - 2 * ∑ i, j i) (p + q), rankFac I.E M) := by
    have e : p - ∑ i, j i + (q - ∑ i, j i) = p + q - 2 * ∑ i, j i := by omega
    rw [← e, ← hR, gaugeVol,
      (GlobalTheory.T.leftQuotientCovolume_eq_fundamentalDomain_inter I μf fund Set.univ hfund MeasurableSet.univ (fun _ _ _ _ => Set.mem_univ _)).1,
      Set.univ_inter]
  have hK0 : μf I.Kset ≠ 0 := (hKo.measure_pos μf ⟨1, by rw [← hKs]; exact Ks.one_mem⟩).ne'
  have hK : μf I.Kset ≠ ⊤ := hKc.measure_lt_top.ne
  have hC0 : ENNReal.ofReal (∏ v, c v) ≠ 0 := by
    simpa using Finset.prod_pos fun v _ => hc0 v
  obtain ⟨hRpos, hle⟩ := div_le_of_scaled hC0 ENNReal.ofReal_ne_top hK0 hK hpos.ne' hfin.ne hU hR'
  refine hle.trans (le_of_eq ?_)
  congr 1
  have hv := vInv_nonneg I.E
  have hres := (dedekindZeta_residue_pos I.E).le
  rw [← GlobalTheory.T.prod_five_factors_hermitian_volume I.E I.cm.cmUnram p q a j hjq (by omega), ENNReal.ofReal_div_of_pos hRpos, hf, hpq,
    ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (cIw_nonneg p q j) _) (by positivity)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => mul_nonneg (by positivity)
      (mul_nonneg (by positivity) (Finset.prod_nonneg fun l _ => zetaE_nonneg I.E l)))]
  congr 2
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [GlobalTheory.T.genLin_tamagawa_volume I.E I.cm.cmUnram.1 (j i) (hj i), hf]
  exact (ENNReal.ofReal_mul (by positivity)).symm

end GlobalTheory.FlagMeas.Bound
