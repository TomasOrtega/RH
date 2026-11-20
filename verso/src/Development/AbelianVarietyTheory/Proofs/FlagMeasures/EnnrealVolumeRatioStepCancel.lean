import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphicInstanceExistsFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NegLogProdLValEtaLeAndPosStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianSumStabiliserUnfoldingStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeEqFundamentalDomainInterStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianQuadricDensityExistsPosContinuousStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutInstDegreeRootDiscriminantRankStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitVectorOrthogonalInstanceRankThreeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRatioRankFactorStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

noncomputable section

namespace GlobalTheory.GaussMean.Step

/- English proof (translation)
Establish `: 0 < sphV i`. Unfold `sphV`. Conclude with `Finset.prod_pos fun l _ => by have := Real.pi_pos; positivity`. Unfold `volU`. Check the signs of the components of the expression.
-/
theorem volU_pos (i : ℕ) : 0 < volU i := by
  have : 0 < sphV i := by
    unfold sphV
    exact Finset.prod_pos fun l _ => by have := Real.pi_pos; positivity
  unfold volU
  positivity

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.vInv`. Establish `: (0 : ℝ) < |(discr E : ℝ)|` using `abs_pos.2 (by exact_mod_cast discr_ne_zero E)`. Check the signs of the components of the expression.
-/
theorem vInv_pos (E : Type) [Field E] [NumberField E] : 0 < Formalism.HermitianLatticesTheory.vInv E := by
  unfold Formalism.HermitianLatticesTheory.vInv
  have : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero E)
  positivity

/- English proof (translation)
Establish `hv` using `vInv_pos E`. Unfold `rankFac meanConst`. Use `set v := Formalism.HermitianLatticesTheory.vInv E`. Use `set f := Formalism.HermitianLatticesTheory.fDeg E`. Use `set L := Formalism.HermitianLatticesTheory.lValEta E M`.

Establish `h2 : 0 < 2 * v` using `by positivity`. Establish `key : (2 * v) ^ ((f : ℝ) * ((M : ℝ) - 1 / 2)) * (2 * v) ^ ((f : ℝ) / 2) = 2 ^ (M * f) * v ^ (M * f)`. Rewrite using `[← Real.rpow_add h2, ← mul_pow, ← Real.rpow_natCast]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hp : 0 < v ^ (M * f)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts. Use `_ = 2 ^ (M * f) := by rw [key]; field_simp`.
-/
theorem rankFac_mul_meanConst (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ)
    (hL : 0 < Formalism.HermitianLatticesTheory.lValEta E M) :
    rankFac E M * meanConst E M = 2 ^ (M * Formalism.HermitianLatticesTheory.fDeg E) := by
  have hv := vInv_pos E
  unfold rankFac meanConst
  set v := Formalism.HermitianLatticesTheory.vInv E
  set f := Formalism.HermitianLatticesTheory.fDeg E
  set L := Formalism.HermitianLatticesTheory.lValEta E M
  have h2 : 0 < 2 * v := by positivity
  have key : (2 * v) ^ ((f : ℝ) * ((M : ℝ) - 1 / 2)) * (2 * v) ^ ((f : ℝ) / 2)
      = 2 ^ (M * f) * v ^ (M * f) := by
    rw [← Real.rpow_add h2, ← mul_pow, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hp : 0 < v ^ (M * f) := by positivity
  calc (2 * v) ^ ((f : ℝ) * ((M : ℝ) - 1 / 2)) * L * ((2 * v) ^ ((f : ℝ) / 2) * (v ^ (M * f))⁻¹ / L)
      = ((2 * v) ^ ((f : ℝ) * ((M : ℝ) - 1 / 2)) * (2 * v) ^ ((f : ℝ) / 2)) * (v ^ (M * f))⁻¹ := by
        field_simp
    _ = 2 ^ (M * f) := by rw [key]; field_simp

/- English proof (translation)
Establish `hv` using `vInv_pos E`. Unfold `meanConst`. Check the signs of the components of the expression.
-/
theorem meanConst_pos (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ)
    (hL : 0 < Formalism.HermitianLatticesTheory.lValEta E M) : 0 < meanConst E M := by
  have hv := vInv_pos E
  unfold meanConst
  positivity

/- English proof (translation)
Establish `hv` using `vInv_pos E`. Unfold `rankFac`. Check the signs of the components of the expression.
-/
theorem rankFac_pos (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ)
    (hL : 0 < Formalism.HermitianLatticesTheory.lValEta E M) : 0 < rankFac E M := by
  have hv := vInv_pos E
  unfold rankFac
  positivity

/- English proof (translation)
Establish `hmd : 0 < m * d` using `mul_pos hm hd`. Establish `h1 : X = Y * ENNReal.ofReal r`. Establish `e : t * d = r * (m * d)` using `by rw [← ht]; ring`. Rewrite `h` using `[e, ENNReal.ofReal_mul hr.le, ← mul_assoc]`. Conclude with `(ENNReal.mul_left_inj (ENNReal.ofReal_pos.2 hmd).ne' ENNReal.ofReal_ne_top).1 h`.

Establish `e2 : ρ = b * (r / a)` using `by field_simp; linarith`. Rewrite using `[h1, e2, ENNReal.ofReal_mul hb.le, ← mul_assoc, ENNReal.div_mul_cancel (ENNReal.ofReal_pos.2 hb).ne' ENNReal.ofReal_ne_top, ENNReal.ofReal_div_of_pos ha, mul_div_assoc]`.
-/
theorem ennreal_volume_ratio_step_cancel (X Y : ENNReal) (m d t r a b ρ : ℝ) (hm : 0 < m) (hd : 0 < d) (hr : 0 < r)
    (ha : 0 < a) (hb : 0 < b) (ht : r * m = t) (hρ : ρ * a = r * b)
    (h : X * ENNReal.ofReal (m * d) = Y * ENNReal.ofReal (t * d)) :
    X / ENNReal.ofReal a = Y / ENNReal.ofReal b * ENNReal.ofReal ρ := by
  have hmd : 0 < m * d := mul_pos hm hd
  have h1 : X = Y * ENNReal.ofReal r := by
    have e : t * d = r * (m * d) := by rw [← ht]; ring
    rw [e, ENNReal.ofReal_mul hr.le, ← mul_assoc] at h
    exact (ENNReal.mul_left_inj (ENNReal.ofReal_pos.2 hmd).ne' ENNReal.ofReal_ne_top).1 h
  have e2 : ρ = b * (r / a) := by field_simp; linarith
  rw [h1, e2, ENNReal.ofReal_mul hb.le, ← mul_assoc,
    ENNReal.div_mul_cancel (ENNReal.ofReal_pos.2 hb).ne' ENNReal.ofReal_ne_top,
    ENNReal.ofReal_div_of_pos ha, mul_div_assoc]

/- English proof (translation)
Introduce `hS I P Q hPQ hn s hs`. Take `⟨I', e, x, A, xf, hperp, hsig⟩` from `GlobalTheory.T.exists_unit_vector_orthogonal_instance_rank_three I P Q hPQ hn s hs`. Use `⟨I', e, x, A, hperp.1, hperp.2.1, hperp.2.2.1, hperp.2.2.2.1, hperp.2.2.2.2.1, hsig, ?_⟩` and prove the remaining obligations. Introduce `c μf _ _ c' μf' _ _ hc hc'`. Take `⟨fund, hfund⟩` from `GlobalTheory.T.automorphicInstance_exists_fundamental_domain I μf`.

Establish `hU` using `GlobalTheory.T.gaussianSum_stabiliserUnfolding I I' e s x A xf hn hperp c μf c' μf' fund hc hc' hfund`. Take `⟨-, hM⟩` from `hS I hn s μf fund hfund`. Establish `hcov` using `(GlobalTheory.T.leftQuotientCovolume_eq_fundamentalDomain_inter I μf fund Set.univ hfund MeasurableSet.univ (fun _ _ _ _ => Set.mem_univ _)).1`. Rewrite `hcov` using `[Set.univ_inter]`. Establish `hf : Formalism.HermitianLatticesTheory.fDeg I.E = I.f` using `(GlobalTheory.T.autInst_degree_rootDiscriminant_rank I).1`.

Establish `hL : 0 < Formalism.HermitianLatticesTheory.lValEta I.E I.n`. Use `(GlobalTheory.T.neg_log_prod_lValEta_le_and_pos I.E I.cm.cmUnram (I.n - 1) I.n (by omega)).2` as an intermediate fact. Establish `hI : Finset.Ioc (I.n - 1) I.n = {I.n}`. Use extensionality with `k`. Simplify using `only [Finset.mem_Ioc, Finset.mem_singleton]`.

Use linear arithmetic over natural numbers and integers. Rewrite `this` using `[hI, Finset.prod_singleton]`. Then use the resulting hypothesis. Establish `hd : 0 < ∏ v, gaussDens (I.ε v) (sgn ℝ s)`. Use `Finset.prod_pos fun v _ => (GlobalTheory.T.gaussianQuadricDensity_exists_pos_continuous I.n (I.ε v)).2.2 s ?_` and prove the remaining obligations. Take `⟨hp, hq⟩` from `hPQ v`.

Consider the cases of `s`. Establish `: 0 < I.qAt v`. Establish `h1 : 1 ≤ Q` using `by simpa using hs`. Use linear arithmetic over natural numbers and integers. Take `⟨a, ha⟩` from `Finset.card_pos.1 this`.

Conclude with `⟨a, (Finset.mem_filter.1 ha).2⟩`. Establish `: 0 < I.pAt v`. Establish `h1 : 1 ≤ P` using `by simpa using hs`. Use linear arithmetic over natural numbers and integers. Take `⟨a, ha⟩` from `Finset.card_pos.1 this`.

Conclude with `⟨a, (Finset.mem_filter.1 ha).2⟩`. Establish `hR` using `GlobalTheory.T.mass_ratio_rank_factor I.E I.n (by omega)`. Establish `hn' : I.n - 1 = I'.n` using `by have := hperp.2.1; omega`. Rewrite `hR` using `[hf, hn']`. Establish `hrm` using `rankFac_mul_meanConst I.E I.n hL`.

Rewrite `hrm` using `[hf]`. Use `ennreal_volume_ratio_step_cancel _ _ _ _ _ _ _ _ _ (meanConst_pos I.E I.n hL) hd (rankFac_pos I.E I.n hL) (pow_pos (volU_pos _) _) (pow_pos (volU_pos _) _) hrm hR ?_` and prove the remaining obligations. Rewrite using `[← hU, hM, gaugeVol, hcov]`. Simplify using `only [div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem volumeStep_of_siegelMean : SiegelMean → VolumeStep := by
  intro hS I P Q hPQ hn s hs
  obtain ⟨I', e, x, A, xf, hperp, hsig⟩ := GlobalTheory.T.exists_unit_vector_orthogonal_instance_rank_three I P Q hPQ hn s hs
  refine ⟨I', e, x, A, hperp.1, hperp.2.1, hperp.2.2.1, hperp.2.2.2.1, hperp.2.2.2.2.1, hsig, ?_⟩
  intro c μf _ _ c' μf' _ _ hc hc'
  obtain ⟨fund, hfund⟩ := GlobalTheory.T.automorphicInstance_exists_fundamental_domain I μf
  have hU := GlobalTheory.T.gaussianSum_stabiliserUnfolding I I' e s x A xf hn hperp c μf c' μf' fund hc hc' hfund
  obtain ⟨-, hM⟩ := hS I hn s μf fund hfund
  have hcov := (GlobalTheory.T.leftQuotientCovolume_eq_fundamentalDomain_inter I μf fund Set.univ hfund MeasurableSet.univ
    (fun _ _ _ _ => Set.mem_univ _)).1
  rw [Set.univ_inter] at hcov
  have hf : Formalism.HermitianLatticesTheory.fDeg I.E = I.f := (GlobalTheory.T.autInst_degree_rootDiscriminant_rank I).1
  have hL : 0 < Formalism.HermitianLatticesTheory.lValEta I.E I.n := by
    have := (GlobalTheory.T.neg_log_prod_lValEta_le_and_pos I.E I.cm.cmUnram (I.n - 1) I.n (by omega)).2
    have hI : Finset.Ioc (I.n - 1) I.n = {I.n} := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_singleton]
      omega
    rwa [hI, Finset.prod_singleton] at this
  have hd : 0 < ∏ v, gaussDens (I.ε v) (sgn ℝ s) := by
    refine Finset.prod_pos fun v _ => (GlobalTheory.T.gaussianQuadricDensity_exists_pos_continuous I.n (I.ε v)).2.2 s ?_
    obtain ⟨hp, hq⟩ := hPQ v
    cases s
    · have : 0 < I.qAt v := by
        have h1 : 1 ≤ Q := by simpa using hs
        omega
      obtain ⟨a, ha⟩ := Finset.card_pos.1 this
      exact ⟨a, (Finset.mem_filter.1 ha).2⟩
    · have : 0 < I.pAt v := by
        have h1 : 1 ≤ P := by simpa using hs
        omega
      obtain ⟨a, ha⟩ := Finset.card_pos.1 this
      exact ⟨a, (Finset.mem_filter.1 ha).2⟩
  have hR := GlobalTheory.T.mass_ratio_rank_factor I.E I.n (by omega)
  have hn' : I.n - 1 = I'.n := by have := hperp.2.1; omega
  rw [hf, hn'] at hR
  have hrm := rankFac_mul_meanConst I.E I.n hL
  rw [hf] at hrm
  refine ennreal_volume_ratio_step_cancel _ _ _ _ _ _ _ _ _ (meanConst_pos I.E I.n hL) hd (rankFac_pos I.E I.n hL)
    (pow_pos (volU_pos _) _) (pow_pos (volU_pos _) _) hrm hR ?_
  rw [← hU, hM, gaugeVol, hcov]
  simp only [div_eq_mul_inv]
  ring

end GlobalTheory.GaussMean.Step
