import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLawsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpBinomialPowerSubOneSeriesIntegralityCompositioStatement
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

/- English proof (translation)
Unfold `DT`. Rewrite using `[← smul_eq_C_mul, Derivation.map_smul, smul_eq_C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hatmul_DT_C_mul {q : ℕ} [Fact q.Prime] (c : ℂ_[q]) (f : ℂ_[q]⟦X⟧) :
    DT (C c * f) = C c * DT f := by
  unfold DT
  rw [← smul_eq_C_mul, Derivation.map_smul, smul_eq_C_mul]
  ring

/- English proof (translation)
Establish `: constantCoeff (logS : ℂ_[q]⟦X⟧) = 0`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply]`. Simplify using `[logS]`. Simplify using `[this]`.
-/
lemma hatmul_const_log {q : ℕ} [Fact q.Prime] (ω : ℂ_[q]) :
    constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
  have : constantCoeff (logS : ℂ_[q]⟦X⟧) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [logS]
  simp [this]

/- English proof (translation)
Take `⟨-, -, -, -, hd, -, -⟩` from `GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q ι _ (hatmul_const_log ω)`. Take `⟨-, -, -, -, hl, -⟩` from `GlobalTheory.T.cpBinomialPowerSubOneSeries_integrality_composition_log q`. Establish `h1 : DT (C ω * logS : ℂ_[q]⟦X⟧) = C ω` using `by rw [hatmul_DT_C_mul, hl, mul_one]`. Unfold `DT at h1 ⊢`. Rewrite using `[hd G hG, ← mul_assoc, h1]`.
-/
lemma hatmul_DT_hat {q : ℕ} [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ)
    (hG : AnalyticAt ℂ G 0) :
    DT (hat ι (C ω * logS) G) = C ω * hat ι (C ω * logS) (deriv G) := by
  obtain ⟨-, -, -, -, hd, -, -⟩ := GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q ι _ (hatmul_const_log ω)
  obtain ⟨-, -, -, -, hl, -⟩ := GlobalTheory.T.cpBinomialPowerSubOneSeries_integrality_composition_log q
  have h1 : DT (C ω * logS : ℂ_[q]⟦X⟧) = C ω := by rw [hatmul_DT_C_mul, hl, mul_one]
  unfold DT at h1 ⊢
  rw [hd G hG, ← mul_assoc, h1]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro G _`. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `G hG`.

Establish `hk : AnalyticAt ℂ (iteratedDeriv k G) 0`. Rewrite using `[iteratedDeriv_eq_iterate]`. Conclude with `hG.iterated_deriv k`. Rewrite using `[Function.iterate_succ_apply', ih G hG, hatmul_DT_C_mul, hatmul_DT_hat ι ω _ hk, iteratedDeriv_succ, pow_succ, map_mul, mul_assoc]`.
-/
lemma hatmul_iter {q : ℕ} [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (k : ℕ) :
    ∀ (G : ℂ → ℂ), AnalyticAt ℂ G 0 →
      DT^[k] (hat ι (C ω * logS) G) = C (ω ^ k) * hat ι (C ω * logS) (iteratedDeriv k G) := by
  induction k with
  | zero => intro G _; simp
  | succ k ih =>
    intro G hG
    have hk : AnalyticAt ℂ (iteratedDeriv k G) 0 := by
      rw [iteratedDeriv_eq_iterate]
      exact hG.iterated_deriv k
    rw [Function.iterate_succ_apply', ih G hG, hatmul_DT_C_mul, hatmul_DT_hat ι ω _ hk,
      iteratedDeriv_succ, pow_succ, map_mul, mul_assoc]

/- English proof (translation)
Take `⟨-, -, -, -, -, -, hs⟩` from `GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q ι _ (hatmul_const_log ω)`. Take `⟨hm, -⟩` from `GlobalTheory.T.cpBinomialPowerSubOneSeries_integrality_composition_log q`. Take `⟨-, h0, -, hl⟩` from `hm a`. Establish `hsub : HasSubst (mulS a : ℂ_[q]⟦X⟧)` using `HasSubst.of_constantCoeff_zero' h0`. Rewrite using `[hs G _ h0, ← smul_eq_C_mul (a := ω), subst_smul hsub, hl, smul_eq_C_mul, map_mul, mul_assoc]`.
-/
lemma hatmul_subst {q : ℕ} [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ) (a : ℤ_[q]) :
    hat ι (C (ω * zc a) * logS) G = (hat ι (C ω * logS) G).subst (mulS a : ℂ_[q]⟦X⟧) := by
  obtain ⟨-, -, -, -, -, -, hs⟩ := GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q ι _ (hatmul_const_log ω)
  obtain ⟨hm, -⟩ := GlobalTheory.T.cpBinomialPowerSubOneSeries_integrality_composition_log q
  obtain ⟨-, h0, -, hl⟩ := hm a
  have hsub : HasSubst (mulS a : ℂ_[q]⟦X⟧) := HasSubst.of_constantCoeff_zero' h0
  rw [hs G _ h0, ← smul_eq_C_mul (a := ω), subst_smul hsub, hl, smul_eq_C_mul, map_mul, mul_assoc]

/- English proof (translation)
Introduce `q _ ι ω G hG`. Use `⟨hatmul_DT_hat ι ω G hG, fun k => ?_, fun α a ha => ?_, hatmul_subst ι ω G⟩` and prove the remaining obligations. Take `⟨-, -, -, hc, -⟩` from `GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q ι _ (hatmul_const_log ω)`. Rewrite using `[hatmul_iter ι ω k G hG, map_mul, hc, constantCoeff_C]`. Take `⟨-, -, -, -, -, hα, -⟩` from `GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q ι _ (hatmul_const_log ω)`.

Rewrite using `[hα G α hG, ← hatmul_subst, ha, map_mul, ← mul_assoc, mul_comm (C (zc a))]`.
-/
theorem hat_multiplicative_chart : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ), AnalyticAt ℂ G 0 → (DT (hat ι (C ω * logS) G) = C ω * hat ι (C ω * logS) (deriv G)) ∧ (∀ k : ℕ, constantCoeff (DT^[k] (hat ι (C ω * logS) G)) = ω ^ k * ι (iteratedDeriv k G 0)) ∧ (∀ (α : ℂ) (a : ℤ_[q]), ι α = zc a → hat ι (C ω * logS) (fun z => G (α * z)) = (hat ι (C ω * logS) G).subst (mulS a : ℂ_[q]⟦X⟧)) ∧ ∀ a : ℤ_[q], hat ι (C (ω * zc a) * logS) G = (hat ι (C ω * logS) G).subst (mulS a : ℂ_[q]⟦X⟧) := by
  intro q _ ι ω G hG
  refine ⟨hatmul_DT_hat ι ω G hG, fun k => ?_, fun α a ha => ?_, hatmul_subst ι ω G⟩
  · obtain ⟨-, -, -, hc, -⟩ := GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q ι _ (hatmul_const_log ω)
    rw [hatmul_iter ι ω k G hG, map_mul, hc, constantCoeff_C]
  · obtain ⟨-, -, -, -, -, hα, -⟩ := GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q ι _ (hatmul_const_log ω)
    rw [hα G α hG, ← hatmul_subst, ha, map_mul, ← mul_assoc, mul_comm (C (zc a))]

end GlobalTheory.MomOne
