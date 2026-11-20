import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.FlipOneThree
import Formalism.SharpRestriction.CuspSpanNormBounds.KFinOfLowUnitH

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

/- English proof (translation)
Introduce `hSchH hNI hGG _hDD _hBC hRS hIn k r L h μG w0 l l' hOPKF γ μR νR ν hCD b hb hab' hpm v v' hv hv' ξ ξ'`. Take `⟨hOP, hK1, hK2⟩` from `hOPKF`. Take `⟨hgap, hOK, -, hw0, hμG, -, -⟩` from `hOP`. Take `⟨hγ, hGf, hmono, hrel, hμR, hOQ, hQ⟩` from `hCD`. Establish `hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ` using `L.hσ`.

Take `⟨d, hd, hSch⟩` from `hSchH k r L.ε L.lam L.Hs L.σ μG L.hlam hσ hμG`. Establish `hw0K : PI.UpqRep.IsKFinHpk (k` using `k) (r := r) L.σ w0 := Formalism.MainNotions.KFiniteLowUnitary.kFin_of_lowUnitH' hw0`. Establish `hw0s : w0 ∈ PI.UpqRep.smoothVecs (k` using `k) (r := r) L.σ := hIn.2.2.1 k r L.ε L.lam L.Hs L.σ L.hlam hσ w0 hw0K`. Take `⟨P, hP, hw⟩` from `hw0`. Establish `hnorm : ‖w0‖ = 1` using `hw.1`.

Establish `hw0ne : w0 ≠ 0`. Introduce `h0`. Rewrite `hnorm` using `[h0, norm_zero]`. Conclude with `zero_ne_one hnorm`. Establish `hw1 : ⟪w0, w0⟫_ℂ = 1`.

Rewrite using `[inner_self_eq_norm_sq_to_K, hnorm]`. Simplify using the standard rewrite rules. Establish `hfd : PI.BesselPeriodGGP.fdegH μG L.σ w0 = d` using `Formalism.FourierDecayAlt.P.S3dx6.fdeg_of_schur hw0ne hd (hSch w0 w0 w0 w0).2`. Take `⟨C1, Ws1, -, hC1⟩` from `hIn.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hOK v hv`. Take `⟨C2, Ws2, -, hC2⟩` from `hIn.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hOK v' hv'`.

Establish `e1 : (1 : ℝ) - Formalism.FourierDecayAlt.ThreeDimData.aOf r h = -(Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1)` using `by ring`. Establish `hC1' : ∀ g ∈ UH (Hpk k r), ‖⟪v, L.σ g w0⟫_ℂ‖ ≤ (C1 * (Ws1.map fun W => ‖PI.UpqRep.dsigW (k` using `k) (r := r) L.σ W w0‖).sum) * Formalism.FourierDecayAlt.B.gN g ^ (-(Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1)) := fun g hg => by`. Rewrite using `[← e1]`. Conclude with `hC1 w0 hw0s g hg`. Establish `hC2' : ∀ g ∈ UH (Hpk k r), ‖⟪v', L.σ g w0⟫_ℂ‖ ≤ (C2 * (Ws2.map fun W => ‖PI.UpqRep.dsigW (k` using `k) (r := r) L.σ W w0‖).sum) * Formalism.FourierDecayAlt.B.gN g ^ (-(Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1)) := fun g hg => by`.

Rewrite using `[← e1]`. Conclude with `hC2 w0 hw0s g hg`. Establish `hAG0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r` using `by unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity`. Establish `hab : b ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1` using `by linarith`. Establish `hIG : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - (Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1))) μG`.

Establish `h1` using `hGG k r μG (Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b) hμG (by linarith)`. Simplify `h1` using `only [neg_sub]`. Establish `hinv : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k` using `k) (r := r)) μR μR := ⟨Formalism.FourierDecayAlt.P.B7.measurable_invM, hRS k r L γ μR hOK.1 hγ hGf hrel hmono hμR⟩`. Rewrite using `[hfd]`. Conclude with `amp_core' L hμG hd hSch hNI hw1 l l' hγ hrel hμR hOQ hQ hinv hb hab hIG hpm (fun t ht => hK1 _ (Formalism.FourierDecayAlt.P.S3dx6.mem_DD L.σ w0 ht) v hv) (fun t ht => hK2 _ (Formalism.FourierDecayAlt.P.S3dx6.mem_DD L.σ w0 ht) v' hv') hC1' hC2' ξ ξ'`.
-/
theorem amplitude_K_finite_decay : Formalism.MainNotions.S.Pv.AmpDD.AmpKFOfSteps := by
  intro hSchH hNI hGG _hDD _hBC hRS hIn k r L h μG w0 l l' hOPKF γ μR νR ν hCD b hb hab' hpm v v' hv hv' ξ ξ'
  obtain ⟨hOP, hK1, hK2⟩ := hOPKF
  obtain ⟨hgap, hOK, -, hw0, hμG, -, -⟩ := hOP
  obtain ⟨hγ, hGf, hmono, hrel, hμR, hOQ, hQ⟩ := hCD
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  obtain ⟨d, hd, hSch⟩ := hSchH k r L.ε L.lam L.Hs L.σ μG L.hlam hσ hμG
  have hw0K : PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ w0 := Formalism.MainNotions.KFiniteLowUnitary.kFin_of_lowUnitH' hw0
  have hw0s : w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) L.σ :=
    hIn.2.2.1 k r L.ε L.lam L.Hs L.σ L.hlam hσ w0 hw0K
  obtain ⟨P, hP, hw⟩ := hw0
  have hnorm : ‖w0‖ = 1 := hw.1
  have hw0ne : w0 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hw1 : ⟪w0, w0⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    simp
  have hfd : PI.BesselPeriodGGP.fdegH μG L.σ w0 = d :=
    Formalism.FourierDecayAlt.P.S3dx6.fdeg_of_schur hw0ne hd (hSch w0 w0 w0 w0).2
  obtain ⟨C1, Ws1, -, hC1⟩ := hIn.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hOK v hv
  obtain ⟨C2, Ws2, -, hC2⟩ := hIn.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hOK v' hv'
  have e1 : (1 : ℝ) - Formalism.FourierDecayAlt.ThreeDimData.aOf r h = -(Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1) := by ring
  have hC1' : ∀ g ∈ UH (Hpk k r), ‖⟪v, L.σ g w0⟫_ℂ‖ ≤
      (C1 * (Ws1.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) L.σ W w0‖).sum) *
        Formalism.FourierDecayAlt.B.gN g ^ (-(Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1)) := fun g hg => by
    rw [← e1]; exact hC1 w0 hw0s g hg
  have hC2' : ∀ g ∈ UH (Hpk k r), ‖⟪v', L.σ g w0⟫_ℂ‖ ≤
      (C2 * (Ws2.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) L.σ W w0‖).sum) *
        Formalism.FourierDecayAlt.B.gN g ^ (-(Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1)) := fun g hg => by
    rw [← e1]; exact hC2 w0 hw0s g hg
  have hAG0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have hab : b ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 := by linarith
  have hIG : Integrable (fun x : Mt k r =>
      Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - (Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1))) μG := by
    have h1 := hGG k r μG (Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b) hμG (by linarith)
    simpa only [neg_sub] using h1
  have hinv : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μR μR :=
    ⟨Formalism.FourierDecayAlt.P.B7.measurable_invM, hRS k r L γ μR hOK.1 hγ hGf hrel hmono hμR⟩
  rw [hfd]
  exact amp_core' L hμG hd hSch hNI hw1 l l' hγ hrel hμR hOQ hQ hinv hb hab hIG hpm
    (fun t ht => hK1 _ (Formalism.FourierDecayAlt.P.S3dx6.mem_DD L.σ w0 ht) v hv)
    (fun t ht => hK2 _ (Formalism.FourierDecayAlt.P.S3dx6.mem_DD L.σ w0 ht) v' hv') hC1' hC2' ξ ξ'

end Formalism.MainNotions.S.Pv.AmpDDPf
