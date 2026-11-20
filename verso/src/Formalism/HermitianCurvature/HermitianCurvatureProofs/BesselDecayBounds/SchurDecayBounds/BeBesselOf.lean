import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.GrowthIntegrals.BeBessel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.HaarCompactGrowth.IsHaarOnUWsetOfIsHaarOnOfUnivEqOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.NormIdFix
import Formalism.HermitianCurvature.BesselNonvanishingReduction

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.WBL.S5

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL PI.WBL.Cv PI.WBL.Cv.BeC

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Proceed by induction on `W with`. Consider the case `nil => rfl`. Consider the case `cons X W ih => show Formalism.MainNotions.S.dsig (k := k) (r := r) σ X (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ W v) = PI.UpqRep.dsig (k := k) (r := r) σ X (PI.UpqRep.dsigW (k := k) (r := r) σ W v)`. Rewrite using `[ih]`. Both sides reduce to the same expression.
-/
theorem dsigW_eq (σ : Mx k r → (H →L[ℂ] H)) (W : List (Mx k r)) (v : H) :
    Formalism.MainNotions.S.dsigW (k := k) (r := r) σ W v = PI.UpqRep.dsigW (k := k) (r := r) σ W v := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    show Formalism.MainNotions.S.dsig (k := k) (r := r) σ X (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ W v) =
      PI.UpqRep.dsig (k := k) (r := r) σ X (PI.UpqRep.dsigW (k := k) (r := r) σ W v)
    rw [ih]
    rfl

/- English proof (translation)
Take `⟨C, Ws, hW, hB⟩` from `h`. Use `⟨C, Ws, hW, fun v hv => ?_⟩` and prove the remaining obligations. Establish `h1` using `hB v hv`. Simplify using `only [dsigW_eq] at h1`. Conclude with `h1`.
-/
theorem cwCont_conv {Wp : Type} [NormedAddCommGroup Wp] {σ : Mx k r → (H →L[ℂ] H)} {B : H → Wp}
    (h : Formalism.MainNotions.S.IsCWCont (k := k) (r := r) σ B) : PI.BesselMapUniq.IsCWCont (k := k) (r := r) σ B := by
  obtain ⟨C, Ws, hW, hB⟩ := h
  refine ⟨C, Ws, hW, fun v hv => ?_⟩
  have h1 := hB v hv
  simp only [dsigW_eq] at h1
  exact h1

/- English proof (translation)
Introduce `k r z c g`. Simplify using `only [Formalism.QuantumDeterminants.psi, PI.BesselMapUniq.psiGen, ← Finset.mul_sum]`. Both sides reduce to the same expression.
-/
theorem psiConst : Formalism.FourierDecayAlt.ThreeDimData.PsiConst := by
  intro k r z c g
  simp only [Formalism.QuantumDeterminants.psi, PI.BesselMapUniq.psiGen, ← Finset.mul_sum]
  rfl

/- English proof (translation)
Introduce `hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hSide v hv ξ`. Take `⟨-, hDI, -, -⟩` from `hIn`. Take `⟨hlam, hds, hgap, hOK, hw0, hz, hT, hc, hπ, hμW, hμN, hμG, hq⟩` from `hSide`. Establish `: SigmaFinite μN` using `hμN.1`. Establish `hds' : Formalism.MainNotions.S.IsDSHpk k r ε lam σ` using `hds`.

Establish `hπ' : Formalism.MainNotions.S.IsHCTypeW k r z u π` using `hπ`. Establish `hw0' : Formalism.MainNotions.S.IsLowUnitH k r ε lam σ w0` using `hw0`. Establish `hM` using `Formalism.MainNotions.MeasFS.measF_side hz hT hπ hμW hμN`. Use `set a := Formalism.FourierDecayAlt.ThreeDimData.aOf r h with ha_def`. Take `⟨ha1, hAG, -⟩` from `PI.WBL.NIS.thresholds hOK.2.2.1`.

Establish `hAG0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r` using `by unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity`. Establish `hAG' : Formalism.FourierDecayAlt.ThreeDimData.AG k r < a - 1` using `by linarith`. Establish `hgr0` using `hGS k r z μW μN μG νq (a - 1) hz hT hμW hμN hμG hq hAG'`. Establish `hgr : Integrable (fun p : Mt k r × Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2 : Mx k r) ^ (1 - a)) (μW.prod μN)`. Use `hgr0.congr (ae_of_all _ fun p => ?_)` and prove the remaining obligations.

Simplify using `only [neg_sub]`. Establish `hK : PtDec σ a (fun v => Formalism.MainNotions.S.IsKFinHpk (k` using `k) (r := r) σ v) := by`. Introduce `v0 hv0`. Take `⟨C, Ws, hWs, hb⟩` from `hDI k r ε lam h H σ hlam hds hgap hOK v0 hv0`. Use `⟨C, Ws, hWs, fun w hw x hx => ?_⟩` and prove the remaining obligations.

Use `hb w hw x hx` as an intermediate fact. Simplify `this` using `only [dsigW_eq]`. Establish `hB : Formalism.MainNotions.S.IsBesselMapSm (k` using `k) (r := r) z (psi k r z c) σ π (fun x => (∫ p, Formalism.MainNotions.DoubleDerivativeSmoothness.FI z c π σ x v p ∂(μW.prod μN)) ξ) := by`. Break down `hv with hvD | hvK` into its components or cases. Establish `h0 : PtB σ a w0` using `hK w0 (Formalism.MainNotions.DoubleDerivativeSmoothness.kfinHpk_of_lowUnitH hw0')`.

Conclude with `Formalism.MainNotions.BeBesselW.beBessel_DD (u := u) z c π μW μN σ w0 a hds' hz hT hπ' hM hgr ha1 h0 v hvD ξ`. Conclude with `Formalism.MainNotions.BeBesselW.beBessel_K (u := u) z c π μW μN σ a hds' hz hT hπ' hM hgr hK v hvK ξ`. Take `⟨h1, h2, h3, h4⟩` from `hB`. Conclude with `⟨h1, h2, h3, cwCont_conv h4⟩`.
-/
theorem beBessel_of (hGS : Formalism.FourierDecayAlt.ThreeDimData.GrowthS) : Formalism.FourierDecayAlt.ThreeDimData.BeBessel := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hSide v hv ξ
  obtain ⟨-, hDI, -, -⟩ := hIn
  obtain ⟨hlam, hds, hgap, hOK, hw0, hz, hT, hc, hπ, hμW, hμN, hμG, hq⟩ := hSide
  have : SigmaFinite μN := hμN.1
  have hds' : Formalism.MainNotions.S.IsDSHpk k r ε lam σ := hds
  have hπ' : Formalism.MainNotions.S.IsHCTypeW k r z u π := hπ
  have hw0' : Formalism.MainNotions.S.IsLowUnitH k r ε lam σ w0 := hw0
  have hM := Formalism.MainNotions.MeasFS.measF_side hz hT hπ hμW hμN
  set a := Formalism.FourierDecayAlt.ThreeDimData.aOf r h with ha_def
  obtain ⟨ha1, hAG, -⟩ := PI.WBL.NIS.thresholds hOK.2.2.1
  have hAG0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have hAG' : Formalism.FourierDecayAlt.ThreeDimData.AG k r < a - 1 := by linarith
  have hgr0 := hGS k r z μW μN μG νq (a - 1) hz hT hμW hμN hμG hq hAG'
  have hgr : Integrable (fun p : Mt k r × Mt k r =>
      Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2 : Mx k r) ^ (1 - a)) (μW.prod μN) := by
    refine hgr0.congr (ae_of_all _ fun p => ?_)
    simp only [neg_sub]
  have hK : PtDec σ a (fun v => Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) σ v) := by
    intro v0 hv0
    obtain ⟨C, Ws, hWs, hb⟩ := hDI k r ε lam h H σ hlam hds hgap hOK v0 hv0
    refine ⟨C, Ws, hWs, fun w hw x hx => ?_⟩
    have := hb w hw x hx
    simpa only [dsigW_eq] using this
  have hB : Formalism.MainNotions.S.IsBesselMapSm (k := k) (r := r) z (psi k r z c) σ π
      (fun x => (∫ p, Formalism.MainNotions.DoubleDerivativeSmoothness.FI z c π σ x v p ∂(μW.prod μN)) ξ) := by
    rcases hv with hvD | hvK
    · have h0 : PtB σ a w0 := hK w0 (Formalism.MainNotions.DoubleDerivativeSmoothness.kfinHpk_of_lowUnitH hw0')
      exact Formalism.MainNotions.BeBesselW.beBessel_DD (u := u) z c π μW μN σ w0 a hds' hz hT hπ' hM hgr ha1 h0 v hvD ξ
    · exact Formalism.MainNotions.BeBesselW.beBessel_K (u := u) z c π μW μN σ a hds' hz hT hπ' hM hgr hK v hvK ξ
  obtain ⟨h1, h2, h3, h4⟩ := hB
  exact ⟨h1, h2, h3, cwCont_conv h4⟩

end PI.WBL.S5
