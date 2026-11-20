import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDiscriminantTwelfthRootOfIdeal
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.OneEntryMem
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyStandardLatticesEqBaseVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaLineStd

/- English proof (translation)
The claim follows from `GlobalTheory.Mem.Col2.Th.perAA_top D.host`.
-/
theorem aaOf_top (D : D7) : (Formalism.L2.PairingIndexBounds.F.aaOf D ⊤) = (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) :=
  GlobalTheory.Mem.Col2.Th.perAA_top D.host

/- English proof (translation)
Introduce `B X I l Z w i hi F hF`. Set `Bk : Formalism.L2.Ker.Base (I.rec7 l Z) ⊤ I.J.δ` to `GlobalTheory.Mem.Col2.Th.VacIn.toRec (D := I.rec7 l Z) I.J.V`. Establish `hS : Bk.StdOK` using `GlobalTheory.FourthRootStd.stdOK Bk (GlobalTheory.Glob.IntegralWittCoefficients.isCurveIdeal_top _) ((GlobalTheory.Mem.Col2.Th.isDiscriminantTwelfthRoot_host_iff (I.rec7 l Z) ⊤ I.J.δ).1 w.ok.amb_ok.delta)`. Establish `hZ : I.J.V.thZero (B.R.N i) (B.R.N (i + 1)) = Bk.thZero (B.R.N i) (B.R.N (i + 1))` using `rfl`. Establish `hLa : LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1))) = Formalism.MainNotions.TaylorLogMetric.La (I …`.

Rewrite using `[← Formalism.L2.KerInert.RepComb.lamK_eq, Formalism.L2.KerInert.RepComb.lamK, aaOf_top]`. Both sides reduce to the same expression. Establish `hH : (HV (ι` using `(I.rec7 l Z).what₂.Tau) (a := B.R.N i) (b := B.R.N (i + 1)) I.A.sc) = formV (Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf (I.rec7 l Z) ⊤ I.J.δ)) (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1)) := Formalism.L2.KerInert.RepComb.HV_eq_form …`. Rewrite `hF` using `[hLa, alV, hH]`. Establish `hF' : F ∈ Formalism.L2.Th1.H.Th (formV (Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf (I.rec7 l Z) ⊤ I.J.δ)) (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1))) (Formalism.MainNotions.TaylorLogMetric.al (I.rec7 l Z) Bk.tor) (Formalism.MainN …`.

Use `Formalism.L2.Ker.Th_congr _ _ _ _ (fun x hx => ?_) hF` and prove the remaining obligations. Take `⟨m, hm⟩` from `Bk.qInt0 hS _ _ x hx`. Conclude with `(Formalism.L2.Ker.al_eq _ Bk.tor x m hm).symm`. Take `⟨c, hc⟩` from `Formalism.L2.PairingIndexBounds.Eq.J.thZeroSpans hS _ _ F hF'`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Establish `hM : I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1))) = Bk.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Forma …` using `rfl`. Take `⟨x, hx, hI⟩` from `GlobalTheory.NatAtStd.Iop_self (I.rec7 l Z) Bk.tor (Formalism.MainNotions.TaylorLogMetric.La (I.rec7 l Z) Bk.tor (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))))`. Establish `hfix : (fun z => Formalism.MainNotions.TaylorLogMetric.al (I.rec7 l Z) Bk.tor x * Formalism.MainNotions.TaylorLogMetric.U (I.rec7 l Z) Bk.tor x (Bk.thZero (B.R.N i) (B.R.N (i + 1))) z) = Bk.thZero (B.R.N i) (B.R.N (i + 1))`. Use function extensionality and compare the values at `fun z => (Bk.thZeroMem hS _ _).2 x hx z`. Establish `hMz : Bk.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))) = Bk.thZero (B.R.N i) (B.R.N (i + 1))`.

Unfold `Formalism.L2.Ker.Base.thMoved Formalism.L2.Ker.Base.thHalf`. Rewrite using `[hI, hI, hfix, hfix]`. Rewrite using `[hM, hMz]`. Conclude with `hc`.
-/
theorem thetaSpace_std_eq_line : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z) (i : ℕ) (hi : i + 1 ≤ B.R.m), ∀ F ∈ Formalism.L2.Th1.H.Th (HV I.A.sc) (alV (I.rec7 l Z).host.d I.A.sc) (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1)))), ∃ c : ℂ, F = c • I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1))) := by
  intro B X I l Z w i hi F hF
  let Bk : Formalism.L2.Ker.Base (I.rec7 l Z) ⊤ I.J.δ := GlobalTheory.Mem.Col2.Th.VacIn.toRec (D := I.rec7 l Z) I.J.V
  have hS : Bk.StdOK := GlobalTheory.FourthRootStd.stdOK Bk (GlobalTheory.Glob.IntegralWittCoefficients.isCurveIdeal_top _)
    ((GlobalTheory.Mem.Col2.Th.isDiscriminantTwelfthRoot_host_iff (I.rec7 l Z) ⊤ I.J.δ).1 w.ok.amb_ok.delta)
  have hZ : I.J.V.thZero (B.R.N i) (B.R.N (i + 1)) = Bk.thZero (B.R.N i) (B.R.N (i + 1)) := rfl
  have hLa : LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1))) = Formalism.MainNotions.TaylorLogMetric.La (I.rec7 l Z) (Formalism.MainNotions.TaylorLogMetric.tor0 (I.rec7 l Z) ⊤ I.J.δ) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))) := by
    rw [← Formalism.L2.KerInert.RepComb.lamK_eq, Formalism.L2.KerInert.RepComb.lamK, aaOf_top]
    rfl
  have hH : (HV (ι := (I.rec7 l Z).what₂.Tau) (a := B.R.N i) (b := B.R.N (i + 1)) I.A.sc) = formV (Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf (I.rec7 l Z) ⊤ I.J.δ)) (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1)) :=
    Formalism.L2.KerInert.RepComb.HV_eq_formV _
  rw [hLa, alV, hH] at hF
  have hF' : F ∈ Formalism.L2.Th1.H.Th (formV (Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf (I.rec7 l Z) ⊤ I.J.δ)) (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1))) (Formalism.MainNotions.TaylorLogMetric.al (I.rec7 l Z) Bk.tor) (Formalism.MainNotions.TaylorLogMetric.La (I.rec7 l Z) Bk.tor (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1)))) := by
    refine Formalism.L2.Ker.Th_congr _ _ _ _ (fun x hx => ?_) hF
    obtain ⟨m, hm⟩ := Bk.qInt0 hS _ _ x hx
    exact (Formalism.L2.Ker.al_eq _ Bk.tor x m hm).symm
  obtain ⟨c, hc⟩ := Formalism.L2.PairingIndexBounds.Eq.J.thZeroSpans hS _ _ F hF'
  refine ⟨c, ?_⟩
  have hM : I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1))) = Bk.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))) := rfl
  obtain ⟨x, hx, hI⟩ := GlobalTheory.NatAtStd.Iop_self (I.rec7 l Z) Bk.tor (Formalism.MainNotions.TaylorLogMetric.La (I.rec7 l Z) Bk.tor (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))))
  have hfix : (fun z => Formalism.MainNotions.TaylorLogMetric.al (I.rec7 l Z) Bk.tor x * Formalism.MainNotions.TaylorLogMetric.U (I.rec7 l Z) Bk.tor x (Bk.thZero (B.R.N i) (B.R.N (i + 1))) z) = Bk.thZero (B.R.N i) (B.R.N (i + 1)) :=
    funext fun z => (Bk.thZeroMem hS _ _).2 x hx z
  have hMz : Bk.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))) = Bk.thZero (B.R.N i) (B.R.N (i + 1)) := by
    unfold Formalism.L2.Ker.Base.thMoved Formalism.L2.Ker.Base.thHalf
    rw [hI, hI, hfix, hfix]
  rw [hM, hMz]
  exact hc

end GlobalTheory.ThetaLineStd
