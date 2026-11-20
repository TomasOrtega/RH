import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ConvRight
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableStandardPairThetaWeilRange

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

/- English proof (translation)
The claim follows from `Summable.of_enorm hh.ne`.
-/
theorem summable_of_absTheta {D : D7} {V : HSp D} {n : ℕ} (φ : Mx D V.rank n → ℂ) (h : GA D V)
    (hh : GlobalTheory.SiegelFormula.absTheta V φ h < ⊤) :
    Summable fun ξ : Matrix (Fin V.rank) (Fin n) D.host.E => φ (GlobalTheory.SiegelFormula.invPt V h ξ) :=
  Summable.of_enorm hh.ne

/- English proof (translation)
Introduce `D n V ψ χ θ μ ω H l s ν Φ Φ' hS hS' hR g`. Take `⟨h1, h2, hr⟩` from `hR`. Establish `hn : 1 ≤ n` using `by omega`. Establish `hI` using `GlobalTheory.StdThetaInt.integrable_theta hP D n V hn hr θ hS.hθ ω ν hS.hν Φ g`. Establish `hI'` using `GlobalTheory.StdThetaInt.integrable_theta hP D n V hn hr θ hS.hθ ω ν hS.hν Φ' g`.

Establish `hae : ∀ φ : schwartzA θ V.rank n, ∀ᵐ q ∂autMeasure V ν, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ.1) q < ⊤`. Introduce `φ`. Establish `hfin : GlobalTheory.SiegelFormula.absThetaInt V ν φ.1 < ⊤` using `hP D n V hn (Or.inr hr) θ hS.hθ ν hS.hν φ`. Establish `hcont : Continuous φ.1` using `(GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hS.hθ _ _ φ.1 (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hS.hθ _ _ φ.1 φ.2)).1`. Conclude with `ae_lt_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hcont) hfin.ne`.

Establish `heq : (fun q => GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω (Φ + Φ') g) q) =ᵐ[autMeasure V ν] fun q => GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω Φ g) q + GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω Φ' g) q` using `by filter_upwards [hae (ω g Φ), hae (ω g Φ')] with q hq hq'`. Simplify using `only [GlobalTheory.AutomorphicL2Unitary.descend] at hq hq' ⊢`. Establish `s1` using `summable_of_absTheta (ω g Φ).1 _ hq`. Establish `s2` using `summable_of_absTheta (ω g Φ').1 _ hq'`. Use `show (∑' ξ, (ω g (Φ + Φ')).1 (GlobalTheory.SiegelFormula.invPt V _ ξ)) = (∑' ξ, (ω g Φ).1 (GlobalTheory.SiegelFormula.invPt V _ ξ)) + ∑' ξ, (ω g Φ').1 (GlobalTheory.SiegelFormula.invPt V _ ξ)`.

Rewrite using `[← s1.tsum_add s2]`. Use `congr 1`. Use function extensionality and compare the values at `ξ`. Simplify using `[map_add]`. Unfold `thetaInt`.

Rewrite using `[MeasureTheory.average_eq, MeasureTheory.average_eq, MeasureTheory.average_eq, integral_congr_ae heq, integral_add hI hI', smul_add]`.
-/
theorem thLin_of (hP : GlobalTheory.Published.WeilThetaConvergence) : ThLin := by
  intro D n V ψ χ θ μ ω H l s ν Φ Φ' hS hS' hR g
  obtain ⟨h1, h2, hr⟩ := hR
  have hn : 1 ≤ n := by omega
  have hI := GlobalTheory.StdThetaInt.integrable_theta hP D n V hn hr θ hS.hθ ω ν hS.hν Φ g
  have hI' := GlobalTheory.StdThetaInt.integrable_theta hP D n V hn hr θ hS.hθ ω ν hS.hν Φ' g
  have hae : ∀ φ : schwartzA θ V.rank n,
      ∀ᵐ q ∂autMeasure V ν, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ.1) q < ⊤ := by
    intro φ
    have hfin : GlobalTheory.SiegelFormula.absThetaInt V ν φ.1 < ⊤ := hP D n V hn (Or.inr hr) θ hS.hθ ν hS.hν φ
    have hcont : Continuous φ.1 := (GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hS.hθ _ _ φ.1
      (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hS.hθ _ _ φ.1 φ.2)).1
    exact ae_lt_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hcont) hfin.ne
  have heq : (fun q => GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω (Φ + Φ') g) q) =ᵐ[autMeasure V ν]
      fun q => GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω Φ g) q + GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω Φ' g) q := by
    filter_upwards [hae (ω g Φ), hae (ω g Φ')] with q hq hq'
    simp only [GlobalTheory.AutomorphicL2Unitary.descend] at hq hq' ⊢
    have s1 := summable_of_absTheta (ω g Φ).1 _ hq
    have s2 := summable_of_absTheta (ω g Φ').1 _ hq'
    show (∑' ξ, (ω g (Φ + Φ')).1 (GlobalTheory.SiegelFormula.invPt V _ ξ)) =
      (∑' ξ, (ω g Φ).1 (GlobalTheory.SiegelFormula.invPt V _ ξ)) + ∑' ξ, (ω g Φ').1 (GlobalTheory.SiegelFormula.invPt V _ ξ)
    rw [← s1.tsum_add s2]
    congr 1
    funext ξ
    simp [map_add]
  unfold thetaInt
  rw [MeasureTheory.average_eq, MeasureTheory.average_eq, MeasureTheory.average_eq, integral_congr_ae heq,
    integral_add hI hI', smul_add]

end PositivityTheory.Rg.Sw.Glob
