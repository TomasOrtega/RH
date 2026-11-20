import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCharQuotientLFunctionEntireNeZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto.QuotL

variable {D : D7}

/- English proof (translation)
Introduce `a` and use `by obtain ⟨⟨η, hη⟩, h⟩ := (hc.hecke k hk).2 exact (h η hη a).trans (pow_zero _)`.
-/
theorem trivialOnF {c : Com D} (hc : c.Is) {k : ℕ} (hk : k < c.m) :
    GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter.TrivialOnF (c.χ k) := fun a => by
  obtain ⟨⟨η, hη⟩, h⟩ := (hc.hecke k hk).2
  exact (h η hη a).trans (pow_zero _)

/- English proof (translation)
Introduce `D c hc i j hij hj`. Establish `hi : i < c.m` using `hij.trans hj`. Take `⟨τ⟩ : Nonempty D.what₂.Tau` from `⟨D.eTau.symm 1⟩`. Establish `hexp : ∃ (τ : D.what₂.Tau) (e e' : ℚ), HasInfExp D (c.χ i) τ (-e) ∧ HasInfExp D (c.χ j) τ (-e') ∧ e ≠ e'` using `⟨τ, -(c.a i τ), -(c.a j τ), by rw [neg_neg]; exact hc.exp i hi τ, by rw [neg_neg]; exact hc.exp j hj τ, fun h => hc.ne i j hij hj τ (neg_injective h)⟩`. Establish `R` using `GlobalTheory.HeckeRatio.heckeRatioPos D (c.χ i) (c.χ j) (hc.hecke i hi).1 (hc.hecke j hj).1 (trivialOnF hc hi) (trivialOnF hc hj) hexp`.

Take `⟨Λ, hL, -⟩` from `(R 0).2 c.S`. Take `⟨hd, hp⟩` from `hL`. Use `⟨Λ, hd, fun z hz => ?_, fun n h1 h0 => ?_⟩` and prove the remaining obligations. Establish `hunr : ∀ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))), GlobalTheory.LFun.UnrAt (c.χ i * (c.χ j)⁻¹) w` using `fun w hw => (hc.unr i hi w hw).mul (hc.unr j hj w hw).inv`. Establish `hoff : ∀ P, OffS D c.S P ↔ P ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))` using `fun P => (GlobalTheory.HeckeRatio.offS_iff c.S P).trans Iff.rfl`.

Set `e` to `Equiv.subtypeEquivRight hoff`. Establish `k` using `hp z hz`. Rewrite `k` using `[GlobalTheory.HeckeRatio.lfac_eq]`. Establish `k2 : HasProd (fun w : {w // w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))} => GlobalTheory.LFun.locL (fun w => {GlobalTheory.LFun.val (F` using `D.host.F) (c.χ i * (c.χ j)⁻¹) w}) w.1 z) (Λ z) := by`. Use `(e.hasProd_iff).1 (k.congr_fun fun P => ?_)` and prove the remaining obligations.

Establish `hu` using `hunr P.1 ((hoff P.1).1 P.2)`. Rewrite using `[GlobalTheory.LFun.lfac_eq_locL (Formalism.IndefR.ThmB.InputsHecke.isCMExt D)]`. Simplify using `only [Function.comp_apply, e, Equiv.subtypeEquivRight_apply_coe, GlobalTheory.LFun.locL, GlobalTheory.LFun.charFam_of_unrAt hu]`. Conclude with `k2.tprod_eq.symm`. Take `⟨Λn, hLn, hpos⟩` from `(R n).2 c.S`.

Establish `hEq : Λ = Λn` using `GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter.IsPartialL.unique ⟨hd, hp⟩ hLn`. Use `(hpos n h1 le_rfl).2` as an intermediate fact. Rewrite `this` using `[← hEq, h0, Complex.zero_re]`. Conclude with `lt_irrefl _ this`.
-/
theorem quotL_entire_ne_zero : ∀ (D : D7) (c : Com D), c.Is → ∀ i j : ℕ, i < j → j < c.m →
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))))
        (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.χ i * (c.χ j)⁻¹) w}) z) ∧
      ∀ n : ℕ, 1 ≤ n → Λ n ≠ 0 := by
  intro D c hc i j hij hj
  have hi : i < c.m := hij.trans hj
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hexp : ∃ (τ : D.what₂.Tau) (e e' : ℚ), HasInfExp D (c.χ i) τ (-e) ∧
      HasInfExp D (c.χ j) τ (-e') ∧ e ≠ e' :=
    ⟨τ, -(c.a i τ), -(c.a j τ), by rw [neg_neg]; exact hc.exp i hi τ, by rw [neg_neg]; exact hc.exp j hj τ,
      fun h => hc.ne i j hij hj τ (neg_injective h)⟩
  have R := GlobalTheory.HeckeRatio.heckeRatioPos D (c.χ i) (c.χ j) (hc.hecke i hi).1 (hc.hecke j hj).1
    (trivialOnF hc hi) (trivialOnF hc hj) hexp
  obtain ⟨Λ, hL, -⟩ := (R 0).2 c.S
  obtain ⟨hd, hp⟩ := hL
  refine ⟨Λ, hd, fun z hz => ?_, fun n h1 h0 => ?_⟩
  · have hunr : ∀ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))),
        GlobalTheory.LFun.UnrAt (c.χ i * (c.χ j)⁻¹) w := fun w hw =>
      (hc.unr i hi w hw).mul (hc.unr j hj w hw).inv
    have hoff : ∀ P, OffS D c.S P ↔ P ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) :=
      fun P => (GlobalTheory.HeckeRatio.offS_iff c.S P).trans Iff.rfl
    let e := Equiv.subtypeEquivRight hoff
    have k := hp z hz
    rw [GlobalTheory.HeckeRatio.lfac_eq] at k
    have k2 : HasProd (fun w : {w // w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))} =>
        GlobalTheory.LFun.locL (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.χ i * (c.χ j)⁻¹) w}) w.1 z) (Λ z) := by
      refine (e.hasProd_iff).1 (k.congr_fun fun P => ?_)
      have hu := hunr P.1 ((hoff P.1).1 P.2)
      rw [GlobalTheory.LFun.lfac_eq_locL (Formalism.IndefR.ThmB.InputsHecke.isCMExt D)]
      simp only [Function.comp_apply, e, Equiv.subtypeEquivRight_apply_coe, GlobalTheory.LFun.locL,
        GlobalTheory.LFun.charFam_of_unrAt hu]
    exact k2.tprod_eq.symm
  · obtain ⟨Λn, hLn, hpos⟩ := (R n).2 c.S
    have hEq : Λ = Λn := GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter.IsPartialL.unique ⟨hd, hp⟩ hLn
    have := (hpos n h1 le_rfl).2
    rw [← hEq, h0, Complex.zero_re] at this
    exact lt_irrefl _ this

end GlobalTheory.EvenOnto.QuotL

end
