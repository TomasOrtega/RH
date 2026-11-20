import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.HeckeIntertwinersInert
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPrimeIdemOfInert
open Formalism.BasicNotions IsDedekindDomain NumberField

noncomputable section

namespace GlobalTheory.LocEltLocal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Take `⟨e, f, g, hpi, hg, hx, hs⟩` from `h`. Take `⟨Φ, hΦ⟩` from `GlobalTheory.IdemSupport.exists_comp D`. Take `⟨-, ε, hε, rfl⟩` from `GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hpi`. Establish `h1` using `(GlobalTheory.HeckeRowsCompare.suppF_iff V hε hg).1 hs`. Rewrite `h1` using `[GlobalTheory.HeckeRowsCompare.mem_locGrp]`.

Establish `h2 : GlobalTheory.HeckeRowsCompare.fin V g = x` using `Subtype.ext hx.symm`. Rewrite `h1` using `[h2]`. Conclude with `(GlobalTheory.HeckeRowsCompare.locAt_iff V _ x).2 h1`.
-/
theorem locAt_of_isLocElt {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (P : Formalism.L2.DIV.Pl D.host.E)
    (x : Formalism.IndefR.Bridge.Gf V) (_hP : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.IsInertPl P) (h : Formalism.IndefR.Links.IsLocElt V P x) :
    GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V (GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.plF P) x := by
  obtain ⟨e, f, g, hpi, hg, hx, hs⟩ := h
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, ε, hε, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hpi
  have h1 := (GlobalTheory.HeckeRowsCompare.suppF_iff V hε hg).1 hs
  rw [GlobalTheory.HeckeRowsCompare.mem_locGrp] at h1
  have h2 : GlobalTheory.HeckeRowsCompare.fin V g = x := Subtype.ext hx.symm
  rw [h2] at h1
  exact (GlobalTheory.HeckeRowsCompare.locAt_iff V _ x).2 h1

/- English proof (translation)
Introduce `V P x hP h` and use `locAt_of_isLocElt V P x hP h`.
-/
theorem main : ∀ {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (x : Formalism.IndefR.Bridge.Gf V),
    GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.IsInertPl P → Formalism.IndefR.Links.IsLocElt V P x →
      GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V (GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.plF P) x :=
  fun V P x hP h => locAt_of_isLocElt V P x hP h

end GlobalTheory.LocEltLocal
