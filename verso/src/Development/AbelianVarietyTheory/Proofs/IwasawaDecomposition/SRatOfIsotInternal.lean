import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RhoStabChiInLL0
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsCAtState
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelCharacterEqProdSuperdiagonalSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHeckeAtZeroOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterPsiConditionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigSpanOfIsotInternal

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
  GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.RatSide

/- English proof (translation)
Introduce `hp hs hi hL`. Establish `A` using `StepW.and (formsC_at_state hL) (StepW.and (GlobalTheory.HeightCounting.ThetaSt.main hL) (StepW.and (GlobalTheory.HeightCounting.RatSide.HeckeAtState.heckeAtState hL hp.decay hs.hkTr hs.hkRead) (StepW.and (GlobalTheory.T.level_character_psi_condition hL hp.decay hs.hkInt hs.hkTr h …`. Use `StepW.trans A (StepW.of_all fun K B f T w _ _ H => ?_)` and prove the remaining obligations. Introduce `P x hx`. Take `⟨hF, hθ, hH, hI, hE⟩` from `H`.

Take `⟨θ, θne, hlp⟩` from `hθ P x hx`. Take `⟨hL', hst, h0, hrd⟩` from `hH P x hx`. Take `⟨eig, hea, hsp⟩` from `hE P x hx θ hL' θne hlp hst h0 hrd`. Establish `hint` using `hI P x hx θ hL' hlp hst hrd`. Establish `hrc` using `GlobalTheory.Mem.RatDatRExp.rhoStab_chiInLL0 (Dof x) _ _ _ _ _ x.m.z.core x.m.z.R x.m.z.F x.m.z.cG x.m.z.geo (kKsOf x) (hkOf x) x.m.z.pins x.m.inGeo`.

Conclude with `⟨⟨kKsOf x, hkOf x, { Sb := SbD (Dof x) rho := fun j a b => (hrc j a b).1 chi := fun j a b => (hrc j a b).2 ks := fun j a b => (hF P x hx j a b).1 fd := fun j a b => (hF P x hx j a b).2.1 mk_fg := fun j a b => (hF P x hx j a b).2.2 hL := hL' hs := hst hL_zero := h0 θ := θ θ_ne := …`.
-/
theorem sRat_of_isotInternal : PrN → SerN → (AllSt fun _ _ _ _ _ _ x => Formalism.BasicNotions.Rows.IsotInternal (Dof x).what₂) →
    ∀ hL : GlobalTheory.Published.LocalLanglandsGL, SRat hL := by
  intro hp hs hi hL
  have A := StepW.and (formsC_at_state hL) (StepW.and (GlobalTheory.HeightCounting.ThetaSt.main hL)
    (StepW.and (GlobalTheory.HeightCounting.RatSide.HeckeAtState.heckeAtState hL hp.decay hs.hkTr hs.hkRead)
    (StepW.and (GlobalTheory.T.level_character_psi_condition hL hp.decay hs.hkInt hs.hkTr hs.hkRead) (eig_span_of_isotInternal hp hi hL))))
  refine StepW.trans A (StepW.of_all fun K B f T w _ _ H => ?_)
  intro P x hx
  obtain ⟨hF, hθ, hH, hI, hE⟩ := H
  obtain ⟨θ, θne, hlp⟩ := hθ P x hx
  obtain ⟨hL', hst, h0, hrd⟩ := hH P x hx
  obtain ⟨eig, hea, hsp⟩ := hE P x hx θ hL' θne hlp hst h0 hrd
  have hint := hI P x hx θ hL' hlp hst hrd
  have hrc := GlobalTheory.Mem.RatDatRExp.rhoStab_chiInLL0 (Dof x) _ _ _ _ _ x.m.z.core x.m.z.R x.m.z.F x.m.z.cG x.m.z.geo (kKsOf x)
    (hkOf x) x.m.z.pins x.m.inGeo
  exact ⟨⟨kKsOf x, hkOf x,
    { Sb := SbD (Dof x)
      rho := fun j a b => (hrc j a b).1
      chi := fun j a b => (hrc j a b).2
      ks := fun j a b => (hF P x hx j a b).1
      fd := fun j a b => (hF P x hx j a b).2.1
      mk_fg := fun j a b => (hF P x hx j a b).2.2
      hL := hL'
      hs := hst
      hL_zero := h0
      θ := θ
      θ_ne := θne
      eig := eig
      span := hsp
      hL_int := hint },
    { hecke := hrd
      eig := hea
      Sb_le := overSet_SbD _
      lvl := hlp.1
      psi := hlp.2 }⟩⟩

/- English proof (translation)
Introduce `_` and use `sRat_of_isotInternal`.
-/
theorem sRat_of_duties : GlobalTheory.Published.DiscreteSeriesUpqUnique → PrN → SerN →
    (AllSt fun _ _ _ _ _ _ x => Formalism.BasicNotions.Rows.IsotInternal (Dof x).what₂) →
    ∀ hL : GlobalTheory.Published.LocalLanglandsGL, SRat hL :=
  fun _ => sRat_of_isotInternal

end GlobalTheory.HeightCounting.RatSide

end
