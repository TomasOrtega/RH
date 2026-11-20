import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.EmDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureConjugation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSmulH
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

namespace GlobalTheory.CompanionTheory.HermSc

section Main

open GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.HermVol GlobalTheory.CompanionTheory.CgMod PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `hid htop D t S e he lam hlam g hg`. Take `⟨hee, hce⟩` from `(hid D S).2 e he`. Take `⟨i1, i2, i3, i4, -, -⟩` from `lattice_Mx D t t`. Use `haveI : IsTopologicalAddGroup (Mx D t t) := i1`. Use `haveI : LocallyCompactSpace (Mx D t t) := i2`.

Use `haveI : SecondCountableTopology (Mx D t t) := i3`. Use `haveI : T2Space (Mx D t t) := i4`. Use `haveI : BorelSpace (Mx D t t) := ⟨rfl⟩`. Use `haveI : SecondCountableTopology (hermA D t) := Topology.IsInducing.subtypeVal.secondCountableTopology`. Use `haveI : T2Space (hermA D t) := Topology.IsEmbedding.subtypeVal.t2Space`.

Use `haveI : LocallyCompactSpace (hermA D t) := (isClosed_hermA (D := D) (r := t)).isClosedEmbedding_subtypeVal.locallyCompactSpace`. Take `⟨-, -, -, -, -, -, hb, hs2, hlc⟩` from `htop D 0 0 t e`. Use `haveI : BorelSpace (hermS D t e) := hb`. Use `haveI : SecondCountableTopology (hermS D t e) := hs2`. Use `haveI : LocallyCompactSpace (hermS D t e) := hlc`.

Use `haveI : T2Space (hermS D t e) := Topology.IsEmbedding.subtypeVal.t2Space`. Use `haveI : lam.IsAddHaarMeasure := hlam`. Use `set U := restr (hermA D t) (GlobalTheory.ModuLR.lrCE g (ad g)⁻¹) (lr_herm g) (lr_herm_symm g) with hUdef`. Establish `hU : ∀ s ∈ hermS D t e, U s ∈ hermS D t e` using `fun s hs => smul_sandwich e _ _ s.1 hs`. Establish `hU' : ∀ s ∈ hermS D t e, U.symm s ∈ hermS D t e` using `fun s hs => smul_sandwich e _ _ s.1 hs`.

Establish `hPm : ∀ x, smulH (n` using `t) e hce x ∈ hermS D t e := fun x => by`. Express the relevant statement in the definitionally equal form `e • e • x.1 = e • x.1`. Rewrite using `[smul_smul, hee]`. Establish `hPs : ∀ s ∈ hermS D t e, smulH (n` using `t) e hce s = s := fun s hs => Subtype.ext hs`. Establish `hfix : ∀ x, smulH (n` using `t) e hce x = 0 → U x = x := fun x hx => Subtype.ext (sandwich_fix g hg x (congrArg Subtype.val hx))`.

Establish `hchar` using `char_restr (hermS D t e) (smulH e hce) (continuous_smulH e hce) hPm hPs U hU hU' hfix`. Rewrite `hchar` using `[char_herm g]`. Use `set c := restr (hermS D t e) U hU hU' with hc`. Use `⟨c, fun x => rfl, ?_⟩` and prove the remaining obligations. Establish `key` using `addEquivAddHaarChar_smul_map lam c`.

Establish `hne : addEquivAddHaarChar c ≠ 0` using `(addEquivAddHaarChar_pos c).ne'`. Establish `hmap : lam.map c = (addEquivAddHaarChar c)⁻¹ • lam`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[inv_mul_cancel₀ hne, one_smul]`. Use `_ = (addEquivAddHaarChar c)⁻¹ • lam := by rw [mul_smul, key]`.

Rewrite using `[hmap, hchar, inv_pow]`.
-/
theorem hermScale_main : PositivityTheory.Rg.Rsw.L.IdemEx → PositivityTheory.Rg.Rsw.Em.TopX → PositivityTheory.Rg.Rsw.Em.HermScale := by
  intro hid htop D t S e he lam hlam g hg
  obtain ⟨hee, hce⟩ := (hid D S).2 e he
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D t t
  haveI : IsTopologicalAddGroup (Mx D t t) := i1
  haveI : LocallyCompactSpace (Mx D t t) := i2
  haveI : SecondCountableTopology (Mx D t t) := i3
  haveI : T2Space (Mx D t t) := i4
  haveI : BorelSpace (Mx D t t) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D t) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D t) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : LocallyCompactSpace (hermA D t) :=
    (isClosed_hermA (D := D) (r := t)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨-, -, -, -, -, -, hb, hs2, hlc⟩ := htop D 0 0 t e
  haveI : BorelSpace (hermS D t e) := hb
  haveI : SecondCountableTopology (hermS D t e) := hs2
  haveI : LocallyCompactSpace (hermS D t e) := hlc
  haveI : T2Space (hermS D t e) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : lam.IsAddHaarMeasure := hlam
  set U := restr (hermA D t) (GlobalTheory.ModuLR.lrCE g (ad g)⁻¹) (lr_herm g) (lr_herm_symm g) with hUdef
  have hU : ∀ s ∈ hermS D t e, U s ∈ hermS D t e := fun s hs =>
    smul_sandwich e _ _ s.1 hs
  have hU' : ∀ s ∈ hermS D t e, U.symm s ∈ hermS D t e := fun s hs =>
    smul_sandwich e _ _ s.1 hs
  have hPm : ∀ x, smulH (n := t) e hce x ∈ hermS D t e := fun x => by
    change e • e • x.1 = e • x.1
    rw [smul_smul, hee]
  have hPs : ∀ s ∈ hermS D t e, smulH (n := t) e hce s = s := fun s hs => Subtype.ext hs
  have hfix : ∀ x, smulH (n := t) e hce x = 0 → U x = x := fun x hx =>
    Subtype.ext (sandwich_fix g hg x (congrArg Subtype.val hx))
  have hchar := char_restr (hermS D t e) (smulH e hce) (continuous_smulH e hce) hPm hPs U hU hU' hfix
  rw [char_herm g] at hchar
  set c := restr (hermS D t e) U hU hU' with hc
  refine ⟨c, fun x => rfl, ?_⟩
  have key := addEquivAddHaarChar_smul_map lam c
  have hne : addEquivAddHaarChar c ≠ 0 := (addEquivAddHaarChar_pos c).ne'
  have hmap : lam.map c = (addEquivAddHaarChar c)⁻¹ • lam := by
    calc lam.map c = ((addEquivAddHaarChar c)⁻¹ * addEquivAddHaarChar c) • lam.map c := by
          rw [inv_mul_cancel₀ hne, one_smul]
      _ = (addEquivAddHaarChar c)⁻¹ • lam := by rw [mul_smul, key]
  rw [hmap, hchar, inv_pow]

end Main

end GlobalTheory.CompanionTheory.HermSc
