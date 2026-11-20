import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.NormalFrameClauses
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ChainMatrices
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompChainSpaceDefiniteAddNormalFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAuxiliaryHyperbolicVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAdaptedVectorSystemECoZCo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VertexAtOfLevTransport

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mi Formalism.IndefR.Seed.Frm IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FramesExistLev

open GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices

/- English proof (translation)
Introduce `D C Pg hPg`. Set `L : LevCh D Empty` to `{ C := C, xiH := fun t => t.elim, mu0 := fun _ => 1, eta := 1, xi := fun t => t.elim, Pg := Pg, Q := fun t => t.elim, chi := fun _ _ => 1, xiR := fun t => t.elim, ΛY := fun _ => ⊥, ΛX := ⊥, ΛV := fun _ => ⊥, ΛW := fun _ => ⊥, βY := fun _ => 1, βX := 1, βV := fun _ => 1, βW := fun …`. Establish `hP : ∀ PP, PP ∈ L.Pg ↔ ∃ l, L.C.P.Div l PP` using `hPg`. Establish `hQ : ∀ t, Formalism.IndefR.Lev.IsTwistPlaces D.host.g (L.Q t)` using `fun t => t.elim`. Use `choose γ hγ using fun j => GlobalTheory.StdFrames.exists_base (D.sp.X j)`.

Establish `hγ' : ∀ j, j < D.R.m → IsFrame (γ j) (Formalism.L2.Herm.crdLat (D.sp.X j) (D.sp.X j).L0)` using `fun j _ => by`. Rewrite using `[hγ j]`. Conclude with `GlobalTheory.StdFrames.isFrame_lat _`. Establish `hex : ∀ j, ∃ (E Ev : ℕ → (D.sp.Y j).V) (z : (D.sp.Y j).V), j < D.R.m → IsAuxiliaryHeckeCharacter D j E Ev z` using `fun j => by`. Distinguish the cases in `hj : j < D.R.m`.

Take `⟨E, Ev, z, h⟩` from `GlobalTheory.StandardGramVectors.exists_auxiliaryHyperbolicVectors D j hj`. Conclude with `⟨E, Ev, z, fun _ => h⟩`. Conclude with `⟨0, 0, 0, fun h => absurd h hj⟩`. Use `choose E₁ Ev₁ z₁ hA₁ using hex`. Set `E : ∀ j, ℕ → (D.sp.Y j).V` to `fun j => match j with`.

Consider the case `0 => fun i => if h : i < D.R.rS then D.sp.hypE ⟨i, h⟩ else 0`. Consider the case `j + 1 => E₁ (j + 1)`. Set `Ev : ∀ j, ℕ → (D.sp.Y j).V` to `fun j => match j with`. Consider the case `0 => fun i => if h : i < D.R.rS then D.sp.hypF ⟨i, h⟩ else 0`. Consider the case `j + 1 => Ev₁ (j + 1)`.

Set `z : ∀ j, (D.sp.Y j).V` to `fun j => match j with`. Consider the case `0 => D.sp.zm`. Consider the case `j + 1 => z₁ (j + 1)`. Establish `hAux : ∀ j, j < D.R.m → IsAuxiliaryHeckeCharacter D j (E j) (Ev j) (z j)`. Introduce `j hj`.

Consider the cases of `j with`. Consider the case `zero => exact isAuxiliaryHyperbolicPart_initialChainSpace`. Consider the case `succ j => exact hA₁ (j + 1) hj`. Establish `hE0 : ∀ i (hi : i < D.R.rS), E 0 i = D.sp.hypE ⟨i, hi⟩ ∧ Ev 0 i = D.sp.hypF ⟨i, hi⟩` using `fun i hi => ⟨dif_pos hi, dif_pos hi⟩`. Establish `hz0 : z 0 = D.sp.zm` using `rfl`.

Take `⟨L', hS, hF, hSh⟩` from `GlobalTheory.StdFrames.framesStdExist D Empty L hP hQ γ E Ev z hγ'`. Establish `hPg' : L'.Pg = Pg` using `hS.2.2.2.2.2.1`. Establish `hP' : ∀ PP, PP ∈ L'.Pg ↔ ∃ l, L'.C.P.Div l PP`. Rewrite using `[hS.1]`. Conclude with `hS.2.2.2.2.2.1 ▸ hP`.

Take `⟨⟨e, ev, z', κ, s, h1, h2⟩, hX⟩` from `GlobalTheory.NormalFramesStd.normalFrames_of_stdShape L' hP' γ E Ev z hγ' hAux hE0 hz0 hSh`. Establish `hV : ∀ i : Fin D.R.m, ∃ (eW : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W ((i : ℕ) + 1)).rank) (ι : GL (Fin (D.sp.W ((i : ℕ) + 1)).rank) (Formalism.IndefR.Lev.EAf D)), VertexAt ((i : ℕ) + 1) (betaYOf L'.βY 0) (L'.βW i) eW ι L'.Pg` using `fun i => GlobalTheory.VertexFromTransport.vertexAt_of_levTransport L' hP' i (hSh.2.2.2.2 i)`. Rewrite using `[← hPg']`. Conclude with `⟨L'.ΛY, L'.ΛX, L'.ΛV, L'.ΛW, L'.βY, L'.βX, L'.βV, L'.βW, hF, ⟨e, ev, z', κ, s, ⟨h1, h2⟩, hV⟩, hX⟩`.
-/
theorem selfDual_frames_normal_at_level_places_of_charFrame : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (Pg : Finset (Pl D.host.E)),
    (∀ PP, PP ∈ Pg ↔ ∃ l, C.P.Div l PP) → FramesExistDiagonal D Pg := by
  intro D C Pg hPg
  let L : LevCh D Empty :=
    { C := C, xiH := fun t => t.elim, mu0 := fun _ => 1, eta := 1, xi := fun t => t.elim, Pg := Pg,
      Q := fun t => t.elim, chi := fun _ _ => 1, xiR := fun t => t.elim,
      ΛY := fun _ => ⊥, ΛX := ⊥, ΛV := fun _ => ⊥, ΛW := fun _ => ⊥,
      βY := fun _ => 1, βX := 1, βV := fun _ => 1, βW := fun _ => 1 }
  have hP : ∀ PP, PP ∈ L.Pg ↔ ∃ l, L.C.P.Div l PP := hPg
  have hQ : ∀ t, Formalism.IndefR.Lev.IsTwistPlaces D.host.g (L.Q t) := fun t => t.elim
  choose γ hγ using fun j => GlobalTheory.StdFrames.exists_base (D.sp.X j)
  have hγ' : ∀ j, j < D.R.m → IsFrame (γ j) (Formalism.L2.Herm.crdLat (D.sp.X j) (D.sp.X j).L0) := fun j _ => by
    rw [hγ j]; exact GlobalTheory.StdFrames.isFrame_lat _
  have hex : ∀ j, ∃ (E Ev : ℕ → (D.sp.Y j).V) (z : (D.sp.Y j).V), j < D.R.m → IsAuxiliaryHeckeCharacter D j E Ev z := fun j => by
    by_cases hj : j < D.R.m
    · obtain ⟨E, Ev, z, h⟩ := GlobalTheory.StandardGramVectors.exists_auxiliaryHyperbolicVectors D j hj
      exact ⟨E, Ev, z, fun _ => h⟩
    · exact ⟨0, 0, 0, fun h => absurd h hj⟩
  choose E₁ Ev₁ z₁ hA₁ using hex
  let E : ∀ j, ℕ → (D.sp.Y j).V := fun j => match j with
    | 0 => fun i => if h : i < D.R.rS then D.sp.hypE ⟨i, h⟩ else 0
    | j + 1 => E₁ (j + 1)
  let Ev : ∀ j, ℕ → (D.sp.Y j).V := fun j => match j with
    | 0 => fun i => if h : i < D.R.rS then D.sp.hypF ⟨i, h⟩ else 0
    | j + 1 => Ev₁ (j + 1)
  let z : ∀ j, (D.sp.Y j).V := fun j => match j with
    | 0 => D.sp.zm
    | j + 1 => z₁ (j + 1)
  have hAux : ∀ j, j < D.R.m → IsAuxiliaryHeckeCharacter D j (E j) (Ev j) (z j) := by
    intro j hj
    cases j with
    | zero => exact isAuxiliaryHyperbolicPart_initialChainSpace
    | succ j => exact hA₁ (j + 1) hj
  have hE0 : ∀ i (hi : i < D.R.rS), E 0 i = D.sp.hypE ⟨i, hi⟩ ∧ Ev 0 i = D.sp.hypF ⟨i, hi⟩ := fun i hi =>
    ⟨dif_pos hi, dif_pos hi⟩
  have hz0 : z 0 = D.sp.zm := rfl
  obtain ⟨L', hS, hF, hSh⟩ := GlobalTheory.StdFrames.framesStdExist D Empty L hP hQ γ E Ev z hγ'
  have hPg' : L'.Pg = Pg := hS.2.2.2.2.2.1
  have hP' : ∀ PP, PP ∈ L'.Pg ↔ ∃ l, L'.C.P.Div l PP := by
    rw [hS.1]; exact hS.2.2.2.2.2.1 ▸ hP
  obtain ⟨⟨e, ev, z', κ, s, h1, h2⟩, hX⟩ :=
    GlobalTheory.NormalFramesStd.normalFrames_of_stdShape L' hP' γ E Ev z hγ' hAux hE0 hz0 hSh
  have hV : ∀ i : Fin D.R.m, ∃ (eW : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W ((i : ℕ) + 1)).rank)
      (ι : GL (Fin (D.sp.W ((i : ℕ) + 1)).rank) (Formalism.IndefR.Lev.EAf D)),
      VertexAt ((i : ℕ) + 1) (betaYOf L'.βY 0) (L'.βW i) eW ι L'.Pg := fun i =>
    GlobalTheory.VertexFromTransport.vertexAt_of_levTransport L' hP' i (hSh.2.2.2.2 i)
  rw [← hPg']
  exact ⟨L'.ΛY, L'.ΛX, L'.ΛV, L'.ΛW, L'.βY, L'.βX, L'.βV, L'.βW, hF, ⟨e, ev, z', κ, s, ⟨h1, h2⟩, hV⟩, hX⟩

end GlobalTheory.FramesExistLev

end
