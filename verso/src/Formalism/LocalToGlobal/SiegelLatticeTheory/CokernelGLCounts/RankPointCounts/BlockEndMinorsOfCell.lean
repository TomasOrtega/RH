import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.KExpCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.DifferentIdealMapNeBot

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut

namespace Formalism.L2.SG.NGCut.PtPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Proceed by induction on `b using Fin.lastCases with`. Consider the case `last => rw [Formalism.MainNotions.LatticeGluingRadicals.a_frame_last]`. Conclude with `hz`. Consider the case `cast b`. Rewrite using `[Formalism.MainNotions.LatticeGluingRadicals.a_frame_castSucc]`.

Establish `h : F.fl.e b ∈ XLam Λ F` using `by rw [hX]; exact Formalism.MainNotions.BridgeLemma₂.basis_vector_mem_span D F.fl b`. Conclude with `h.1`.
-/
theorem frame_mem {D : D7} {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (hz : F.fl.z ∈ Λ) (hX : XLam Λ F = XS D F.fl) (b : Fin (D.R.rS + 1)) : frame F b ∈ Λ := by
  induction b using Fin.lastCases with
  | last => rw [Formalism.MainNotions.LatticeGluingRadicals.a_frame_last]; exact hz
  | cast b =>
    rw [Formalism.MainNotions.LatticeGluingRadicals.a_frame_castSucc]
    have h : F.fl.e b ∈ XLam Λ F := by rw [hX]; exact Formalism.MainNotions.BridgeLemma₂.basis_vector_mem_span D F.fl b
    exact h.1

/- English proof (translation)
Take `⟨c, hc⟩` from `Formalism.MainNotions.LatticeGluingRadicals.d_Lam_int hun (hF i) (hF' j)`. Establish `hZ : ZhatL F F' i j = (VS D).hT (frame F i) (frame F' j)` using `rfl`. Establish `h1 : IsIntegral ℤ ((-1 : D.host.E) ^ (D.R.rS - j.val))` using `(isIntegral_one.neg).pow _`. Use `show IsIntegral ℤ ((-1 : D.host.E) ^ (D.R.rS - j.val) * ZhatL F F' i j)`. Rewrite using `[hZ, ← hc]`.

Conclude with `h1.mul (RingOfIntegers.isIntegral_coe c)`.
-/
theorem zhatOM_isIntegral {D : D7} {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (hun : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    (hF : ∀ b, frame F b ∈ Λ) (hF' : ∀ b, frame F' b ∈ Λ) (i j : Fin (D.R.rS + 1)) :
    IsIntegral ℤ (ZhatOM (ZhatL F F') i j) := by
  obtain ⟨c, hc⟩ := Formalism.MainNotions.LatticeGluingRadicals.d_Lam_int hun (hF i) (hF' j)
  have hZ : ZhatL F F' i j = (VS D).hT (frame F i) (frame F' j) := rfl
  have h1 : IsIntegral ℤ ((-1 : D.host.E) ^ (D.R.rS - j.val)) := (isIntegral_one.neg).pow _
  show IsIntegral ℤ ((-1 : D.host.E) ^ (D.R.rS - j.val) * ZhatL F F' i j)
  rw [hZ, ← hc]
  exact h1.mul (RingOfIntegers.isIntegral_coe c)

open Formalism.MainNotions.BesselShellMomentBounds Formalism.HermitianLatticeCounting.ExpansionTerms in

/- English proof (translation)
Take `⟨L, U, hL, hU, rfl⟩` from `hc`. Introduce `(a : Fin (toComp γ).length)`. Establish `key` using `Formalism.HermitianLatticeCounting.Final.ExpansionTerms.integral_evaluation_fourth D.host.E (integralClosure ℤ D.host.E).toSubring (D.R.rS + 1) (toComp γ) (toT γ) (toT_ne γ) L U ⟨fun i => (hL i i).2 rfl, fun i j hij => (hL i j).1 hij⟩ ⟨fun i => (hU i i).2 rfl, fun i j hij => (hU …`. Use `key.1 ((a : ℕ) + 1)` as an intermediate fact. Apply the tactic sequence `show IsIntegral ℤ (IndexedMinorEntry (toComp γ).blocksFun (toT γ) a) ∧ IndexedMinorEntry (toComp γ).blocksFun (toT γ) a ≠ 0`.

Rewrite using `[E5minor_eq]`. Conclude with `this`.
-/
theorem blockEndMinors_of_cell {D : D7} (Z : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hZ : ∀ i j, IsIntegral ℤ (Z i j)) (γ : Point D.host.E (D.R.rS + 1)) (hc : IsInCell Z γ) :
    BlockEndMinorsIntegral (toSig γ) := by
  obtain ⟨L, U, hL, hU, rfl⟩ := hc
  intro (a : Fin (toComp γ).length)
  have key := Formalism.HermitianLatticeCounting.Final.ExpansionTerms.integral_evaluation_fourth D.host.E (integralClosure ℤ D.host.E).toSubring (D.R.rS + 1)
    (toComp γ) (toT γ) (toT_ne γ) L U
    ⟨fun i => (hL i i).2 rfl, fun i j hij => (hL i j).1 hij⟩
    ⟨fun i => (hU i i).2 rfl, fun i j hij => (hU i j).1 hij⟩
    (by intro i j; rw [← ptMat_eq]; exact hZ i j)
  have := key.1 ((a : ℕ) + 1)
  show IsIntegral ℤ (IndexedMinorEntry (toComp γ).blocksFun (toT γ) a) ∧ IndexedMinorEntry (toComp γ).blocksFun (toT γ) a ≠ 0
  rw [E5minor_eq]
  exact this

/- English proof (translation)
Introduce `Cg cb Cw cT CT C0`. Use `⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hc νL νB ng γ hγ => ?_⟩` and prove the remaining obligations. Take `⟨c, ν, t, ht, hv, -, hpt, -⟩` from `hγ`. Establish `hG : t.toTerm.G ≠ 0`. Introduce `h`.

Apply `ht.1` to reduce the goal to its premises. Use `show Gt t = 0`. Establish `h' : t.G = 0` using `h`. Simplify using `[Gt, h']`. Establish `hrel : t.toTerm.relevant`.

Assume the negation of the conclusion as `hr`. Apply `hv` to reduce the goal to its premises. Establish `h0 : OOt t = 0` using `hOV Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc t hr`. Use `show vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0`. Unfold `vec ampN`.

Rewrite using `[h0]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Take `⟨w, hw⟩` from `hAt Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc t.toTerm hG hrel`. Establish `hat` using `Formalism.L2.SG.PairVal.ptOf_spec t.toTerm ⟨w, hw, hrel⟩`.

Take `⟨F', ⟨hP, -⟩, -, hcell⟩` from `hat`. Establish `hrow` using `(Y.rowsOK u).1 t.toTerm.lam t.toTerm.mem`. Establish `hF : ∀ b, frame (lf D (X.Fu u)) b ∈ t.toTerm.lam` using `frame_mem _ hrow.2.1.2.2.1.1 hrow.2.2`. Establish `hF' : ∀ b, frame F' b ∈ t.toTerm.lam` using `frame_mem _ hP.1.1 hP.2.2.2`. Establish `hE` using `blockEndMinors_of_cell _ (zhatOM_isIntegral _ _ hrow.2.1.2.1 hF hF') _ hcell`.

Rewrite using `[← hpt]`. Conclude with `hE`.
-/
theorem stepPoints_of_ctx
    (hOV : ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hAt : ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    StepPoints := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hc νL νB ng γ hγ => ?_⟩
  obtain ⟨c, ν, t, ht, hv, -, hpt, -⟩ := hγ
  have hG : t.toTerm.G ≠ 0 := by
    intro h
    apply ht.1
    show Gt t = 0
    have h' : t.G = 0 := h
    simp [Gt, h']
  have hrel : t.toTerm.relevant := by
    by_contra hr
    apply hv
    have h0 : OOt t = 0 := hOV Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc t hr
    show vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0
    unfold vec ampN
    rw [h0]
    simp
    rfl
  obtain ⟨w, hw⟩ := hAt Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc t.toTerm hG hrel
  have hat := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm ⟨w, hw, hrel⟩
  obtain ⟨F', ⟨hP, -⟩, -, hcell⟩ := hat
  have hrow := (Y.rowsOK u).1 t.toTerm.lam t.toTerm.mem
  have hF : ∀ b, frame (lf D (X.Fu u)) b ∈ t.toTerm.lam := frame_mem _ hrow.2.1.2.2.1.1 hrow.2.2
  have hF' : ∀ b, frame F' b ∈ t.toTerm.lam := frame_mem _ hP.1.1 hP.2.2.2
  have hE := blockEndMinors_of_cell _ (zhatOM_isIntegral _ _ hrow.2.1.2.1 hF hF') _ hcell
  rw [← hpt]
  exact hE

/- English proof (translation)
The claim follows from `stepPoints_of_ctx (fun _ _ _ _ _ _ _ _ D _ X Y u u' _ => hOV D X Y u u') (fun _ _ _ _ _ _ _ _ D _ X Y u u' _ => hAt D X Y u u')`.
-/
theorem stepPoints_of
    (hOV : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hAt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
      (t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u)), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    StepPoints :=
  stepPoints_of_ctx (fun _ _ _ _ _ _ _ _ D _ X Y u u' _ => hOV D X Y u u')
    (fun _ _ _ _ _ _ _ _ D _ X Y u u' _ => hAt D X Y u u')

open Formalism.L2.SG.TermOp.Vanish in

/- English proof (translation)
The claim follows from `stepPoints_of (fun _ _ Y _ _ t ht => ooVanish_of hA hU hN hC hG h1 h2 h3 h4 Y t ht) hAt`.
-/
theorem stepPoints_of_leaves (hA : AvgCore) (hU : GinfUnimod) (hN : NLamNinf) (hC : ChiTrivialC) (hG : PsiInfChar)
    (h1 : RClosedC) (h2 : RODiscreteC) (h3 : RCocompactC) (h4 : NonRelCharC)
    (hAt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
      (t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u)), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    StepPoints :=
  stepPoints_of (fun _ _ Y _ _ t ht => ooVanish_of hA hU hN hC hG h1 h2 h3 h4 Y t ht) hAt

end Formalism.L2.SG.NGCut.PtPf
