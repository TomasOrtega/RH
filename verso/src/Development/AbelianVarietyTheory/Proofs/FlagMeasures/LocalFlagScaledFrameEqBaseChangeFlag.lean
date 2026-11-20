import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Ia

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlagBaseChange

/- English proof (translation)
Break down `A with ⟨f, es, T0, h1, h2, h3, h4, h5⟩` into its components or cases. Simplify using `only at hA`. Substitute `hA` using the available equality. Establish `hb` using `h4 b b`. Simplify using `only at hb`.

Rewrite `hb` using `[if_pos rfl, (locH Z p).h_smul_left]`. Conclude with `⟨⟨_, _, hb, (mul_comm _ _).trans hb⟩, rfl⟩`.
-/
theorem isUnit_frFac {D : D7} {T : D.host.E} (G : LFlag (VS D) D.R.rS T) (Z : LocDat D) (p : PlF D)
    (A : LocNG.FrameD (locH Z p) D.R.rS) (hA : A.f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a))
    (b : Fin D.R.rS) : IsUnit (frFac Z.δ p b.castSucc) := by
  rcases A with ⟨f, es, T0, h1, h2, h3, h4, h5⟩
  dsimp only at hA
  subst hA
  have hb := h4 b b
  dsimp only at hb
  rw [if_pos rfl, (locH Z p).h_smul_left] at hb
  exact ⟨⟨_, _, hb, (mul_comm _ _).trans hb⟩, rfl⟩

/- English proof (translation)
Introduce `D T G Z A hA p j`. Unfold `LocNG.FrameD.Fj LocNG.FrameD.e FlagG.Xa`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Rewrite `hx` using `[SetLike.mem_coe]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨i, hi, rfl⟩` from `hy`. Take `⟨u, hu⟩` from `GlobalTheory.FlagBaseChange.isUnit_frFac G Z p (A p) (hA p) i`.

Establish `hmem : (A p).f i.castSucc ∈ Submodule.span (D.s.atP p).Ep ((fun a : Fin D.R.rS => (A p).f a.castSucc) '' {a : Fin D.R.rS | (a : ℕ) < j})` using `Submodule.subset_span ⟨i, hi, rfl⟩`. Establish `hf : (A p).f i.castSucc = frFac Z.δ p i.castSucc • baseChange₂ D p (G.fl.e i)`. Rewrite using `[hA p]`. Simplify using `only`. Rewrite using `[Formalism.L2.SG.Pf.frame_castSucc_sat]`.

Rewrite `hmem` using `[hf, ← hu]`. Establish `hv` using `Submodule.smul_mem _ (↑u⁻¹ : (D.s.atP p).Ep) hmem`. Rewrite `hv` using `[smul_smul, Units.inv_mul, one_smul]`. Conclude with `hv`. Consider the case `zero`.

Rewrite using `[map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul a x _ hx`. Rewrite using `[baseChange_smul₂]`. Conclude with `Submodule.smul_mem _ _ hx`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, hi, rfl⟩`.

Simplify using `only`. Rewrite using `[hA p]`. Simplify using `only`. Apply `Submodule.smul_mem` to reduce the goal to its premises. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨G.fl.e i, Submodule.subset_span ⟨i, hi, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Formalism.L2.SG.Pf.frame_castSucc_sat]`.
-/
theorem span_bcP_Xa_eq_Fj : ∀ (D : D7) (T : D.host.E) (G : LFlag (VS D) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ (p : PlF D) (j : ℕ), Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (G.fl.Xa j : Set (VS D).V)) = (A p).Fj j := by
  intro D T G Z A hA p j
  unfold LocNG.FrameD.Fj LocNG.FrameD.e FlagG.Xa
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      obtain ⟨u, hu⟩ := GlobalTheory.FlagBaseChange.isUnit_frFac G Z p (A p) (hA p) i
      have hmem : (A p).f i.castSucc ∈
          Submodule.span (D.s.atP p).Ep ((fun a : Fin D.R.rS => (A p).f a.castSucc) '' {a : Fin D.R.rS | (a : ℕ) < j}) :=
        Submodule.subset_span ⟨i, hi, rfl⟩
      have hf : (A p).f i.castSucc = frFac Z.δ p i.castSucc • baseChange₂ D p (G.fl.e i) := by
        rw [hA p]
        dsimp only
        rw [Formalism.L2.SG.Pf.frame_castSucc_sat]
      rw [hf, ← hu] at hmem
      have hv := Submodule.smul_mem _ (↑u⁻¹ : (D.s.atP p).Ep) hmem
      rw [smul_smul, Units.inv_mul, one_smul] at hv
      exact hv
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [baseChange_smul₂]
      exact Submodule.smul_mem _ _ hx
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    dsimp only
    rw [hA p]
    dsimp only
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨G.fl.e i, Submodule.subset_span ⟨i, hi, rfl⟩, ?_⟩
    rw [Formalism.L2.SG.Pf.frame_castSucc_sat]

end GlobalTheory.FlagBaseChange
