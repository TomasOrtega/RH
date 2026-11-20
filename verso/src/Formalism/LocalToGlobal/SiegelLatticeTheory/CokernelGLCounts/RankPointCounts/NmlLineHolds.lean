import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsomHTSymm

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

/- English proof (translation)
Introduce `h'`. Apply `h` to reduce the goal to its premises. Simplify using `only [Formalism.L2.SG.TermOp.Gt]`. Rewrite using `[if_pos]`. Conclude with `(Formalism.L2.SG.TermDef.Gt_mk (PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all _ _ _) _).trans h'`.
-/
theorem G_ne_of_Gt {t : TauC Y u u'} (h : Gt t ≠ 0) : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
  intro h'
  apply h
  simp only [Formalism.L2.SG.TermOp.Gt]
  rw [if_pos]
  exact (Formalism.L2.SG.TermDef.Gt_mk (PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all _ _ _) _).trans h'

/- English proof (translation)
Establish `hdim` using `Formalism.L2.SG.Corank.finrank_VS D`. Take `⟨hrow, hs0⟩` from `hR`. Establish `hlam : t.lam = t0.lam` using `congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow`. Establish `hlam' : t.lam' = t0.lam'` using `congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow`. Establish `hlat : Submodule.IsLattice D.host.E t0.lam` using `((Y.rowsOK u).1 t0.lam t0.mem).2.1.1`.

Establish `hLF : IsLift t0.lam (lf D (X.Fu u))` using `((Y.rowsOK u).1 t0.lam t0.mem).2.1.2.2.1`. Establish `hL1 : IsLift t0.lam t0.frame` using `t0.rep.2.2.2.2.1`. Establish `hL2 : IsLift t0.lam t.frame` using `by rw [← hlam]; exact t.rep.2.2.2.2.1`. Establish `hG1` using `G_ne_of_Gt Y h0`. Establish `hG12 : Gval (lf D (X.Fu u)) t.frame = Gval (lf D (X.Fu u)) t0.frame`.

Rewrite using `[← Formalism.L2.SG.Pf.SatGram.gterm_G Y t, ← Formalism.L2.SG.Pf.SatGram.gterm_G Y t0, hG]`. Establish `hs0' : Lat.s0 t0.lam (lf D (X.Fu u)) t0.frame t.frame (t.lin * t0.lin⁻¹) D.R.k = 1`. Establish `h1 : Formalism.L2.SG.TermOp.s0T t0 t = 1` using `hs0`. Unfold `Formalism.L2.SG.TermOp.s0T at h1`. Rewrite `h1` using `[if_pos ⟨hlam.symm, hlam'.symm⟩]`.

Conclude with `h1`. Establish `hTh` using `(CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t0.lam hlat _ t0.frame t.frame _ hLF hL1 hG1).1 hs0'`. Establish `hTE : ((Tu D u : ℕ) : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Establish `hTE' : ((Tu D u' : ℕ) : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Establish `hTs : star ((Tu D u : ℕ) : D.host.E) = ((Tu D u : ℕ) : D.host.E)` using `star_natCast _`.

Establish `hTs' : star ((Tu D u' : ℕ) : D.host.E) = ((Tu D u' : ℕ) : D.host.E)` using `star_natCast _`. Use `⟨line_pair D.R.k hdim t0.lam hlat (lf D (X.Fu u)) t0.frame t.frame _ hLF hL1 hL2 hG1 hG12 hTE hTs hTh, line_pair' D.R.k hdim t0.lam hlat (lf D (X.Fu u)) (lf D (X.Fu u')) t0.lin t.lin t0.rep.2.2.1 t.rep.2.2.1 hLF hL1 hL2 hG1 hG12 hTE' hTs' hTh⟩` and prove the remaining obligations.
-/
theorem line_occ (t0 t : TauC Y u u') (h0 : Gt t0 ≠ 0) (h : Gt t ≠ 0) (hR : RelC Y u u' t0 t) (hG : t.G = t0.G)
    (hT : 3 ≤ Tu D u) (hT' : 3 ≤ Tu D u') :
    (yT Y u u' t - coefA Y u u' t0 t • yT Y u u' t0 ∈ (X.Fu u).X ∧
      coefA Y u u' t0 t * star (coefA Y u u' t0 t) = 1) ∧
    (yT' Y u u' t - coefA' Y u u' t0 t • yT' Y u u' t0 ∈ (X.Fu u').X ∧
      coefA' Y u u' t0 t * star (coefA' Y u u' t0 t) = 1) := by
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  obtain ⟨hrow, hs0⟩ := hR
  have hlam : t.lam = t0.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow
  have hlam' : t.lam' = t0.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow
  have hlat : Submodule.IsLattice D.host.E t0.lam := ((Y.rowsOK u).1 t0.lam t0.mem).2.1.1
  have hLF : IsLift t0.lam (lf D (X.Fu u)) := ((Y.rowsOK u).1 t0.lam t0.mem).2.1.2.2.1
  have hL1 : IsLift t0.lam t0.frame := t0.rep.2.2.2.2.1
  have hL2 : IsLift t0.lam t.frame := by rw [← hlam]; exact t.rep.2.2.2.2.1
  have hG1 := G_ne_of_Gt Y h0
  have hG12 : Gval (lf D (X.Fu u)) t.frame = Gval (lf D (X.Fu u)) t0.frame := by
    rw [← Formalism.L2.SG.Pf.SatGram.gterm_G Y t, ← Formalism.L2.SG.Pf.SatGram.gterm_G Y t0, hG]
  have hs0' : Lat.s0 t0.lam (lf D (X.Fu u)) t0.frame t.frame (t.lin * t0.lin⁻¹) D.R.k = 1 := by
    have h1 : Formalism.L2.SG.TermOp.s0T t0 t = 1 := hs0
    unfold Formalism.L2.SG.TermOp.s0T at h1
    rw [if_pos ⟨hlam.symm, hlam'.symm⟩] at h1
    exact h1
  have hTh := (CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t0.lam hlat _ t0.frame t.frame _ hLF hL1 hG1).1 hs0'
  have hTE : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hTE' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hTs : star ((Tu D u : ℕ) : D.host.E) = ((Tu D u : ℕ) : D.host.E) := star_natCast _
  have hTs' : star ((Tu D u' : ℕ) : D.host.E) = ((Tu D u' : ℕ) : D.host.E) := star_natCast _
  refine ⟨line_pair D.R.k hdim t0.lam hlat (lf D (X.Fu u)) t0.frame t.frame _ hLF hL1 hL2 hG1 hG12 hTE hTs hTh,
    line_pair' D.R.k hdim t0.lam hlat (lf D (X.Fu u)) (lf D (X.Fu u')) t0.lin t.lin t0.rep.2.2.1 t.rep.2.2.1 hLF
      hL1 hL2 hG1 hG12 hTE' hTs' hTh⟩

/- English proof (translation)
Introduce `Cg cb Cw cT CT C0`. Use `⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hC γ hγ t0 t h0 h hp0 hp hR => ?_⟩` and prove the remaining obligations. Unfold `Formalism.L2.SG.NGCut.Ctx at hC`. Establish `hT : 3 ≤ Tu D u` using `hC.2.1.2.2.2.1`. Establish `hT' : 3 ≤ Tu D u'` using `hC.2.1.2.2.2.2.1`.

Establish `hG : t.G = t0.G`. Establish `e` using `gval_occ Y t (by rw [hp]; exact hγ)`. Establish `e0` using `gval_occ Y t0 (by rw [hp0]; exact hγ)`. Rewrite `e` using `[hp]`. Rewrite `e0` using `[hp0]`.

Establish `e1 : t.G = Gval (lf D (X.Fu u)) t.frame` using `Formalism.L2.SG.TermDef.Gt_mk (PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all _ _ _) _`. Establish `e2 : t0.G = Gval (lf D (X.Fu u)) t0.frame` using `Formalism.L2.SG.TermDef.Gt_mk (PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all _ _ _) _`. Rewrite using `[e1, e2, e, e0]`. Establish `L` using `line_occ Y t0 t h0 h hR hG hT hT'`. Conclude with `⟨L.1.2, L.2.2⟩`.
-/
theorem NmlLine_holds : NmlLine := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hC γ hγ t0 t h0 h hp0 hp hR => ?_⟩
  unfold Formalism.L2.SG.NGCut.Ctx at hC
  have hT : 3 ≤ Tu D u := hC.2.1.2.2.2.1
  have hT' : 3 ≤ Tu D u' := hC.2.1.2.2.2.2.1
  have hG : t.G = t0.G := by
    have e := gval_occ Y t (by rw [hp]; exact hγ)
    have e0 := gval_occ Y t0 (by rw [hp0]; exact hγ)
    rw [hp] at e
    rw [hp0] at e0
    have e1 : t.G = Gval (lf D (X.Fu u)) t.frame :=
      Formalism.L2.SG.TermDef.Gt_mk (PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all _ _ _) _
    have e2 : t0.G = Gval (lf D (X.Fu u)) t0.frame :=
      Formalism.L2.SG.TermDef.Gt_mk (PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all _ _ _) _
    rw [e1, e2, e, e0]
  have L := line_occ Y t0 t h0 h hR hG hT hT'
  exact ⟨L.1.2, L.2.2⟩

end Formalism.L2.SG.NGCut.NormalVectorPairings
