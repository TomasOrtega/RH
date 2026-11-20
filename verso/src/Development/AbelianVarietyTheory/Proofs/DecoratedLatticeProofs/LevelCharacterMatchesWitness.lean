import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedArgsColumnHeq
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

/- English proof (translation)
Establish `h1 : a.x.R.C = Fr.at (w.st Z) f` using `eq_of_heq (R3.twArgs_lev K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t a).1`. Establish `h2` using `a.x.pins.char.base.lev.mu0 j`. Establish `h3 : a.x.R.C.mu0 j = w.I.C.mu0 j` using `(congrArg (fun C => C.mu0 j) h1).trans (congrArg (fun g : Fr B.toPre => g.mu0 j) w.C_eq).symm`. Conclude with `h3 ▸ h2`.
-/
theorem twistedAdelicData_characters_eq_frame (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt)
    (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : G.Inst (w.st Z).toD7 L)
    (Gl : G.LatInst (w.st Z).toD7) (Kc : G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC)
    (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : Bl.RowsT K w Z Wt ex.p0) (a : R3.TwArgs ex t) (j : Fin B.R.m) :
    Formalism.IndefR.Links.ChrEq (D := (w.st Z).toD7) (a.x.R.mu0 ((j : ℕ) + 1)) (w.I.C.mu0 j) := by
  have h1 : a.x.R.C = Fr.at (w.st Z) f := eq_of_heq (R3.twArgs_lev K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t a).1
  have h2 := a.x.pins.char.base.lev.mu0 j
  have h3 : a.x.R.C.mu0 j = w.I.C.mu0 j :=
    (congrArg (fun C => C.mu0 j) h1).trans (congrArg (fun g : Fr B.toPre => g.mu0 j) w.C_eq).symm
  exact h3 ▸ h2

/- English proof (translation)
Introduce `hL p K q c b hw j`. Take `⟨x, a, ax, y, -⟩` from `hw`. Establish `hx : a.x = x` using `eq_of_heq ax`. Establish `h0` using `twistedAdelicData_characters_eq_frame _ _ _ _ q.w q.Z _ _ _ _ _ _ _ _ _ _ a j`. Establish `e : b.B.Q.Rl.mu0 = x.R.mu0` using `congrArg (fun k : Bl.RPk b.R b.S => k.B.Q.Rl.mu0) y.eq`.

Establish `e' : a.x.R.mu0 = x.R.mu0` using `congrArg (fun z : R3.TwIn q.O.ex => z.R.mu0) hx`. Establish `e2 : (pk (packB b)).mu0 = a.x.R.mu0` using `e.trans e'.symm`. Rewrite using `[e2]`. Conclude with `h0`.
-/
theorem level_character_matches_witness : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → ∀ j : Fin q.B.R.m, Formalism.IndefR.Links.ChrEq ((pk (packB b)).mu0 ((j : ℕ) + 1)) (q.w.I.C.mu0 j) := by
  intro hL p K q c b hw j
  obtain ⟨x, a, ax, y, -⟩ := hw
  have hx : a.x = x := eq_of_heq ax
  have h0 := twistedAdelicData_characters_eq_frame _ _ _ _ q.w q.Z _ _ _ _ _ _ _ _ _ _ a j
  have e : b.B.Q.Rl.mu0 = x.R.mu0 := congrArg (fun k : Bl.RPk b.R b.S => k.B.Q.Rl.mu0) y.eq
  have e' : a.x.R.mu0 = x.R.mu0 := congrArg (fun z : R3.TwIn q.O.ex => z.R.mu0) hx
  have e2 : (pk (packB b)).mu0 = a.x.R.mu0 := e.trans e'.symm
  rw [e2]
  exact h0

end GlobalTheory.Fam
