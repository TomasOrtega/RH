import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MapBaseTiedSel
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealPins3RealTOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealPinsRealTOf
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `hL p`. Use `GlobalTheory.Fc.EvP.of_all fun _ K _ q c b w _ => ?_` and prove the remaining obligations. Establish `hR : b.R.T.n.cf = GlobalTheory.Mem.Col2.TC.cf q.w.I q.w.l q.Z` using `congrArg Sigma.fst w.recPin.s.chr`. Rewrite using `[hR]`. Establish `hC : q.x.what₂.r.z.R.toRealDat.C = GlobalTheory.Mem.Col2.TC.cf q.w.I q.w.l q.Z` using `q.x.what₂.r.z.lev.C`.

Rewrite using `[← hC]`. Take `⟨x, a, ax, y⟩` from `w`. Consider the cases of `ax`. Take `⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩` from `a`. Take `⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩` from `x`.

Simplify using `only at pack ⊢`. Consider the cases of `pack`. Both sides reduce to the same expression.
-/
theorem bwit_cf_eq : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : GlobalTheory.Fc.Bundle (q.w.D q.Z) q.O c) (w : BWit q b), q.O.L.sc = K.s → w.x.R.C = b.R.T.n.cf := by
  intro hL p
  refine GlobalTheory.Fc.EvP.of_all fun _ K _ q c b w _ => ?_
  have hR : b.R.T.n.cf = GlobalTheory.Mem.Col2.TC.cf q.w.I q.w.l q.Z := congrArg Sigma.fst w.recPin.s.chr
  rw [hR]
  have hC : q.x.what₂.r.z.R.toRealDat.C = GlobalTheory.Mem.Col2.TC.cf q.w.I q.w.l q.Z := q.x.what₂.r.z.lev.C
  rw [← hC]
  obtain ⟨x, a, ax, y⟩ := w
  cases ax
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  rfl

end GlobalTheory.Mem.Top.Bl
