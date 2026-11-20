import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.TopShape
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc

set_option maxHeartbeats 4000000 in
/- English proof (authored)
Apply the shape theorem to the family and selections carried by the hypothesis record. Pass the S-component of each C-selection. Translate the divisibility rows and the service condition using their equivalences in the shape interface. For the rank rows, retain the existing constants and eventual threshold, and keep the listed fields of the first row together with the second row intact. This gives the row condition in the form required by the shape theorem. The record and the supplied proofs of V and NR give all remaining inputs, so the theorem yields G.
-/
theorem GlobalTheory.Fc.of_hyps (V NR : Prop) (N : FamClass → Prop) (G : Prop) (t : TopShape V NR N G) (hV : V) (hR : NR) (h : Hyps N DRS) : G :=
  t h.𝒜 h.cT h.hEx (sel h.σ) h.hduty (selS h.σ) (selP h.σ) (selDH h.σ) (fun Fm hc x hx k i => (selC h.σ Fm hc x hx k i).toS) (selB h.σ) h.hRB h.hTw h.hPA h.hLamP
    (fun Fm hc x hx k i => (GlobalTheory.Cp.divRows3G_iff _).1 (h.hDivG Fm hc x hx k i)) h.hDcPtG h.hTu h.hn4 h.hLit hV h.hWu h.hRF h.hTF h.c30 h.hc30 h.sTy h.sNG h.sM h.sLp h.sO h.h30 h.hInstR h.selJ h.jOn h.hMt
    (h.rRows.imp fun Fm CH _ r hc => let ⟨C, h0, x0, r⟩ := r hc
      ⟨C, h0, x0, fun x hx k hx0 i => let ⟨a, d⟩ := r x hx k hx0 i
        ⟨⟨a.w1, a.covol, a.onto, a.lamLow, a.seeIso, a.miStar, a.fun0, a.pass, a.kap⟩, d⟩⟩)
    h.aPt0 h.aPtTw h.aPer0 h.aPerTw h.aP10 h.aAtG h.aC2 ((GlobalTheory.Cp.servT_iff _ _).1 h.hServ) hR h.nRest h.cIc h.hcI h.irrC h.zL h.tie h.hU h.hG

/- English proof (authored)
Fix the four parameters and the shape theorem. Apply of_hyps with the supplied proofs of V and NR and the family hypothesis record to obtain G.
-/
theorem GlobalTheory.Fc.shape_of : ∀ (V NR : Prop) (N : FamClass → Prop) (G : Prop), TopShape V NR N G → V → NR → Hyps N DRS → G :=
  fun V NR N G t hV hR h => GlobalTheory.Fc.of_hyps V NR N G t hV hR h
