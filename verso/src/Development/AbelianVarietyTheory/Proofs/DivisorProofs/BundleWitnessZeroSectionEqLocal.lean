import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MapBaseTiedSel
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealPins3RealTOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealPinsRealTOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentEqClosedContentNumericalDatum
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Split into cases according to the possible forms of the given data. Establish an intermediate fact. Equip the data with the indicated structure. Equip the data with the indicated structure. Establish an intermediate fact.

Simplify by unfolding definitions. Extract witnesses or component facts from the available result. Simplify by unfolding definitions. Extract witnesses or component facts from the available result. Simplify by unfolding definitions.

Split into cases according to the possible forms of the given data. A detailed English derivation is pending.
-/
theorem GlobalTheory.Mem.Top.Bl.bundle_witness_zero_section_eq : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : GlobalTheory.Fc.Bundle (q.w.D q.Z) q.O c) (w : BWit q b), q.O.L.sc = K.s → HEq (w.a.Zsc (zsOf q.x.what₂.r.z.R q.x.what₂.r.z.F)).F0 (F0K K.s (q.w.D q.Z)) := by
  intro hL p
  apply GlobalTheory.Fc.EvP.of_all
  intro _ K _ q c b w hsc
  have hK : DV.KapDef (q.w.D q.Z) := b.R.T.what₂.ka
  have hB : ∀ Zs, HEq ((rpkB b).Zsc Zs).F0 (F0K K.s (q.w.D q.Z)) := by
    intro Zs
    apply heq_of_eq
    funext y j
    rw [← hsc]
    exact (forcedContent_eq_closedContent_numericalDatum _ _ _ _ hK y j).symm
  obtain ⟨x, a, ax, y, _⟩ := w
  cases ax
  have hX := y.eq ▸ hB
  letI := a.x.grp
  letI := a.x.fin
  have hX' : ∀ Zs : DefSub a.x.A3.fam3.amb3, HEq (a.x.F.Zsc Zs).F0 (F0K K.s (q.w.D q.Z)) := hX
  dsimp only
  clear * - hX'
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x', pack, _⟩ := a
  dsimp only at hX' ⊢
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x'
  dsimp only at pack hX' ⊢
  cases pack
  exact hX' _
