import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceIsSplit
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TieFrob
/- English proof (translation)
Introduce `_ hL D P X _ _ i hμ j hj w hG _`. Establish `hIs` using `X.recR.base.lev`. Use `set t := X.tupT (D.nd.mu i) with ht`. Establish `hV : GlobalTheory.DownLift.valV X.R j t w = (X.R.C.mu0 j * X.R.xiH t * X.R.C.eta⁻¹).val w`. Establish `e1 : GlobalTheory.DownLift.valV X.R j t w = GlobalTheory.LFun.val (X.R.toLevCh.mu0 (j.1 + 1)) w * GlobalTheory.LFun.val (X.R.toLevCh.xi t) w * (GlobalTheory.LFun.val X.R.toLevCh.eta w)⁻¹` using `by show GlobalTheory.LFun.val (X.R.toLevCh.mu0 (j.1 + 1) * X.R.toLevCh.xi t * X.R.toLevCh.eta⁻¹) w = _`.

Rewrite using `[GlobalTheory.LFun.val_mul, GlobalTheory.LFun.val_mul, GlobalTheory.LFun.val_inv]`. Rewrite using `[e1, GlobalTheory.LFun.val_eq_of_chrEq (hIs.mu0 j), GlobalTheory.LFun.val_eq_of_chrEq (hIs.xi t), GlobalTheory.LFun.val_eq_of_chrEq hIs.eta, HChar.val_mul, HChar.val_mul, HChar.val_inv]`. Establish `hxi : X.R.xiH t = P.tp.xi (D.nd.mu i)`. Rewrite using `[X.recR.tupXi _ hμ]`. Conclude with `congrFun (xi_eq_of_heq X.cfEq X.Tp P.tp X.tpEq) _`.

Establish `hE : (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 = X.R.C.mu0 j * X.R.xiH t * X.R.C.eta⁻¹`. Rewrite using `[P.chr.tw, P.chr.muC i j hj, P.chr.etaTinv, hxi, X.cfEq]`. Both sides reduce to the same expression. Establish `hU : (X.R.C.mu0 j * X.R.xiH t * X.R.C.eta⁻¹).UnrAt w`. Use `HChar.UnrAt.mul (HChar.UnrAt.mul ?_ ?_) (HChar.UnrAt.inv (X.R.C.isEta.unr w))` and prove the remaining obligations.

Use `(X.R.C.isMu0 j).unr w fun k hk => ?_` and prove the remaining obligations. Break down `GlobalTheory.StepLaw.div_or_isConjPl_div D X.R.C.P k w hk with hd | ⟨PP, hd, hc⟩` into its components or cases. Conclude with `(hG w (Or.inl ((hIs.Pg w).2 ⟨k, hd⟩))).1 rfl`. Conclude with `(hG PP (Or.inl ((hIs.Pg PP).2 ⟨k, hd⟩))).2 hc`. Assume the negation of the conclusion as `hn`.

Break down `(hIs.Q_ram t w).1 hn with hq | ⟨PP, hq, hc⟩` into its components or cases. Conclude with `(hG w (Or.inr hq)).1 rfl`. Conclude with `(hG PP (Or.inr hq)).2 hc`. Rewrite using `[P.chr.frob _ w (by rw [hE]; exact hU), hE, hV, Units.val_inv_eq_inv_val]`.
-/
theorem frobEig_tw_eq_inv_valV_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (w : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) = {((GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w : ℂˣ) : ℂ)⁻¹} := by
  intro _ hL D P X _ _ i hμ j hj w hG _
  have hIs := X.recR.base.lev
  set t := X.tupT (D.nd.mu i) with ht
  have hV : GlobalTheory.DownLift.valV X.R j t w = (X.R.C.mu0 j * X.R.xiH t * X.R.C.eta⁻¹).val w := by
    have e1 : GlobalTheory.DownLift.valV X.R j t w =
        GlobalTheory.LFun.val (X.R.toLevCh.mu0 (j.1 + 1)) w * GlobalTheory.LFun.val (X.R.toLevCh.xi t) w *
          (GlobalTheory.LFun.val X.R.toLevCh.eta w)⁻¹ := by
      show GlobalTheory.LFun.val (X.R.toLevCh.mu0 (j.1 + 1) * X.R.toLevCh.xi t * X.R.toLevCh.eta⁻¹) w = _
      rw [GlobalTheory.LFun.val_mul, GlobalTheory.LFun.val_mul, GlobalTheory.LFun.val_inv]
    rw [e1, GlobalTheory.LFun.val_eq_of_chrEq (hIs.mu0 j), GlobalTheory.LFun.val_eq_of_chrEq (hIs.xi t),
      GlobalTheory.LFun.val_eq_of_chrEq hIs.eta, HChar.val_mul, HChar.val_mul, HChar.val_inv]
  have hxi : X.R.xiH t = P.tp.xi (D.nd.mu i) := by
    rw [X.recR.tupXi _ hμ]
    exact congrFun (xi_eq_of_heq X.cfEq X.Tp P.tp X.tpEq) _
  have hE : (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 = X.R.C.mu0 j * X.R.xiH t * X.R.C.eta⁻¹ := by
    rw [P.chr.tw, P.chr.muC i j hj, P.chr.etaTinv, hxi, X.cfEq]
    rfl
  have hU : (X.R.C.mu0 j * X.R.xiH t * X.R.C.eta⁻¹).UnrAt w := by
    refine HChar.UnrAt.mul (HChar.UnrAt.mul ?_ ?_) (HChar.UnrAt.inv (X.R.C.isEta.unr w))
    · refine (X.R.C.isMu0 j).unr w fun k hk => ?_
      rcases GlobalTheory.StepLaw.div_or_isConjPl_div D X.R.C.P k w hk with hd | ⟨PP, hd, hc⟩
      · exact (hG w (Or.inl ((hIs.Pg w).2 ⟨k, hd⟩))).1 rfl
      · exact (hG PP (Or.inl ((hIs.Pg PP).2 ⟨k, hd⟩))).2 hc
    · by_contra hn
      rcases (hIs.Q_ram t w).1 hn with hq | ⟨PP, hq, hc⟩
      · exact (hG w (Or.inr hq)).1 rfl
      · exact (hG PP (Or.inr hq)).2 hc
  rw [P.chr.frob _ w (by rw [hE]; exact hU), hE, hV, Units.val_inv_eq_inv_val]
end GlobalTheory.TieFrob
end
