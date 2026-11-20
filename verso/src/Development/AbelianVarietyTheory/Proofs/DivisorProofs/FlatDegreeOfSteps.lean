import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint

noncomputable section

namespace GlobalTheory.FlatCore

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c r U x hL logOm hA hF hD Z τ`. Use `⟨?_, fun s => ?_⟩` and prove the remaining obligations. Take `⟨s⟩` from `hA Z τ choose ρ hρ using hF Z τ s`. Establish `hP` using `GlobalTheory.FlatLine.hasPts U hL.pos hL.good hL.unf Z`. Establish `hfin` using `(hD Z τ s ρ hρ).1`.

Use `⟨⟨s.sig, s.inv, s.sig_mem, s.inv_mem, s.idem_sig, s.idem_inv, s.mul_inv, s.cInf, s.cInf_pos, s.norm_inf, ρ - flDefect_vw Dw c τ, fun w => image_eq_singleton_iff.2 ⟨hP.2 w, fun v hv => ?_⟩, (hfin.union (finite_flDefect_vw τ)).subset (Function.support_sub _ _)⟩⟩` and prove the remaining obligations. Rewrite using `[hρ w v hv, Pi.sub_apply, add_sub_cancel]`. Establish `h` using `(hD Z τ (ArchSec.ofConst s.toFrame) s.toFrame.rho_vw fun w v hv => by`. Establish `h1` using `s.toFrame.val_eq hv`. Rewrite `h1` using `[Pi.zero_apply, zero_add]`.

Conclude with `h1).2`. Rewrite using `[s.deg_eq_toFrame, neg_neg, flatDegVal, ← h]`. Both sides reduce to the same expression.
-/
theorem flatDegree_of_steps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ logOm : ℝ, ArchEx U x → FinConst U x → FrameDeg U x logOm → FlatDegree U x logOm := by
  intro E _ _ _ H Dw l Xo c r U x hL logOm hA hF hD Z τ
  refine ⟨?_, fun s => ?_⟩
  · obtain ⟨s⟩ := hA Z τ
    choose ρ hρ using hF Z τ s
    have hP := GlobalTheory.FlatLine.hasPts U hL.pos hL.good hL.unf Z
    have hfin := (hD Z τ s ρ hρ).1
    refine ⟨⟨s.sig, s.inv, s.sig_mem, s.inv_mem, s.idem_sig, s.idem_inv, s.mul_inv, s.cInf, s.cInf_pos, s.norm_inf,
      ρ - flDefect_vw Dw c τ, fun w => image_eq_singleton_iff.2 ⟨hP.2 w, fun v hv => ?_⟩,
      (hfin.union (finite_flDefect_vw τ)).subset (Function.support_sub _ _)⟩⟩
    rw [hρ w v hv, Pi.sub_apply, add_sub_cancel]
  · have h := (hD Z τ (ArchSec.ofConst s.toFrame) s.toFrame.rho_vw fun w v hv => by
      have h1 := s.toFrame.val_eq hv
      rw [Pi.zero_apply, zero_add] at h1
      exact h1).2
    rw [s.deg_eq_toFrame, neg_neg, flatDegVal, ← h]
    rfl

end GlobalTheory.FlatCore

end
