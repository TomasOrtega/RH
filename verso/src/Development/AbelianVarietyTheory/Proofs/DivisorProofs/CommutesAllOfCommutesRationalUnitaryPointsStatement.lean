import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutesAllOfCommutesRationalUnitaryPoints
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.BridgeTie
set_option autoImplicit false
noncomputable section
open NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCommutesAllOfCommutesRationalUnitaryPoints.lean&line=242#L242)
-/
theorem _root_.GlobalTheory.T.commutes_all_of_commutes_rationalUnitaryPoints : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (tauL : D.what₂.Tau → (D.host.E →+* D.what₂.LL)),
    (∀ τ, D.what₂.embLL.comp (tauL τ) = Formalism.BasicNotions.TH.tauE D τ) →
    ∀ (lam : D.what₂.Tau → DomWeight V.rank) (g : Module.End D.what₂.LL (VV D.what₂.LL lam)),
    (∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE →
      ∀ v, g (rhoVr tauL lam γE v) = rhoVr tauL lam γE (g v)) →
    ∀ (h : D.what₂.Tau → GL (Fin V.rank) D.what₂.LL) v, g (rhoK lam h v) = rhoK lam h (g v) := by
  first | exact @GlobalTheory.RatDenseEnd.comm_all | exact GlobalTheory.RatDenseEnd.comm_all | (intros; apply GlobalTheory.RatDenseEnd.comm_all <;> assumption)
