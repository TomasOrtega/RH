import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.GaussJetBounds.StatementN
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DerivationCoordinateChange
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames

open MvPowerSeries GlobalTheory.Proof.DirectionalDerivative

section Formal

variable {p : ℕ} [Fact p.Prime] {σ κ : Type}

/- English proof (translation)
Unfold `JetsIntegral GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.JetsIntegral GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.jetAt Formalism.DworkPowerSeriesWeights.mfact`. Simplify using `[Finsupp.prod, Nat.cast_prod]`.
-/
theorem jetsIntegral_iff (G : MvPowerSeries κ ℂ_[p]) :
    JetsIntegral G ↔ GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.JetsIntegral G := by
  unfold JetsIntegral GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.JetsIntegral GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.jetAt Formalism.DworkPowerSeriesWeights.mfact
  simp [Finsupp.prod, Nat.cast_prod]

/- English proof (translation)
Proceed by induction on `l generalizing G with`. Consider the case `nil => simp [jetAt_zero, constantCoeff_linAt]`. Consider the case `cons x l ih`. Rewrite using `[List.map_cons, List.sum_cons, add_comm, jetAt_add_single, pderiv_linAt, ih, List.foldl_cons]`.
-/
theorem jetAt_linAt_list [Fintype σ] [Fintype κ] (c : σ → κ → ℂ_[p]) (l : List κ) (G : MvPowerSeries σ ℂ_[p]) :
    GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.jetAt (linAt c G) (l.map fun x => Finsupp.single x 1).sum =
      constantCoeff (l.foldl (fun H x => dirDer (fun k => c k x) H) G) := by
  induction l generalizing G with
  | nil => simp [jetAt_zero, constantCoeff_linAt]
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, add_comm, jetAt_add_single, pderiv_linAt, ih, List.foldl_cons]

end Formal

/- English proof (translation)
Introduce `D N N' p _ lm Yl F`. Use `⟨⟨fun hF n y hy => ?_, fun h n y hy => ?_⟩, fun hF ν _ M hM => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `JetsIntegral (linAt (fun k j => vecY D lm (y j) k) F)`. Rewrite using `[jetsIntegral_iff]`. Conclude with `jetsIntegral_linAt _ (JetsInt D lm Yl) (fun G hG => jetsInt_const D lm Yl hG) (fun x G hG => keeps_vecY D lm Yl (hy x) G hG) F hF`.

Establish `hJ` using `(jetsIntegral_iff _).1 (h n y hy)`. Express the relevant statement in the definitionally equal form `GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.JetsIntegral (linAt (fun k j => vecY D lm (y j) k) F) at hJ`. Use `hJ (((List.finRange n).reverse.map fun x => Finsupp.single x 1).sum)` as an intermediate fact. Rewrite `this` using `[jetAt_linAt_list, List.foldl_reverse]`. Use `show ‖constantCoeff ((List.ofFn y).foldr (fun y' G => der D lm y' G) F)‖ ≤ 1`.

Rewrite using `[List.ofFn_eq_map, List.foldr_map]`. Establish `hfun : (fun x G => der D lm (y x) G) = fun x G => dirDer (fun k => vecY D lm (y x) k) G`. Use function extensionality and compare the values at `x G`. Conclude with `der_eq D lm (y x) G`. Rewrite using `[hfun]`.

Conclude with `this`. Express the relevant statement in the definitionally equal form `JetsIntegral (linAt M F)`. Rewrite using `[jetsIntegral_iff]`. Use `jetsIntegral_linAt _ (JetsInt D lm Yl) (fun G hG => jetsInt_const D lm Yl hG) (fun x => ?_) F hF` and prove the remaining obligations. Take `⟨n, r, y, hr, hy, hMx⟩` from `hM x`.

Establish `e : (fun k => M k x) = ∑ j, r j • vecY D lm (y j)`. Use function extensionality and compare the values at `k`. Rewrite using `[hMx k, Finset.sum_apply]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `Finset.sum_induction _ (Keeps D lm Yl) (fun _ _ ha hb => keeps_add D lm Yl ha hb) (keeps_zero D lm Yl) fun j _ => keeps_smul D lm Yl (hr j) (keeps_vecY D lm Yl (hy j))`.
-/
theorem jetsInt_frames : ∀ (D : D7) (N N' : ℕ) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (Yl : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)) (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (JetsInt D lm Yl F ↔ ∀ (n : ℕ) (y : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, y j ∈ Yl) → JetsIntegral (atLin (fun k j => tauEmb D lm k.1 (y j k.2.1 k.2.2)) (fun j => MvPowerSeries.X j) F)) ∧ (JetsInt D lm Yl F → ∀ (ν : Type) [Fintype ν] (M : D.what₂.Tau × Fin N' × Fin N → ν → ℂ_[p]), (∀ x, ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (y : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, ‖r j‖ ≤ 1) ∧ (∀ j, y j ∈ Yl) ∧ ∀ k, M k x = ∑ j, r j * tauEmb D lm k.1 (y j k.2.1 k.2.2)) → JetsIntegral (atLin M (fun j => MvPowerSeries.X j) F)) := by
  intro D N N' p _ lm Yl F
  refine ⟨⟨fun hF n y hy => ?_, fun h n y hy => ?_⟩, fun hF ν _ M hM => ?_⟩
  · change JetsIntegral (linAt (fun k j => vecY D lm (y j) k) F)
    rw [jetsIntegral_iff]
    exact jetsIntegral_linAt _ (JetsInt D lm Yl) (fun G hG => jetsInt_const D lm Yl hG)
      (fun x G hG => keeps_vecY D lm Yl (hy x) G hG) F hF
  · have hJ := (jetsIntegral_iff _).1 (h n y hy)
    change GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.JetsIntegral (linAt (fun k j => vecY D lm (y j) k) F) at hJ
    have := hJ (((List.finRange n).reverse.map fun x => Finsupp.single x 1).sum)
    rw [jetAt_linAt_list, List.foldl_reverse] at this
    show ‖constantCoeff ((List.ofFn y).foldr (fun y' G => der D lm y' G) F)‖ ≤ 1
    rw [List.ofFn_eq_map, List.foldr_map]
    have hfun : (fun x G => der D lm (y x) G) = fun x G => dirDer (fun k => vecY D lm (y x) k) G := by
      funext x G
      exact der_eq D lm (y x) G
    rw [hfun]
    exact this
  · change JetsIntegral (linAt M F)
    rw [jetsIntegral_iff]
    refine jetsIntegral_linAt _ (JetsInt D lm Yl) (fun G hG => jetsInt_const D lm Yl hG) (fun x => ?_) F hF
    obtain ⟨n, r, y, hr, hy, hMx⟩ := hM x
    have e : (fun k => M k x) = ∑ j, r j • vecY D lm (y j) := by
      funext k
      rw [hMx k, Finset.sum_apply]
      rfl
    rw [e]
    exact Finset.sum_induction _ (Keeps D lm Yl) (fun _ _ ha hb => keeps_add D lm Yl ha hb) (keeps_zero D lm Yl)
      fun j _ => keeps_smul D lm Yl (hr j) (keeps_vecY D lm Yl (hy j))

end GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames
