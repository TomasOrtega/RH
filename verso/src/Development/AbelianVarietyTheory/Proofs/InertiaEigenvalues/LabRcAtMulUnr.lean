import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LabFixed
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL

/- English proof (translation)
Unfold `rcAt`. Take `⟨a, ha, ε, -, H⟩` from `ParLaws.isRec_locRec hL (D.nd.plOm.2 (D.naut.plGw k v))`. Establish `e1 : LocLanglands.cls (Irr.ofDet 1 (ξ * η) hξη).toIrrRep = (GlobalTheory.LocGL.IrrGL.ofChar ξ hξ).tw η hη`. Rewrite using `[GlobalTheory.LocGL.IrrGL.tw_ofChar]`. Both sides reduce to the same expression.

Establish `e2 : LocLanglands.cls (Irr.ofDet 1 ξ hξ).toIrrRep = GlobalTheory.LocGL.IrrGL.ofChar ξ hξ` using `rfl`. Rewrite using `[e1, e2, H.twist, H.one η hη, lpChar_lpOfChar, WD.lab_lpTwist]`. Introduce `σ`. Establish `hd` using `ha.ord_eq (ineIncl _ σ)`. Rewrite `hd` using `[deg_ineIncl, neg_zero]`.

Apply `hu` to reduce the goal to its premises. Establish `h0 : Valued.v ((a ((ineIncl _) σ) : (HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v))ˣ) : HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v)) ≠ 0` using `by simp`. Rewrite `hd` using `[GlobalTheory.SmGL.SphCompletion.ord_completion, neg_eq_zero]`. Unfold `Formalism.L2.Host.IsUnitAt`. Rewrite using `[← WithZero.exp_log h0, hd, WithZero.exp_zero]`.
-/
theorem lab_rcAt_mul_unr (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (k : Fin 2) (v : D.nd.PlG k)
    (ξ η : (HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v))ˣ →* ℂˣ) (hξ : IsSmoothChar ξ)
    (hη : IsSmoothChar η) (hu : ∀ x, Formalism.L2.Host.IsUnitAt (D.naut.plGw k v) x → η x = 1) (hξη : IsSmoothChar (ξ * η)) :
    WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (rcAt hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 (ξ * η) hξη)) =
      WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (rcAt hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 ξ hξ)) := by
  unfold rcAt
  obtain ⟨a, ha, ε, -, H⟩ := ParLaws.isRec_locRec hL (D.nd.plOm.2 (D.naut.plGw k v))
  have e1 : LocLanglands.cls (Irr.ofDet 1 (ξ * η) hξη).toIrrRep = (GlobalTheory.LocGL.IrrGL.ofChar ξ hξ).tw η hη := by
    rw [GlobalTheory.LocGL.IrrGL.tw_ofChar]; rfl
  have e2 : LocLanglands.cls (Irr.ofDet 1 ξ hξ).toIrrRep = GlobalTheory.LocGL.IrrGL.ofChar ξ hξ := rfl
  rw [e1, e2, H.twist, H.one η hη, lpChar_lpOfChar, WD.lab_lpTwist]
  intro σ
  have hd := ha.ord_eq (ineIncl _ σ)
  rw [deg_ineIncl, neg_zero] at hd
  apply hu
  have h0 : Valued.v ((a ((ineIncl _) σ) : (HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v))ˣ) :
      HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v)) ≠ 0 := by simp
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion, neg_eq_zero] at hd
  unfold Formalism.L2.Host.IsUnitAt
  rw [← WithZero.exp_log h0, hd, WithZero.exp_zero]

/- English proof (translation)
Introduce `hPr hL D P S hT i k v hw hχ s`. Use `haveI := host_isCMField D.host`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j : Fin D.R.m, (j : ℕ) + 1 = D.nd.j i := by`. Use `D.nd.j_range i` as an intermediate fact. Conclude with `⟨⟨D.nd.j i - 1, by omega⟩, by simp only; omega⟩`.

Establish `hμ : IsComp (P.tp.tup (D.nd.mu i) j) (D.naut.plGw k v) (S i _ hw).mu` using `hT.mu i _ hw j hj`. Establish `hψ : (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 = P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹`. Rewrite using `[P.chr.tw, P.chr.muC i j hj, P.chr.etaTinv]`. Establish `hc : IsComp (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 (D.naut.plGw k v) ((P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹).loc (D.naut.plGw k v))`. Rewrite using `[hψ]`.

Conclude with `⟨ParLaws.isSmoothChar_loc _ _, fun x => rfl⟩`. Rewrite using `[P.lab k v, P.T.tw, WD.lab_lpTw, GlobalTheory.RankOneComp.locG_rankOne_eq_rcAt hPr.fin hL D P _ _ _ hc, labAt]`. Establish `hηs : IsSmoothChar (P.cf.eta.loc (D.naut.plGw k v))⁻¹`. Use `ParLaws.isSmoothChar_loc (P.cf.eta⁻¹) (D.naut.plGw k v)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Conclude with `MonoidHom.ext fun x => rfl`. Establish `hu : ∀ x, Formalism.L2.Host.IsUnitAt (D.naut.plGw k v) x → (P.cf.eta.loc (D.naut.plGw k v))⁻¹ x = 1`. Introduce `x hx`. Rewrite using `[MonoidHom.inv_apply, P.cf.isEta.unr _ x hx, inv_one]`. Establish `e : (P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹).loc (D.naut.plGw k v) = (S i _ hw).mu * (P.cf.eta.loc (D.naut.plGw k v))⁻¹`.

Rewrite using `[GlobalTheory.Published.ParamAboveModel.eq_loc hμ]`. Both sides reduce to the same expression. Establish `key : ∀ (ξ' : (HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v))ˣ →* ℂˣ) (h' : IsSmoothChar ξ'), ξ' = (S i _ hw).mu * (P.cf.eta.loc (D.naut.plGw k v))⁻¹ → WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (rcAt hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 ξ' h')) = WD.lab (D.ntype …`. Introduce and unpack `_ h' rfl`. Conclude with `lab_rcAt_mul_unr hL D k v _ _ hχ hηs hu h'`.

Conclude with `key _ _ e`.
-/
theorem labFixed : ∀ (hPr : GlobalTheory.NRows.Hypotheses₂) (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (S : Reading P.T), IsTrue P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (s : ℝ), D.naut.items₂ k (D.naut.plGw k v) (D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (D.naut.plGw k v)) s) = labAt hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) := by
  intro hPr hL D P S hT i k v hw hχ s
  haveI := host_isCMField D.host
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, (j : ℕ) + 1 = D.nd.j i := by
    have := D.nd.j_range i
    exact ⟨⟨D.nd.j i - 1, by omega⟩, by simp only; omega⟩
  have hμ : IsComp (P.tp.tup (D.nd.mu i) j) (D.naut.plGw k v) (S i _ hw).mu := hT.mu i _ hw j hj
  have hψ : (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 = P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹ := by
    rw [P.chr.tw, P.chr.muC i j hj, P.chr.etaTinv]
  have hc : IsComp (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 (D.naut.plGw k v)
      ((P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹).loc (D.naut.plGw k v)) := by
    rw [hψ]; exact ⟨ParLaws.isSmoothChar_loc _ _, fun x => rfl⟩
  rw [P.lab k v, P.T.tw, WD.lab_lpTw, GlobalTheory.RankOneComp.locG_rankOne_eq_rcAt hPr.fin hL D P _ _ _ hc, labAt]
  have hηs : IsSmoothChar (P.cf.eta.loc (D.naut.plGw k v))⁻¹ := by
    have := ParLaws.isSmoothChar_loc (P.cf.eta⁻¹) (D.naut.plGw k v)
    convert this using 1
    exact MonoidHom.ext fun x => rfl
  have hu : ∀ x, Formalism.L2.Host.IsUnitAt (D.naut.plGw k v) x → (P.cf.eta.loc (D.naut.plGw k v))⁻¹ x = 1 := by
    intro x hx
    rw [MonoidHom.inv_apply, P.cf.isEta.unr _ x hx, inv_one]
  have e : (P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹).loc (D.naut.plGw k v) =
      (S i _ hw).mu * (P.cf.eta.loc (D.naut.plGw k v))⁻¹ := by
    rw [GlobalTheory.Published.ParamAboveModel.eq_loc hμ]
    rfl
  have key : ∀ (ξ' : (HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v))ˣ →* ℂˣ) (h' : IsSmoothChar ξ'),
      ξ' = (S i _ hw).mu * (P.cf.eta.loc (D.naut.plGw k v))⁻¹ →
      WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (rcAt hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 ξ' h')) =
        WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (rcAt hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 (S i _ hw).mu hχ)) := by
    rintro _ h' rfl
    exact lab_rcAt_mul_unr hL D k v _ _ hχ hηs hu h'
  exact key _ _ e

end GlobalTheory.LabFixed
