import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatakeGLOfHasSatakeParametersPrincipalSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharCMEtaLocalEqNegOnePowValInert
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Establish `h : (Finset.range t).val = (Finset.univ : Finset (Fin t)).val.map (fun i : Fin t => (i : ℕ))`. Establish `h' : Finset.range t = (Finset.univ : Finset (Fin t)).map Fin.valEmbedding`. Use extensionality with `i`. Simplify using `only [Finset.mem_range, Finset.mem_map, Finset.mem_univ, true_and, Fin.valEmbedding_apply]`. Conclude with `⟨fun hi => ⟨⟨i, hi⟩, rfl⟩, fun ⟨j, hj⟩ => hj ▸ j.2⟩`.

Rewrite using `[h', Finset.map_val]`. Both sides reduce to the same expression. Rewrite using `[h, Multiset.map_map]`. Both sides reduce to the same expression.
-/
private theorem range_map_eq {α : Type} (t : ℕ) (F : ℕ → α) :
    (Finset.univ : Finset (Fin t)).val.map (fun i : Fin t => F (i : ℕ)) = (Finset.range t).val.map F := by
  have h : (Finset.range t).val = (Finset.univ : Finset (Fin t)).val.map (fun i : Fin t => (i : ℕ)) := by
    have h' : Finset.range t = (Finset.univ : Finset (Fin t)).map Fin.valEmbedding := by
      ext i
      simp only [Finset.mem_range, Finset.mem_map, Finset.mem_univ, true_and, Fin.valEmbedding_apply]
      exact ⟨fun hi => ⟨⟨i, hi⟩, rfl⟩, fun ⟨j, hj⟩ => hj ▸ j.2⟩
    rw [h', Finset.map_val]
    rfl
  rw [h, Multiset.map_map]
  rfl

/- English proof (translation)
Introduce `K _ _ w t c hc ϖ hϖ`. Establish `hv : valuation (w.adicCompletion K) (ϖ : w.adicCompletion K) = uniformizer (w.adicCompletion K)` using `GlobalTheory.MuInert.valuation_eq_uniformizer w hϖ`. Establish `hord : Formalism.UG.ordV K w (ϖ : w.adicCompletion K) = 1`. Rewrite using `[GlobalTheory.LGrp.BorelCompletion.ordV_eq, show Valued.v (ϖ : w.adicCompletion K) = _ from hϖ]`. Both sides reduce to the same expression.

Establish `h` using `GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake K w t _ _ _ (hasSatake_detRep hc hv)`. Establish `hm : GlobalTheory.LFun.seg w (c ϖ) t = (Finset.univ : Finset (Fin t)).val.map (fun i : Fin t => c ϖ * absPow (w.adicCompletion K) (((i : ℕ) : ℂ) - ((t : ℂ) - 1) / 2) ϖ)`. Rewrite using `[GlobalTheory.LFun.seg, ← range_map_eq]`. Use `Multiset.map_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 1`.

Use `ext`. Rewrite using `[GlobalTheory.SatInd.val_absPow_completion, hord]`. Simplify using `only [GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.npow, Formalism.UG.qV]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hm]`. Conclude with `h`.
-/
theorem UpperTheory.Gal.TP.Loc.satDet :
    UpperTheory.Gal.TP.Loc.SatDet := by
  intro K _ _ w t c hc ϖ hϖ
  have hv : valuation (w.adicCompletion K) (ϖ : w.adicCompletion K) = uniformizer (w.adicCompletion K) :=
    GlobalTheory.MuInert.valuation_eq_uniformizer w hϖ
  have hord : Formalism.UG.ordV K w (ϖ : w.adicCompletion K) = 1 := by
    rw [GlobalTheory.LGrp.BorelCompletion.ordV_eq, show Valued.v (ϖ : w.adicCompletion K) = _ from hϖ]
    rfl
  have h := GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake K w t _ _ _ (hasSatake_detRep hc hv)
  have hm : GlobalTheory.LFun.seg w (c ϖ) t = (Finset.univ : Finset (Fin t)).val.map
      (fun i : Fin t => c ϖ * absPow (w.adicCompletion K) (((i : ℕ) : ℂ) - ((t : ℂ) - 1) / 2) ϖ) := by
    rw [GlobalTheory.LFun.seg, ← range_map_eq]
    refine Multiset.map_congr rfl fun i _ => ?_
    congr 1
    ext
    rw [GlobalTheory.SatInd.val_absPow_completion, hord]
    simp only [GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.npow, Formalism.UG.qV]
    congr 1
    push_cast
    ring
  rw [hm]
  exact h
