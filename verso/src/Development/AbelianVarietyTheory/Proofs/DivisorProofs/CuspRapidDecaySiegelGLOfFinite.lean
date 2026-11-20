import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRapidDecaySiegelConeRealPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTranslatesSmoothFunctionOfCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealDiagonalInfGLEqPositiveIdeleDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetAdelicGLExistsCompactDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFormOperatorActStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ a φ hφ ω hω hωB _ t ht lam`. Take `⟨Ω, Kf, hΩ, hKf, hgeom⟩` from `GlobalTheory.T.siegelSet_adelicGL_exists_compact_decomposition E a ω hω hωB t ht`. Take `⟨S, hS⟩` from `GlobalTheory.T.finite_translates_smoothFunction_of_compact E a φ hφ.1.level Kf hKf`. Establish `hcore` using `fun f' : GL (Fin a) (Af E) => GlobalTheory.T.cuspForm_rapidDecay_siegelCone_realPoints hfin E a (finRep E a f' φ) (GlobalTheory.T.isCuspForm_operator_act hfin E a (.fin f') φ hφ) Ω hΩ t ht lam`. Use `choose C hC0 hC using hcore`.

Use `⟨∑ f' ∈ S, C f', fun b hb r hr hchain hprod k hk => ?_⟩` and prove the remaining obligations. Take `⟨d, hd, hdiag⟩` from `GlobalTheory.T.exists_realDiagonal_infGL_eq_positiveIdeleDiagonal E a r hr`. Rewrite using `[hdiag]`. Take `⟨c, hc, f, hf, heq⟩` from `hgeom r d hr hchain hd b hb k hk`. Rewrite using `[heq]`.

Take `⟨f', hf', hff'⟩` from `hS f hf`. Establish `e : φ.1 (infGL E a (d * c) * finGL E a f) = (finRep E a f' φ).1 (infGL E a (d * c))`. Rewrite using `[← hff']`. Both sides reduce to the same expression. Rewrite using `[e]`.

Use `(hC f' r d hr hchain hd hprod c hc).trans ?_` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => hC0 i) hf') (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hr i).le _)`.
-/
theorem cuspRapidDecaySiegelGL_of_finite (hfin : GlobalTheory.Published.AutomorphicFormsFiniteGL) :
    GlobalTheory.Published.CuspRapidDecaySiegelGL := by
  intro E _ _ _ a φ hφ ω hω hωB _ t ht lam
  obtain ⟨Ω, Kf, hΩ, hKf, hgeom⟩ := GlobalTheory.T.siegelSet_adelicGL_exists_compact_decomposition E a ω hω hωB t ht
  obtain ⟨S, hS⟩ := GlobalTheory.T.finite_translates_smoothFunction_of_compact E a φ hφ.1.level Kf hKf
  have hcore := fun f' : GL (Fin a) (Af E) =>
    GlobalTheory.T.cuspForm_rapidDecay_siegelCone_realPoints hfin E a (finRep E a f' φ) (GlobalTheory.T.isCuspForm_operator_act hfin E a (.fin f') φ hφ) Ω hΩ t ht lam
  choose C hC0 hC using hcore
  refine ⟨∑ f' ∈ S, C f', fun b hb r hr hchain hprod k hk => ?_⟩
  obtain ⟨d, hd, hdiag⟩ := GlobalTheory.T.exists_realDiagonal_infGL_eq_positiveIdeleDiagonal E a r hr
  rw [hdiag]
  obtain ⟨c, hc, f, hf, heq⟩ := hgeom r d hr hchain hd b hb k hk
  rw [heq]
  obtain ⟨f', hf', hff'⟩ := hS f hf
  have e : φ.1 (infGL E a (d * c) * finGL E a f) = (finRep E a f' φ).1 (infGL E a (d * c)) := by
    rw [← hff']; rfl
  rw [e]
  refine (hC f' r d hr hchain hd hprod c hc).trans ?_
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => hC0 i) hf')
    (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hr i).le _)

end GlobalTheory
