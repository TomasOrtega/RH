import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLatticeSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

noncomputable section

namespace GlobalTheory.ThK.FunFin

/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B a a' G X om om' hT f φ h v hSB hvac`. Establish `hp` using `GlobalTheory.ThK.Inhab.pairV hT`. Establish `hstd : ∀ᶠ w in cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1` using `(hvac.and hT.geo.hM.std).mono fun w hw => hw.1.trans hw.2`. Take `⟨r, hr, er⟩` from `GlobalTheory.PureFactor.exists_rest_factor v f φ hstd`. Establish `hmem : ∀ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), pure f (Function.update φ v χ) ∈ schA F (Fin a × Fin (a + a'))`.

Introduce `χ hχ`. Use `GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually φ v χ hstd)` and prove the remaining obligations. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[Function.update_self]`.

Conclude with `hχ`. Rewrite using `[Function.update_of_ne hw]`. Conclude with `hSB w`. Establish `hrange : a + a' + 2 * min (a - G.p) G.p < 2 * a ∨ min (a - G.p) G.p = 0`. Establish `h1` using `hT.geo.eBig`.

Establish `h2` using `hT.geo.lt`. Use `left`. Use linear arithmetic over natural numbers and integers. Establish `hconv : ∀ Φ ∈ schA F (Fin a × Fin (a + a')), G.M.Conv om Φ` using `fun Φ hΦ => ((GlobalTheory.T.weil_convergence_of_kernel hK F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hp hrange).1 Φ hΦ).1`. Establish `hadd : ∀ χ₁ χ₂, pure f (Function.update φ v (χ₁ + χ₂)) = pure f (Function.update φ v χ₁) + pure f (Function.update φ v χ₂)`.

Introduce `χ₁ χ₂`. Rewrite using `[← er, ← er, ← er]`. Use function extensionality and compare the values at `x`. Simplify using `only [tens, Pi.add_apply, add_mul]`. Establish `hsmul : ∀ (c : ℂ) χ, pure f (Function.update φ v (c • χ)) = c • pure f (Function.update φ v χ)`.

Introduce `c χ`. Rewrite using `[← er, ← er]`. Use function extensionality and compare the values at `x`. Simplify using `only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]`. Use `⟨fun p hp₀ q hq => ?_, fun c p hp₀ => ?_, fun g hg p hp₀ p₁ hp₁ hA => ?_⟩` and prove the remaining obligations.

Establish `e : ∀ x, theta om (pure f (Function.update φ v (p + q))) x h = theta om (pure f (Function.update φ v p)) x h + theta om (pure f (Function.update φ v q)) x h`. Introduce `x`. Simplify using `only [theta, hadd, map_add]`. Conclude with `thetaSum_add F (hp.weil.isUSplitting.pres _ _ (hmem p hp₀)) (hp.weil.isUSplitting.pres _ _ (hmem q hq))`. Simplify using `only [Model.I, e]`.

Conclude with `integral_add (hconv _ (hmem p hp₀) h) (hconv _ (hmem q hq) h)`. Simplify using `only [Model.I, theta, hsmul, map_smul, thetaSum_smul]`. Conclude with `integral_const_mul c _`. Establish `e1 : om (g, 1) (pure f (Function.update φ v p)) = pure f (Function.update φ v p₁)`. Rewrite using `[← er, ← er]`.

Conclude with `hA r ⟨hr, by rw [er]; exact hmem p hp₀⟩`. Rewrite using `[← e1, GlobalTheory.ThetaIntegralInv.integral_translate hK.base hp g _ (hmem p hp₀)]`.
-/
theorem thetaIntegral_fin : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ (f : SInf F (Fin a × Fin (a + a'))) (φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ)
      (h : UA σ G.W.J) (v : Pl F), (∀ w, φ w ∈ SB _) → (∀ᶠ w in cofinite, φ w = G.M.vac w) →
      (∀ p ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ q ∈ SB (Fin a × Fin (a + a') → Fv F v),
        G.M.I om (pure f (Function.update φ v (p + q))) h =
          G.M.I om (pure f (Function.update φ v p)) h + G.M.I om (pure f (Function.update φ v q)) h) ∧
      (∀ c : ℂ, ∀ p ∈ SB (Fin a × Fin (a + a') → Fv F v),
        G.M.I om (pure f (Function.update φ v (c • p))) h = c * G.M.I om (pure f (Function.update φ v p)) h) ∧
      ∀ g ∈ UAt σ G.V (evFin F v), ∀ p ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ p₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (g, 1)) p p₁ →
        G.M.I om (pure f (Function.update φ v p₁)) h = G.M.I om (pure f (Function.update φ v p)) h := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT f φ h v hSB hvac
  have hp := GlobalTheory.ThK.Inhab.pairV hT
  have hstd : ∀ᶠ w in cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    (hvac.and hT.geo.hM.std).mono fun w hw => hw.1.trans hw.2
  obtain ⟨r, hr, er⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
  have hmem : ∀ χ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      pure f (Function.update φ v χ) ∈ schA F (Fin a × Fin (a + a')) := by
    intro χ hχ
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually φ v χ hstd)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hχ
    · rw [Function.update_of_ne hw]; exact hSB w
  have hrange : a + a' + 2 * min (a - G.p) G.p < 2 * a ∨ min (a - G.p) G.p = 0 := by
    have h1 := hT.geo.eBig
    have h2 := hT.geo.lt
    left
    omega
  have hconv : ∀ Φ ∈ schA F (Fin a × Fin (a + a')), G.M.Conv om Φ := fun Φ hΦ =>
    ((GlobalTheory.T.weil_convergence_of_kernel hK F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hp hrange).1 Φ hΦ).1
  have hadd : ∀ χ₁ χ₂, pure f (Function.update φ v (χ₁ + χ₂)) =
      pure f (Function.update φ v χ₁) + pure f (Function.update φ v χ₂) := by
    intro χ₁ χ₂
    rw [← er, ← er, ← er]
    funext x
    simp only [tens, Pi.add_apply, add_mul]
  have hsmul : ∀ (c : ℂ) χ, pure f (Function.update φ v (c • χ)) = c • pure f (Function.update φ v χ) := by
    intro c χ
    rw [← er, ← er]
    funext x
    simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]
  refine ⟨fun p hp₀ q hq => ?_, fun c p hp₀ => ?_, fun g hg p hp₀ p₁ hp₁ hA => ?_⟩
  · have e : ∀ x, theta om (pure f (Function.update φ v (p + q))) x h =
        theta om (pure f (Function.update φ v p)) x h + theta om (pure f (Function.update φ v q)) x h := by
      intro x
      simp only [theta, hadd, map_add]
      exact thetaSum_add F (hp.weil.isUSplitting.pres _ _ (hmem p hp₀)) (hp.weil.isUSplitting.pres _ _ (hmem q hq))
    simp only [Model.I, e]
    exact integral_add (hconv _ (hmem p hp₀) h) (hconv _ (hmem q hq) h)
  · simp only [Model.I, theta, hsmul, map_smul, thetaSum_smul]
    exact integral_const_mul c _
  · have e1 : om (g, 1) (pure f (Function.update φ v p)) = pure f (Function.update φ v p₁) := by
      rw [← er, ← er]
      exact hA r ⟨hr, by rw [er]; exact hmem p hp₀⟩
    rw [← e1, GlobalTheory.ThetaIntegralInv.integral_translate hK.base hp g _ (hmem p hp₀)]

end GlobalTheory.ThK.FunFin

end
