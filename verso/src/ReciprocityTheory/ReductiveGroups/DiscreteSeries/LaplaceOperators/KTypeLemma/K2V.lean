import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.RightHolPowerDetDiag
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.SACommSES
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.LowestKTypeLink
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.LowestKTypeVectorExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary

noncomputable section

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

/- English proof (translation)
Introduce `ε lam h H _ _ _ σ D E V s hσ hD hV hc hVK hint hanti hgap hp hq`. Take `⟨T, μ, ι, hμ, hιK, hcoef⟩` from `k2vLink n ε lam h H σ D E V hσ hD hV hc hVK hint hanti hgap hp hq`. Take `⟨hEM, hlow, hwt, hgen⟩` from `k2vM lam μ hμ`. Establish `hVst` using `hV.2.1`. Establish `: FiniteDimensional ℂ V` using `hV.1`.

Establish `hw0` using `lowestKType_vector_exists ε lam σ D E V hσ hD hV T ι hιK`. Establish `hU` using `isInfUnitary_of_isDerivedOn hσ hD`. Establish `hU' : ∀ a b, ε a = ε b → ∀ x y : D, ⟪E a b x, y⟫_ℂ = ⟪x, E b a y⟫_ℂ`. Introduce `a b hab x y`. Rewrite using `[hU a b x y, adjSign, if_pos hab, one_mul]`.

Establish `hℓ : ∀ (a : Fin n) (v w : V), (w : D) = E a a v → submoduleEvaluationFunctional V (ι.symm T.w) w = ((lowK ε lam a : ℝ) : ℂ) * submoduleEvaluationFunctional V (ι.symm T.w) v`. Introduce `a v w hw`. Establish `e1 : submoduleEvaluationFunctional V (ι.symm T.w) w = ⟪((ι.symm T.w : V) : D), (w : D)⟫_ℂ` using `rfl`. Establish `e2 : submoduleEvaluationFunctional V (ι.symm T.w) v = ⟪((ι.symm T.w : V) : D), (v : D)⟫_ℂ` using `rfl`. Rewrite using `[e1, e2, hw, ← hU' a a rfl, hw0.1 a, inner_smul_left, Complex.conj_ofReal]`.

Use `lowestKType_tensor_lift ε lam s hanti E (genSub E V) (eMM μ) (phiMM μ) hEM hlow hwt hgen (sT E V) (sθ V (eMM μ) (phiMM μ) (submoduleEvaluationFunctional V (ι.symm T.w))) (sES V) (sA ε E V hVst) (sA_isKRel ε E V hVst hD.glRep) (sT_sES E V) (sθ_sES V _ _ _) (fun a b hab => sA_comm_ …` and prove the remaining obligations. Introduce `a x`. Conclude with `sθ_sA ε E V hVst (eMM μ) hEM (phiMM μ) (lam + rho n) (lowK ε lam) hwt (submoduleEvaluationFunctional V (ι.symm T.w)) hℓ a x`. Introduce `W hW hθ`. Conclude with `lowestKType_trace ε lam h H σ D E V hσ hD hV hc hVK hint hanti hgap hp hq T μ ι hμ hιK hcoef W hW hθ`.

Introduce `μ' f hf hk`. Conclude with `lift_highestWeightVector ε E V hVst hD.glRep hU' μ' f hf hk`.
-/
theorem k2V (n : ℕ) : EigenspaceWeightConeStandard n := by
  intro ε lam h H _ _ _ σ D E V s hσ hD hV hc hVK hint hanti hgap hp hq
  obtain ⟨T, μ, ι, hμ, hιK, hcoef⟩ := k2vLink n ε lam h H σ D E V hσ hD hV hc hVK hint hanti hgap hp hq
  obtain ⟨hEM, hlow, hwt, hgen⟩ := k2vM lam μ hμ
  have hVst := hV.2.1
  have : FiniteDimensional ℂ V := hV.1
  have hw0 := lowestKType_vector_exists ε lam σ D E V hσ hD hV T ι hιK
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hU' : ∀ a b, ε a = ε b → ∀ x y : D, ⟪E a b x, y⟫_ℂ = ⟪x, E b a y⟫_ℂ := by
    intro a b hab x y
    rw [hU a b x y, adjSign, if_pos hab, one_mul]
  have hℓ : ∀ (a : Fin n) (v w : V), (w : D) = E a a v →
      submoduleEvaluationFunctional V (ι.symm T.w) w = ((lowK ε lam a : ℝ) : ℂ) * submoduleEvaluationFunctional V (ι.symm T.w) v := by
    intro a v w hw
    have e1 : submoduleEvaluationFunctional V (ι.symm T.w) w = ⟪((ι.symm T.w : V) : D), (w : D)⟫_ℂ := rfl
    have e2 : submoduleEvaluationFunctional V (ι.symm T.w) v = ⟪((ι.symm T.w : V) : D), (v : D)⟫_ℂ := rfl
    rw [e1, e2, hw, ← hU' a a rfl, hw0.1 a, inner_smul_left, Complex.conj_ofReal]
  refine lowestKType_tensor_lift ε lam s hanti E (genSub E V) (eMM μ) (phiMM μ) hEM hlow hwt hgen (sT E V)
    (sθ V (eMM μ) (phiMM μ) (submoduleEvaluationFunctional V (ι.symm T.w))) (sES V) (sA ε E V hVst)
    (sA_isKRel ε E V hVst hD.glRep) (sT_sES E V) (sθ_sES V _ _ _)
    (fun a b hab => sA_comm_sES ε E V hVst a b hab) ?_ ?_ ?_
  · intro a x
    exact sθ_sA ε E V hVst (eMM μ) hEM (phiMM μ) (lam + rho n) (lowK ε lam) hwt (submoduleEvaluationFunctional V (ι.symm T.w)) hℓ a x
  · intro W hW hθ
    exact lowestKType_trace ε lam h H σ D E V hσ hD hV hc hVK hint hanti hgap hp hq T μ ι hμ hιK hcoef W hW hθ
  · intro μ' f hf hk
    exact lift_highestWeightVector ε E V hVst hD.glRep hU' μ' f hf hk

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
