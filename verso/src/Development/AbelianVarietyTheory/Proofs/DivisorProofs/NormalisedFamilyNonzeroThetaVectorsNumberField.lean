import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaVectorFamilyOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LineDerivListCompForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Formalism.LocalToGlobal.GlobalTheory.GL3.ProvisionExtensionLink
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgTAll

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

/- English proof (translation)
Introduce `D cc δ B χ _ _ hc hδ hχ _ N N' L L' hA`. Take `⟨h1, h2⟩` from `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.vector_bound_link D cc hc δ hδ B χ hχ N N' L L' hA`. Use `⟨h1, h2, ?_⟩` and prove the remaining obligations. Take `⟨χ', e, -, hv, -⟩` from `GlobalTheory.TrueTheta.exists_family_of_curve D cc δ ⟨hc, hδ⟩`. Take `⟨e1, e2, M, hM, hC⟩` from `hv N N' L L' hA`.

Take `⟨c, hcE⟩` from `(GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ ⟨hc, hδ⟩ N N' _ (Or.inr ⟨_, _, hA.2.2.1, hA.2.2.2, rfl⟩)).1 _ h1 _ e1 e2`. Establish `hE : B.eNat χ N N' L L' = fun z => c * e N N' L L' z` using `hcE`. Establish `hQ : ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α ∈ Qbar`. Introduce `α`. Use `GlobalTheory.ThLoc.algTAll D cc δ B χ hc hδ hχ N N' L L' hA 0 ⟨1, one_pos, by simpa using zero_mem _⟩ α` as an intermediate fact.

Establish `hU : U D B.tor 0 (B.eNat χ N N' L L') = B.eNat χ N N' L L'`. Use function extensionality and compare the values at `z`. Simplify using `[U, Hf]`. Rewrite `this` using `[hU]`. Then use the resulting hypothesis. Establish `ht : ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α = c * Formalism.MainNotions.TaylorLogMetric.taylor D (e N N' L L') α` using `fun α => by`.

Rewrite using `[hE, GlobalTheory.ProdThetaConj.taylor_const_mul e1.1]`. Choose the witnesses or unpack the hypotheses as in `⟨α, hα⟩ : ∃ α, Formalism.MainNotions.TaylorLogMetric.taylor D (e N N' L L') α ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `e2` to reduce the goal to its premises.

Use function extensionality and compare the values at `z`. Rewrite using `[← GlobalTheory.ProdThetaConj.tsum_taylor_mono D e1.1 z]`. Simplify using `[h]`. Establish `hMQ : ∀ x ∈ M, x ∈ Qbar` using `fun x hx => mem_algebraicClosure_iff.2 (IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic (⟨x, hx⟩ : M)))`. Establish `hcQ : c ∈ Qbar`.

Establish `: c = Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α / Formalism.MainNotions.TaylorLogMetric.taylor D (e N N' L L') α` using `by rw [ht, mul_div_cancel_right₀ _ hα]`. Rewrite using `[this]`. Conclude with `div_mem (hQ α) (hMQ _ (hC α))`. Use `haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {c}) := IntermediateField.adjoin.finiteDimensional (mem_algebraicClosure_iff.1 hcQ).isIntegral`. Use `⟨M ⊔ IntermediateField.adjoin ℚ {c}, IntermediateField.finiteDimensional_sup _ _, fun β => ?_⟩` and prove the remaining obligations.

Rewrite using `[ht]`. Conclude with `mul_mem ((le_sup_right : IntermediateField.adjoin ℚ {c} ≤ _) (IntermediateField.subset_adjoin ℚ {c} (Set.mem_singleton _))) ((le_sup_left : M ≤ _) (hC β))`.
-/
theorem GlobalTheory.ColNorms.familyVectors : GlobalTheory.ColNorms.FamilyVectors := by
  intro D cc δ B χ _ _ hc hδ hχ _ N N' L L' hA
  obtain ⟨h1, h2⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.vector_bound_link D cc hc δ hδ B χ hχ N N' L L' hA
  refine ⟨h1, h2, ?_⟩
  obtain ⟨χ', e, -, hv, -⟩ := GlobalTheory.TrueTheta.exists_family_of_curve D cc δ ⟨hc, hδ⟩
  obtain ⟨e1, e2, M, hM, hC⟩ := hv N N' L L' hA
  obtain ⟨c, hcE⟩ := (GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ ⟨hc, hδ⟩ N N' _
    (Or.inr ⟨_, _, hA.2.2.1, hA.2.2.2, rfl⟩)).1 _ h1 _ e1 e2
  have hE : B.eNat χ N N' L L' = fun z => c * e N N' L L' z := hcE
  have hQ : ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α ∈ Qbar := by
    intro α
    have := GlobalTheory.ThLoc.algTAll D cc δ B χ hc hδ hχ N N' L L' hA 0 ⟨1, one_pos, by simpa using zero_mem _⟩ α
    have hU : U D B.tor 0 (B.eNat χ N N' L L') = B.eNat χ N N' L L' := by
      funext z; simp [U, Hf]
    rwa [hU] at this
  have ht : ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α = c * Formalism.MainNotions.TaylorLogMetric.taylor D (e N N' L L') α := fun α => by
    rw [hE, GlobalTheory.ProdThetaConj.taylor_const_mul e1.1]
  obtain ⟨α, hα⟩ : ∃ α, Formalism.MainNotions.TaylorLogMetric.taylor D (e N N' L L') α ≠ 0 := by
    by_contra h
    push_neg at h
    apply e2
    funext z
    rw [← GlobalTheory.ProdThetaConj.tsum_taylor_mono D e1.1 z]
    simp [h]
  have hMQ : ∀ x ∈ M, x ∈ Qbar := fun x hx => mem_algebraicClosure_iff.2
    (IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic (⟨x, hx⟩ : M)))
  have hcQ : c ∈ Qbar := by
    have : c = Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α / Formalism.MainNotions.TaylorLogMetric.taylor D (e N N' L L') α := by rw [ht, mul_div_cancel_right₀ _ hα]
    rw [this]
    exact div_mem (hQ α) (hMQ _ (hC α))
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {c}) :=
    IntermediateField.adjoin.finiteDimensional (mem_algebraicClosure_iff.1 hcQ).isIntegral
  refine ⟨M ⊔ IntermediateField.adjoin ℚ {c}, IntermediateField.finiteDimensional_sup _ _, fun β => ?_⟩
  rw [ht]
  exact mul_mem ((le_sup_right : IntermediateField.adjoin ℚ {c} ≤ _) (IntermediateField.subset_adjoin ℚ {c} (Set.mem_singleton _)))
    ((le_sup_left : M ≤ _) (hC β))
