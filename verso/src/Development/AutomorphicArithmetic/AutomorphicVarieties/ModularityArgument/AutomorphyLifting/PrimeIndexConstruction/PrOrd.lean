import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.MixSeedPAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.OrdPlain

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Prove the second alternative. Prove the first alternative.
-/
theorem UpperTheory.V.Z.Win.Birth.prOrd :
    UpperTheory.V.Z.Win.Birth.PrOrd := by
  intro F Ω _ _ _ _ _ _ l _ ι ξ s c m a π r h
  refine ⟨π, h.reg, h.att, fun v => ?_⟩
  by_cases hB : ∃ B, π.HasSat v B
  · exact Or.inr hB
  · exact Or.inl fun σ hσ =>
      (UpperTheory.V.Z.Win.Birth.ordPlain F Ω l ι ξ s c m a π r h v σ hσ).resolve_right hB
