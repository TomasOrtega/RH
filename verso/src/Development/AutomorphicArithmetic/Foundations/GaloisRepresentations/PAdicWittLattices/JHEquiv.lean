import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.BcSumSingle
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.OmegaPullSCompRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.Leaves

open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.G3.jHEquiv :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_equiv := by
  intro k k' _ _ _ J e M N M₀ N₀ _ _ _ _ _ _ _ _ ψ E E' ψ₀ h hψ
  let R : (J →₀ M₀) ≃+ (J →₀ M) := Finsupp.mapRange.addEquiv E.toAddEquiv
  have key : ∀ f : J →₀ M₀, bcSum e ψ₀ f = E' (bcSum e ψ (R f)) := by
    intro f
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [map_add, map_add, map_add, map_add, hf, hg]
    | single j m =>
      simp only [R, Finsupp.mapRange.addEquiv_apply, Finsupp.mapRange_single]
      rw [bcSum_single, bcSum_single, h, map_smul]
      rfl
  have hfun : ⇑(bcSum e ψ₀) = ⇑E' ∘ ⇑(bcSum e ψ) ∘ ⇑R := funext key
  show Function.Bijective ⇑(bcSum e ψ₀)
  rw [hfun]
  exact E'.bijective.comp (hψ.comp R.bijective)
