import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.BcSumSingle
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.OmegaPullSCompRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.Leaves

open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

/- English proof (translation)
Introduce `k k' _ _ _ J e M N M₀ N₀ _ _ _ _ _ _ _ _ ψ E E' ψ₀ h hψ`. Set `R : (J →₀ M₀) ≃+ (J →₀ M)` to `Finsupp.mapRange.addEquiv E.toAddEquiv`. Establish `key : ∀ f : J →₀ M₀, bcSum e ψ₀ f = E' (bcSum e ψ (R f))`. Introduce `f`. Proceed by induction on `f using Finsupp.induction_linear with`.

Consider the case `zero => simp`. Consider the case `add f g hf hg => rw [map_add, map_add, map_add, map_add, hf, hg]`. Consider the case `single j m`. Simplify using `only [R, Finsupp.mapRange.addEquiv_apply, Finsupp.mapRange_single]`. Rewrite using `[bcSum_single, bcSum_single, h, map_smul]`.

Both sides reduce to the same expression. Establish `hfun : ⇑(bcSum e ψ₀) = ⇑E' ∘ ⇑(bcSum e ψ) ∘ ⇑R` using `funext key`. Use `show Function.Bijective ⇑(bcSum e ψ₀)`. Rewrite using `[hfun]`. Conclude with `E'.bijective.comp (hψ.comp R.bijective)`.
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
