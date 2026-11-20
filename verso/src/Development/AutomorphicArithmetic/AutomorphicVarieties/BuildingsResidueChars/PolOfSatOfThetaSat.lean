import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspContragredientIsCMConjTwistOfPairedInvTranspStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

/- English proof (translation)
Introduce `hθ hJ hG E _ _ _ n hn P ψ h`. Use `GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E n P ψ (hG E n _) ?_` and prove the remaining obligations. Establish `hiso : (GlobalTheory.ThetaPull.thetaSub P).Iso (P.twist ψ⁻¹)`. Use `Quotient.exact (hJ.strong_multiplicity_one hn (CG.mk (GlobalTheory.ThetaPull.thetaSub P)) (CG.mk (P.twist ψ⁻¹)) ?_)` and prove the remaining obligations. Use `h.mono fun w ⟨hu, B, B', h1, h2, e⟩ => ⟨B'.map (·⁻¹), hθ E n P w B' h2, ?_⟩` and prove the remaining obligations.

Establish `hu' : (ψ⁻¹).UnrAt w` using `fun x hx => by`. Establish `h3 : ψ.loc w x = 1` using `hu x hx`. Conclude with `(congrArg Inv.inv h3).trans inv_one`. Rewrite using `[e]`. Conclude with `GlobalTheory.SphGal.hasSatGL_twist E n P ψ⁻¹ w B hu' h1`.

Take `⟨T, hT⟩` from `hiso`. Use `⟨((GlobalTheory.ThetaPull.pull E n).submoduleMap P.V).trans T, fun o φ => ?_⟩` and prove the remaining obligations. Conclude with `(congrArg T (Subtype.ext (GlobalTheory.ThetaPull.act_pull o φ.1).symm)).trans (hT o ((GlobalTheory.ThetaPull.pull E n).submoduleMap P.V φ))`.
-/
theorem UpperTheory.polOfSat_of_thetaSat :
    UpperTheory.V.Af.Bc.ThetaSat → UpperTheory.V.Af.Bc.PolOfSat := by
  intro hθ hJ hG E _ _ _ n hn P ψ h
  refine GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E n P ψ (hG E n _) ?_
  have hiso : (GlobalTheory.ThetaPull.thetaSub P).Iso (P.twist ψ⁻¹) := by
    refine Quotient.exact (hJ.strong_multiplicity_one hn (CG.mk (GlobalTheory.ThetaPull.thetaSub P)) (CG.mk (P.twist ψ⁻¹)) ?_)
    refine h.mono fun w ⟨hu, B, B', h1, h2, e⟩ => ⟨B'.map (·⁻¹), hθ E n P w B' h2, ?_⟩
    have hu' : (ψ⁻¹).UnrAt w := fun x hx => by
      have h3 : ψ.loc w x = 1 := hu x hx
      exact (congrArg Inv.inv h3).trans inv_one
    rw [e]
    exact GlobalTheory.SphGal.hasSatGL_twist E n P ψ⁻¹ w B hu' h1
  obtain ⟨T, hT⟩ := hiso
  refine ⟨((GlobalTheory.ThetaPull.pull E n).submoduleMap P.V).trans T, fun o φ => ?_⟩
  exact (congrArg T (Subtype.ext (GlobalTheory.ThetaPull.act_pull o φ.1).symm)).trans
    (hT o ((GlobalTheory.ThetaPull.pull E n).submoduleMap P.V φ))
