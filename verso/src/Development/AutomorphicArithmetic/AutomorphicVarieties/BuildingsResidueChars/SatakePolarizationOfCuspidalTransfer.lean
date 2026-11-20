import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SdDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RInv2
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsContragredientCuspSub
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

/- English proof (translation)
Take `⟨e, he, -⟩` from `h`. Use `InvT.hasSatGL_invT e (fun g x => ?_) hB` and prove the remaining obligations. Rewrite using `[TR.CuspSub.locRep_eq, TR.CuspSub.locRep_eq, he, InvT.locGL_invT]`.
-/
private theorem hasSat_invT {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ} {π π' : TR.CuspSub F a}
    (h : IsInvTOf π π') {w : HeightOneSpectrum (𝓞 F)} {B : Multiset ℂˣ} (hB : π.HasSat w B) :
    π'.HasSat w (B.map (·⁻¹)) := by
  obtain ⟨e, he, -⟩ := h
  refine InvT.hasSatGL_invT e (fun g x => ?_) hB
  rw [TR.CuspSub.locRep_eq, TR.CuspSub.locRep_eq, he, InvT.locGL_invT]

/- English proof (translation)
Use `⟨π.toTwist χ, (TR.dchi χ).toLinearMap, fun z u hu => ?_, fun k φ => ?_, fun k φ => ?_, fun X φ => ?_⟩` and prove the remaining obligations. Establish `e : u = TR.expU z` using `Units.ext (funext hu)`. Rewrite using `[e]`. Conclude with `TR.chiInf_expU χ z`. Apply the tactic sequence `all_goals simp [TR.CuspSub.op_toTwist, TR.opMul, TR.opAdd]`.
-/
private theorem isTwistOf_twist {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ} (π : TR.CuspSub F a)
    (χ : HChar F) : IsTwistOf π χ (π.twist χ) := by
  refine ⟨π.toTwist χ, (TR.dchi χ).toLinearMap, fun z u hu => ?_, fun k φ => ?_, fun k φ => ?_, fun X φ => ?_⟩
  · have e : u = TR.expU z := Units.ext (funext hu)
    rw [e]
    exact TR.chiInf_expU χ z
  all_goals simp [TR.CuspSub.op_toTwist, TR.opMul, TR.opAdd]

/- English proof (translation)
Introduce `H F _ _ _ n hn π ψ h`. Take `⟨π₁, h₁, -⟩` from `UpperTheory.exists_contragredient_cuspSub F n π`. Take `⟨B, hl, hr', hf, hc, hX⟩` from `H.gkR F n π`. Use `isSelfDualBy_of_iso B hl hr' hf hc hX h₁ (isTwistOf_twist π₁ ψ) (H.smoR F n hn _ _ ?_)` and prove the remaining obligations. Use `filter_upwards [h] with w ⟨hu, S, hS, hE⟩`.

Use `⟨S, hS, ?_⟩` and prove the remaining obligations. Establish `e : (S.map (·⁻¹)).map (· * ψ.val w) = S`. Rewrite using `[hE, Multiset.map_map]`. Simplify using the standard rewrite rules. Conclude with `e ▸ (hasSat_invT h₁ hS).twist hu`.
-/
theorem UpperTheory.satakePolarization_of_cuspidalTransfer :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.Sol.PolSatR := by
  intro H F _ _ _ n hn π ψ h
  obtain ⟨π₁, h₁, -⟩ := UpperTheory.exists_contragredient_cuspSub F n π
  obtain ⟨B, hl, hr', hf, hc, hX⟩ := H.gkR F n π
  refine isSelfDualBy_of_iso B hl hr' hf hc hX h₁ (isTwistOf_twist π₁ ψ) (H.smoR F n hn _ _ ?_)
  filter_upwards [h] with w ⟨hu, S, hS, hE⟩
  refine ⟨S, hS, ?_⟩
  have e : (S.map (·⁻¹)).map (· * ψ.val w) = S := by
    rw [hE, Multiset.map_map]
    simp
  exact e ▸ (hasSat_invT h₁ hS).twist hu
