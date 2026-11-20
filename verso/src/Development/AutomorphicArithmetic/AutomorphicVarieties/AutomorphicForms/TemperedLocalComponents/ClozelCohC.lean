import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Wigner
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.DualIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.MsetSep
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.AlgIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.CohTransport
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible

/- English proof (translation)
Introduce `lit E _ _ _ a ha π Ξ h`. Use `choose m h1 h2 using h`. Establish `hd : ∀ τ, GlobalTheory.WignerGL.HasDualInfChar Ξ τ (m τ)` using `fun τ => (dualIff E a Ξ τ _).1 (h2 τ)`. Establish `hreg : (CG.mk π).IsRegAlg` using `(GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by`. Take `⟨m', e1, e2, e3⟩` from `GlobalTheory.AlgInfChar.exists_dualInfChar E a Ξ τ`.

Establish `e : m τ = m'` using `msetSep _ _ fun u => by haveI : Nonempty (Fin Ξ.d) := ⟨⟨0, Ξ.pos⟩⟩`. Conclude with `smul_left_injective ℂ one_ne_zero (((hd τ).2 u).symm.trans (e1.2 u))`. Establish `h3 : (CG.mk π).HasInfChar τ (m τ)` using `h1 τ`. Rewrite using `[h3.infChar_eq, e]`. Conclude with `⟨e2, e3⟩`.

Take `⟨Ξ', hΞ'⟩` from `lit.aut.coh E a ha π hreg`. Use `choose m' g1 g2 g3 using GlobalTheory.AlgInfChar.exists_dualInfChar E a Ξ'`. Establish `e : m = m'`. Assume the negation of the conclusion as `hne`. Conclude with `wigner E a π Ξ' m m' h1 g1 hne hΞ'`.

Substitute `e` using the available equality. Take `⟨T, hT⟩` from `algIso E a Ξ' Ξ (fun τ => (m τ).map Neg.neg) (fun τ => (dualIff E a Ξ' τ _).2 (g1 τ)) h2`. Conclude with `cohTransport E a π Ξ' Ξ T hT hΞ'`.
-/
theorem UpperTheory.V.Af.clozelCohC :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → UpperTheory.V.Published.ClozelCohC := by
  intro lit E _ _ _ a ha π Ξ h
  choose m h1 h2 using h
  have hd : ∀ τ, GlobalTheory.WignerGL.HasDualInfChar Ξ τ (m τ) := fun τ => (dualIff E a Ξ τ _).1 (h2 τ)
  have hreg : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    obtain ⟨m', e1, e2, e3⟩ := GlobalTheory.AlgInfChar.exists_dualInfChar E a Ξ τ
    have e : m τ = m' := msetSep _ _ fun u => by
      haveI : Nonempty (Fin Ξ.d) := ⟨⟨0, Ξ.pos⟩⟩
      exact smul_left_injective ℂ one_ne_zero (((hd τ).2 u).symm.trans (e1.2 u))
    have h3 : (CG.mk π).HasInfChar τ (m τ) := h1 τ
    rw [h3.infChar_eq, e]
    exact ⟨e2, e3⟩
  obtain ⟨Ξ', hΞ'⟩ := lit.aut.coh E a ha π hreg
  choose m' g1 g2 g3 using GlobalTheory.AlgInfChar.exists_dualInfChar E a Ξ'
  have e : m = m' := by
    by_contra hne
    exact wigner E a π Ξ' m m' h1 g1 hne hΞ'
  subst e
  obtain ⟨T, hT⟩ := algIso E a Ξ' Ξ (fun τ => (m τ).map Neg.neg) (fun τ => (dualIff E a Ξ' τ _).2 (g1 τ)) h2
  exact cohTransport E a π Ξ' Ξ T hT hΞ'
