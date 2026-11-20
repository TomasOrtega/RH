import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.WhitSide

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem matchMono_of' (hψ : PsiPlaces) (hR : RealMatch) (hRc : RealConj) (hH : HeightWN) (hF : FinMatch)
    (hM : ConjMod) (hT : ValueSide) (hU : Unfold) (hK : HeightKInv) (hA : HaarFam) : MatchMono := by
  intro D n V ψ χ θ μ ω H l s ν Φ hstd hrange lam 𝓖 nb hcd w hw β hβ a k hk φ hφ
  obtain ⟨hchar, hpl⟩ := hψ D n V ψ χ θ μ ω H l s ν Φ hstd
  obtain ⟨hsch, hfock⟩ := monoSchStd D n V ψ χ θ μ ω H l s ν Φ hstd φ hφ
  obtain ⟨e, c, g, d, bs, gv, hpure, hφeq⟩ := hφ
  obtain ⟨εG, frG, PG, hfr, hreal⟩ := hR D n V ψ θ l s hstd.hθ hstd.hl hstd.hs e c a
  obtain ⟨L, hLco, hLstd, hLnu⟩ := hH D n H hstd.hH θ hstd.hθ nb hcd.1 w hw
  obtain ⟨lamS, hlamS⟩ := hA D n
  obtain ⟨L₁, L₂, Φf, Φv, hco, hstd', hpure', hΦf, hnu2⟩ :=
    hF D n V.rank a d bs g gv hpure lamS L hlamS hLco (hLstd d bs)
  obtain ⟨𝓕μ, hμ⟩ := hstd.hμ
  refine ⟨d, bs, θ, l, εG, frG, aTau θ a, PG, lamS, L₁, L₂, fun X => φ (HMul.hMul (tupOf X) a.1), Φf, Φv,
    μ.map tupInv, lam.map hermTo, ψ, ?_, npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n), ?_, ?_⟩
  · constructor
    · exact GlobalTheory.DefiniteQuotient.cmExt D
    · exact GlobalTheory.DefiniteQuotient.gram_hermND V
    · exact hrange.1
    · intro i j
      exact congrFun (congrFun β.2 i) j
    · exact hβ
    · exact hchar
    · exact hpl
    · exact hfr
    · exact hlamS
    · exact hco
    · exact hstd'
    · exact hpure'
    · intro X
      have h1 := hreal (tupOf X)
      have h2 := hΦf (tupOf X)
      rw [tupInv_tupOf] at h1 h2
      change φ (HMul.hMul (tupOf X) a.1) = _
      rw [hφeq]
      simp only
      rw [h1, h2]
    · exact sdW_map V hchar hμ
    · exact sdHerm_map hchar hcd.2
  · exact whit_side hRc hM hU hK hstd hrange hcd hw hβ a hk hsch hfock lamS hlamS L L₁ L₂ hLnu hnu2 𝓕μ hμ
  · intro μH 𝓕 hHaar hFD
    exact congrArg _ (hT D n V ν hstd.hν (fun x => φ (HMul.hMul x a.1)) β hβ μH 𝓕 hHaar hFD)

end PositivityTheory.PfSWUS.SwMatch

end
