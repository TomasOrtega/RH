import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultisetSeparation

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.FactorLimProof

/- English proof (translation)
Apply the tactic sequence `apply _root_.UpperTheory.Reformulated.B.MultisetSeparation.msetSep <;> assumption`.
-/
theorem multiset_eq_of_prod_shift {m m' : Multiset ℂ}
    (h : ∀ u : ℂ, (m.map (u + ·)).prod = (m'.map (u + ·)).prod) : m = m' :=
  by apply _root_.UpperTheory.Reformulated.B.MultisetSeparation.msetSep <;> assumption

/- English proof (translation)
Introduce `_ hLT hLB hCI hIE hCE hMF hTS hGr hIT E _ _ _ Θs Θf Ωs Ωf N t ψ m n B hLim hRA hRed hGood hAll hψ hψ0 hCap hB hCl`. Establish `leaf` using `fun k => hLB E N (t k) (ψ k) (m k) B hIT (hGood k) (hψ k) (hψ0 k) (hCap k) (hB k)`. Take `⟨φ, t', s, hφ, hConv, hRs, hGs, hAs, hDisc, hEmb⟩` from `hLT hTS hGr E Θs Θf Ωs Ωf N hLim hRA N le_rfl t (2 * B) hRed hGood hAll leaf`. Use `⟨φ, t', s, hφ, hConv, hRs, hGs, hAs, hDisc, fun τ => ?_, hEmb⟩` and prove the remaining obligations. Take `⟨m₀, mk, hs, hk, hprod⟩` from `hCI E N t' s τ hConv hGs`.

Establish `hst : ∀ k, IsStable (t (φ k)).space` using `fun k => hTS E N _ (disc_stable (good_disc (hGood _)))`. Establish `hmk : ∀ k, mk k = m (φ k) τ`. Introduce `k`. Take `⟨e, he1, he2, he3⟩` from `hEmb k`. Establish `hne : e (ψ (φ k)) ≠ 0` using `fun h => hψ0 _ (he2 _ (hψ _) h)`.

Establish `hc : CapEig (e (ψ (φ k))) (m (φ k))` using `hCE E N _ e _ _ (hst k) he3 (hψ _) (hCap _)`. Conclude with `hIE E N (t' k) _ _ τ _ hIT (hk k) (he1 _ (hψ _)) hne hc`. Establish `hlim : ∀ u : ℂ, Tendsto (fun k => ((m (φ k) τ).map (u + ·)).prod) atTop (𝓝 (((n τ).map (u + ·)).prod))` using `fun u => hMF.2.2 (fun k => m (φ k) τ) (n τ) (fun ε hε => hφ.tendsto_atTop.eventually (hCl τ ε hε)) u`. Establish `hm₀ : m₀ = n τ` using `multiset_eq_of_prod_shift fun u => tendsto_nhds_unique (by simpa only [hmk] using hprod u) (hlim u)`. Conclude with `hm₀ ▸ hIT E N s τ m₀ hs`.
-/
theorem factorLim_of_parts : GlobalTheory.CompanionTheory.EGlue.ConvComp → GlobalTheory.CompanionTheory.EGlue.LimTrees → GlobalTheory.CompanionTheory.EGlue.LeafBound →
    GlobalTheory.CompanionTheory.EGlue.ConvInf → GlobalTheory.CompanionTheory.EGlue.InfOfEq → GlobalTheory.CompanionTheory.EGlue.CapEquiv → GlobalTheory.CompanionTheory.EGlue.MCloseFacts →
    GlobalTheory.CompanionTheory.EGlue.FactorLim := by
  intro _ hLT hLB hCI hIE hCE hMF hTS hGr hIT E _ _ _ Θs Θf Ωs Ωf N t ψ m n B hLim hRA hRed hGood hAll hψ hψ0 hCap hB hCl
  have leaf := fun k => hLB E N (t k) (ψ k) (m k) B hIT (hGood k) (hψ k) (hψ0 k) (hCap k) (hB k)
  obtain ⟨φ, t', s, hφ, hConv, hRs, hGs, hAs, hDisc, hEmb⟩ :=
    hLT hTS hGr E Θs Θf Ωs Ωf N hLim hRA N le_rfl t (2 * B) hRed hGood hAll leaf
  refine ⟨φ, t', s, hφ, hConv, hRs, hGs, hAs, hDisc, fun τ => ?_, hEmb⟩
  obtain ⟨m₀, mk, hs, hk, hprod⟩ := hCI E N t' s τ hConv hGs
  have hst : ∀ k, IsStable (t (φ k)).space := fun k =>
    hTS E N _ (disc_stable (good_disc (hGood _)))
  have hmk : ∀ k, mk k = m (φ k) τ := by
    intro k
    obtain ⟨e, he1, he2, he3⟩ := hEmb k
    have hne : e (ψ (φ k)) ≠ 0 := fun h => hψ0 _ (he2 _ (hψ _) h)
    have hc : CapEig (e (ψ (φ k))) (m (φ k)) := hCE E N _ e _ _ (hst k) he3 (hψ _) (hCap _)
    exact hIE E N (t' k) _ _ τ _ hIT (hk k) (he1 _ (hψ _)) hne hc
  have hlim : ∀ u : ℂ, Tendsto (fun k => ((m (φ k) τ).map (u + ·)).prod) atTop
      (𝓝 (((n τ).map (u + ·)).prod)) := fun u =>
    hMF.2.2 (fun k => m (φ k) τ) (n τ)
      (fun ε hε => hφ.tendsto_atTop.eventually (hCl τ ε hε)) u
  have hm₀ : m₀ = n τ := multiset_eq_of_prod_shift fun u =>
    tendsto_nhds_unique (by simpa only [hmk] using hprod u) (hlim u)
  exact hm₀ ▸ hIT E N s τ m₀ hs

end GlobalTheory.CompanionTheory.EGlue.FactorLimProof
