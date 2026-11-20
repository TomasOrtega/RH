import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdmissibleOfRankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOfSamePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRecLawsSuppUnitSurj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TempGal

open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp

/- English proof (translation)
Introduce `π w σ _ α hα`. Take `⟨ξ, hξ, -, hξu⟩` from `GlobalTheory.HeckeComp.main D.host.E (P.chr.e1 π).1 w`. Establish `he` using `GlobalTheory.RankOneComp.locG_rankOne_eq_rcAt hAF hL D P π w ξ hξ`. Rewrite `hα` using `[WDTie.eig, he]`. Unfold `WD.inePol at hα`.

Use `split_ifs at hα with hσ`. Conclude with `GlobalTheory.LocLanglands.IsRec.recUnit (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 w)) ξ (Irr.ofDet 1 ξ hξ.1) (hξu (P.chr.e1 π).2) ⟨Representation.Equiv.refl _⟩ ⟨σ, hσ⟩ α hα`. Simplify using `at hα`.
-/
theorem rankOneUnitary (hAF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7)
    (P : Pin hL D) : RankOneUnitary P.T := by
  intro π w σ _ α hα
  obtain ⟨ξ, hξ, -, hξu⟩ := GlobalTheory.HeckeComp.main D.host.E (P.chr.e1 π).1 w
  have he := GlobalTheory.RankOneComp.locG_rankOne_eq_rcAt hAF hL D P π w ξ hξ
  rw [WDTie.eig, he] at hα
  unfold WD.inePol at hα
  split_ifs at hα with hσ
  · exact GlobalTheory.LocLanglands.IsRec.recUnit (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 w)) ξ
      (Irr.ofDet 1 ξ hξ.1) (hξu (P.chr.e1 π).2) ⟨Representation.Equiv.refl _⟩ ⟨σ, hσ⟩ α hα
  · simp at hα

/- English proof (translation)
Use `host_isCMField D.host` as an intermediate fact. Establish `ha1 : 1 ≤ a` using `by omega`. Take `⟨π₀, hπ₀⟩` from `Quotient.exists_rep (P.cg.e a π).1`. Establish `hmk : CG.mk π₀ = (P.cg.e a π).1` using `hπ₀`. Establish `hc₀ : π₀.IsCsd`.

Establish `h1` using `(P.cg.csd a π).1 hc`. Rewrite `h1` using `[CGu.IsCsd, ← hmk]`. Conclude with `h1`. Establish `hinf : ∀ τ, D.naut.infG π τ = (CG.mk π₀).infChar τ` using `fun τ => by`. Rewrite using `[P.cg.inf, CGu.infChar, ← hmk]`.

Establish `hr₀ : (CG.mk π₀).IsRegAlg` using `(GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by`. Use `(D.naut.ralg_def π).1 hr τ` as an intermediate fact. Rewrite `this` using `[hinf]`. Then use the resulting hypothesis. Take `⟨r, wt, HT, H⟩` from `hG.of_isCsd D.nd.Om ι ha1 hr₀ hc₀`. Establish `hloc : ∀ (w : PlE D.host) (u : ℝ), P.T.e w (D.naut.lpTw (D.naut.locG π w) u) = (ParLaws.locPar hL (CG.mk π₀) (D.nd.plOm.2 w)).lpTw u` using `fun w u => by`.

Rewrite using `[P.T.tw, P.cg.loc, hmk]`. Both sides reduce to the same expression. Establish `haway : ∀ (w : PlE D.host) (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal), wdOf (D.nd.plOm.2 w) hl ι r = P.T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))` using `fun w hl => by`. Rewrite using `[GlobalTheory.GalFirstClause.wdOfEqLocPar hL hF H hl, hloc]`. Establish `hv : (1 - (a : ℝ)) / 2 + (wt : ℝ) / 2 = 0`.

Use `GlobalTheory.GalFirstClause.exponentEqZero D.naut ha1 π hc l _ fun w hl => ?_` and prove the remaining obligations. Establish `h1` using `H.tempered_wdOf hl (D.nd.plOm.2 w)`. Rewrite `h1` using `[haway w hl, ← P.T.tw, ← P.T.tempered, D.naut.lpTw_add]`. Conclude with `h1`. Establish `h1` using `H.tempered_wdOf hlw (D.nd.plOm.2 w)`.

Rewrite `h1` using `[haway w hlw, ← P.T.tw, ← P.T.tempered, D.naut.lpTw_add, hv, D.naut.lpTw_zero]`. Conclude with `h1`.
-/
theorem temperedAway (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal)
    (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (a : ℕ) (π : D.naut.CG a) (ha : 2 ≤ a)
    (hc : D.naut.csd π) (hr : D.naut.ralg π) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : PlE D.host)
    (hlw : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) : D.naut.tempered (D.naut.locG π w) := by
  have := host_isCMField D.host
  have ha1 : 1 ≤ a := by omega
  obtain ⟨π₀, hπ₀⟩ := Quotient.exists_rep (P.cg.e a π).1
  have hmk : CG.mk π₀ = (P.cg.e a π).1 := hπ₀
  have hc₀ : π₀.IsCsd := by
    have h1 := (P.cg.csd a π).1 hc
    rw [CGu.IsCsd, ← hmk] at h1
    exact h1
  have hinf : ∀ τ, D.naut.infG π τ = (CG.mk π₀).infChar τ := fun τ => by
    rw [P.cg.inf, CGu.infChar, ← hmk]
  have hr₀ : (CG.mk π₀).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [hinf] at this
  obtain ⟨r, wt, HT, H⟩ := hG.of_isCsd D.nd.Om ι ha1 hr₀ hc₀
  have hloc : ∀ (w : PlE D.host) (u : ℝ), P.T.e w (D.naut.lpTw (D.naut.locG π w) u) =
      (ParLaws.locPar hL (CG.mk π₀) (D.nd.plOm.2 w)).lpTw u := fun w u => by
    rw [P.T.tw, P.cg.loc, hmk]
    rfl
  have haway : ∀ (w : PlE D.host) (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
      wdOf (D.nd.plOm.2 w) hl ι r = P.T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) := fun w hl => by
    rw [GlobalTheory.GalFirstClause.wdOfEqLocPar hL hF H hl, hloc]
  have hv : (1 - (a : ℝ)) / 2 + (wt : ℝ) / 2 = 0 := by
    refine GlobalTheory.GalFirstClause.exponentEqZero D.naut ha1 π hc l _ fun w hl => ?_
    have h1 := H.tempered_wdOf hl (D.nd.plOm.2 w)
    rw [haway w hl, ← P.T.tw, ← P.T.tempered, D.naut.lpTw_add] at h1
    exact h1
  have h1 := H.tempered_wdOf hlw (D.nd.plOm.2 w)
  rw [haway w hlw, ← P.T.tw, ← P.T.tempered, D.naut.lpTw_add, hv, D.naut.lpTw_zero] at h1
  exact h1

/- English proof (translation)
Distinguish the cases in `h2 : ((2 : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal`. Establish `h3 : ((3 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal` using `fun h3 => w.isPrime.ne_top <| by`. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `e : ((3 : ℕ) : 𝓞 D.host.E) - ((2 : ℕ) : 𝓞 D.host.E) = 1` using `by push_cast; ring`. Rewrite using `[← e]`.

Conclude with `w.asIdeal.sub_mem h3 h2`. Take `⟨ι⟩ : Nonempty (Qbar 3 ≃+* ℂ)` from `GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 3`. Conclude with `temperedAway hF hG hL D P a π ha hc hr 3 ι w h3`. Take `⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ)` from `GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2`. Conclude with `temperedAway hF hG hL D P a π ha hc hr 2 ι w h2`.
-/
theorem rankTwo (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal)
    (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (a : ℕ) (π : D.naut.CG a) (ha : 2 ≤ a)
    (hc : D.naut.csd π) (hr : D.naut.ralg π) (w : PlE D.host) : D.naut.tempered (D.naut.locG π w) := by
  by_cases h2 : ((2 : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
  · have h3 : ((3 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun h3 => w.isPrime.ne_top <| by
      rw [Ideal.eq_top_iff_one]
      have e : ((3 : ℕ) : 𝓞 D.host.E) - ((2 : ℕ) : 𝓞 D.host.E) = 1 := by push_cast; ring
      rw [← e]
      exact w.asIdeal.sub_mem h3 h2
    obtain ⟨ι⟩ : Nonempty (Qbar 3 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 3
    exact temperedAway hF hG hL D P a π ha hc hr 3 ι w h3
  · obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
    exact temperedAway hF hG hL D P a π ha hc hr 2 ι w h2

/- English proof (translation)
Introduce `hF hG hL D P`. Conclude with `admissible_of_rank_one_unitary D P.T (rankOneUnitary hF hL D P) (fun a π ha hc hr w => rankTwo hF hG hL D P a π ha hc hr w)`.
-/
theorem main : GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), Formalism.MainNotions.SumRepresentations.adm7 D := by
  intro hF hG hL D P
  exact admissible_of_rank_one_unitary D P.T (rankOneUnitary hF hL D P)
    (fun a π ha hc hr w => rankTwo hF hG hL D P a π ha hc hr w)

end GlobalTheory.TempGal
