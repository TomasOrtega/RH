import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureFundamentalDomainLtTop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemidirectHaarMeasureFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupSemidirectProductRational
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBesselGroupsClosedHaarProduct
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesselQuot

/- English proof (translation)
Introduce `D ρ B`. Take `⟨-, hcl, hHaar⟩` from `GlobalTheory.MixPer.jacGrp_besGrp_haar D B.V B.V₀ B.A B.L ρ B.d B.o B.vN.ν B.vN.𝓝 B.vN.unit`. Establish `hμR : B.μR.IsHaarMeasure` using `hHaar B.vA.μ B.vA.haar`. Take `⟨hsc, hNcl, hnorm, huniq, hrat⟩` from `GlobalTheory.Unf.besSemi D ρ B`. Take `⟨⟨KN, hKN, hKNcov⟩, -⟩` from `GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B.V ρ B.d.e (GlobalTheory.MixPer.isIsoSub_e B.d)`.

Take `⟨KA, hKA, hKAcov⟩` from `B.cpt`. Establish `hγA : ∀ γ ∈ GQ B.A, embA B.d B.o γ ∈ GQ B.V` using `fun γ hγ => by`. Establish `h1` using `(hrat 1 (one_mem _) γ).2 ⟨one_mem _, hγ⟩`. Simplify using `using h1`. Use `set Ω : Set (GA D B.V) := (fun p : GA D B.V × GA D B.A => p.1 * embA B.d B.o p.2) '' ((Subtype.val '' KN) ×ˢ KA) with hΩ`.

Establish `hΩc : IsCompact Ω` using `((hKN.image continuous_subtype_val).prod hKA).image (continuous_fst.mul (hsc.comp continuous_snd))`. Establish `hΩsub : Ω ⊆ (besGrp B.d B.o : Set (GA D B.V))`. Introduce and unpack `_ ⟨⟨_, a⟩, ⟨⟨k, hk, rfl⟩, -⟩, rfl⟩`. Conclude with `mul_mem (Subgroup.mem_sup_left k.2) (Subgroup.mem_sup_right ⟨a, rfl⟩)`. Establish `hcov : ∀ s ∈ besGrp B.d B.o, ∃ γ ∈ GQ B.V ⊓ besGrp B.d B.o, γ * s ∈ Ω`.

Introduce `s hs`. Take `⟨n, hn, a, rfl⟩` from `(GlobalTheory.CharLaws.mem_besGrp B.d B.o s).1 hs`. Take `⟨γA, hγAQ, hγAK⟩` from `hKAcov a`. Establish `hn1 : embA B.d B.o γA * n * (embA B.d B.o γA)⁻¹ ∈ flagN B.d` using `hnorm n hn γA`. Take `⟨γN, hγN, k, hk, he⟩` from `hKNcov ⟨_, hn1⟩`.

Establish `he' : embA B.d B.o γA * n * (embA B.d B.o γA)⁻¹ = γN.1 * k.1` using `congrArg Subtype.val he`. Establish `hk1 : k.1 = γN.1⁻¹ * (embA B.d B.o γA * n * (embA B.d B.o γA)⁻¹)` using `eq_inv_mul_of_mul_eq he'.symm`. Establish `hQ : γN.1⁻¹ * embA B.d B.o γA ∈ GQ B.V` using `Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.1 hγN)) (hγA γA hγAQ)`. Establish `hR : γN.1⁻¹ * embA B.d B.o γA ∈ besGrp B.d B.o` using `Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left γN.2)) (Subgroup.mem_sup_right ⟨γA, rfl⟩)`. Use `⟨γN.1⁻¹ * embA B.d B.o γA, Subgroup.mem_inf.2 ⟨hQ, hR⟩, ?_⟩` and prove the remaining obligations.

Use `⟨(k.1, γA * a), ⟨⟨k, hk, rfl⟩, hγAK⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [hk1, map_mul]`. Use `group`. Establish `hcovA : ∀ g : GA D B.A, ∃ γ ∈ GQ B.A, ∃ k ∈ KA, g = γ * k` using `fun g => by`. Take `⟨γ, hγ, hk⟩` from `hKAcov g`.

Conclude with `⟨γ⁻¹, Subgroup.inv_mem _ hγ, γ * g, hk, by group⟩`. Use `B.vA.haar` as an intermediate fact. Establish `hFfin : B.vA.μ B.vA.𝓕 < ⊤` using `GlobalTheory.BesselConvDefinite.measure_fundamentalDomain_lt_top (GQ B.A) hKA hcovA B.vA.μ B.vA.fund`. Establish `hNfin : B.vN.ν B.vN.𝓝 < ⊤` using `by rw [B.vN.unit.2.2]; exact ENNReal.one_lt_top`. Take `⟨𝓡, hfd, hint⟩` from `GlobalTheory.Unf.semiFd_iterated D B.V B.A (flagN B.d) (embA B.d B.o) hsc hNcl hnorm huniq hrat B.vA B.vN.ν B.vN.𝓝 B.vN.unit.1 B.vN.unit.2.1 hμR`.

Establish `: IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕)` using `isFiniteMeasure_restrict.2 hFfin.ne`. Establish `: IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝)` using `isFiniteMeasure_restrict.2 hNfin.ne`. Use `⟨hμR, hcl, ⟨Ω, hΩc, hcov⟩, 𝓡, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Subgroup.inf_subgroupOf_right]`. Conclude with `hfd`.

Establish `h1` using `(hint (fun _ => (1 : ℂ)) measurable_const).1.2 (integrable_const _)`. Conclude with `((integrableOn_const_iff).1 h1).resolve_left (by simp)`. Introduce `F hF hinv classical set F' : GA D B.V → ℂ := (besGrp B.d B.o : Set (GA D B.V)).piecewise F 0 with hF'`. Establish `hF'm : Measurable F'` using `hF.measurable_piecewise continuousOn_const hcl.measurableSet`. Take `⟨C, hC⟩` from `hΩc.exists_bound_of_continuousOn (hF.mono hΩsub)`.

Establish `hb : ∀ x, ‖F' x‖ ≤ max C 0`. Introduce `x`. Distinguish the cases in `hx : x ∈ (besGrp B.d B.o : Set (GA D B.V))`. Take `⟨γ, hγ, hγx⟩` from `hcov x hx`. Rewrite using `[hF', Set.piecewise_eq_of_mem _ _ _ hx, ← hinv γ hγ x hx]`.

Conclude with `(hC _ hγx).trans (le_max_left _ _)`. Rewrite using `[hF', Set.piecewise_eq_of_notMem _ _ _ hx]`. Simplify using the standard rewrite rules. Establish `hAC : AbsConv B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝 fun h n => F' (n.1 * embA B.d B.o h)`. Use `Integrable.of_bound ?_ (max C 0) (Filter.Eventually.of_forall fun p => hb _)` and prove the remaining obligations.

Conclude with `(hF'm.comp ((continuous_subtype_val.comp continuous_snd).mul (hsc.comp continuous_fst)).measurable).aestronglyMeasurable`. Establish `hpt : ∀ r : ↥(flagN B.d ⊔ (embA B.d B.o).range), F' r = F r` using `fun r => Set.piecewise_eq_of_mem _ _ _ r.2`. Establish `hpt2 : ∀ a (n : flagN B.d), F' (n.1 * embA B.d B.o a) = F (n.1 * embA B.d B.o a)` using `fun a n => Set.piecewise_eq_of_mem _ _ _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨a, rfl⟩))`. Take `⟨hi1, hi2⟩` from `hint F' hF'm`. Establish `e1 : (fun r : ↥(flagN B.d ⊔ (embA B.d B.o).range) => F' r) = fun r : ↥(flagN B.d ⊔ (embA B.d B.o).range) => F r` using `funext hpt`.

Establish `e2 : (fun a => ∫ n in B.vN.𝓝, F' (n.1 * embA B.d B.o a) ∂B.vN.ν) = fun a => ∫ n in B.vN.𝓝, F (n.1 * embA B.d B.o a) ∂B.vN.ν` using `funext fun a => by simp only [hpt2]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h3` using `hi1.2 hAC`. Rewrite `h3` using `[e1]`. Conclude with `h3`.

Establish `h3` using `hi2 hAC`. Rewrite `h3` using `[e1, e2]`. Conclude with `h3`.
-/
theorem besGrp_quotient : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ), B.μR.IsHaarMeasure ∧ IsClosed (besGrp B.d B.o : Set (GA D B.V)) ∧ (∃ Ω : Set (GA D B.V), IsCompact Ω ∧ ∀ s ∈ besGrp B.d B.o, ∃ γ ∈ GQ B.V ⊓ besGrp B.d B.o, γ * s ∈ Ω) ∧ ∃ 𝓢 : Set (besGrp B.d B.o), IsFundamentalDomain ((GQ B.V).subgroupOf (besGrp B.d B.o)) 𝓢 B.μR ∧ B.μR 𝓢 < ⊤ ∧ ∀ F : GA D B.V → ℂ, ContinuousOn F (besGrp B.d B.o : Set (GA D B.V)) → (∀ γ ∈ GQ B.V ⊓ besGrp B.d B.o, ∀ s ∈ besGrp B.d B.o, F (γ * s) = F s) → IntegrableOn (fun s : besGrp B.d B.o => F s) 𝓢 B.μR ∧ ∫ s in 𝓢, F s ∂B.μR = ∫ a in B.vA.𝓕, ∫ n in B.vN.𝓝, F (n.1 * embA B.d B.o a) ∂B.vN.ν ∂B.vA.μ := by
  intro D ρ B
  obtain ⟨-, hcl, hHaar⟩ := GlobalTheory.MixPer.jacGrp_besGrp_haar D B.V B.V₀ B.A B.L ρ B.d B.o B.vN.ν B.vN.𝓝 B.vN.unit
  have hμR : B.μR.IsHaarMeasure := hHaar B.vA.μ B.vA.haar
  obtain ⟨hsc, hNcl, hnorm, huniq, hrat⟩ := GlobalTheory.Unf.besSemi D ρ B
  obtain ⟨⟨KN, hKN, hKNcov⟩, -⟩ :=
    GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B.V ρ B.d.e (GlobalTheory.MixPer.isIsoSub_e B.d)
  obtain ⟨KA, hKA, hKAcov⟩ := B.cpt
  have hγA : ∀ γ ∈ GQ B.A, embA B.d B.o γ ∈ GQ B.V := fun γ hγ => by
    have h1 := (hrat 1 (one_mem _) γ).2 ⟨one_mem _, hγ⟩
    simpa using h1
  set Ω : Set (GA D B.V) := (fun p : GA D B.V × GA D B.A => p.1 * embA B.d B.o p.2) '' ((Subtype.val '' KN) ×ˢ KA) with hΩ
  have hΩc : IsCompact Ω :=
    ((hKN.image continuous_subtype_val).prod hKA).image (continuous_fst.mul (hsc.comp continuous_snd))
  have hΩsub : Ω ⊆ (besGrp B.d B.o : Set (GA D B.V)) := by
    rintro _ ⟨⟨_, a⟩, ⟨⟨k, hk, rfl⟩, -⟩, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left k.2) (Subgroup.mem_sup_right ⟨a, rfl⟩)
  have hcov : ∀ s ∈ besGrp B.d B.o, ∃ γ ∈ GQ B.V ⊓ besGrp B.d B.o, γ * s ∈ Ω := by
    intro s hs
    obtain ⟨n, hn, a, rfl⟩ := (GlobalTheory.CharLaws.mem_besGrp B.d B.o s).1 hs
    obtain ⟨γA, hγAQ, hγAK⟩ := hKAcov a
    have hn1 : embA B.d B.o γA * n * (embA B.d B.o γA)⁻¹ ∈ flagN B.d := hnorm n hn γA
    obtain ⟨γN, hγN, k, hk, he⟩ := hKNcov ⟨_, hn1⟩
    have he' : embA B.d B.o γA * n * (embA B.d B.o γA)⁻¹ = γN.1 * k.1 := congrArg Subtype.val he
    have hk1 : k.1 = γN.1⁻¹ * (embA B.d B.o γA * n * (embA B.d B.o γA)⁻¹) := eq_inv_mul_of_mul_eq he'.symm
    have hQ : γN.1⁻¹ * embA B.d B.o γA ∈ GQ B.V :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.1 hγN)) (hγA γA hγAQ)
    have hR : γN.1⁻¹ * embA B.d B.o γA ∈ besGrp B.d B.o :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left γN.2)) (Subgroup.mem_sup_right ⟨γA, rfl⟩)
    refine ⟨γN.1⁻¹ * embA B.d B.o γA, Subgroup.mem_inf.2 ⟨hQ, hR⟩, ?_⟩
    refine ⟨(k.1, γA * a), ⟨⟨k, hk, rfl⟩, hγAK⟩, ?_⟩
    simp only [hk1, map_mul]
    group
  have hcovA : ∀ g : GA D B.A, ∃ γ ∈ GQ B.A, ∃ k ∈ KA, g = γ * k := fun g => by
    obtain ⟨γ, hγ, hk⟩ := hKAcov g
    exact ⟨γ⁻¹, Subgroup.inv_mem _ hγ, γ * g, hk, by group⟩
  have := B.vA.haar
  have hFfin : B.vA.μ B.vA.𝓕 < ⊤ :=
    GlobalTheory.BesselConvDefinite.measure_fundamentalDomain_lt_top (GQ B.A) hKA hcovA B.vA.μ B.vA.fund
  have hNfin : B.vN.ν B.vN.𝓝 < ⊤ := by rw [B.vN.unit.2.2]; exact ENNReal.one_lt_top
  obtain ⟨𝓡, hfd, hint⟩ := GlobalTheory.Unf.semiFd_iterated D B.V B.A (flagN B.d) (embA B.d B.o) hsc hNcl hnorm huniq hrat B.vA
    B.vN.ν B.vN.𝓝 B.vN.unit.1 B.vN.unit.2.1 hμR
  have : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.2 hFfin.ne
  have : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 hNfin.ne
  refine ⟨hμR, hcl, ⟨Ω, hΩc, hcov⟩, 𝓡, ?_, ?_, ?_⟩
  · rw [← Subgroup.inf_subgroupOf_right]; exact hfd
  · have h1 := (hint (fun _ => (1 : ℂ)) measurable_const).1.2 (integrable_const _)
    exact ((integrableOn_const_iff).1 h1).resolve_left (by simp)
  · intro F hF hinv
    classical
    set F' : GA D B.V → ℂ := (besGrp B.d B.o : Set (GA D B.V)).piecewise F 0 with hF'
    have hF'm : Measurable F' := hF.measurable_piecewise continuousOn_const hcl.measurableSet
    obtain ⟨C, hC⟩ := hΩc.exists_bound_of_continuousOn (hF.mono hΩsub)
    have hb : ∀ x, ‖F' x‖ ≤ max C 0 := by
      intro x
      by_cases hx : x ∈ (besGrp B.d B.o : Set (GA D B.V))
      · obtain ⟨γ, hγ, hγx⟩ := hcov x hx
        rw [hF', Set.piecewise_eq_of_mem _ _ _ hx, ← hinv γ hγ x hx]
        exact (hC _ hγx).trans (le_max_left _ _)
      · rw [hF', Set.piecewise_eq_of_notMem _ _ _ hx]; simp
    have hAC : AbsConv B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝 fun h n => F' (n.1 * embA B.d B.o h) := by
      refine Integrable.of_bound ?_ (max C 0) (Filter.Eventually.of_forall fun p => hb _)
      exact (hF'm.comp ((continuous_subtype_val.comp continuous_snd).mul
        (hsc.comp continuous_fst)).measurable).aestronglyMeasurable
    have hpt : ∀ r : ↥(flagN B.d ⊔ (embA B.d B.o).range), F' r = F r := fun r => Set.piecewise_eq_of_mem _ _ _ r.2
    have hpt2 : ∀ a (n : flagN B.d), F' (n.1 * embA B.d B.o a) = F (n.1 * embA B.d B.o a) := fun a n =>
      Set.piecewise_eq_of_mem _ _ _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨a, rfl⟩))
    obtain ⟨hi1, hi2⟩ := hint F' hF'm
    have e1 : (fun r : ↥(flagN B.d ⊔ (embA B.d B.o).range) => F' r) =
        fun r : ↥(flagN B.d ⊔ (embA B.d B.o).range) => F r := funext hpt
    have e2 : (fun a => ∫ n in B.vN.𝓝, F' (n.1 * embA B.d B.o a) ∂B.vN.ν) =
        fun a => ∫ n in B.vN.𝓝, F (n.1 * embA B.d B.o a) ∂B.vN.ν := funext fun a => by simp only [hpt2]
    refine ⟨?_, ?_⟩
    · have h3 := hi1.2 hAC
      rw [e1] at h3
      exact h3
    · have h3 := hi2 hAC
      rw [e1, e2] at h3
      exact h3

end GlobalTheory.BesselQuot
