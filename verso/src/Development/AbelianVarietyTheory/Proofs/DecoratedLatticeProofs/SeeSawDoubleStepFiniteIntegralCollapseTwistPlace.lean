import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepFiniteIntegralCollapseTwistPlaceAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqIntegralFactorQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSetStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceCmHostAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentAnisotropicProjectionEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandLeftInvariantFourierJacobiFirStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantFirstOffLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantFirstFixedLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepIntegrandVanishesOffFourierJacobStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandLeftInvariantBesselSecondStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantSecondOffLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantSecondFixedLeveStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepIntegrandVanishesOffBesselStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticeStabilizerTwistAndLevelAwayStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

noncomputable section

namespace GlobalTheory.DStepCell

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h ρ₁ μ₁ ρ₂ μ₂ hN₁ hN₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf z hz`. Express the relevant statement in the definitionally equal form `Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun q₁ q₂ => integ v w j σ h Ψ₁ Ψ₂ φ f q₁.1 q₂.1) z at hz`. Express the relevant statement in the definitionally equal form `Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ => integ v w j σ h Ψ₁ Ψ₂ φ f q₁.1 q₂.1) (v.kap j σ h * z)`. Establish `hA1` using `GlobalTheory.T.doubleStep_integrand_leftInvariant_fourierJacobi_first D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf`. Establish `hA2` using `GlobalTheory.T.doubleStepIntegrand_rightInvariant_first_offLevel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf`.

Establish `hA3` using `GlobalTheory.T.doubleStepIntegrand_rightInvariant_first_fixedLevel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf`. Establish `hB` using `GlobalTheory.T.seeSaw_doubleStep_integrand_vanishes_off_fourierJacobi D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf`. Establish `hC1` using `GlobalTheory.T.doubleStep_integrand_leftInvariant_bessel_second D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf`. Establish `hC2` using `GlobalTheory.T.doubleStepIntegrand_rightInvariant_second_offLevel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf`. Establish `hC3` using `GlobalTheory.T.doubleStepIntegrand_rightInvariant_second_fixedLevel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf`.

Establish `hC4` using `GlobalTheory.T.seeSaw_doubleStep_integrand_vanishes_off_bessel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf`. Use `set F := integ v w j σ h Ψ₁ Ψ₂ φ f with hFdef`. Take `⟨f₁', hf₁', hinn⟩` from `hz`. Take `⟨-, hfc₁, -, -, -, hd₁⟩` from `GlobalTheory.T.unitaryAdelic_inf_fin_split_periods_unimodular D (c.V (j + 1))`. Take `⟨-, hfc₂, -, -, -, hd₂⟩` from `GlobalTheory.T.unitaryAdelic_inf_fin_split_periods_unimodular D (c.V (j + 1 + 1))`.

Establish `invJ : (c.ρJ j (σ + 1) h).IsInvInvariant` using `(hd₁ _ _ (c.jac j (σ + 1) h).d).1.2.2 _ (hc.ρJ j (σ + 1) h)`. Establish `invB : (c.ρB (j + 1 + 1) σ (idx_step h)).IsInvInvariant` using `((hd₂ _ _ (c.bes (j + 1 + 1) σ (idx_step h)).d).2 _ _ (c.bes (j + 1 + 1) σ (idx_step h)).o).2.2 _ (hc.ρB _ _ _)`. Take `⟨hQc₁, hQ'c₁, hQle₁, hQ'le₁, hcm₁, he₁, -, -, -, hR₁⟩` from `GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D (c.V (j + 1)) w.Q`. Take `⟨hQc₂, hQ'c₂, hQle₂, hQ'le₂, hcm₂, he₂, -, -, -, hR₂⟩` from `GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D (c.V (j + 1 + 1)) w.Q`. Establish `splitJ` using `(hR₁ _ _ (c.jac j (σ + 1) h).d).1`.

Establish `splitB` using `(hR₂ _ _ (c.bes (j + 1 + 1) σ (idx_step h)).d).2 _ _ (c.bes (j + 1 + 1) σ (idx_step h)).o`. Establish `hJcl` using `GlobalTheory.jacGrp_isClosed D _ _ _ (c.jac j (σ + 1) h).d`. Establish `hBcl` using `GlobalTheory.BesClosed.besGrp_isClosed D _ _ _ _ _ (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o`. Take `⟨hJG₁, hJG₁c, hJG₁o⟩` from `hv.JG (j + 1) (by omega)`. Take `⟨hJG₂, hJG₂c, hJG₂o⟩` from `hv.JG (j + 1 + 1) (by omega)`.

Take `⟨K₁, K₂, hK₁, hK₁Q, hK₂Q, hK₁c, hK₂c, hK₁o, hK₂o, hK₂, hKK⟩` from `GlobalTheory.T.exists_latticeStabilizer_twist_and_level_away D _ (v.N (j + 1)) v.gP w.Q (v.JG (j + 1)) (hv.sd _ (by omega)) hVF.disjG hJG₁ hJG₁c hJG₁o`. Take `⟨K₁', K₂', hK₁', hK₁Q', hK₂Q', hK₁c', hK₂c', hK₁o', hK₂o', hK₂', hKK'⟩` from `GlobalTheory.T.exists_latticeStabilizer_twist_and_level_away D _ (v.N (j + 1 + 1)) v.gP w.Q (v.JG (j + 1 + 1)) (hv.sd _ (by omega)) hVF.disjG hJG₂ hJG₂c hJG₂o`. Establish `hμ₁K : μ₁ {g | (g : GA D (c.V (j + 1))) ∈ K₁} = 1`. Rewrite using `[show {g : grpAt (c.V (j + 1)) (· ∈ w.Q) | (g : GA D (c.V (j + 1))) ∈ K₁} = {g | InK _ (v.N (j + 1)) (· ∈ w.Q) g.1} from Set.ext fun g => hK₁ g.1]`. Conclude with `hN₁.2.2.1`.

Establish `hρ₁K : ρ₁ {g | ((g : grpAt (c.V (j + 1)) (· ∈ w.Q)) : GA D (c.V (j + 1))) ∈ K₁} = 1`. Rewrite using `[show {g : (jacGrp (c.jac j (σ + 1) h).d).subgroupOf (grpAt (c.V (j + 1)) (· ∈ w.Q)) | ((g : grpAt (c.V (j + 1)) (· ∈ w.Q)) : GA D (c.V (j + 1))) ∈ K₁} = {g | InK _ (v.N (j + 1)) (· ∈ w.Q) g.1.1} from Set.ext fun g => hK₁ g.1.1]`. Conclude with `hN₁.2.2.2`. Establish `hμ₂K : μ₂ {g | (g : GA D (c.V (j + 1 + 1))) ∈ K₁'} = 1`. Rewrite using `[show {g : grpAt (c.V (j + 1 + 1)) (· ∈ w.Q) | (g : GA D (c.V (j + 1 + 1))) ∈ K₁'} = {g | InK _ (v.N (j + 1 + 1)) (· ∈ w.Q) g.1} from Set.ext fun g => hK₁' g.1]`.

Conclude with `hN₂.2.2.1`. Establish `hρ₂K : ρ₂ {g | ((g : grpAt (c.V (j + 1 + 1)) (· ∈ w.Q)) : GA D (c.V (j + 1 + 1))) ∈ K₁'} = 1`. Rewrite using `[show {g : (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o).subgroupOf (grpAt (c.V (j + 1 + 1)) (· ∈ w.Q)) | ((g : grpAt (c.V (j + 1 + 1)) (· ∈ w.Q)) : GA D (c.V (j + 1 + 1))) ∈ K₁'} = {g | InK _ (v.N (j + 1 + 1)) (· ∈ w.Q) g.1.1} from Set.ext fu …`. Conclude with `hN₂.2.2.2`. Establish `hinner : ∀ q₁ : grpAt (c.V (j + 1)) (· ∈ w.Q), IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun g => F q₁.1 g.1) (v.vr (j + 1 + 1) _ (c.ρB (j + 1 + 1) σ (idx_step h)) * f₁' q₁)`.

Introduce `q₁`. Establish `hl : ∀ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o, r ∈ GfC (c.V (j + 1 + 1)) → ∀ g ∈ GfC (c.V (j + 1 + 1)), F q₁.1 (r * g) = F q₁.1 g` using `fun r hr _ g _ => hC1 r hr q₁.1 g`. Establish `hr : ∀ k ∈ K₂', ∀ g ∈ GfC (c.V (j + 1 + 1)), F q₁.1 (g * k) = F q₁.1 g`. Introduce `k hk g _`. Take `⟨κ, hκ, k', hk', rfl⟩` from `(hK₂' k).1 hk`.

Rewrite using `[← mul_assoc, hC3 k' hk', hC2 κ hκ]`. Establish `hs : ∀ g ∈ GfC (c.V (j + 1 + 1)), F q₁.1 g ≠ 0 → ∃ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o, r ∈ GfC (c.V (j + 1 + 1)) ∧ ∃ y ∈ grpAt (c.V (j + 1 + 1)) (· ∈ w.Q), ∃ k ∈ K₂', g = r * y * k`. Introduce `g hg hne`. Take `⟨r, hr, hrG, y, hy, κ, hκ, k, hk, e⟩` from `hC4 q₁.1 q₁.2 g hg hne`. Conclude with `⟨r, hr, hrG, y, hy, κ * k, (hK₂' _).2 ⟨κ, hκ, k, hk, rfl⟩, e⟩`.

Establish `H` using `GlobalTheory.T.integral_quotient_eq_integral_factor_quotient (GA D (c.V (j + 1 + 1))) (GfC _) (grpAt _ (· ∈ w.Q)) (grpAt _ (· ∉ w.Q)) (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o) K₁' K₂' hfc₂ hQc₂ hQ'c₂ hBcl hQle₂ hQ'le₂ hcm₂ he₂ splitB hK₁Q' …`. Establish `e1 : {g : GfC (c.V (j + 1 + 1)) | ∃ a ∈ K₁', ∃ b ∈ K₂', (g : GA D (c.V (j + 1 + 1))) = a * b} = {g | g.1 ∈ v.K (j + 1 + 1)}` using `Set.ext fun g => hKK' g.1`. Establish `e2 : {g : (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o).subgroupOf (GfC (c.V (j + 1 + 1))) | ∃ a ∈ K₁', ∃ b ∈ K₂', ((g : GfC (c.V (j + 1 + 1))) : GA D (c.V (j + 1 + 1))) = a * b} = {g | g.1.1 ∈ v.K (j + 1 + 1)}` using `Set.ext fun g => hKK' g.1.1`. Rewrite `H` using `[e1, e2]`. Conclude with `H`.

Use `haveI : LocallyCompactSpace (GfC (c.V (j + 1 + 1))) := hfc₂.locallyCompactSpace`. Use `haveI := hc.μf (j + 1 + 1)`. Use `haveI := hc.ρB (j + 1 + 1) σ (idx_step h)`. Use `haveI := invB`. Establish `hBcl' : IsClosed (((besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o).subgroupOf (GfC (c.V (j + 1 + 1))) : Subgroup _) : Set (GfC (c.V (j + 1 + 1))))` using `hBcl.preimage continuous_subtype_val`.

Establish `huniq : ∀ (Φ : GfC (c.V (j + 1 + 1)) → ℂ) (z₁ z₂ : ℂ), IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) Φ z₁ → IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) Φ z₂ → z₁ = z₂` using `fun Φ z₁ z₂ h1 h2 => IsQuotIntL1.unique hBcl' h1 h2`. Establish `hex : ∀ q : GfC (c.V (j + 1)), ∃ z', IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun g => F q.1 g.1) z'`. Introduce `q`. Distinguish the cases in `hq : ∃ q₂, F q.1 q₂ ≠ 0`. Take `⟨q₂, hq₂⟩` from `hq`.

Take `⟨r, hr, -, y, hy, κ, hκ, k, hk, e⟩` from `hB q.1 q.2 q₂ hq₂`. Establish `e' : F q.1 = F y` using `funext fun q₂ => by rw [e, ← mul_assoc, hA3 k hk, hA2 κ hκ, hA1 r hr]`. Conclude with `⟨_, by rw [e']; exact hinner ⟨y, hy⟩⟩`. Use `push_neg at hq`. Use `⟨0, ?_⟩` and prove the remaining obligations.

Establish `e : (fun g : GfC (c.V (j + 1 + 1)) => F q.1 g.1) = 0` using `funext fun g => hq g.1`. Rewrite using `[e]`. Conclude with `IsQuotIntL1.zero`. Set `fo : GA D (c.V (j + 1)) → ℂ` to `fun y => if hy : y ∈ GfC (c.V (j + 1)) then (hex ⟨y, hy⟩).choose else 0`. Establish `hfo_spec : ∀ y (hy : y ∈ GfC (c.V (j + 1))), IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun g => F y g.1) (fo y)`.

Introduce `y hy`. Establish `e : fo y = (hex ⟨y, hy⟩).choose` using `dif_pos hy`. Rewrite using `[e]`. Conclude with `(hex ⟨y, hy⟩).choose_spec`. Establish `hleft : ∀ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ GfC (c.V (j + 1)) → ∀ g ∈ GfC (c.V (j + 1)), fo (r * g) = fo g`.

Introduce `r hr hrG g hg`. Establish `e : F (r * g) = F g` using `funext fun q₂ => hA1 r hr g q₂`. Establish `h1` using `hfo_spec _ (mul_mem hrG hg)`. Rewrite `h1` using `[e]`. Conclude with `huniq _ _ _ h1 (hfo_spec g hg)`.

Establish `hright : ∀ k ∈ K₂, ∀ g ∈ GfC (c.V (j + 1)), fo (g * k) = fo g`. Introduce `k hk g hg`. Establish `hkG : k ∈ GfC (c.V (j + 1))` using `hQ'le₁ (hK₂Q hk)`. Take `⟨κ, hκ, k', hk', e0⟩` from `(hK₂ k).1 hk`. Establish `e : F (g * k) = F g` using `funext fun q₂ => by rw [e0, ← mul_assoc, hA3 k' hk', hA2 κ hκ]`.

Establish `h1` using `hfo_spec _ (mul_mem hg hkG)`. Rewrite `h1` using `[e]`. Conclude with `huniq _ _ _ h1 (hfo_spec g hg)`. Establish `hsupp : ∀ g ∈ GfC (c.V (j + 1)), fo g ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ GfC (c.V (j + 1)) ∧ ∃ y ∈ grpAt (c.V (j + 1)) (· ∈ w.Q), ∃ k ∈ K₂, g = r * y * k`. Introduce `g hg hne`.

Establish `hq : ∃ q₂, F g q₂ ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hne` to reduce the goal to its premises. Establish `e : (fun g' : GfC (c.V (j + 1 + 1)) => F g g'.1) = 0` using `funext fun g' => hcon g'.1`.

Establish `h0` using `hfo_spec g hg`. Rewrite `h0` using `[e]`. Conclude with `huniq _ _ _ h0 IsQuotIntL1.zero`. Take `⟨q₂, hq₂⟩` from `hq`. Take `⟨r, hr, hrG, y, hy, κ, hκ, k, hk, e⟩` from `hB g hg q₂ hq₂`.

Conclude with `⟨r, hr, hrG, y, hy, κ * k, (hK₂ _).2 ⟨κ, hκ, k, hk, rfl⟩, e⟩`. Establish `hint : IsQuotIntL1 ρ₁ μ₁ (fun y : grpAt (c.V (j + 1)) (· ∈ w.Q) => fo y.1) (v.vr (j + 1 + 1) _ (c.ρB (j + 1 + 1) σ (idx_step h)) * z)`. Establish `e : (fun y : grpAt (c.V (j + 1)) (· ∈ w.Q) => fo y.1) = v.vr (j + 1 + 1) _ (c.ρB (j + 1 + 1) σ (idx_step h)) • f₁'` using `funext fun y => by`. Rewrite using `[Pi.smul_apply, smul_eq_mul]`. Conclude with `huniq _ _ _ (hfo_spec y.1 (hQle₁ y.2)) (hinner y)`.

Rewrite using `[e]`. Conclude with `hf₁'.smul _`. Establish `Hout` using `GlobalTheory.T.integral_quotient_eq_integral_factor_quotient (GA D (c.V (j + 1))) (GfC _) (grpAt _ (· ∈ w.Q)) (grpAt _ (· ∉ w.Q)) (jacGrp (c.jac j (σ + 1) h).d) K₁ K₂ hfc₁ hQc₁ hQ'c₁ hJcl hQle₁ hQ'le₁ hcm₁ he₁ splitJ hK₁Q hK₂Q hK₁c hK₂c hK₁o hK₂o (c.ρJ j (σ + 1) h) (c.μf _) ρ₁ μ₁ …`. Establish `e1 : {g : GfC (c.V (j + 1)) | ∃ a ∈ K₁, ∃ b ∈ K₂, (g : GA D (c.V (j + 1))) = a * b} = {g | g.1 ∈ v.K (j + 1)}` using `Set.ext fun g => hKK g.1`. Establish `e2 : {g : (jacGrp (c.jac j (σ + 1) h).d).subgroupOf (GfC (c.V (j + 1))) | ∃ a ∈ K₁, ∃ b ∈ K₂, ((g : GfC (c.V (j + 1))) : GA D (c.V (j + 1))) = a * b} = {g | g.1.1 ∈ v.K (j + 1)}` using `Set.ext fun g => hKK g.1.1`.

Rewrite `Hout` using `[e1, e2]`. Use `⟨fun q => fo q.1, ?_, fun q => hfo_spec q.1 q.2⟩` and prove the remaining obligations. Establish `ek : v.kap j σ h * z = v.vr (j + 1) _ (c.ρJ j (σ + 1) h) * (v.vr (j + 1 + 1) _ (c.ρB (j + 1 + 1) σ (idx_step h)) * z)`. Unfold `VCom.kap`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[ek]`. Conclude with `Hout`.
-/
theorem cell_collapse : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) ρ₁ μ₁ ρ₂ μ₂, IsNormAt (c.V (j + 1)) (jacGrp (c.jac j (σ + 1) h).d) (v.N (j + 1)) (· ∈ w.Q) ρ₁ μ₁ → IsNormAt (c.V (j + 1 + 1)) (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o) (v.N (j + 1 + 1)) (· ∈ w.Q) ρ₂ μ₂ → ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ z, Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun q₁ q₂ : _ => ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)) z → Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ : _ => ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)) (v.kap j σ h * z) := by
  classical
  intro D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h ρ₁ μ₁ ρ₂ μ₂ hN₁ hN₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf z hz
  change Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun q₁ q₂ => integ v w j σ h Ψ₁ Ψ₂ φ f q₁.1 q₂.1) z at hz
  change Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1))
    (fun q₁ q₂ => integ v w j σ h Ψ₁ Ψ₂ φ f q₁.1 q₂.1) (v.kap j σ h * z)
  have hA1 := GlobalTheory.T.doubleStep_integrand_leftInvariant_fourierJacobi_first D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hA2 := GlobalTheory.T.doubleStepIntegrand_rightInvariant_first_offLevel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hA3 := GlobalTheory.T.doubleStepIntegrand_rightInvariant_first_fixedLevel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hB := GlobalTheory.T.seeSaw_doubleStep_integrand_vanishes_off_fourierJacobi D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hC1 := GlobalTheory.T.doubleStep_integrand_leftInvariant_bessel_second D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hC2 := GlobalTheory.T.doubleStepIntegrand_rightInvariant_second_offLevel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hC3 := GlobalTheory.T.doubleStepIntegrand_rightInvariant_second_fixedLevel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hC4 := GlobalTheory.T.seeSaw_doubleStep_integrand_vanishes_off_bessel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  set F := integ v w j σ h Ψ₁ Ψ₂ φ f with hFdef
  obtain ⟨f₁', hf₁', hinn⟩ := hz

  obtain ⟨-, hfc₁, -, -, -, hd₁⟩ := GlobalTheory.T.unitaryAdelic_inf_fin_split_periods_unimodular D (c.V (j + 1))
  obtain ⟨-, hfc₂, -, -, -, hd₂⟩ := GlobalTheory.T.unitaryAdelic_inf_fin_split_periods_unimodular D (c.V (j + 1 + 1))
  have invJ : (c.ρJ j (σ + 1) h).IsInvInvariant := (hd₁ _ _ (c.jac j (σ + 1) h).d).1.2.2 _ (hc.ρJ j (σ + 1) h)
  have invB : (c.ρB (j + 1 + 1) σ (idx_step h)).IsInvInvariant :=
    ((hd₂ _ _ (c.bes (j + 1 + 1) σ (idx_step h)).d).2 _ _ (c.bes (j + 1 + 1) σ (idx_step h)).o).2.2 _ (hc.ρB _ _ _)
  obtain ⟨hQc₁, hQ'c₁, hQle₁, hQ'le₁, hcm₁, he₁, -, -, -, hR₁⟩ := GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D (c.V (j + 1)) w.Q
  obtain ⟨hQc₂, hQ'c₂, hQle₂, hQ'le₂, hcm₂, he₂, -, -, -, hR₂⟩ := GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D (c.V (j + 1 + 1)) w.Q
  have splitJ := (hR₁ _ _ (c.jac j (σ + 1) h).d).1
  have splitB := (hR₂ _ _ (c.bes (j + 1 + 1) σ (idx_step h)).d).2 _ _ (c.bes (j + 1 + 1) σ (idx_step h)).o
  have hJcl := GlobalTheory.jacGrp_isClosed D _ _ _ (c.jac j (σ + 1) h).d
  have hBcl := GlobalTheory.BesClosed.besGrp_isClosed D _ _ _ _ _ (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o

  obtain ⟨hJG₁, hJG₁c, hJG₁o⟩ := hv.JG (j + 1) (by omega)
  obtain ⟨hJG₂, hJG₂c, hJG₂o⟩ := hv.JG (j + 1 + 1) (by omega)
  obtain ⟨K₁, K₂, hK₁, hK₁Q, hK₂Q, hK₁c, hK₂c, hK₁o, hK₂o, hK₂, hKK⟩ :=
    GlobalTheory.T.exists_latticeStabilizer_twist_and_level_away D _ (v.N (j + 1)) v.gP w.Q (v.JG (j + 1)) (hv.sd _ (by omega)) hVF.disjG hJG₁ hJG₁c hJG₁o
  obtain ⟨K₁', K₂', hK₁', hK₁Q', hK₂Q', hK₁c', hK₂c', hK₁o', hK₂o', hK₂', hKK'⟩ :=
    GlobalTheory.T.exists_latticeStabilizer_twist_and_level_away D _ (v.N (j + 1 + 1)) v.gP w.Q (v.JG (j + 1 + 1)) (hv.sd _ (by omega)) hVF.disjG hJG₂ hJG₂c hJG₂o
  have hμ₁K : μ₁ {g | (g : GA D (c.V (j + 1))) ∈ K₁} = 1 := by
    rw [show {g : grpAt (c.V (j + 1)) (· ∈ w.Q) | (g : GA D (c.V (j + 1))) ∈ K₁} =
      {g | InK _ (v.N (j + 1)) (· ∈ w.Q) g.1} from Set.ext fun g => hK₁ g.1]
    exact hN₁.2.2.1
  have hρ₁K : ρ₁ {g | ((g : grpAt (c.V (j + 1)) (· ∈ w.Q)) : GA D (c.V (j + 1))) ∈ K₁} = 1 := by
    rw [show {g : (jacGrp (c.jac j (σ + 1) h).d).subgroupOf (grpAt (c.V (j + 1)) (· ∈ w.Q)) |
      ((g : grpAt (c.V (j + 1)) (· ∈ w.Q)) : GA D (c.V (j + 1))) ∈ K₁} =
      {g | InK _ (v.N (j + 1)) (· ∈ w.Q) g.1.1} from Set.ext fun g => hK₁ g.1.1]
    exact hN₁.2.2.2
  have hμ₂K : μ₂ {g | (g : GA D (c.V (j + 1 + 1))) ∈ K₁'} = 1 := by
    rw [show {g : grpAt (c.V (j + 1 + 1)) (· ∈ w.Q) | (g : GA D (c.V (j + 1 + 1))) ∈ K₁'} =
      {g | InK _ (v.N (j + 1 + 1)) (· ∈ w.Q) g.1} from Set.ext fun g => hK₁' g.1]
    exact hN₂.2.2.1
  have hρ₂K : ρ₂ {g | ((g : grpAt (c.V (j + 1 + 1)) (· ∈ w.Q)) : GA D (c.V (j + 1 + 1))) ∈ K₁'} = 1 := by
    rw [show {g : (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o).subgroupOf
        (grpAt (c.V (j + 1 + 1)) (· ∈ w.Q)) |
      ((g : grpAt (c.V (j + 1 + 1)) (· ∈ w.Q)) : GA D (c.V (j + 1 + 1))) ∈ K₁'} =
      {g | InK _ (v.N (j + 1 + 1)) (· ∈ w.Q) g.1.1} from Set.ext fun g => hK₁' g.1.1]
    exact hN₂.2.2.2

  have hinner : ∀ q₁ : grpAt (c.V (j + 1)) (· ∈ w.Q), IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1))
      (fun g => F q₁.1 g.1) (v.vr (j + 1 + 1) _ (c.ρB (j + 1 + 1) σ (idx_step h)) * f₁' q₁) := by
    intro q₁
    have hl : ∀ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o,
        r ∈ GfC (c.V (j + 1 + 1)) → ∀ g ∈ GfC (c.V (j + 1 + 1)), F q₁.1 (r * g) = F q₁.1 g :=
      fun r hr _ g _ => hC1 r hr q₁.1 g
    have hr : ∀ k ∈ K₂', ∀ g ∈ GfC (c.V (j + 1 + 1)), F q₁.1 (g * k) = F q₁.1 g := by
      intro k hk g _
      obtain ⟨κ, hκ, k', hk', rfl⟩ := (hK₂' k).1 hk
      rw [← mul_assoc, hC3 k' hk', hC2 κ hκ]
    have hs : ∀ g ∈ GfC (c.V (j + 1 + 1)), F q₁.1 g ≠ 0 → ∃ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d
        (c.bes (j + 1 + 1) σ (idx_step h)).o, r ∈ GfC (c.V (j + 1 + 1)) ∧ ∃ y ∈ grpAt (c.V (j + 1 + 1)) (· ∈ w.Q),
        ∃ k ∈ K₂', g = r * y * k := by
      intro g hg hne
      obtain ⟨r, hr, hrG, y, hy, κ, hκ, k, hk, e⟩ := hC4 q₁.1 q₁.2 g hg hne
      exact ⟨r, hr, hrG, y, hy, κ * k, (hK₂' _).2 ⟨κ, hκ, k, hk, rfl⟩, e⟩
    have H := GlobalTheory.T.integral_quotient_eq_integral_factor_quotient (GA D (c.V (j + 1 + 1))) (GfC _) (grpAt _ (· ∈ w.Q)) (grpAt _ (· ∉ w.Q))
      (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o) K₁' K₂'
      hfc₂ hQc₂ hQ'c₂ hBcl hQle₂ hQ'le₂ hcm₂ he₂ splitB hK₁Q' hK₂Q' hK₁c' hK₂c' hK₁o' hK₂o'
      (c.ρB _ _ _) (c.μf _) ρ₂ μ₂ (hc.ρB _ _ _) (hc.μf _) hN₂.2.1 hN₂.1 invB hμ₂K hρ₂K (F q₁.1) (f₁' q₁) hl hr hs (hinn q₁)
    have e1 : {g : GfC (c.V (j + 1 + 1)) | ∃ a ∈ K₁', ∃ b ∈ K₂', (g : GA D (c.V (j + 1 + 1))) = a * b} =
        {g | g.1 ∈ v.K (j + 1 + 1)} := Set.ext fun g => hKK' g.1
    have e2 : {g : (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o).subgroupOf
        (GfC (c.V (j + 1 + 1))) | ∃ a ∈ K₁', ∃ b ∈ K₂', ((g : GfC (c.V (j + 1 + 1))) : GA D (c.V (j + 1 + 1))) = a * b} =
        {g | g.1.1 ∈ v.K (j + 1 + 1)} := Set.ext fun g => hKK' g.1.1
    rw [e1, e2] at H
    exact H

  haveI : LocallyCompactSpace (GfC (c.V (j + 1 + 1))) := hfc₂.locallyCompactSpace
  haveI := hc.μf (j + 1 + 1)
  haveI := hc.ρB (j + 1 + 1) σ (idx_step h)
  haveI := invB
  have hBcl' : IsClosed (((besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o).subgroupOf
      (GfC (c.V (j + 1 + 1))) : Subgroup _) : Set (GfC (c.V (j + 1 + 1)))) := hBcl.preimage continuous_subtype_val
  have huniq : ∀ (Φ : GfC (c.V (j + 1 + 1)) → ℂ) (z₁ z₂ : ℂ), IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h))
      (c.μf (j + 1 + 1)) Φ z₁ → IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) Φ z₂ → z₁ = z₂ :=
    fun Φ z₁ z₂ h1 h2 => IsQuotIntL1.unique hBcl' h1 h2

  have hex : ∀ q : GfC (c.V (j + 1)), ∃ z', IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1))
      (fun g => F q.1 g.1) z' := by
    intro q
    by_cases hq : ∃ q₂, F q.1 q₂ ≠ 0
    · obtain ⟨q₂, hq₂⟩ := hq
      obtain ⟨r, hr, -, y, hy, κ, hκ, k, hk, e⟩ := hB q.1 q.2 q₂ hq₂
      have e' : F q.1 = F y := funext fun q₂ => by rw [e, ← mul_assoc, hA3 k hk, hA2 κ hκ, hA1 r hr]
      exact ⟨_, by rw [e']; exact hinner ⟨y, hy⟩⟩
    · push_neg at hq
      refine ⟨0, ?_⟩
      have e : (fun g : GfC (c.V (j + 1 + 1)) => F q.1 g.1) = 0 := funext fun g => hq g.1
      rw [e]
      exact IsQuotIntL1.zero
  let fo : GA D (c.V (j + 1)) → ℂ := fun y => if hy : y ∈ GfC (c.V (j + 1)) then (hex ⟨y, hy⟩).choose else 0
  have hfo_spec : ∀ y (hy : y ∈ GfC (c.V (j + 1))), IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1))
      (fun g => F y g.1) (fo y) := by
    intro y hy
    have e : fo y = (hex ⟨y, hy⟩).choose := dif_pos hy
    rw [e]
    exact (hex ⟨y, hy⟩).choose_spec
  have hleft : ∀ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ GfC (c.V (j + 1)) → ∀ g ∈ GfC (c.V (j + 1)), fo (r * g) = fo g := by
    intro r hr hrG g hg
    have e : F (r * g) = F g := funext fun q₂ => hA1 r hr g q₂
    have h1 := hfo_spec _ (mul_mem hrG hg)
    rw [e] at h1
    exact huniq _ _ _ h1 (hfo_spec g hg)
  have hright : ∀ k ∈ K₂, ∀ g ∈ GfC (c.V (j + 1)), fo (g * k) = fo g := by
    intro k hk g hg
    have hkG : k ∈ GfC (c.V (j + 1)) := hQ'le₁ (hK₂Q hk)
    obtain ⟨κ, hκ, k', hk', e0⟩ := (hK₂ k).1 hk
    have e : F (g * k) = F g := funext fun q₂ => by rw [e0, ← mul_assoc, hA3 k' hk', hA2 κ hκ]
    have h1 := hfo_spec _ (mul_mem hg hkG)
    rw [e] at h1
    exact huniq _ _ _ h1 (hfo_spec g hg)
  have hsupp : ∀ g ∈ GfC (c.V (j + 1)), fo g ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ GfC (c.V (j + 1)) ∧
      ∃ y ∈ grpAt (c.V (j + 1)) (· ∈ w.Q), ∃ k ∈ K₂, g = r * y * k := by
    intro g hg hne
    have hq : ∃ q₂, F g q₂ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hne
      have e : (fun g' : GfC (c.V (j + 1 + 1)) => F g g'.1) = 0 := funext fun g' => hcon g'.1
      have h0 := hfo_spec g hg
      rw [e] at h0
      exact huniq _ _ _ h0 IsQuotIntL1.zero
    obtain ⟨q₂, hq₂⟩ := hq
    obtain ⟨r, hr, hrG, y, hy, κ, hκ, k, hk, e⟩ := hB g hg q₂ hq₂
    exact ⟨r, hr, hrG, y, hy, κ * k, (hK₂ _).2 ⟨κ, hκ, k, hk, rfl⟩, e⟩
  have hint : IsQuotIntL1 ρ₁ μ₁ (fun y : grpAt (c.V (j + 1)) (· ∈ w.Q) => fo y.1)
      (v.vr (j + 1 + 1) _ (c.ρB (j + 1 + 1) σ (idx_step h)) * z) := by
    have e : (fun y : grpAt (c.V (j + 1)) (· ∈ w.Q) => fo y.1) =
        v.vr (j + 1 + 1) _ (c.ρB (j + 1 + 1) σ (idx_step h)) • f₁' := funext fun y => by
      rw [Pi.smul_apply, smul_eq_mul]
      exact huniq _ _ _ (hfo_spec y.1 (hQle₁ y.2)) (hinner y)
    rw [e]
    exact hf₁'.smul _
  have Hout := GlobalTheory.T.integral_quotient_eq_integral_factor_quotient (GA D (c.V (j + 1))) (GfC _) (grpAt _ (· ∈ w.Q)) (grpAt _ (· ∉ w.Q))
    (jacGrp (c.jac j (σ + 1) h).d) K₁ K₂ hfc₁ hQc₁ hQ'c₁ hJcl hQle₁ hQ'le₁ hcm₁ he₁ splitJ hK₁Q hK₂Q hK₁c hK₂c hK₁o hK₂o
    (c.ρJ j (σ + 1) h) (c.μf _) ρ₁ μ₁ (hc.ρJ _ _ _) (hc.μf _) hN₁.2.1 hN₁.1 invJ hμ₁K hρ₁K fo _ hleft hright hsupp hint
  have e1 : {g : GfC (c.V (j + 1)) | ∃ a ∈ K₁, ∃ b ∈ K₂, (g : GA D (c.V (j + 1))) = a * b} =
      {g | g.1 ∈ v.K (j + 1)} := Set.ext fun g => hKK g.1
  have e2 : {g : (jacGrp (c.jac j (σ + 1) h).d).subgroupOf (GfC (c.V (j + 1))) |
      ∃ a ∈ K₁, ∃ b ∈ K₂, ((g : GfC (c.V (j + 1))) : GA D (c.V (j + 1))) = a * b} =
      {g | g.1.1 ∈ v.K (j + 1)} := Set.ext fun g => hKK g.1.1
  rw [e1, e2] at Hout
  refine ⟨fun q => fo q.1, ?_, fun q => hfo_spec q.1 q.2⟩
  have ek : v.kap j σ h * z = v.vr (j + 1) _ (c.ρJ j (σ + 1) h) * (v.vr (j + 1 + 1) _ (c.ρB (j + 1 + 1) σ (idx_step h)) * z) := by
    unfold VCom.kap; ring
  rw [ek]
  exact Hout

end GlobalTheory.DStepCell

end
