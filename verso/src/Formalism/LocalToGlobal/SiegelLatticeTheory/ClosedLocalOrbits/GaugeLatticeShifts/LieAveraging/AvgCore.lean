import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.LsSetresAvg

noncomputable section

open MeasureTheory Topology Set
open scoped Pointwise ENNReal

namespace Formalism.L2.SG.AvgPf

/- English proof (translation)
Take `⟨hΩm, hΩc, hΩu⟩` from `hΩ`. Use `hdisc` as an intermediate fact. Establish `: Countable Γ` using `countable_of_Lindelof_of_discrete`. Distinguish the cases in `hV : CompleteSpace V`. Use `swap`.

Conclude with `integral_of_not_completeSpace hV`. Distinguish the cases in `hint : Integrable f (μ.restrict Ω)`. Use `swap`. Conclude with `integral_undef hint`. Take `⟨K, hK, hKc⟩` from `hcpt`.

Take `⟨D, hDm, hDK, hDR, hDc, hDu⟩` from `exists_fd R Γ hR hΓR K hK hKc`. Establish `: LocallyCompactSpace R` using `hR.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Establish `: SecondCountableTopology R` using `TopologicalSpace.Subtype.secondCountableTopology (R : Set G)`. Establish `: MeasurableSMul Γ G` using `{ measurable_const_smul := fun c => measurable_const_mul (c : G) measurable_smul_const := fun x => measurable_subtype_coe.mul_const x }`. Use `set νR : Measure R := Measure.haar with hνR`.

Use `set ν : Measure G := νR.map Subtype.val with hν`. Establish `hνapp : ∀ A : Set G, MeasurableSet A → ν A = νR (Subtype.val ⁻¹' A)` using `fun A hA => Measure.map_apply measurable_subtype_coe hA`. Establish `hνRc : ν (R : Set G)ᶜ = 0`. Rewrite using `[hνapp _ hR.isOpen_compl.measurableSet]`. Establish `: (Subtype.val ⁻¹' (R : Set G)ᶜ : Set R) = ∅` using `by ext x; simp`.

Rewrite using `[this, measure_empty]`. Establish `hae : ∀ᵐ x ∂ν, x ∈ R`. Rewrite using `[ae_iff]`. Conclude with `hνRc`. Establish `hνuniv : ν univ ≠ 0`.

Rewrite using `[hνapp _ MeasurableSet.univ, Set.preimage_univ]`. Conclude with `(Measure.measure_univ_pos.2 (NeZero.ne _)).ne'`. Establish `hνK : ∀ C : Set G, IsCompact C → ν C < ∞`. Introduce `C hC`. Rewrite using `[hνapp _ hC.isClosed.measurableSet]`.

Conclude with `(hR.isClosedEmbedding_subtypeVal.isCompact_preimage hC).measure_lt_top`. Establish `hleft : ∀ r ∈ R, Measure.map (fun x => r * x) ν = ν`. Introduce `r hr`. Rewrite using `[hν, Measure.map_map (measurable_const_mul r) measurable_subtype_coe]`. Establish `: (fun x => r * x) ∘ (Subtype.val : R → G) = Subtype.val ∘ (fun y : R => (⟨r, hr⟩ : R) * y)` using `rfl`.

Rewrite using `[this, ← Measure.map_map measurable_subtype_coe (measurable_const_mul _), map_mul_left_eq_self]`. Establish `hright0 : ∀ r ∈ R, ∃ c : NNReal, Measure.map (fun x => x * r) ν = c • ν`. Introduce `r hr`. Use `Measure.isHaarMeasure_map_mul_right νR (⟨r, hr⟩ : R)` as an intermediate fact. Use `⟨(Measure.map (fun y : R => y * ⟨r, hr⟩) νR).haarScalarFactor νR, ?_⟩` and prove the remaining obligations.

Rewrite using `[hν, Measure.map_map (measurable_mul_const r) measurable_subtype_coe]`. Establish `: (fun x => x * r) ∘ (Subtype.val : R → G) = Subtype.val ∘ (fun y : R => y * (⟨r, hr⟩ : R))` using `rfl`. Rewrite using `[this, ← Measure.map_map measurable_subtype_coe (measurable_mul_const _), ← Measure.map_smul, ← Measure.isMulLeftInvariant_eq_smul]`. Establish `: SMulInvariantMeasure Γ G ν` using `⟨fun c A hA => by`. Use `congrArg (fun m : Measure G => m A) (hleft c (hΓR c.2))` as an intermediate fact.

Rewrite `this` using `[Measure.map_apply (measurable_const_mul _) hA]`. Conclude with `this⟩`. Establish `hDfd : IsFundamentalDomain Γ D ν`. Use `isFD_of_strict ν hDm ?_ ?_` and prove the remaining obligations. Use `filter_upwards [hae] with x hx`.

Take `⟨s, hs, h⟩` from `hDc x hx`. Conclude with `⟨⟨s, hs⟩, h⟩`. Introduce `x hx g hg`. Conclude with `Subtype.ext (hDu x hx g g.2 hg)`. Establish `hD0 : ν D ≠ 0` using `fd_ne_zero hDfd hνuniv`.

Establish `hDtop : ν D ≠ ∞` using `(lt_of_le_of_lt (measure_mono hDK) (hνK K hK)).ne`. Establish `hTfd : ∀ r ∈ R, IsFundamentalDomain Γ ((fun x => x * r⁻¹) ⁻¹' D) ν`. Introduce `r hr`. Use `isFD_of_strict ν ((measurable_mul_const _) hDm) ?_ ?_` and prove the remaining obligations. Use `filter_upwards [hae] with x hx`.

Take `⟨s, hs, h⟩` from `hDc (x * r⁻¹) (R.mul_mem hx (R.inv_mem hr))`. Conclude with `⟨⟨s, hs⟩, by simpa [mul_assoc] using h⟩`. Introduce `x hx g hg`. Use `Subtype.ext (hDu (x * r⁻¹) hx g g.2 ?_)` and prove the remaining obligations. Establish `hg' : (g : G) * x * r⁻¹ ∈ D` using `hg`.

Simplify `hg'` using `[mul_assoc]`. Establish `hright : ∀ r ∈ R, Measure.map (fun x => x * r) ν = ν`. Introduce `r hr`. Take `⟨c, hc⟩` from `hright0 r⁻¹⁻¹ (R.inv_mem (R.inv_mem hr))`. Establish `h1 : ν ((fun x => x * r⁻¹⁻¹) ⁻¹' D) = ν D` using `(hTfd r⁻¹ (R.inv_mem hr)).measure_eq hDfd`.

Rewrite `h1` using `[← Measure.map_apply (measurable_mul_const _) hDm, hc, Measure.smul_apply]`. Establish `h1' : (c : ℝ≥0∞) * ν D = ν D`. Rewrite `h1` using `[ENNReal.smul_def, smul_eq_mul]`. Conclude with `h1`. Establish `hc1 : (c : ℝ≥0∞) = 1`.

Establish `h2 : ν D * c = ν D * 1` using `by rw [mul_one, mul_comm]; exact h1'`. Conclude with `(ENNReal.mul_right_inj hD0 hDtop).1 h2`. Rewrite `hc` using `[inv_inv]`. Establish `hc1' : c = 1` using `by exact_mod_cast hc1`. Rewrite using `[hc, hc1', one_smul]`.

Use `set χ' : G → ℂ := (R : Set G).indicator χ with hχ'`. Establish `hχ'inv : ∀ s ∈ Γ, ∀ x, χ' (s * x) = χ' x`. Introduce `s hs x`. Distinguish the cases in `hx : x ∈ R`. Establish `hsx : s * x ∈ R` using `R.mul_mem (hΓR hs) hx`.

Simplify using `only [hχ', Set.indicator_of_mem (show s * x ∈ (R : Set G) from hsx), Set.indicator_of_mem (show x ∈ (R : Set G) from hx), hχm s (hΓR hs) x hx, hχΓ s hs, one_mul]`. Establish `hsx : s * x ∉ R` using `fun h => hx ((R.mul_mem_cancel_left (hΓR hs)).1 h)`. Simplify using `only [hχ', Set.indicator_of_notMem (show s * x ∉ (R : Set G) from hsx), Set.indicator_of_notMem (show x ∉ (R : Set G) from hx)]`. Establish `hI : ∫ x in D, χ' x ∂ν = 0`. Take `⟨r0, hr0, hne⟩` from `hχne`.

Establish `hmp : MeasurePreserving (fun x => x * r0) ν ν` using `⟨measurable_mul_const r0, hright r0 hr0⟩`. Establish `h1` using `hmp.setIntegral_image_emb (MeasurableEquiv.mulRight r0).measurableEmbedding χ' D`. Rewrite `h1` using `[Set.image_mul_right]`. Establish `h2` using `(hTfd r0 hr0).setIntegral_eq hDfd (f := χ') fun g x => hχ'inv g g.2 x`. Establish `h3 : ∫ x in D, χ' (x * r0) ∂ν = (∫ x in D, χ' x ∂ν) * χ r0`.

Rewrite using `[← integral_mul_const]`. Use `setIntegral_congr_fun hDm fun x hx => ?_` and prove the remaining obligations. Establish `hxR : x ∈ R` using `hDR hx`. Simplify using `only [hχ', Set.indicator_of_mem (show x * r0 ∈ (R : Set G) from R.mul_mem hxR hr0), Set.indicator_of_mem (show x ∈ (R : Set G) from hxR), hχm x hxR r0 hr0]`. Rewrite `h1` using `[h2, h3]`.

Establish `h4 : (∫ x in D, χ' x ∂ν) * (χ r0 - 1) = 0` using `by rw [mul_sub, mul_one, ← h1, sub_self]`. Conclude with `(mul_eq_zero.1 h4).resolve_right (sub_ne_zero.2 hne)`. Use `set νi : Measure G := ν.map (fun x => x⁻¹) with hνi`. Establish `hνiapp : ∀ A : Set G, MeasurableSet A → νi A = ν ((fun x => x⁻¹) ⁻¹' A)` using `fun A hA => Measure.map_apply measurable_inv hA`. Establish `hνiRc : νi (R : Set G)ᶜ = 0`.

Rewrite using `[hνiapp _ hR.isOpen_compl.measurableSet]`. Establish `: (fun x : G => x⁻¹) ⁻¹' (R : Set G)ᶜ = (R : Set G)ᶜ` using `by ext x; simp`. Rewrite using `[this, hνRc]`. Establish `haei : ∀ᵐ x ∂νi, x ∈ R` using `by rw [ae_iff]; exact hνiRc`. Establish `hνiuniv : νi univ ≠ 0` using `by rw [hνiapp _ MeasurableSet.univ, Set.preimage_univ]; exact hνuniv`.

Establish `: SMulInvariantMeasure Γ G νi` using `⟨fun c A hA => by`. Rewrite using `[hνiapp _ (measurable_const_smul c hA), hνiapp _ hA]`. Establish `h : (Measure.map (fun x => x * (c : G)⁻¹) ν) ((fun x => x⁻¹) ⁻¹' A) = ν ((fun x => x⁻¹) ⁻¹' A)`. Rewrite using `[hright _ (R.inv_mem (hΓR c.2))]`. Rewrite `h` using `[Measure.map_apply (measurable_mul_const _) (measurable_inv hA)]`.

Establish `e : (fun x : G => x⁻¹) ⁻¹' ((fun x => c • x) ⁻¹' A) = (fun x => x * (c : G)⁻¹) ⁻¹' ((fun x => x⁻¹) ⁻¹' A)`. Use extensionality with `x`. Simplify using `[Subgroup.smul_def, mul_inv_rev]`. Rewrite using `[e]`. Conclude with `h⟩`.

Establish `hDfdi : IsFundamentalDomain Γ D νi`. Use `isFD_of_strict νi hDm ?_ ?_` and prove the remaining obligations. Use `filter_upwards [haei] with x hx`. Take `⟨s, hs, h⟩` from `hDc x hx`. Conclude with `⟨⟨s, hs⟩, h⟩`.

Introduce `x hx g hg`. Conclude with `Subtype.ext (hDu x hx g g.2 hg)`. Use `set κ := νi D with hκ`. Establish `hκ0 : κ ≠ 0` using `fd_ne_zero hDfdi hνiuniv`. Establish `hκtop : κ ≠ ∞`.

Rewrite using `[hκ, hνiapp _ hDm]`. Conclude with `(lt_of_le_of_lt (measure_mono (show (fun x : G => x⁻¹) ⁻¹' D ⊆ K⁻¹ from fun x hx => hDK hx)) (hνK _ hK.inv)).ne`. Establish `hκx : ∀ x, ν {r | r⁻¹ * x ∈ Ω} = κ`. Introduce `x`. Establish `hfd : IsFundamentalDomain Γ ((fun y => y * x) ⁻¹' Ω) νi`.

Use `isFD_of_strict νi ((measurable_mul_const x) hΩm) (Filter.Eventually.of_forall fun y => ?_) ?_` and prove the remaining obligations. Take `⟨s, hs, h⟩` from `hΩc (y * x)`. Use `⟨⟨s, hs⟩, ?_⟩` and prove the remaining obligations. Use `show (s : G) * y * x ∈ Ω`. Rewrite using `[mul_assoc]`.

Conclude with `h`. Introduce `y hy g hg`. Establish `hg' : (g : G) * y * x ∈ Ω` using `hg`. Rewrite `hg'` using `[mul_assoc]`. Conclude with `Subtype.ext (hΩu (y * x) hy g g.2 hg')`.

Use `hfd.measure_eq hDfdi` as an intermediate fact. Rewrite `this` using `[hνiapp _ ((measurable_mul_const x) hΩm)]`. Conclude with `this`. Establish `: MeasurableConstSMul Γ (G × G)` using `⟨fun c => (measurable_const_mul (c : G)).prodMap (measurable_const_mul (c : G))⟩`. Establish `: SMulInvariantMeasure Γ (G × G) (ν.prod μ)` using `⟨fun c A hA => by`.

Establish `h1 : MeasurePreserving (fun x => (c : G) * x) ν ν` using `⟨measurable_const_mul _, hleft c (hΓR c.2)⟩`. Establish `h2` using `h1.prod (measurePreserving_mul_left μ (c : G))`. Conclude with `h2.measure_preimage hA.nullMeasurableSet⟩`. Use `set H : G × G → V := {p : G × G | p.1⁻¹ * p.2 ∈ Ω}.indicator (fun p => f p.2) with hH`. Establish `hSm : MeasurableSet {p : G × G | p.1⁻¹ * p.2 ∈ Ω}` using `(measurable_fst.inv.mul measurable_snd) hΩm`.

Establish `hfΓ : ∀ s ∈ Γ, ∀ x, f (s * x) = f x` using `fun s hs x => by rw [hf s (hΓR hs), hχΓ s hs, one_smul]`. Establish `hHinv : ∀ (g : Γ) (p : G × G), H (g • p) = H p`. Introduce `g p`. Establish `e1 : (g • p).1⁻¹ * (g • p).2 = p.1⁻¹ * p.2` using `by show ((g : G) * p.1)⁻¹ * ((g : G) * p.2) = p.1⁻¹ * p.2 group`. Distinguish the cases in `h : p.1⁻¹ * p.2 ∈ Ω`.

Rewrite using `[hH, Set.indicator_of_mem (show g • p ∈ {p : G × G | p.1⁻¹ * p.2 ∈ Ω} from by show (g • p).1⁻¹ * (g • p).2 ∈ Ω; rw [e1]; exact h), Set.indicator_of_mem (show p ∈ {p : G × G | p.1⁻¹ * p.2 ∈ Ω} from h)]`. Conclude with `hfΓ g g.2 p.2`. Rewrite using `[hH, Set.indicator_of_notMem (show g • p ∉ {p : G × G | p.1⁻¹ * p.2 ∈ Ω} from by show ¬ (g • p).1⁻¹ * (g • p).2 ∈ Ω; rw [e1]; exact h), Set.indicator_of_notMem (show p ∉ {p : G × G | p.1⁻¹ * p.2 ∈ Ω} from h)]`. Establish `hFD1 : IsFundamentalDomain Γ (univ ×ˢ Ω) (ν.prod μ)`. Use `isFD_of_strict _ (MeasurableSet.univ.prod hΩm) (Filter.Eventually.of_forall fun p => ?_) ?_` and prove the remaining obligations.

Take `⟨s, hs, h⟩` from `hΩc p.2`. Conclude with `⟨⟨s, hs⟩, ⟨trivial, h⟩⟩`. Introduce `p hp g hg`. Conclude with `Subtype.ext (hΩu p.2 hp.2 g g.2 hg.2)`. Establish `hFD2 : IsFundamentalDomain Γ (D ×ˢ univ) (ν.prod μ)`.

Establish `hnull : (ν.prod μ) {p : G × G | ¬ p.1 ∈ R} = 0`. Establish `: {p : G × G | ¬ p.1 ∈ R} = (R : Set G)ᶜ ×ˢ univ` using `by ext p; simp`. Rewrite using `[this, Measure.prod_prod, hνRc, zero_mul]`. Establish `hae2 : ∀ᵐ p ∂(ν.prod μ), p.1 ∈ R` using `by rw [ae_iff]; exact hnull`. Use `isFD_of_strict _ (hDm.prod MeasurableSet.univ) ?_ ?_` and prove the remaining obligations.

Use `filter_upwards [hae2] with p hp`. Take `⟨s, hs, h⟩` from `hDc p.1 hp`. Conclude with `⟨⟨s, hs⟩, ⟨h, trivial⟩⟩`. Introduce `p hp g hg`. Conclude with `Subtype.ext (hDu p.1 hp.1 g g.2 hg.1)`.

Establish `hEq` using `hFD1.setIntegral_eq hFD2 (f := H) hHinv`. Establish `hSy : ∀ y, MeasurableSet {r : G | r⁻¹ * y ∈ Ω}` using `fun y => (measurable_inv.mul_const y) hΩm`. Establish `hHy : ∀ y, (fun r => H (r, y)) = {r : G | r⁻¹ * y ∈ Ω}.indicator (fun _ => f y)`. Introduce `y`. Use extensionality with `r`.

Simplify using `[hH, Set.indicator]`. Establish `hL : ∫ p in univ ×ˢ Ω, H p ∂(ν.prod μ) = κ.toReal • ∫ x in Ω, f x ∂μ`. Rewrite using `[← Measure.prod_restrict, Measure.restrict_univ]`. Establish `hint2 : Integrable H (ν.prod (μ.restrict Ω))`. Establish `hm0 : AEStronglyMeasurable (fun p : G × G => f p.2) (ν.prod (μ.restrict Ω))` using `hint.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd`.

Establish `hm : AEStronglyMeasurable H (ν.prod (μ.restrict Ω))`. Rewrite using `[hH]`. Conclude with `hm0.indicator hSm`. Use `(integrable_prod_iff' hm).2 ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hHy y]`.

Conclude with `(integrable_indicator_iff (hSy y)).2 (integrableOn_const (by rw [hκx y]; exact hκtop))`. Establish `: (fun y => ∫ r, ‖H (r, y)‖ ∂ν) = fun y => κ.toReal * ‖f y‖`. Use function extensionality and compare the values at `y`. Establish `e2 : (fun r => ‖H (r, y)‖) = {r : G | r⁻¹ * y ∈ Ω}.indicator (fun _ => ‖f y‖)`. Apply the tactic sequence `ext r; simp [hH, Set.indicator]; split_ifs <;> simp`.

Rewrite using `[e2, integral_indicator_const _ (hSy y), measureReal_def, hκx y, smul_eq_mul]`. Rewrite using `[this]`. Conclude with `hint.norm.const_mul _`. Rewrite using `[integral_prod_symm H hint2]`. Establish `: (fun y => ∫ r, H (r, y) ∂ν) = fun y => κ.toReal • f y`.

Use function extensionality and compare the values at `y`. Rewrite using `[hHy y, integral_indicator_const _ (hSy y), measureReal_def, hκx y]`. Rewrite using `[this, integral_smul]`. Establish `hemb : MeasurableEmbedding (fun z : G × G => (z.1, z.1 * z.2))`. Conclude with `(MeasurableEquiv.shearMulRight G).measurableEmbedding`.

Establish `hRt : ∫ p in D ×ˢ univ, H p ∂(ν.prod μ) = (∫ x in D, χ' x ∂ν) • ∫ x in Ω, f x ∂μ`. Rewrite using `[← integral_indicator (hDm.prod MeasurableSet.univ), ← (measurePreserving_prod_mul ν μ).integral_comp hemb]`. Establish `e : ∀ z : G × G, (D ×ˢ (univ : Set G)).indicator H (z.1, z.1 * z.2) = D.indicator χ' z.1 • Ω.indicator f z.2`. Introduce and unpack `⟨r, y⟩`. Distinguish the cases in `hr : r ∈ D`.

Establish `hrR : r ∈ R` using `hDR hr`. Establish `hH' : H (r, r * y) = Ω.indicator (fun y => f (r * y)) y`. Simplify using `[hH, Set.indicator, inv_mul_cancel_left]`. Rewrite using `[Set.indicator_of_mem (show (r, r * y) ∈ D ×ˢ (univ : Set G) from ⟨hr, trivial⟩), hH', Set.indicator_of_mem hr]`. Distinguish the cases in `hy : y ∈ Ω`.

Rewrite using `[Set.indicator_of_mem hy, Set.indicator_of_mem hy, hf r hrR, hχ', Set.indicator_of_mem (show r ∈ (R : Set G) from hrR)]`. Rewrite using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, smul_zero]`. Rewrite using `[Set.indicator_of_notMem (show (r, r * y) ∉ D ×ˢ (univ : Set G) from fun h => hr h.1), Set.indicator_of_notMem hr, zero_smul]`. Use `show ∫ z, (D ×ˢ (univ : Set G)).indicator H (z.1, z.1 * z.2) ∂(ν.prod μ) = _`. Rewrite using `[show (fun z : G × G => (D ×ˢ (univ : Set G)).indicator H (z.1, z.1 * z.2)) = fun z => D.indicator χ' z.1 • Ω.indicator f z.2 from funext e]`.

Rewrite using `[integral_prod_smul, integral_indicator hDm, integral_indicator hΩm]`. Establish `hfin : κ.toReal • ∫ x in Ω, f x ∂μ = 0` using `by rw [← hL, hEq, hRt, hI, zero_smul]`. Establish `hκr : κ.toReal ≠ 0` using `ENNReal.toReal_ne_zero.2 ⟨hκ0, hκtop⟩`. Conclude with `(smul_eq_zero.1 hfin).resolve_left hκr`.
-/
theorem avg_core (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (R Γ : Subgroup G) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (χ : G → ℂ) (f : G → V) (Ω : Set G)
    (hR : IsClosed (R : Set G)) (hΓR : Γ ≤ R) (hdisc : DiscreteTopology Γ)
    (hcpt : ∃ K : Set G, IsCompact K ∧ ∀ r ∈ R, ∃ s ∈ Γ, s * r ∈ K)
    (hχm : ∀ r ∈ R, ∀ r' ∈ R, χ (r * r') = χ r * χ r') (hχΓ : ∀ s ∈ Γ, χ s = 1)
    (hχne : ∃ r ∈ R, χ r ≠ 1) (hf : ∀ r ∈ R, ∀ x, f (r * x) = χ r • f x)
    (hΩ : MeasurableSet Ω ∧ (∀ x, ∃ s ∈ (Γ : Set G), s * x ∈ Ω) ∧
      ∀ x ∈ Ω, ∀ s ∈ (Γ : Set G), s * x ∈ Ω → s = 1) :
    ∫ x in Ω, f x ∂μ = 0 := by
  classical
  obtain ⟨hΩm, hΩc, hΩu⟩ := hΩ
  have := hdisc
  have : Countable Γ := countable_of_Lindelof_of_discrete
  by_cases hV : CompleteSpace V
  swap
  · exact integral_of_not_completeSpace hV
  by_cases hint : Integrable f (μ.restrict Ω)
  swap
  · exact integral_undef hint
  obtain ⟨K, hK, hKc⟩ := hcpt
  obtain ⟨D, hDm, hDK, hDR, hDc, hDu⟩ := exists_fd R Γ hR hΓR K hK hKc
  have : LocallyCompactSpace R := hR.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology (R : Set G)
  have : MeasurableSMul Γ G :=
    { measurable_const_smul := fun c => measurable_const_mul (c : G)
      measurable_smul_const := fun x => measurable_subtype_coe.mul_const x }

  set νR : Measure R := Measure.haar with hνR
  set ν : Measure G := νR.map Subtype.val with hν
  have hνapp : ∀ A : Set G, MeasurableSet A → ν A = νR (Subtype.val ⁻¹' A) := fun A hA =>
    Measure.map_apply measurable_subtype_coe hA
  have hνRc : ν (R : Set G)ᶜ = 0 := by
    rw [hνapp _ hR.isOpen_compl.measurableSet]
    have : (Subtype.val ⁻¹' (R : Set G)ᶜ : Set R) = ∅ := by ext x; simp
    rw [this, measure_empty]
  have hae : ∀ᵐ x ∂ν, x ∈ R := by
    rw [ae_iff]; exact hνRc
  have hνuniv : ν univ ≠ 0 := by
    rw [hνapp _ MeasurableSet.univ, Set.preimage_univ]; exact (Measure.measure_univ_pos.2 (NeZero.ne _)).ne'
  have hνK : ∀ C : Set G, IsCompact C → ν C < ∞ := by
    intro C hC
    rw [hνapp _ hC.isClosed.measurableSet]
    exact (hR.isClosedEmbedding_subtypeVal.isCompact_preimage hC).measure_lt_top
  have hleft : ∀ r ∈ R, Measure.map (fun x => r * x) ν = ν := by
    intro r hr
    rw [hν, Measure.map_map (measurable_const_mul r) measurable_subtype_coe]
    have : (fun x => r * x) ∘ (Subtype.val : R → G) = Subtype.val ∘ (fun y : R => (⟨r, hr⟩ : R) * y) := rfl
    rw [this, ← Measure.map_map measurable_subtype_coe (measurable_const_mul _), map_mul_left_eq_self]
  have hright0 : ∀ r ∈ R, ∃ c : NNReal, Measure.map (fun x => x * r) ν = c • ν := by
    intro r hr
    have := Measure.isHaarMeasure_map_mul_right νR (⟨r, hr⟩ : R)
    refine ⟨(Measure.map (fun y : R => y * ⟨r, hr⟩) νR).haarScalarFactor νR, ?_⟩
    rw [hν, Measure.map_map (measurable_mul_const r) measurable_subtype_coe]
    have : (fun x => x * r) ∘ (Subtype.val : R → G) = Subtype.val ∘ (fun y : R => y * (⟨r, hr⟩ : R)) := rfl
    rw [this, ← Measure.map_map measurable_subtype_coe (measurable_mul_const _),
      ← Measure.map_smul, ← Measure.isMulLeftInvariant_eq_smul]
  have : SMulInvariantMeasure Γ G ν := ⟨fun c A hA => by
    have := congrArg (fun m : Measure G => m A) (hleft c (hΓR c.2))
    rw [Measure.map_apply (measurable_const_mul _) hA] at this
    exact this⟩
  have hDfd : IsFundamentalDomain Γ D ν := by
    refine isFD_of_strict ν hDm ?_ ?_
    · filter_upwards [hae] with x hx
      obtain ⟨s, hs, h⟩ := hDc x hx
      exact ⟨⟨s, hs⟩, h⟩
    · intro x hx g hg
      exact Subtype.ext (hDu x hx g g.2 hg)
  have hD0 : ν D ≠ 0 := fd_ne_zero hDfd hνuniv
  have hDtop : ν D ≠ ∞ := (lt_of_le_of_lt (measure_mono hDK) (hνK K hK)).ne

  have hTfd : ∀ r ∈ R, IsFundamentalDomain Γ ((fun x => x * r⁻¹) ⁻¹' D) ν := by
    intro r hr
    refine isFD_of_strict ν ((measurable_mul_const _) hDm) ?_ ?_
    · filter_upwards [hae] with x hx
      obtain ⟨s, hs, h⟩ := hDc (x * r⁻¹) (R.mul_mem hx (R.inv_mem hr))
      exact ⟨⟨s, hs⟩, by simpa [mul_assoc] using h⟩
    · intro x hx g hg
      refine Subtype.ext (hDu (x * r⁻¹) hx g g.2 ?_)
      have hg' : (g : G) * x * r⁻¹ ∈ D := hg
      simpa [mul_assoc] using hg'
  have hright : ∀ r ∈ R, Measure.map (fun x => x * r) ν = ν := by
    intro r hr
    obtain ⟨c, hc⟩ := hright0 r⁻¹⁻¹ (R.inv_mem (R.inv_mem hr))
    have h1 : ν ((fun x => x * r⁻¹⁻¹) ⁻¹' D) = ν D := (hTfd r⁻¹ (R.inv_mem hr)).measure_eq hDfd
    rw [← Measure.map_apply (measurable_mul_const _) hDm, hc, Measure.smul_apply] at h1
    have h1' : (c : ℝ≥0∞) * ν D = ν D := by
      rw [ENNReal.smul_def, smul_eq_mul] at h1; exact h1
    have hc1 : (c : ℝ≥0∞) = 1 := by
      have h2 : ν D * c = ν D * 1 := by rw [mul_one, mul_comm]; exact h1'
      exact (ENNReal.mul_right_inj hD0 hDtop).1 h2
    rw [inv_inv] at hc
    have hc1' : c = 1 := by exact_mod_cast hc1
    rw [hc, hc1', one_smul]

  set χ' : G → ℂ := (R : Set G).indicator χ with hχ'
  have hχ'inv : ∀ s ∈ Γ, ∀ x, χ' (s * x) = χ' x := by
    intro s hs x
    by_cases hx : x ∈ R
    · have hsx : s * x ∈ R := R.mul_mem (hΓR hs) hx
      simp only [hχ', Set.indicator_of_mem (show s * x ∈ (R : Set G) from hsx),
        Set.indicator_of_mem (show x ∈ (R : Set G) from hx), hχm s (hΓR hs) x hx, hχΓ s hs, one_mul]
    · have hsx : s * x ∉ R := fun h => hx ((R.mul_mem_cancel_left (hΓR hs)).1 h)
      simp only [hχ', Set.indicator_of_notMem (show s * x ∉ (R : Set G) from hsx),
        Set.indicator_of_notMem (show x ∉ (R : Set G) from hx)]
  have hI : ∫ x in D, χ' x ∂ν = 0 := by
    obtain ⟨r0, hr0, hne⟩ := hχne
    have hmp : MeasurePreserving (fun x => x * r0) ν ν := ⟨measurable_mul_const r0, hright r0 hr0⟩
    have h1 := hmp.setIntegral_image_emb (MeasurableEquiv.mulRight r0).measurableEmbedding χ' D
    rw [Set.image_mul_right] at h1
    have h2 := (hTfd r0 hr0).setIntegral_eq hDfd (f := χ') fun g x => hχ'inv g g.2 x
    have h3 : ∫ x in D, χ' (x * r0) ∂ν = (∫ x in D, χ' x ∂ν) * χ r0 := by
      rw [← integral_mul_const]
      refine setIntegral_congr_fun hDm fun x hx => ?_
      have hxR : x ∈ R := hDR hx
      simp only [hχ', Set.indicator_of_mem (show x * r0 ∈ (R : Set G) from R.mul_mem hxR hr0),
        Set.indicator_of_mem (show x ∈ (R : Set G) from hxR), hχm x hxR r0 hr0]
    rw [h2, h3] at h1
    have h4 : (∫ x in D, χ' x ∂ν) * (χ r0 - 1) = 0 := by rw [mul_sub, mul_one, ← h1, sub_self]
    exact (mul_eq_zero.1 h4).resolve_right (sub_ne_zero.2 hne)

  set νi : Measure G := ν.map (fun x => x⁻¹) with hνi
  have hνiapp : ∀ A : Set G, MeasurableSet A → νi A = ν ((fun x => x⁻¹) ⁻¹' A) := fun A hA =>
    Measure.map_apply measurable_inv hA
  have hνiRc : νi (R : Set G)ᶜ = 0 := by
    rw [hνiapp _ hR.isOpen_compl.measurableSet]
    have : (fun x : G => x⁻¹) ⁻¹' (R : Set G)ᶜ = (R : Set G)ᶜ := by ext x; simp
    rw [this, hνRc]
  have haei : ∀ᵐ x ∂νi, x ∈ R := by rw [ae_iff]; exact hνiRc
  have hνiuniv : νi univ ≠ 0 := by rw [hνiapp _ MeasurableSet.univ, Set.preimage_univ]; exact hνuniv
  have : SMulInvariantMeasure Γ G νi := ⟨fun c A hA => by
    rw [hνiapp _ (measurable_const_smul c hA), hνiapp _ hA]
    have h : (Measure.map (fun x => x * (c : G)⁻¹) ν) ((fun x => x⁻¹) ⁻¹' A) = ν ((fun x => x⁻¹) ⁻¹' A) := by
      rw [hright _ (R.inv_mem (hΓR c.2))]
    rw [Measure.map_apply (measurable_mul_const _) (measurable_inv hA)] at h
    have e : (fun x : G => x⁻¹) ⁻¹' ((fun x => c • x) ⁻¹' A) =
        (fun x => x * (c : G)⁻¹) ⁻¹' ((fun x => x⁻¹) ⁻¹' A) := by
      ext x; simp [Subgroup.smul_def, mul_inv_rev]
    rw [e]; exact h⟩
  have hDfdi : IsFundamentalDomain Γ D νi := by
    refine isFD_of_strict νi hDm ?_ ?_
    · filter_upwards [haei] with x hx
      obtain ⟨s, hs, h⟩ := hDc x hx
      exact ⟨⟨s, hs⟩, h⟩
    · intro x hx g hg
      exact Subtype.ext (hDu x hx g g.2 hg)
  set κ := νi D with hκ
  have hκ0 : κ ≠ 0 := fd_ne_zero hDfdi hνiuniv
  have hκtop : κ ≠ ∞ := by
    rw [hκ, hνiapp _ hDm]
    exact (lt_of_le_of_lt (measure_mono (show (fun x : G => x⁻¹) ⁻¹' D ⊆ K⁻¹ from fun x hx => hDK hx))
      (hνK _ hK.inv)).ne
  have hκx : ∀ x, ν {r | r⁻¹ * x ∈ Ω} = κ := by
    intro x
    have hfd : IsFundamentalDomain Γ ((fun y => y * x) ⁻¹' Ω) νi := by
      refine isFD_of_strict νi ((measurable_mul_const x) hΩm) (Filter.Eventually.of_forall fun y => ?_) ?_
      · obtain ⟨s, hs, h⟩ := hΩc (y * x)
        refine ⟨⟨s, hs⟩, ?_⟩
        show (s : G) * y * x ∈ Ω
        rw [mul_assoc]; exact h
      · intro y hy g hg
        have hg' : (g : G) * y * x ∈ Ω := hg
        rw [mul_assoc] at hg'
        exact Subtype.ext (hΩu (y * x) hy g g.2 hg')
    have := hfd.measure_eq hDfdi
    rw [hνiapp _ ((measurable_mul_const x) hΩm)] at this
    exact this

  have : MeasurableConstSMul Γ (G × G) :=
    ⟨fun c => (measurable_const_mul (c : G)).prodMap (measurable_const_mul (c : G))⟩
  have : SMulInvariantMeasure Γ (G × G) (ν.prod μ) := ⟨fun c A hA => by
    have h1 : MeasurePreserving (fun x => (c : G) * x) ν ν := ⟨measurable_const_mul _, hleft c (hΓR c.2)⟩
    have h2 := h1.prod (measurePreserving_mul_left μ (c : G))
    exact h2.measure_preimage hA.nullMeasurableSet⟩
  set H : G × G → V := {p : G × G | p.1⁻¹ * p.2 ∈ Ω}.indicator (fun p => f p.2) with hH
  have hSm : MeasurableSet {p : G × G | p.1⁻¹ * p.2 ∈ Ω} := (measurable_fst.inv.mul measurable_snd) hΩm
  have hfΓ : ∀ s ∈ Γ, ∀ x, f (s * x) = f x := fun s hs x => by rw [hf s (hΓR hs), hχΓ s hs, one_smul]
  have hHinv : ∀ (g : Γ) (p : G × G), H (g • p) = H p := by
    intro g p
    have e1 : (g • p).1⁻¹ * (g • p).2 = p.1⁻¹ * p.2 := by
      show ((g : G) * p.1)⁻¹ * ((g : G) * p.2) = p.1⁻¹ * p.2
      group
    by_cases h : p.1⁻¹ * p.2 ∈ Ω
    · rw [hH, Set.indicator_of_mem (show g • p ∈ {p : G × G | p.1⁻¹ * p.2 ∈ Ω} from by
          show (g • p).1⁻¹ * (g • p).2 ∈ Ω; rw [e1]; exact h),
        Set.indicator_of_mem (show p ∈ {p : G × G | p.1⁻¹ * p.2 ∈ Ω} from h)]
      exact hfΓ g g.2 p.2
    · rw [hH, Set.indicator_of_notMem (show g • p ∉ {p : G × G | p.1⁻¹ * p.2 ∈ Ω} from by
          show ¬ (g • p).1⁻¹ * (g • p).2 ∈ Ω; rw [e1]; exact h),
        Set.indicator_of_notMem (show p ∉ {p : G × G | p.1⁻¹ * p.2 ∈ Ω} from h)]
  have hFD1 : IsFundamentalDomain Γ (univ ×ˢ Ω) (ν.prod μ) := by
    refine isFD_of_strict _ (MeasurableSet.univ.prod hΩm) (Filter.Eventually.of_forall fun p => ?_) ?_
    · obtain ⟨s, hs, h⟩ := hΩc p.2
      exact ⟨⟨s, hs⟩, ⟨trivial, h⟩⟩
    · intro p hp g hg
      exact Subtype.ext (hΩu p.2 hp.2 g g.2 hg.2)
  have hFD2 : IsFundamentalDomain Γ (D ×ˢ univ) (ν.prod μ) := by
    have hnull : (ν.prod μ) {p : G × G | ¬ p.1 ∈ R} = 0 := by
      have : {p : G × G | ¬ p.1 ∈ R} = (R : Set G)ᶜ ×ˢ univ := by ext p; simp
      rw [this, Measure.prod_prod, hνRc, zero_mul]
    have hae2 : ∀ᵐ p ∂(ν.prod μ), p.1 ∈ R := by rw [ae_iff]; exact hnull
    refine isFD_of_strict _ (hDm.prod MeasurableSet.univ) ?_ ?_
    · filter_upwards [hae2] with p hp
      obtain ⟨s, hs, h⟩ := hDc p.1 hp
      exact ⟨⟨s, hs⟩, ⟨h, trivial⟩⟩
    · intro p hp g hg
      exact Subtype.ext (hDu p.1 hp.1 g g.2 hg.1)
  have hEq := hFD1.setIntegral_eq hFD2 (f := H) hHinv

  have hSy : ∀ y, MeasurableSet {r : G | r⁻¹ * y ∈ Ω} := fun y => (measurable_inv.mul_const y) hΩm
  have hHy : ∀ y, (fun r => H (r, y)) = {r : G | r⁻¹ * y ∈ Ω}.indicator (fun _ => f y) := by
    intro y; ext r; simp [hH, Set.indicator]
  have hL : ∫ p in univ ×ˢ Ω, H p ∂(ν.prod μ) = κ.toReal • ∫ x in Ω, f x ∂μ := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
    have hint2 : Integrable H (ν.prod (μ.restrict Ω)) := by
      have hm0 : AEStronglyMeasurable (fun p : G × G => f p.2) (ν.prod (μ.restrict Ω)) :=
        hint.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
      have hm : AEStronglyMeasurable H (ν.prod (μ.restrict Ω)) := by
        rw [hH]; exact hm0.indicator hSm
      refine (integrable_prod_iff' hm).2 ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
      · rw [hHy y]
        exact (integrable_indicator_iff (hSy y)).2 (integrableOn_const (by rw [hκx y]; exact hκtop))
      · have : (fun y => ∫ r, ‖H (r, y)‖ ∂ν) = fun y => κ.toReal * ‖f y‖ := by
          funext y
          have e2 : (fun r => ‖H (r, y)‖) = {r : G | r⁻¹ * y ∈ Ω}.indicator (fun _ => ‖f y‖) := by
            ext r; simp [hH, Set.indicator]; split_ifs <;> simp
          rw [e2, integral_indicator_const _ (hSy y), measureReal_def, hκx y, smul_eq_mul]
        rw [this]
        exact hint.norm.const_mul _
    rw [integral_prod_symm H hint2]
    have : (fun y => ∫ r, H (r, y) ∂ν) = fun y => κ.toReal • f y := by
      funext y; rw [hHy y, integral_indicator_const _ (hSy y), measureReal_def, hκx y]
    rw [this, integral_smul]

  have hemb : MeasurableEmbedding (fun z : G × G => (z.1, z.1 * z.2)) := by
    exact (MeasurableEquiv.shearMulRight G).measurableEmbedding
  have hRt : ∫ p in D ×ˢ univ, H p ∂(ν.prod μ) = (∫ x in D, χ' x ∂ν) • ∫ x in Ω, f x ∂μ := by
    rw [← integral_indicator (hDm.prod MeasurableSet.univ),
      ← (measurePreserving_prod_mul ν μ).integral_comp hemb]
    have e : ∀ z : G × G, (D ×ˢ (univ : Set G)).indicator H (z.1, z.1 * z.2) =
        D.indicator χ' z.1 • Ω.indicator f z.2 := by
      rintro ⟨r, y⟩
      by_cases hr : r ∈ D
      · have hrR : r ∈ R := hDR hr
        have hH' : H (r, r * y) = Ω.indicator (fun y => f (r * y)) y := by
          simp [hH, Set.indicator, inv_mul_cancel_left]
        rw [Set.indicator_of_mem (show (r, r * y) ∈ D ×ˢ (univ : Set G) from ⟨hr, trivial⟩), hH',
          Set.indicator_of_mem hr]
        by_cases hy : y ∈ Ω
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, hf r hrR, hχ',
            Set.indicator_of_mem (show r ∈ (R : Set G) from hrR)]
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, smul_zero]
      · rw [Set.indicator_of_notMem (show (r, r * y) ∉ D ×ˢ (univ : Set G) from fun h => hr h.1),
          Set.indicator_of_notMem hr, zero_smul]
    show ∫ z, (D ×ˢ (univ : Set G)).indicator H (z.1, z.1 * z.2) ∂(ν.prod μ) = _
    rw [show (fun z : G × G => (D ×ˢ (univ : Set G)).indicator H (z.1, z.1 * z.2)) =
      fun z => D.indicator χ' z.1 • Ω.indicator f z.2 from funext e]
    rw [integral_prod_smul, integral_indicator hDm, integral_indicator hΩm]
  have hfin : κ.toReal • ∫ x in Ω, f x ∂μ = 0 := by rw [← hL, hEq, hRt, hI, zero_smul]
  have hκr : κ.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hκ0, hκtop⟩
  exact (smul_eq_zero.1 hfin).resolve_left hκr

end Formalism.L2.SG.AvgPf
