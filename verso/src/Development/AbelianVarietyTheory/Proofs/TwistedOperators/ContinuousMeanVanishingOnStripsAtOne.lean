import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqMeanIntermediateSubgroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalUnitarySubgroupCountableDiscreteFundDoma
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.StripVanish

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D W vW R K hRc hsplit hKf hKc hKo μR hμR hμRinv 𝓡 𝓑 h𝓡 h𝓑 f hfm hfl hfi hfiR hTc hfK hsupp hstrip`. Use `haveI := vW.haar`. Use `haveI : LocallyCompactSpace R := hRc.locallyCompactSpace`. Use `haveI : μR.IsMulRightInvariant := by rw [← Measure.inv_eq_self μR]; infer_instance`. Take `⟨hinfC, -, hcomm, ⟨e, he⟩, -⟩` from `GlobalTheory.AdelicSplit.adelic_split D W`.

Take `⟨hΓc, hΓd, -⟩` from `GlobalTheory.RationalSubgroupFund.countable_discrete_exists_fundamentalDomain D W (GQ W ⊓ R) inf_le_left`. Use `set T : GA D W → ℂ := fun h => ∫ r in 𝓡, f ((r : GA D W) * h) ∂μR with hTdef`. Establish `hQ` using `GlobalTheory.quot_fubini_mean (GA D W) vW.μ R (GQ W ⊓ R) inf_le_right hRc hΓc hΓd μR hμR 𝓡 𝓑 h𝓡 h𝓑 f hfm hfl hfi hfiR`. Establish `hTl : ∀ s ∈ R, ∀ x, T (s * x) = T x` using `fun s hs x => hQ.left hs x`. Establish `hTr : ∀ k ∈ K, ∀ x, T (x * k) = T x`.

Introduce `k hk x`. Simplify using `only [hTdef]`. Use `congr 1`. Use function extensionality and compare the values at `r`. Rewrite using `[← mul_assoc, hfK k hk]`.

Establish `h1 : T 1 = ∫ r in 𝓡, f (r : GA D W) ∂μR` using `by simp [hTdef]`. Rewrite using `[← h1]`. Assume the negation of the conclusion as `hT1`. Establish `hsupT : ∀ x, T x ≠ 0 → ∃ q ∈ R, ∃ a ∈ GinfC W, ∃ k ∈ K, x = q * a * k`. Introduce `x hx`.

Assume the negation of the conclusion as `hno`. Apply `hx` to reduce the goal to its premises. Establish `hz : ∀ r : R, f ((r : GA D W) * x) = 0`. Introduce `r`. Assume the negation of the conclusion as `hr`.

Take `⟨r₁, hr₁, a, ha, k, hk, hrx⟩` from `hsupp _ hr`. Use `hno ⟨(r : GA D W)⁻¹ * r₁, R.mul_mem (R.inv_mem r.2) hr₁, a, ha, k, hk, ?_⟩` and prove the remaining obligations. Rewrite using `[show x = (r : GA D W)⁻¹ * ((r : GA D W) * x) by group, hrx]`. Use `group`. Simplify using `[hTdef, hz]`.

Establish `hP : ∀ C : Set (GA D W), C ⊆ GinfC W → ∀ x ∈ strip W R C, T x ≠ 0 → ∃ c ∈ C, T x = T c`. Introduce and unpack `C hC x ⟨r, hr, c, hc, b, hb, rfl⟩ hx`. Take `⟨q, hq, a, ha, k, hk, hx'⟩` from `hsupT _ hx`. Establish `hkb : k * b⁻¹ ∈ GfC W` using `(GfC W).mul_mem (hKf hk) ((GfC W).inv_mem hb)`. Establish `hc' : c⁻¹ ∈ GinfC W` using `(GinfC W).inv_mem (hC hc)`.

Establish `hac : a * c⁻¹ ∈ GinfC W` using `(GinfC W).mul_mem ha hc'`. Establish `e1 : c⁻¹ * (k * b⁻¹) = (k * b⁻¹) * c⁻¹` using `hcomm _ hc' _ hkb`. Establish `hmem : (a * c⁻¹) * (k * b⁻¹) ∈ R`. Establish `: (a * c⁻¹) * (k * b⁻¹) = q⁻¹ * r`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[this]`. Conclude with `R.mul_mem (R.inv_mem hq) hr`. Take `⟨hacR, -⟩` from `hsplit _ hac _ hkb hmem`. Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Use `set U : Set (GA D W) := {h | (1 : ℝ) / 2 < (T h / T 1).re} with hUdef`. Establish `hUo : IsOpen U` using `isOpen_lt continuous_const (Complex.continuous_re.comp (hTc.div_const (T 1)))`. Establish `h1U : (1 : GA D W) ∈ U` using `by show (1 : ℝ) / 2 < (T 1 / T 1).re`. Rewrite using `[div_self hT1]`. Evaluate the numerical expressions.

Use `haveI : LocallyCompactSpace (GinfC W) := hinfC.locallyCompactSpace`. Establish `hU'o : IsOpen ((Subtype.val : GinfC W → GA D W) ⁻¹' U)` using `hUo.preimage continuous_subtype_val`. Take `⟨C', hC'n, hC'U, hC'c⟩` from `local_compact_nhds (hU'o.mem_nhds (show ((1 : GinfC W) : GA D W) ∈ U from h1U))`. Use `set C : Set (GA D W) := Subtype.val '' C' with hCdef`. Establish `hCinf : C ⊆ GinfC W` using `by rintro _ ⟨y, -, rfl⟩; exact y.2`.

Establish `hCU : C ⊆ U` using `by rintro _ ⟨y, hy, rfl⟩; exact hC'U hy`. Take `⟨hSm, hS0⟩` from `hstrip C (hC'c.image continuous_subtype_val) hCinf`. Use `set S := strip W R C with hSdef`. Establish `hSinv : ∀ s ∈ R, ∀ x, s * x ∈ S ↔ x ∈ S`. Introduce `s hs x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr, c, hc, b, hb, hx⟩`. Use `⟨s⁻¹ * r, R.mul_mem (R.inv_mem hs) hr, c, hc, b, hb, ?_⟩` and prove the remaining obligations. Rewrite using `[show x = s⁻¹ * (s * x) by group, hx]; group`. Introduce and unpack `⟨r, hr, c, hc, b, hb, rfl⟩`.

Conclude with `⟨s * r, R.mul_mem hs hr, c, hc, b, hb, by group⟩`. Establish `hfSl : ∀ γ ∈ GQ W ⊓ R, ∀ g, S.indicator f (γ * g) = S.indicator f g`. Introduce `γ hγ g`. Distinguish the cases in `hg : g ∈ S`. Rewrite using `[Set.indicator_of_mem hg, Set.indicator_of_mem ((hSinv γ hγ.2 g).2 hg), hfl γ hγ g]`.

Rewrite using `[Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt (hSinv γ hγ.2 g).1 hg)]`. Establish `hfSi : ∀ h, IntegrableOn (fun r : R => S.indicator f ((r : GA D W) * h)) 𝓡 μR`. Introduce `h`. Distinguish the cases in `hh : h ∈ S`. Establish `: (fun r : R => S.indicator f ((r : GA D W) * h)) = fun r : R => f ((r : GA D W) * h)`.

Use function extensionality and compare the values at `fun r => Set.indicator_of_mem ((hSinv _ r.2 h).2 hh) _`. Rewrite using `[this]`. Conclude with `hfiR h`. Establish `: (fun r : R => S.indicator f ((r : GA D W) * h)) = fun _ => 0`. Use function extensionality and compare the values at `fun r => by simp [Set.indicator_apply, hSinv _ r.2 h, hh]`.

Rewrite using `[this]`. Conclude with `integrableOn_zero`. Establish `hQS` using `GlobalTheory.quot_fubini_mean (GA D W) vW.μ R (GQ W ⊓ R) inf_le_right hRc hΓc hΓd μR hμR 𝓡 𝓑 h𝓡 h𝓑 (S.indicator f) (hfm.indicator hSm) hfSl (hfi.indicator hSm) hfSi`. Establish `hQS' : IsQuotIntL1 μR vW.μ (S.indicator T) 0`. Establish `e1 : (fun h => ∫ r in 𝓡, S.indicator f ((r : GA D W) * h) ∂μR) = S.indicator T`.

Use function extensionality and compare the values at `h`. Distinguish the cases in `hh : h ∈ S`. Rewrite using `[Set.indicator_of_mem hh]`. Simplify using `only [hTdef]`. Use `congr 1`.

Use function extensionality and compare the values at `r`. Conclude with `Set.indicator_of_mem ((hSinv _ r.2 h).2 hh) _`. Simplify using `[Set.indicator_apply, hSinv _ (Subtype.property _) h, hh]`. Establish `e2 : ∫ g in 𝓑, S.indicator f g ∂vW.μ = 0` using `by rw [setIntegral_indicator hSm, hS0]`. Rewrite `hQS` using `[e1, e2]`.

Conclude with `hQS`. Take `⟨β, -, hβ⟩` from `GlobalTheory.Tw.exists_isCosetCutoff (μT := μR) hRc`. Take `⟨hβi, hβ0⟩` from `hQS'.cutoff hβ`. Establish `hre : ∀ x, 0 ≤ (S.indicator T x / T 1).re ∧ (x ∈ S → T x ≠ 0 → (1 : ℝ) / 2 < (S.indicator T x / T 1).re)`. Introduce `x`.

Distinguish the cases in `hxS : x ∈ S`. Rewrite using `[Set.indicator_of_mem hxS]`. Distinguish the cases in `hx : T x = 0`. Simplify using `[hx]`. Take `⟨c, hc, hTc'⟩` from `hP C hCinf x hxS hx`.

Establish `h2 : (1 : ℝ) / 2 < (T x / T 1).re` using `by rw [hTc']; exact hCU hc`. Conclude with `⟨by linarith, fun _ _ => h2⟩`. Simplify using `[Set.indicator_of_notMem hxS, hxS]`. Use `set φ : GA D W → ℝ := fun x => ((β x : ℝ) • S.indicator T x / T 1).re with hφdef`. Establish `hφ : ∀ x, φ x = (β x : ℝ) * (S.indicator T x / T 1).re`.

Introduce `x`. Simplify using `only [hφdef, Complex.real_smul, mul_div_assoc, Complex.re_ofReal_mul]`. Establish `hφnn : 0 ≤ φ` using `fun x => by rw [hφ]; exact mul_nonneg (NNReal.coe_nonneg _) (hre x).1`. Establish `hφi : Integrable φ vW.μ` using `(hβi.div_const (T 1)).re`. Establish `hφ0 : ∫ x, φ x ∂vW.μ = 0`.

Establish `h` using `integral_re (hβi.div_const (T 1))`. Simplify using `only [RCLike.re_to_complex] at h`. Simplify using `only [hφdef]`. Rewrite using `[h, integral_div, ← hβ0, zero_div, Complex.zero_re]`. Establish `hφae` using `(integral_eq_zero_iff_of_nonneg hφnn hφi).1 hφ0`.

Use `set A : Set (GA D W) := S ∩ {x | T x ≠ 0} with hAdef`. Establish `hAm : MeasurableSet A` using `hSm.inter (hTc.measurable (measurableSet_singleton (0 : ℂ)).compl)`. Establish `hAinv : ∀ s ∈ R, ∀ x, s * x ∈ A ↔ x ∈ A`. Introduce `s hs x`. Simplify using `only [hAdef, Set.mem_inter_iff, Set.mem_setOf_eq, hSinv s hs x, hTl s hs x]`.

Use `set g : GA D W → ENNReal := A.indicator fun x => (β x : ENNReal) with hgdef`. Establish `hgm : Measurable g` using `hβ.1.coe_nnreal_ennreal.indicator hAm`. Establish `hg0 : ∫⁻ x, g x ∂vW.μ = 0`. Rewrite using `[lintegral_eq_zero_iff hgm]`. Use `filter_upwards [hφae] with x hx`.

Distinguish the cases in `hxA : x ∈ A`. Establish `h2` using `(hre x).2 hxA.1 hxA.2`. Rewrite `hx` using `[Pi.zero_apply, hφ]`. Establish `: (β x : ℝ) = 0`. Break down `mul_eq_zero.1 hx with h | h` into its components or cases.

Conclude with `h`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `[hgdef, Set.indicator_of_mem hxA, Pi.zero_apply, NNReal.coe_eq_zero.1 this]`. Simplify using `[hgdef, Set.indicator_of_notMem hxA]`. Establish `hA0 : vW.μ A = 0`.

Establish `hmul : Measurable fun p : GA D W × R => (p.2 : GA D W) * p.1` using `(measurable_subtype_coe.comp measurable_snd).mul measurable_fst`. Establish `e1 : vW.μ A = ∫⁻ x, ∫⁻ t : R, g ((t : GA D W) * x) ∂μR ∂vW.μ`. Rewrite using `[← lintegral_indicator_one hAm]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hxA : x ∈ A`.

Establish `: ∀ t : R, g ((t : GA D W) * x) = β ((t : GA D W) * x)` using `fun t => by`. Simplify using `[hgdef, Set.indicator_of_mem ((hAinv _ t.2 x).2 hxA)]`. Simplify using `only [this, hβ.2 x, Set.indicator_of_mem hxA, Pi.one_apply]`. Establish `: ∀ t : R, g ((t : GA D W) * x) = 0` using `fun t => by`. Simplify using `[hgdef, Set.indicator_of_notMem (mt (hAinv _ t.2 x).1 hxA)]`.

Simplify using `[this, Set.indicator_of_notMem hxA]`. Rewrite using `[e1, lintegral_lintegral_swap (f := fun x (t : R) => g ((t : GA D W) * x)) (hgm.comp hmul).aemeasurable]`. Establish `e2 : ∀ t : R, ∫⁻ x, g ((t : GA D W) * x) ∂vW.μ = 0` using `fun t => by`. Rewrite using `[lintegral_mul_left_eq_self, hg0]`. Simplify using `[e2]`.

Use `set O : Set (GA D W) := e '' (interior C' ×ˢ ((K.subgroupOf (GfC W) : Subgroup (GfC W)) : Set (GfC W))) with hOdef`. Establish `hOo : IsOpen O` using `e.isOpenMap _ (isOpen_interior.prod hKo)`. Establish `h1O : (1 : GA D W) ∈ O` using `⟨(1, 1), ⟨mem_interior_iff_mem_nhds.2 hC'n, (K.subgroupOf (GfC W)).one_mem⟩, by rw [he]; simp⟩`. Establish `hOA : O ⊆ A`. Introduce and unpack `_ ⟨p, ⟨hp1, hp2⟩, rfl⟩`.

Rewrite using `[he]`. Establish `hk : (p.2 : GA D W) ∈ K` using `Subgroup.mem_subgroupOf.1 hp2`. Use `⟨⟨1, R.one_mem, p.1, ⟨p.1, interior_subset hp1, rfl⟩, p.2, p.2.2, by simp⟩, ?_⟩` and prove the remaining obligations. Use `show T (p.1 * p.2) ≠ 0`. Rewrite using `[hTr _ hk]`.

Introduce `h0`. Use `hC'U (interior_subset hp1)` as an intermediate fact. Simplify using `only [Set.mem_preimage, hUdef, Set.mem_setOf_eq, h0, zero_div, Complex.zero_re] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpos` using `hOo.measure_pos vW.μ ⟨1, h1O⟩`.

Conclude with `hpos.ne' (measure_mono_null hOA hA0)`.
-/
theorem mean_eq_zero_of_strips : ∀ (D : D7) (W : HSp D) (vW : GlobalTheory.Unf.Vol W) (R K : Subgroup (GA D W)), IsClosed (R : Set (GA D W)) → (∀ a ∈ GinfC W, ∀ b ∈ GfC W, a * b ∈ R → a ∈ R ∧ b ∈ R) → K ≤ GfC W → IsCompact (K : Set (GA D W)) → IsOpen ((K.subgroupOf (GfC W) : Subgroup (GfC W)) : Set (GfC W)) → ∀ (μR : Measure R), μR.IsHaarMeasure → μR.IsInvInvariant → ∀ (𝓡 : Set R) (𝓑 : Set (GA D W)), IsFundamentalDomain ((GQ W ⊓ R).subgroupOf R) 𝓡 μR → IsFundamentalDomain (GQ W ⊓ R : Subgroup (GA D W)) 𝓑 vW.μ → ∀ f : GA D W → ℂ, Measurable f → (∀ γ ∈ GQ W ⊓ R, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓑 vW.μ → (∀ h, IntegrableOn (fun r : R => f (r * h)) 𝓡 μR) → (Continuous fun h => ∫ r in 𝓡, f ((r : GA D W) * h) ∂μR) → (∀ k ∈ K, ∀ g, f (g * k) = f g) → (∀ h, f h ≠ 0 → ∃ r ∈ R, ∃ a ∈ GinfC W, ∃ k ∈ K, h = r * a * k) → (∀ C : Set (GA D W), IsCompact C → C ⊆ GinfC W → MeasurableSet (strip W R C) ∧ ∫ h in 𝓑 ∩ strip W R C, f h ∂vW.μ = 0) → ∫ r in 𝓡, f r ∂μR = 0 := by
  intro D W vW R K hRc hsplit hKf hKc hKo μR hμR hμRinv 𝓡 𝓑 h𝓡 h𝓑 f hfm hfl hfi hfiR hTc hfK hsupp hstrip
  haveI := vW.haar
  haveI : LocallyCompactSpace R := hRc.locallyCompactSpace
  haveI : μR.IsMulRightInvariant := by rw [← Measure.inv_eq_self μR]; infer_instance
  obtain ⟨hinfC, -, hcomm, ⟨e, he⟩, -⟩ := GlobalTheory.AdelicSplit.adelic_split D W
  obtain ⟨hΓc, hΓd, -⟩ :=
    GlobalTheory.RationalSubgroupFund.countable_discrete_exists_fundamentalDomain D W (GQ W ⊓ R) inf_le_left
  set T : GA D W → ℂ := fun h => ∫ r in 𝓡, f ((r : GA D W) * h) ∂μR with hTdef
  have hQ := GlobalTheory.quot_fubini_mean (GA D W) vW.μ R (GQ W ⊓ R) inf_le_right hRc hΓc hΓd μR hμR 𝓡 𝓑 h𝓡 h𝓑 f hfm
    hfl hfi hfiR
  have hTl : ∀ s ∈ R, ∀ x, T (s * x) = T x := fun s hs x => hQ.left hs x
  have hTr : ∀ k ∈ K, ∀ x, T (x * k) = T x := by
    intro k hk x
    simp only [hTdef]
    congr 1
    funext r
    rw [← mul_assoc, hfK k hk]
  have h1 : T 1 = ∫ r in 𝓡, f (r : GA D W) ∂μR := by simp [hTdef]
  rw [← h1]
  by_contra hT1

  have hsupT : ∀ x, T x ≠ 0 → ∃ q ∈ R, ∃ a ∈ GinfC W, ∃ k ∈ K, x = q * a * k := by
    intro x hx
    by_contra hno
    apply hx
    have hz : ∀ r : R, f ((r : GA D W) * x) = 0 := by
      intro r
      by_contra hr
      obtain ⟨r₁, hr₁, a, ha, k, hk, hrx⟩ := hsupp _ hr
      refine hno ⟨(r : GA D W)⁻¹ * r₁, R.mul_mem (R.inv_mem r.2) hr₁, a, ha, k, hk, ?_⟩
      rw [show x = (r : GA D W)⁻¹ * ((r : GA D W) * x) by group, hrx]
      group
    simp [hTdef, hz]

  have hP : ∀ C : Set (GA D W), C ⊆ GinfC W → ∀ x ∈ strip W R C, T x ≠ 0 → ∃ c ∈ C, T x = T c := by
    rintro C hC x ⟨r, hr, c, hc, b, hb, rfl⟩ hx
    obtain ⟨q, hq, a, ha, k, hk, hx'⟩ := hsupT _ hx
    have hkb : k * b⁻¹ ∈ GfC W := (GfC W).mul_mem (hKf hk) ((GfC W).inv_mem hb)
    have hc' : c⁻¹ ∈ GinfC W := (GinfC W).inv_mem (hC hc)
    have hac : a * c⁻¹ ∈ GinfC W := (GinfC W).mul_mem ha hc'
    have e1 : c⁻¹ * (k * b⁻¹) = (k * b⁻¹) * c⁻¹ := hcomm _ hc' _ hkb
    have hmem : (a * c⁻¹) * (k * b⁻¹) ∈ R := by
      have : (a * c⁻¹) * (k * b⁻¹) = q⁻¹ * r := by
        calc (a * c⁻¹) * (k * b⁻¹) = a * (k * b⁻¹) * c⁻¹ := by rw [mul_assoc, e1, ← mul_assoc]
          _ = q⁻¹ * (q * a * k) * b⁻¹ * c⁻¹ := by group
          _ = q⁻¹ * (r * c * b) * b⁻¹ * c⁻¹ := by rw [hx']
          _ = q⁻¹ * r := by group
      rw [this]
      exact R.mul_mem (R.inv_mem hq) hr
    obtain ⟨hacR, -⟩ := hsplit _ hac _ hkb hmem
    refine ⟨c, hc, ?_⟩
    calc T (r * c * b) = T (q * (a * k)) := by rw [hx', mul_assoc]
      _ = T a := by rw [hTl q hq, hTr k hk]
      _ = T ((a * c⁻¹) * c) := by group
      _ = T c := hTl _ hacR c

  set U : Set (GA D W) := {h | (1 : ℝ) / 2 < (T h / T 1).re} with hUdef
  have hUo : IsOpen U := isOpen_lt continuous_const (Complex.continuous_re.comp (hTc.div_const (T 1)))
  have h1U : (1 : GA D W) ∈ U := by
    show (1 : ℝ) / 2 < (T 1 / T 1).re
    rw [div_self hT1]; norm_num
  haveI : LocallyCompactSpace (GinfC W) := hinfC.locallyCompactSpace
  have hU'o : IsOpen ((Subtype.val : GinfC W → GA D W) ⁻¹' U) := hUo.preimage continuous_subtype_val
  obtain ⟨C', hC'n, hC'U, hC'c⟩ :=
    local_compact_nhds (hU'o.mem_nhds (show ((1 : GinfC W) : GA D W) ∈ U from h1U))
  set C : Set (GA D W) := Subtype.val '' C' with hCdef
  have hCinf : C ⊆ GinfC W := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hCU : C ⊆ U := by rintro _ ⟨y, hy, rfl⟩; exact hC'U hy
  obtain ⟨hSm, hS0⟩ := hstrip C (hC'c.image continuous_subtype_val) hCinf
  set S := strip W R C with hSdef
  have hSinv : ∀ s ∈ R, ∀ x, s * x ∈ S ↔ x ∈ S := by
    intro s hs x
    constructor
    · rintro ⟨r, hr, c, hc, b, hb, hx⟩
      refine ⟨s⁻¹ * r, R.mul_mem (R.inv_mem hs) hr, c, hc, b, hb, ?_⟩
      rw [show x = s⁻¹ * (s * x) by group, hx]; group
    · rintro ⟨r, hr, c, hc, b, hb, rfl⟩
      exact ⟨s * r, R.mul_mem hs hr, c, hc, b, hb, by group⟩

  have hfSl : ∀ γ ∈ GQ W ⊓ R, ∀ g, S.indicator f (γ * g) = S.indicator f g := by
    intro γ hγ g
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((hSinv γ hγ.2 g).2 hg), hfl γ hγ g]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt (hSinv γ hγ.2 g).1 hg)]
  have hfSi : ∀ h, IntegrableOn (fun r : R => S.indicator f ((r : GA D W) * h)) 𝓡 μR := by
      intro h
      by_cases hh : h ∈ S
      · have : (fun r : R => S.indicator f ((r : GA D W) * h)) = fun r : R => f ((r : GA D W) * h) :=
          funext fun r => Set.indicator_of_mem ((hSinv _ r.2 h).2 hh) _
        rw [this]; exact hfiR h
      · have : (fun r : R => S.indicator f ((r : GA D W) * h)) = fun _ => 0 :=
          funext fun r => by simp [Set.indicator_apply, hSinv _ r.2 h, hh]
        rw [this]; exact integrableOn_zero
  have hQS := GlobalTheory.quot_fubini_mean (GA D W) vW.μ R (GQ W ⊓ R) inf_le_right hRc hΓc hΓd μR hμR 𝓡 𝓑 h𝓡 h𝓑
    (S.indicator f) (hfm.indicator hSm) hfSl (hfi.indicator hSm) hfSi
  have hQS' : IsQuotIntL1 μR vW.μ (S.indicator T) 0 := by
    have e1 : (fun h => ∫ r in 𝓡, S.indicator f ((r : GA D W) * h) ∂μR) = S.indicator T := by
      funext h
      by_cases hh : h ∈ S
      · rw [Set.indicator_of_mem hh]
        simp only [hTdef]
        congr 1; funext r
        exact Set.indicator_of_mem ((hSinv _ r.2 h).2 hh) _
      · simp [Set.indicator_apply, hSinv _ (Subtype.property _) h, hh]
    have e2 : ∫ g in 𝓑, S.indicator f g ∂vW.μ = 0 := by rw [setIntegral_indicator hSm, hS0]
    rw [e1, e2] at hQS
    exact hQS
  obtain ⟨β, -, hβ⟩ := GlobalTheory.Tw.exists_isCosetCutoff (μT := μR) hRc
  obtain ⟨hβi, hβ0⟩ := hQS'.cutoff hβ

  have hre : ∀ x, 0 ≤ (S.indicator T x / T 1).re ∧ (x ∈ S → T x ≠ 0 → (1 : ℝ) / 2 < (S.indicator T x / T 1).re) := by
    intro x
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem hxS]
      by_cases hx : T x = 0
      · simp [hx]
      · obtain ⟨c, hc, hTc'⟩ := hP C hCinf x hxS hx
        have h2 : (1 : ℝ) / 2 < (T x / T 1).re := by rw [hTc']; exact hCU hc
        exact ⟨by linarith, fun _ _ => h2⟩
    · simp [Set.indicator_of_notMem hxS, hxS]
  set φ : GA D W → ℝ := fun x => ((β x : ℝ) • S.indicator T x / T 1).re with hφdef
  have hφ : ∀ x, φ x = (β x : ℝ) * (S.indicator T x / T 1).re := by
    intro x
    simp only [hφdef, Complex.real_smul, mul_div_assoc, Complex.re_ofReal_mul]
  have hφnn : 0 ≤ φ := fun x => by rw [hφ]; exact mul_nonneg (NNReal.coe_nonneg _) (hre x).1
  have hφi : Integrable φ vW.μ := (hβi.div_const (T 1)).re
  have hφ0 : ∫ x, φ x ∂vW.μ = 0 := by
    have h := integral_re (hβi.div_const (T 1))
    simp only [RCLike.re_to_complex] at h
    simp only [hφdef]
    rw [h, integral_div, ← hβ0, zero_div, Complex.zero_re]
  have hφae := (integral_eq_zero_iff_of_nonneg hφnn hφi).1 hφ0
  set A : Set (GA D W) := S ∩ {x | T x ≠ 0} with hAdef
  have hAm : MeasurableSet A := hSm.inter (hTc.measurable (measurableSet_singleton (0 : ℂ)).compl)
  have hAinv : ∀ s ∈ R, ∀ x, s * x ∈ A ↔ x ∈ A := by
    intro s hs x
    simp only [hAdef, Set.mem_inter_iff, Set.mem_setOf_eq, hSinv s hs x, hTl s hs x]
  set g : GA D W → ENNReal := A.indicator fun x => (β x : ENNReal) with hgdef
  have hgm : Measurable g := hβ.1.coe_nnreal_ennreal.indicator hAm
  have hg0 : ∫⁻ x, g x ∂vW.μ = 0 := by
    rw [lintegral_eq_zero_iff hgm]
    filter_upwards [hφae] with x hx
    by_cases hxA : x ∈ A
    · have h2 := (hre x).2 hxA.1 hxA.2
      rw [Pi.zero_apply, hφ] at hx
      have : (β x : ℝ) = 0 := by
        rcases mul_eq_zero.1 hx with h | h
        · exact h
        · linarith
      simp [hgdef, Set.indicator_of_mem hxA, Pi.zero_apply, NNReal.coe_eq_zero.1 this]
    · simp [hgdef, Set.indicator_of_notMem hxA]

  have hA0 : vW.μ A = 0 := by
    have hmul : Measurable fun p : GA D W × R => (p.2 : GA D W) * p.1 :=
      (measurable_subtype_coe.comp measurable_snd).mul measurable_fst
    have e1 : vW.μ A = ∫⁻ x, ∫⁻ t : R, g ((t : GA D W) * x) ∂μR ∂vW.μ := by
      rw [← lintegral_indicator_one hAm]
      refine lintegral_congr fun x => ?_
      by_cases hxA : x ∈ A
      · have : ∀ t : R, g ((t : GA D W) * x) = β ((t : GA D W) * x) := fun t => by
          simp [hgdef, Set.indicator_of_mem ((hAinv _ t.2 x).2 hxA)]
        simp only [this, hβ.2 x, Set.indicator_of_mem hxA, Pi.one_apply]
      · have : ∀ t : R, g ((t : GA D W) * x) = 0 := fun t => by
          simp [hgdef, Set.indicator_of_notMem (mt (hAinv _ t.2 x).1 hxA)]
        simp [this, Set.indicator_of_notMem hxA]
    rw [e1, lintegral_lintegral_swap (f := fun x (t : R) => g ((t : GA D W) * x)) (hgm.comp hmul).aemeasurable]
    have e2 : ∀ t : R, ∫⁻ x, g ((t : GA D W) * x) ∂vW.μ = 0 := fun t => by
      rw [lintegral_mul_left_eq_self, hg0]
    simp [e2]

  set O : Set (GA D W) := e '' (interior C' ×ˢ ((K.subgroupOf (GfC W) : Subgroup (GfC W)) : Set (GfC W))) with hOdef
  have hOo : IsOpen O := e.isOpenMap _ (isOpen_interior.prod hKo)
  have h1O : (1 : GA D W) ∈ O :=
    ⟨(1, 1), ⟨mem_interior_iff_mem_nhds.2 hC'n, (K.subgroupOf (GfC W)).one_mem⟩, by rw [he]; simp⟩
  have hOA : O ⊆ A := by
    rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
    rw [he]
    have hk : (p.2 : GA D W) ∈ K := Subgroup.mem_subgroupOf.1 hp2
    refine ⟨⟨1, R.one_mem, p.1, ⟨p.1, interior_subset hp1, rfl⟩, p.2, p.2.2, by simp⟩, ?_⟩
    show T (p.1 * p.2) ≠ 0
    rw [hTr _ hk]
    intro h0
    have := hC'U (interior_subset hp1)
    simp only [Set.mem_preimage, hUdef, Set.mem_setOf_eq, h0, zero_div, Complex.zero_re] at this
    linarith
  have hpos := hOo.measure_pos vW.μ ⟨1, h1O⟩
  exact hpos.ne' (measure_mono_null hOA hA0)

end GlobalTheory.StripVanish
