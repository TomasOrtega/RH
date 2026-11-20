import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPointsClassicalModelRealVectorSpaceStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompactStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.TorusMean

section Abstract

open Pointwise

variable {G V : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  (p : G →+ V) (R : V →+ G) (U : AddSubgroup G)

def tube : AddSubgroup G := U.comap (AddMonoidHom.id G - R.comp p)

omit [TopologicalSpace G] [IsTopologicalAddGroup G] [TopologicalSpace V] [IsTopologicalAddGroup V] in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_tube (w : G) : w ∈ tube p R U ↔ w - R (p w) ∈ U := Iff.rfl

variable {p R U}

omit [IsTopologicalAddGroup V] in

/- English proof (translation)
Use `⟨(fun x : G × V => x.1 + R x.2) '' ((U : Set G) ×ˢ K), (hU.prod hK).image (continuous_fst.add (hR.comp continuous_snd)), ?_⟩` and prove the remaining obligations. Introduce and unpack `w ⟨hwK, hwU⟩`. Use `⟨(w - R (p w), p w), ⟨(mem_tube p R U w).mp hwU, hwK⟩, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem exists_compact (hR : Continuous R) (hU : IsCompact (U : Set G)) {K : Set V} (hK : IsCompact K) :
    ∃ K' : Set G, IsCompact K' ∧ p ⁻¹' K ∩ tube p R U ⊆ K' := by
  refine ⟨(fun x : G × V => x.1 + R x.2) '' ((U : Set G) ×ˢ K),
    (hU.prod hK).image (continuous_fst.add (hR.comp continuous_snd)), ?_⟩
  rintro w ⟨hwK, hwU⟩
  refine ⟨(w - R (p w), p w), ⟨(mem_tube p R U w).mp hwU, hwK⟩, ?_⟩
  simp

/- English proof (translation)
Take `⟨K, hKc, hK0⟩` from `exists_compact_mem_nhds (0 : V)`. Take `⟨K', hK', hsub⟩` from `exists_compact (p := p) (U := U) hR hU hKc`. Establish `hΓc : IsClosed (Γ : Set G)` using `AddSubgroup.isClosed_of_discrete`. Establish `hfin : ((Γ : Set G) ∩ K').Finite`. Apply `(hK'.inter_left hΓc).finite` to reduce the goal to its premises.

Establish `hd : DiscreteTopology (Γ : Set G)` using `inferInstanceAs (DiscreteTopology Γ)`. Establish `hd' : DiscreteTopology ↥((Γ : Set G) ∩ K')` using `DiscreteTopology.of_subset hd Set.inter_subset_left`. Conclude with `⟨hd'⟩`. Establish `hLK : ((L : Set V) ∩ K).Finite`. Apply `(hfin.image p).subset` to reduce the goal to its premises.

Introduce and unpack `v ⟨hvL, hvK⟩`. Take `⟨γ, hγ, hγt, rfl⟩` from `hL v hvL`. Conclude with `⟨γ, ⟨hγ, hsub ⟨hvK, hγt⟩⟩, rfl⟩`. Apply `discreteTopology_of_isOpen_singleton_zero` to reduce the goal to its premises. Establish `hB : IsClosed (((L : Set V) ∩ K) \ {0})` using `(hLK.subset Set.sdiff_subset).isClosed`.

Use `isOpen_induced_iff.mpr ⟨interior K ∩ (((L : Set V) ∩ K) \ {0})ᶜ, isOpen_interior.inter hB.isOpen_compl, ?_⟩` and prove the remaining obligations. Use extensionality with `⟨v, hv⟩`. Simplify using `only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hvK, hvB⟩`.

Assume the negation of the conclusion as `hne`. Apply `hvB` to reduce the goal to its premises. Use `⟨⟨hv, interior_subset hvK⟩, ?_⟩` and prove the remaining obligations. Introduce `h0`. Conclude with `hne (Subtype.ext h0)`.

Introduce `h0`. Establish `hv0 : v = 0` using `congrArg Subtype.val h0`. Substitute `hv0` using the available equality. Conclude with `⟨mem_interior_iff_mem_nhds.mpr hK0, fun h => h.2 rfl⟩`.
-/
theorem discrete_image [T2Space G] [T2Space V] [LocallyCompactSpace V] (hR : Continuous R)
    (hU : IsCompact (U : Set G)) (Γ : AddSubgroup G) [DiscreteTopology Γ] (L : AddSubgroup V)
    (hL : ∀ v ∈ L, ∃ γ ∈ Γ, γ ∈ tube p R U ∧ p γ = v) : DiscreteTopology L := by
  obtain ⟨K, hKc, hK0⟩ := exists_compact_mem_nhds (0 : V)
  obtain ⟨K', hK', hsub⟩ := exists_compact (p := p) (U := U) hR hU hKc
  have hΓc : IsClosed (Γ : Set G) := AddSubgroup.isClosed_of_discrete
  have hfin : ((Γ : Set G) ∩ K').Finite := by
    apply (hK'.inter_left hΓc).finite
    have hd : DiscreteTopology (Γ : Set G) := inferInstanceAs (DiscreteTopology Γ)
    have hd' : DiscreteTopology ↥((Γ : Set G) ∩ K') := DiscreteTopology.of_subset hd Set.inter_subset_left
    exact ⟨hd'⟩
  have hLK : ((L : Set V) ∩ K).Finite := by
    apply (hfin.image p).subset
    rintro v ⟨hvL, hvK⟩
    obtain ⟨γ, hγ, hγt, rfl⟩ := hL v hvL
    exact ⟨γ, ⟨hγ, hsub ⟨hvK, hγt⟩⟩, rfl⟩
  apply discreteTopology_of_isOpen_singleton_zero
  have hB : IsClosed (((L : Set V) ∩ K) \ {0}) := (hLK.subset Set.sdiff_subset).isClosed
  refine isOpen_induced_iff.mpr ⟨interior K ∩ (((L : Set V) ∩ K) \ {0})ᶜ,
    isOpen_interior.inter hB.isOpen_compl, ?_⟩
  ext ⟨v, hv⟩
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hvK, hvB⟩
    by_contra hne
    apply hvB
    refine ⟨⟨hv, interior_subset hvK⟩, ?_⟩
    intro h0
    exact hne (Subtype.ext h0)
  · intro h0
    have hv0 : v = 0 := congrArg Subtype.val h0
    subst hv0
    exact ⟨mem_interior_iff_mem_nhds.mpr hK0, fun h => h.2 rfl⟩

variable [MeasurableSpace G] [BorelSpace G] [MeasurableSpace V] [BorelSpace V]

/- English proof (translation)
Use `set ν' := (μ.restrict (tube p R U)).map p with hν'`. Establish `hpm : Measurable p` using `hp.measurable`. Establish `: IsFiniteMeasureOnCompacts ν'` using `⟨fun K hK => by`. Take `⟨K', hK', hsub⟩` from `exists_compact hR hU hK`. Rewrite using `[hν', Measure.map_apply hpm hK.measurableSet, Measure.restrict_apply (hpm hK.measurableSet)]`.

Conclude with `lt_of_le_of_lt (measure_mono hsub) hK'.measure_lt_top⟩`. Establish `: ν'.IsAddLeftInvariant` using `⟨fun v => by`. Establish `hpre : (fun w => R v + w) ⁻¹' (tube p R U : Set G) = tube p R U`. Use extensionality with `w`. Simplify using `only [Set.mem_preimage, SetLike.mem_coe, mem_tube, map_add, hpR]`.

Rewrite using `[show R v + w - (R v + R (p w)) = w - R (p w) by abel]`. Establish `hpres : MeasurePreserving (fun w => R v + w) (μ.restrict (tube p R U)) (μ.restrict (tube p R U))`. Use `(measurePreserving_add_left μ (R v)).restrict_preimage_emb (measurableEmbedding_addLeft (R v)) (tube p R U : Set G)` as an intermediate fact. Rewrite `this` using `[hpre]`. Then use the resulting hypothesis. Establish `hcomm : (fun x => v + x) ∘ p = p ∘ (fun w => R v + w)`.

Use function extensionality and compare the values at `w`. Simplify using `[hpR]`. Rewrite using `[hν', Measure.map_map (continuous_const_add v).measurable hpm, hcomm, ← Measure.map_map hpm (continuous_const_add (R v)).measurable, hpres.map_eq]⟩`. Conclude with `⟨_, Measure.isAddLeftInvariant_eq_smul ν' ν⟩`.
-/
theorem exists_map_eq_smul [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] (hp : Continuous p)
    (hR : Continuous R) (hpR : ∀ v, p (R v) = v) (hU : IsCompact (U : Set G))
    (μ : Measure G) [μ.IsAddHaarMeasure] (ν : Measure V) [ν.IsAddHaarMeasure] :
    ∃ c : NNReal, (μ.restrict (tube p R U)).map p = c • ν := by
  set ν' := (μ.restrict (tube p R U)).map p with hν'
  have hpm : Measurable p := hp.measurable
  have : IsFiniteMeasureOnCompacts ν' := ⟨fun K hK => by
    obtain ⟨K', hK', hsub⟩ := exists_compact hR hU hK
    rw [hν', Measure.map_apply hpm hK.measurableSet, Measure.restrict_apply (hpm hK.measurableSet)]
    exact lt_of_le_of_lt (measure_mono hsub) hK'.measure_lt_top⟩
  have : ν'.IsAddLeftInvariant := ⟨fun v => by
    have hpre : (fun w => R v + w) ⁻¹' (tube p R U : Set G) = tube p R U := by
      ext w
      simp only [Set.mem_preimage, SetLike.mem_coe, mem_tube, map_add, hpR]
      rw [show R v + w - (R v + R (p w)) = w - R (p w) by abel]
    have hpres : MeasurePreserving (fun w => R v + w) (μ.restrict (tube p R U))
        (μ.restrict (tube p R U)) := by
      have := (measurePreserving_add_left μ (R v)).restrict_preimage_emb
        (measurableEmbedding_addLeft (R v)) (tube p R U : Set G)
      rwa [hpre] at this
    have hcomm : (fun x => v + x) ∘ p = p ∘ (fun w => R v + w) := by
      funext w
      simp [hpR]
    rw [hν', Measure.map_map (continuous_const_add v).measurable hpm, hcomm,
      ← Measure.map_map hpm (continuous_const_add (R v)).measurable, hpres.map_eq]⟩
  exact ⟨_, Measure.isAddLeftInvariant_eq_smul ν' ν⟩

/- English proof (translation)
Establish `hpm : Measurable p` using `hp.measurable`. Establish `hTm : MeasurableSet (tube p R U : Set G)` using `hO.measurableSet`. Take `⟨c, hcν⟩` from `exists_map_eq_smul hp hR hpR hU μ ν`. Establish `hnull : ∀ N : Set V, ν N = 0 → μ ((tube p R U : Set G) ∩ p ⁻¹' N) = 0`. Introduce `N hN`.

Establish `hN0 : ν (toMeasurable ν N) = 0` using `by rwa [measure_toMeasurable]`. Apply `measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono (subset_toMeasurable ν N)))` to reduce the goal to its premises. Rewrite using `[Set.inter_comm, ← Measure.restrict_apply (hpm (measurableSet_toMeasurable ν N)), ← Measure.map_apply hpm (measurableSet_toMeasurable ν N), hcν]`. Simplify using `[hN0]`. Establish `hfac : ∀ w ∈ (tube p R U : Set G), h w = h (R (p w))`.

Introduce `w hw`. Establish `hu : w - R (p w) ∈ U` using `(mem_tube p R U w).mp hw`. Establish `h1` using `hhU _ hu (R (p w))`. Rewrite `h1` using `[show R (p w) + (w - R (p w)) = w by abel]`. Conclude with `h1`.

Establish `hΓT : ∀ γ ∈ Γ, γ ∈ tube p R U → p γ = 0 → γ = 0`. Introduce `γ hγ hγt h0`. Apply `hinj γ hγ` to reduce the goal to its premises. Use `(mem_tube p R U γ).mp hγt` as an intermediate fact. Rewrite `this` using `[h0, map_zero, sub_zero]`. Then use the resulting hypothesis.

Establish `hFdm : NullMeasurableSet Fd ν` using `hFd.nullMeasurableSet`. Establish `hFd₀m : MeasurableSet (toMeasurable ν Fd)` using `measurableSet_toMeasurable ν Fd`. Establish `hFd₀ae : toMeasurable ν Fd =ᵐ[ν] Fd` using `hFdm.toMeasurable_ae_eq`. Establish `hFdsub : Fd ⊆ toMeasurable ν Fd` using `subset_toMeasurable ν Fd`. Establish `hdiff : ν (toMeasurable ν Fd \ Fd) = 0` using `(ae_eq_set.mp hFd₀ae).1`.

Establish `hΦ₀m : MeasurableSet ((tube p R U : Set G) ∩ p ⁻¹' toMeasurable ν Fd)` using `hTm.inter (hpm hFd₀m)`. Establish `hΦae : (((tube p R U : Set G) ∩ p ⁻¹' toMeasurable ν Fd : Set G)) =ᵐ[μ] (((tube p R U : Set G) ∩ p ⁻¹' Fd : Set G))`. Rewrite using `[ae_eq_set]`. Prove the components needed by the constructor for the conclusion. Apply `measure_mono_null _ (hnull _ hdiff)` to reduce the goal to its premises.

Introduce and unpack `w ⟨⟨hwT, hw0⟩, hwn⟩`. Conclude with `⟨hwT, hw0, fun hw => hwn ⟨hwT, hw⟩⟩`. Conclude with `measure_mono_null (fun w hw => (hw.2 ⟨hw.1.1, hFdsub hw.1.2⟩).elim) measure_empty`. Establish `hΦ : IsAddFundamentalDomain Γ ((tube p R U : Set G) ∩ p ⁻¹' Fd) μ`. Use `⟨hΦ₀m.nullMeasurableSet.congr hΦae, ?_, ?_⟩` and prove the remaining obligations.

Establish `hbad : ν {v | ¬ ∃ l : L, l +ᵥ v ∈ Fd} = 0` using `ae_iff.mp hFd.ae_covers`. Rewrite using `[ae_iff]`. Use `measure_mono_null ?_ (measure_iUnion_null fun γ : Γ => (show μ ((fun w => (γ : G) + w) ⁻¹' ((tube p R U : Set G) ∩ p ⁻¹' {v | ¬ ∃ l : L, l +ᵥ v ∈ Fd})) = 0 by` and prove the remaining obligations. Rewrite using `[measure_preimage_add]`. Conclude with `hnull _ hbad))`.

Introduce `w hw`. Simplify using `only [Set.mem_ofPred_eq, not_exists] at hw`. Take `⟨γ, hγ, hγw⟩` from `hcov w`. Use `Set.mem_iUnion.mpr ⟨⟨γ, hγ⟩, hγw, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨l, hl⟩`.

Take `⟨γ', hγ', hγ't, hpl⟩` from `(hL l).mp l.2`. Apply `hw ⟨γ' + γ, Γ.add_mem hγ' hγ⟩` to reduce the goal to its premises. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show γ' + γ + w ∈ tube p R U`. Rewrite using `[add_assoc]`.

Conclude with `(tube p R U).add_mem hγ't hγw`. Use `show p (γ' + γ + w) ∈ Fd`. Rewrite using `[add_assoc, map_add, hpl]`. Conclude with `hl`. Introduce `γ₁ γ₂ hne show μ ((γ₁ +ᵥ ((tube p R U : Set G) ∩ p ⁻¹' Fd)) ∩ (γ₂ +ᵥ ((tube p R U : Set G) ∩ p ⁻¹' Fd))) = 0`.

Establish `hδΓ : (γ₁ : G) - γ₂ ∈ Γ` using `Γ.sub_mem γ₁.2 γ₂.2`. Distinguish the cases in `hδt : (γ₁ : G) - γ₂ ∈ tube p R U`. Establish `hl0 : p ((γ₁ : G) - γ₂) ≠ 0` using `fun h0 => hne (Subtype.ext (sub_eq_zero.mp (hΓT _ hδΓ hδt h0)))`. Establish `hlL : p ((γ₁ : G) - γ₂) ∈ L` using `(hL _).mpr ⟨_, hδΓ, hδt, rfl⟩`. Establish `hN : ν (Fd ∩ ((⟨p ((γ₁ : G) - γ₂), hlL⟩ : L) +ᵥ Fd)) = 0`.

Use `hFd.aedisjoint (show (0 : L) ≠ ⟨p ((γ₁ : G) - γ₂), hlL⟩ from fun h => hl0 (congrArg Subtype.val h).symm)` as an intermediate fact. Rewrite `this` using `[Function.onFun, zero_vadd]`. Conclude with `this`. Use `measure_mono_null ?_ (show μ ((fun w => -(γ₂ : G) + w) ⁻¹' ((tube p R U : Set G) ∩ p ⁻¹' (Fd ∩ ((⟨p ((γ₁ : G) - γ₂), hlL⟩ : L) +ᵥ Fd)))) = 0 by` and prove the remaining obligations. Rewrite using `[measure_preimage_add]`.

Conclude with `hnull _ hN)`. Introduce and unpack `x ⟨hx1, hx2⟩`. Take `⟨y₁, ⟨hy₁T, hy₁F⟩, rfl⟩` from `hx1`. Take `⟨y₂, ⟨hy₂T, hy₂F⟩, hxy⟩` from `hx2`. Establish `hxy' : (γ₂ : G) + y₂ = γ₁ + y₁` using `hxy`.

Establish `e : (γ₁ : G) - γ₂ = y₂ - y₁`. Rewrite using `[sub_eq_sub_iff_add_eq_add, ← hxy']`. Conclude with `add_comm _ _`. Establish `hy : -(γ₂ : G) + ((γ₁ : G) + y₁) = y₂`. Rewrite using `[← hxy', neg_add_cancel_left]`.

Use `show -(γ₂ : G) + ((γ₁ : G) + y₁) ∈ (tube p R U : Set G) ∩ p ⁻¹' (Fd ∩ ((⟨p ((γ₁ : G) - γ₂), hlL⟩ : L) +ᵥ Fd))`. Rewrite using `[hy]`. Use `⟨hy₂T, hy₂F, p y₁, hy₁F, ?_⟩` and prove the remaining obligations. Use `show p ((γ₁ : G) - γ₂) + p y₁ = p y₂`. Rewrite using `[← map_add, e, sub_add_cancel]`.

Use `measure_mono_null ?_ measure_empty` and prove the remaining obligations. Introduce and unpack `x ⟨hx1, hx2⟩`. Take `⟨y₁, ⟨hy₁T, -⟩, rfl⟩` from `hx1`. Take `⟨y₂, ⟨hy₂T, -⟩, hxy⟩` from `hx2`. Establish `hxy' : (γ₂ : G) + y₂ = γ₁ + y₁` using `hxy`.

Establish `e : (γ₁ : G) - γ₂ = y₂ - y₁`. Rewrite using `[sub_eq_sub_iff_add_eq_add, ← hxy']`. Conclude with `add_comm _ _`. Conclude with `hδt (e ▸ (tube p R U).sub_mem hy₂T hy₁T)`. Establish `hint1 : ∫ w in 𝓕, h w ∂μ = ∫ w in (tube p R U : Set G) ∩ p ⁻¹' toMeasurable ν Fd, h w ∂μ`.

Rewrite using `[h𝓕.setIntegral_eq hΦ (fun γ w => hΓ γ γ.2 w), setIntegral_congr_set hΦae.symm]`. Establish `hint2 : ∫ w in (tube p R U : Set G) ∩ p ⁻¹' toMeasurable ν Fd, h w ∂μ = ∫ v in toMeasurable ν Fd, h (R v) ∂((μ.restrict (tube p R U)).map p)`. Rewrite using `[setIntegral_map (f := fun v => h (R v)) hFd₀m (show Continuous (fun v => h (R v)) from hc.comp hR).aestronglyMeasurable hpm.aemeasurable, Measure.restrict_restrict (hpm hFd₀m), Set.inter_comm]`. Apply `setIntegral_congr_fun ((hpm hFd₀m).inter hTm)` to reduce the goal to its premises. Introduce `w hw`.

Conclude with `hfac w hw.2`. Establish `hmass : (c : ENNReal) * ν Fd = 1`. Establish `e2 : μ ((tube p R U : Set G) ∩ p ⁻¹' toMeasurable ν Fd) = (c : ENNReal) * ν Fd`. Rewrite using `[Set.inter_comm, ← Measure.restrict_apply (hpm hFd₀m), ← Measure.map_apply hpm hFd₀m, hcν]`. Simplify using `[measure_toMeasurable]`.

Rewrite using `[← e2, measure_congr hΦae, hΦ.measure_eq h𝓕, h1]`. Establish `hreal : (c : ℝ) * (ν Fd).toReal = 1`. Use `congrArg ENNReal.toReal hmass` as an intermediate fact. Rewrite `this` using `[ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_one]`. Then use the resulting hypothesis. Rewrite using `[hint1, hint2, hcν, Measure.restrict_smul, integral_smul_nnreal_measure, setIntegral_congr_set hFd₀ae, NNReal.smul_def, Complex.real_smul]`.

Use `congr 1`. Conclude with `eq_inv_of_mul_eq_one_left (by exact_mod_cast hreal)`.
-/
theorem integral_eq_mean [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] (hp : Continuous p)
    (hR : Continuous R) (hpR : ∀ v, p (R v) = v) (hU : IsCompact (U : Set G))
    (hO : IsOpen (tube p R U : Set G)) (μ : Measure G) [μ.IsAddHaarMeasure] (ν : Measure V) [ν.IsAddHaarMeasure]
    (Γ : AddSubgroup G) [Countable Γ] (L : AddSubgroup V)
    (hL : ∀ v, v ∈ L ↔ ∃ γ ∈ Γ, γ ∈ tube p R U ∧ p γ = v) (hcov : ∀ w, ∃ γ ∈ Γ, γ + w ∈ tube p R U)
    (hinj : ∀ γ ∈ Γ, γ ∈ U → γ = 0) {𝓕 : Set G} (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h1 : μ 𝓕 = 1)
    {Fd : Set V} (hFd : IsAddFundamentalDomain L Fd ν) {h : G → ℂ} (hc : Continuous h)
    (hΓ : ∀ γ ∈ Γ, ∀ w, h (γ + w) = h w) (hhU : ∀ u ∈ U, ∀ w, h (w + u) = h w) :
    ∫ w in 𝓕, h w ∂μ = ((ν Fd).toReal : ℂ)⁻¹ * ∫ v in Fd, h (R v) ∂ν := by
  classical
  have hpm : Measurable p := hp.measurable
  have hTm : MeasurableSet (tube p R U : Set G) := hO.measurableSet
  obtain ⟨c, hcν⟩ := exists_map_eq_smul hp hR hpR hU μ ν
  have hnull : ∀ N : Set V, ν N = 0 → μ ((tube p R U : Set G) ∩ p ⁻¹' N) = 0 := by
    intro N hN
    have hN0 : ν (toMeasurable ν N) = 0 := by rwa [measure_toMeasurable]
    apply measure_mono_null
      (Set.inter_subset_inter_right _ (Set.preimage_mono (subset_toMeasurable ν N)))
    rw [Set.inter_comm, ← Measure.restrict_apply (hpm (measurableSet_toMeasurable ν N)),
      ← Measure.map_apply hpm (measurableSet_toMeasurable ν N), hcν]
    simp [hN0]
  have hfac : ∀ w ∈ (tube p R U : Set G), h w = h (R (p w)) := by
    intro w hw
    have hu : w - R (p w) ∈ U := (mem_tube p R U w).mp hw
    have h1 := hhU _ hu (R (p w))
    rw [show R (p w) + (w - R (p w)) = w by abel] at h1
    exact h1
  have hΓT : ∀ γ ∈ Γ, γ ∈ tube p R U → p γ = 0 → γ = 0 := by
    intro γ hγ hγt h0
    apply hinj γ hγ
    have := (mem_tube p R U γ).mp hγt
    rwa [h0, map_zero, sub_zero] at this
  have hFdm : NullMeasurableSet Fd ν := hFd.nullMeasurableSet
  have hFd₀m : MeasurableSet (toMeasurable ν Fd) := measurableSet_toMeasurable ν Fd
  have hFd₀ae : toMeasurable ν Fd =ᵐ[ν] Fd := hFdm.toMeasurable_ae_eq
  have hFdsub : Fd ⊆ toMeasurable ν Fd := subset_toMeasurable ν Fd
  have hdiff : ν (toMeasurable ν Fd \ Fd) = 0 := (ae_eq_set.mp hFd₀ae).1
  have hΦ₀m : MeasurableSet ((tube p R U : Set G) ∩ p ⁻¹' toMeasurable ν Fd) := hTm.inter (hpm hFd₀m)
  have hΦae : (((tube p R U : Set G) ∩ p ⁻¹' toMeasurable ν Fd : Set G)) =ᵐ[μ]
      (((tube p R U : Set G) ∩ p ⁻¹' Fd : Set G)) := by
    rw [ae_eq_set]
    constructor
    · apply measure_mono_null _ (hnull _ hdiff)
      rintro w ⟨⟨hwT, hw0⟩, hwn⟩
      exact ⟨hwT, hw0, fun hw => hwn ⟨hwT, hw⟩⟩
    · exact measure_mono_null (fun w hw => (hw.2 ⟨hw.1.1, hFdsub hw.1.2⟩).elim) measure_empty
  have hΦ : IsAddFundamentalDomain Γ ((tube p R U : Set G) ∩ p ⁻¹' Fd) μ := by
    refine ⟨hΦ₀m.nullMeasurableSet.congr hΦae, ?_, ?_⟩
    · have hbad : ν {v | ¬ ∃ l : L, l +ᵥ v ∈ Fd} = 0 := ae_iff.mp hFd.ae_covers
      rw [ae_iff]
      refine measure_mono_null ?_ (measure_iUnion_null fun γ : Γ =>
        (show μ ((fun w => (γ : G) + w) ⁻¹'
            ((tube p R U : Set G) ∩ p ⁻¹' {v | ¬ ∃ l : L, l +ᵥ v ∈ Fd})) = 0 by
          rw [measure_preimage_add]
          exact hnull _ hbad))
      intro w hw
      simp only [Set.mem_ofPred_eq, not_exists] at hw
      obtain ⟨γ, hγ, hγw⟩ := hcov w
      refine Set.mem_iUnion.mpr ⟨⟨γ, hγ⟩, hγw, ?_⟩
      rintro ⟨l, hl⟩
      obtain ⟨γ', hγ', hγ't, hpl⟩ := (hL l).mp l.2
      apply hw ⟨γ' + γ, Γ.add_mem hγ' hγ⟩
      refine ⟨?_, ?_⟩
      · show γ' + γ + w ∈ tube p R U
        rw [add_assoc]
        exact (tube p R U).add_mem hγ't hγw
      · show p (γ' + γ + w) ∈ Fd
        rw [add_assoc, map_add, hpl]
        exact hl
    · intro γ₁ γ₂ hne
      show μ ((γ₁ +ᵥ ((tube p R U : Set G) ∩ p ⁻¹' Fd)) ∩ (γ₂ +ᵥ ((tube p R U : Set G) ∩ p ⁻¹' Fd))) = 0
      have hδΓ : (γ₁ : G) - γ₂ ∈ Γ := Γ.sub_mem γ₁.2 γ₂.2
      by_cases hδt : (γ₁ : G) - γ₂ ∈ tube p R U
      · have hl0 : p ((γ₁ : G) - γ₂) ≠ 0 := fun h0 =>
          hne (Subtype.ext (sub_eq_zero.mp (hΓT _ hδΓ hδt h0)))
        have hlL : p ((γ₁ : G) - γ₂) ∈ L := (hL _).mpr ⟨_, hδΓ, hδt, rfl⟩
        have hN : ν (Fd ∩ ((⟨p ((γ₁ : G) - γ₂), hlL⟩ : L) +ᵥ Fd)) = 0 := by
          have := hFd.aedisjoint
            (show (0 : L) ≠ ⟨p ((γ₁ : G) - γ₂), hlL⟩ from fun h => hl0 (congrArg Subtype.val h).symm)
          rw [Function.onFun, zero_vadd] at this
          exact this
        refine measure_mono_null ?_ (show μ ((fun w => -(γ₂ : G) + w) ⁻¹' ((tube p R U : Set G) ∩
            p ⁻¹' (Fd ∩ ((⟨p ((γ₁ : G) - γ₂), hlL⟩ : L) +ᵥ Fd)))) = 0 by
          rw [measure_preimage_add]
          exact hnull _ hN)
        rintro x ⟨hx1, hx2⟩
        obtain ⟨y₁, ⟨hy₁T, hy₁F⟩, rfl⟩ := hx1
        obtain ⟨y₂, ⟨hy₂T, hy₂F⟩, hxy⟩ := hx2
        have hxy' : (γ₂ : G) + y₂ = γ₁ + y₁ := hxy
        have e : (γ₁ : G) - γ₂ = y₂ - y₁ := by
          rw [sub_eq_sub_iff_add_eq_add, ← hxy']
          exact add_comm _ _
        have hy : -(γ₂ : G) + ((γ₁ : G) + y₁) = y₂ := by
          rw [← hxy', neg_add_cancel_left]
        show -(γ₂ : G) + ((γ₁ : G) + y₁) ∈ (tube p R U : Set G) ∩
          p ⁻¹' (Fd ∩ ((⟨p ((γ₁ : G) - γ₂), hlL⟩ : L) +ᵥ Fd))
        rw [hy]
        refine ⟨hy₂T, hy₂F, p y₁, hy₁F, ?_⟩
        show p ((γ₁ : G) - γ₂) + p y₁ = p y₂
        rw [← map_add, e, sub_add_cancel]
      · refine measure_mono_null ?_ measure_empty
        rintro x ⟨hx1, hx2⟩
        obtain ⟨y₁, ⟨hy₁T, -⟩, rfl⟩ := hx1
        obtain ⟨y₂, ⟨hy₂T, -⟩, hxy⟩ := hx2
        have hxy' : (γ₂ : G) + y₂ = γ₁ + y₁ := hxy
        have e : (γ₁ : G) - γ₂ = y₂ - y₁ := by
          rw [sub_eq_sub_iff_add_eq_add, ← hxy']
          exact add_comm _ _
        exact hδt (e ▸ (tube p R U).sub_mem hy₂T hy₁T)
  have hint1 : ∫ w in 𝓕, h w ∂μ = ∫ w in (tube p R U : Set G) ∩ p ⁻¹' toMeasurable ν Fd, h w ∂μ := by
    rw [h𝓕.setIntegral_eq hΦ (fun γ w => hΓ γ γ.2 w), setIntegral_congr_set hΦae.symm]
  have hint2 : ∫ w in (tube p R U : Set G) ∩ p ⁻¹' toMeasurable ν Fd, h w ∂μ =
      ∫ v in toMeasurable ν Fd, h (R v) ∂((μ.restrict (tube p R U)).map p) := by
    rw [setIntegral_map (f := fun v => h (R v)) hFd₀m
      (show Continuous (fun v => h (R v)) from hc.comp hR).aestronglyMeasurable hpm.aemeasurable,
      Measure.restrict_restrict (hpm hFd₀m), Set.inter_comm]
    apply setIntegral_congr_fun ((hpm hFd₀m).inter hTm)
    intro w hw
    exact hfac w hw.2
  have hmass : (c : ENNReal) * ν Fd = 1 := by
    have e2 : μ ((tube p R U : Set G) ∩ p ⁻¹' toMeasurable ν Fd) = (c : ENNReal) * ν Fd := by
      rw [Set.inter_comm, ← Measure.restrict_apply (hpm hFd₀m), ← Measure.map_apply hpm hFd₀m, hcν]
      simp [measure_toMeasurable]
    rw [← e2, measure_congr hΦae, hΦ.measure_eq h𝓕, h1]
  have hreal : (c : ℝ) * (ν Fd).toReal = 1 := by
    have := congrArg ENNReal.toReal hmass
    rwa [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_one] at this
  rw [hint1, hint2, hcν, Measure.restrict_smul, integral_smul_nnreal_measure,
    setIntegral_congr_set hFd₀ae, NNReal.smul_def, Complex.real_smul]
  congr 1
  exact eq_inv_of_mul_eq_one_left (by exact_mod_cast hreal)

end Abstract

variable {D : D7} {S T : HSp D}

/- English proof (translation)
Use extensionality with `a k`. Simplify using `[finW, TensorProduct.tmul_add]`.
-/
theorem finW_add (y y' : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    finW S T (y + y') = finW S T y + finW S T y' := by
  ext a k
  simp [finW, TensorProduct.tmul_add]

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero`. Use extensionality with `a k`. Simplify using `[finW]`. Consider the case `succ m ih => rw [succ_nsmul, succ_nsmul, finW_add, ih]`.
-/
theorem finW_nsmul (N : ℕ) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    finW S T (N • y) = N • finW S T y := by
  induction N with
  | zero =>
    ext a k
    simp [finW]
  | succ m ih => rw [succ_nsmul, succ_nsmul, finW_add, ih]

/- English proof (translation)
Unfold `IsFinPt`. Use extensionality with `a k`. Simplify using `only [finW, Matrix.map_apply, Matrix.of_apply, Matrix.zero_apply]`. Use `show (Algebra.TensorProduct.map (fstA (F := D.host.F)) (AlgHom.id D.host.F D.host.E)) (pairA D.host.F 0 1 ⊗ₜ[D.host.F] y k a) = 0`. Rewrite using `[Algebra.TensorProduct.map_tmul]`.

Establish `h0 : fstA (F` using `D.host.F) (pairA D.host.F 0 1) = 0 := rfl`. Rewrite using `[h0, TensorProduct.zero_tmul]`.
-/
theorem fin_finW (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) : IsFinPt (finW S T y) := by
  unfold IsFinPt
  ext a k
  simp only [finW, Matrix.map_apply, Matrix.of_apply, Matrix.zero_apply]
  show (Algebra.TensorProduct.map (fstA (F := D.host.F)) (AlgHom.id D.host.F D.host.E))
    (pairA D.host.F 0 1 ⊗ₜ[D.host.F] y k a) = 0
  rw [Algebra.TensorProduct.map_tmul]
  have h0 : fstA (F := D.host.F) (pairA D.host.F 0 1) = 0 := rfl
  rw [h0, TensorProduct.zero_tmul]

/- English proof (translation)
Unfold `IsRealPt`. Use extensionality with `a k`. Simplify using `only [finW, ratW, Matrix.map_apply, Matrix.of_apply, Matrix.zero_apply, Matrix.sub_apply, Matrix.transpose_apply, map_sub]`. Use `show (Algebra.TensorProduct.map (sndA (F := D.host.F)) (AlgHom.id D.host.F D.host.E)) ((1 : AF D.host.F) ⊗ₜ[D.host.F] y k a) - (Algebra.TensorProduct.map (sndA (F := D.host.F)) (AlgHom.id D.host.F D.host.E)) (pairA D.host.F 0 1 ⊗ₜ[D.host.F] y k a) = 0`. Rewrite using `[Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]`.

Establish `h1 : sndA (F` using `D.host.F) (pairA D.host.F 0 1) = 1 := rfl`. Rewrite using `[h1, map_one, sub_self]`.
-/
theorem real_rat_sub (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    IsRealPt (S := S) (T := T) (ratW T S yᵀ - finW S T y) := by
  unfold IsRealPt
  ext a k
  simp only [finW, ratW, Matrix.map_apply, Matrix.of_apply, Matrix.zero_apply, Matrix.sub_apply,
    Matrix.transpose_apply, map_sub]
  show (Algebra.TensorProduct.map (sndA (F := D.host.F)) (AlgHom.id D.host.F D.host.E))
      ((1 : AF D.host.F) ⊗ₜ[D.host.F] y k a) -
    (Algebra.TensorProduct.map (sndA (F := D.host.F)) (AlgHom.id D.host.F D.host.E))
      (pairA D.host.F 0 1 ⊗ₜ[D.host.F] y k a) = 0
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
  have h1 : sndA (F := D.host.F) (pairA D.host.F 0 1) = 1 := rfl
  rw [h1, map_one, sub_self]

/- English proof (translation)
Use function extensionality and compare the values at `σ k a`. Establish `h1 : infPart D (incA D (y k a)) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] y k a` using `by show (Algebra.TensorProduct.map (fstA (F := D.host.F)) (AlgHom.id D.host.F D.host.E)) ((1 : AF D.host.F) ⊗ₜ[D.host.F] y k a) = _`. Rewrite using `[Algebra.TensorProduct.map_tmul, map_one]`. Both sides reduce to the same expression. Establish `h2 : (C.θ (C.m.e.symm σ)) ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y k a) = tauE D (C.m.e.symm σ) (y k a)` using `(C.inf (C.m.e.symm σ)).1 (y k a)`.

Establish `h3` using `C.m.e_emb (C.m.e.symm σ)`. Rewrite `h3` using `[Equiv.apply_symm_apply]`. Simplify using `only [Ctx.realPt, embR, ratW, compAt, Matrix.map_apply, Matrix.transpose_apply]`. Rewrite using `[h1, h2, h3, ComplexEmbedding.conjugate_coe_eq]`.
-/
theorem realPt_ratW (C : Ctx S T) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    C.realPt (ratW T S yᵀ) = embR C.X y := by
  funext σ k a
  have h1 : infPart D (incA D (y k a)) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] y k a := by
    show (Algebra.TensorProduct.map (fstA (F := D.host.F)) (AlgHom.id D.host.F D.host.E))
      ((1 : AF D.host.F) ⊗ₜ[D.host.F] y k a) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  have h2 : (C.θ (C.m.e.symm σ)) ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y k a) =
      tauE D (C.m.e.symm σ) (y k a) := (C.inf (C.m.e.symm σ)).1 (y k a)
  have h3 := C.m.e_emb (C.m.e.symm σ)
  rw [Equiv.apply_symm_apply] at h3
  simp only [Ctx.realPt, embR, ratW, compAt, Matrix.map_apply, Matrix.transpose_apply]
  rw [h1, h2, h3, ComplexEmbedding.conjugate_coe_eq]

/- English proof (translation)
Establish `hN' : (N : F) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `h' : (N : F) • w = (N : F) • w'`. Rewrite using `[Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]`. Conclude with `h`. Conclude with `smul_right_injective _ hN' h'`.
-/
theorem nsmul_cancel_tensor {F A B : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A] [CommRing B] [Algebra F B]
    {m n N : ℕ} (hN : 0 < N) {w w' : Matrix (Fin m) (Fin n) (A ⊗[F] B)} (h : N • w = N • w') : w = w' := by
  have hN' : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have h' : (N : F) • w = (N : F) • w' := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact h
  exact smul_right_injective _ hN' h'

/- English proof (translation)
The claim follows from `nsmul_cancel_tensor (F := D.host.F) hN h`.
-/
theorem nsmul_cancel {N : ℕ} (hN : 0 < N) {w w' : WO S T} (h : N • w = N • w') : w = w' := nsmul_cancel_tensor (F := D.host.F) hN h

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ} (X : Data E r)

/- English proof (translation)
Use extensionality with `k a`. Take `⟨τ0⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Distinguish the cases in `hτ : τ0 ∈ X.Ψ`. Establish `h1` using `congrFun (congrFun (congrFun h ⟨τ0, hτ⟩) k) a`. Simplify `h1` using `[embR]`.

Establish `hc : ComplexEmbedding.conjugate τ0 ∈ X.Ψ`. Assume the negation of the conclusion as `hc`. Conclude with `hτ ((X.cmType τ0).mpr hc)`. Establish `h1` using `congrFun (congrFun (congrFun h ⟨_, hc⟩) k) a`. Simplify `h1` using `[embR]`.
-/
theorem eq_zero_of_embR {y : Matrix (Fin n) (Fin r) E} (h : embR X y = 0) : y = 0 := by
  ext k a
  obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases hτ : τ0 ∈ X.Ψ
  · have h1 := congrFun (congrFun (congrFun h ⟨τ0, hτ⟩) k) a
    simpa [embR] using h1
  · have hc : ComplexEmbedding.conjugate τ0 ∈ X.Ψ := by
      by_contra hc
      exact hτ ((X.cmType τ0).mpr hc)
    have h1 := congrFun (congrFun (congrFun h ⟨_, hc⟩) k) a
    simpa [embR] using h1

/- English proof (translation)
Use function extensionality and compare the values at `τ k a`. Simplify using `[embR]`.
-/
theorem embR_smul (N : ℕ) (y : Matrix (Fin n) (Fin r) E) : embR X (N • y) = N • embR X y := by
  funext τ k a
  simp [embR]

/- English proof (translation)
Unfold `latR`. Prove the components needed by the constructor for the conclusion. Introduce `hv`. Proceed by induction on `hv using AddSubgroup.closure_induction with`. Consider the case `mem x hx => exact hx`.

Consider the case `zero`. Use `⟨0, fun k => show (0 : Fin r → E) ∈ X.Λ from X.Λ.zero_mem, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `τ k a`. Simplify using `[embR]`. Consider the case `add x x' _ _ hx hx'`.

Take `⟨u, hu, rfl⟩` from `hx`. Take `⟨u', hu', rfl⟩` from `hx'`. Use `⟨u + u', fun k => show u k + u' k ∈ X.Λ from X.Λ.add_mem (hu k) (hu' k), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `τ k a`. Simplify using `[embR, smul_add]`.

Consider the case `neg x _ hx`. Take `⟨u, hu, rfl⟩` from `hx`. Use `⟨-u, fun k => show -u k ∈ X.Λ from X.Λ.neg_mem (hu k), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `τ k a`. Simplify using `[embR]`.

Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `AddSubgroup.subset_closure ⟨y, hy, rfl⟩`.
-/
theorem mem_latR_iff (N : ℕ) (v : WR X n) :
    v ∈ latR X n N ↔ ∃ y : Matrix (Fin n) (Fin r) E, (∀ k, y k ∈ X.Λ) ∧ v = N • embR X y := by
  unfold latR
  constructor
  · intro hv
    induction hv using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero =>
      refine ⟨0, fun k => show (0 : Fin r → E) ∈ X.Λ from X.Λ.zero_mem, ?_⟩
      funext τ k a
      simp [embR]
    | add x x' _ _ hx hx' =>
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨u', hu', rfl⟩ := hx'
      refine ⟨u + u', fun k => show u k + u' k ∈ X.Λ from X.Λ.add_mem (hu k) (hu' k), ?_⟩
      funext τ k a
      simp [embR, smul_add]
    | neg x _ hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      refine ⟨-u, fun k => show -u k ∈ X.Λ from X.Λ.neg_mem (hu k), ?_⟩
      funext τ k a
      simp [embR]
  · rintro ⟨y, hy, rfl⟩
    exact AddSubgroup.subset_closure ⟨y, hy, rfl⟩

omit [IsCMField E] in
/- English proof (translation)
Rewrite using `[eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises. Rewrite using `[Pi.basisFun_apply]`. Conclude with `Submodule.subset_span ⟨a, rfl⟩`.
-/
theorem span_stdL : Submodule.span E (stdL E n : Set (Fin n → E)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  apply Submodule.subset_span
  rw [Pi.basisFun_apply]
  exact Submodule.subset_span ⟨a, rfl⟩

/- English proof (translation)
Establish `h1 : (volume : Measure (Fin r → ℂ)).IsAddHaarMeasure`. Rewrite using `[MeasureTheory.volume_pi]`. Conclude with `MeasureTheory.Measure.pi.isAddHaarMeasure _`. Establish `h2 : (volume : Measure (Fin n → Fin r → ℂ)).IsAddHaarMeasure`. Rewrite using `[MeasureTheory.volume_pi]`.

Conclude with `MeasureTheory.Measure.pi.isAddHaarMeasure _`. Unfold `WR`. Rewrite using `[MeasureTheory.volume_pi]`. Conclude with `MeasureTheory.Measure.pi.isAddHaarMeasure _`.
-/
theorem haar_WR : (volume : Measure (WR X n)).IsAddHaarMeasure := by
  have h1 : (volume : Measure (Fin r → ℂ)).IsAddHaarMeasure := by
    rw [MeasureTheory.volume_pi]
    exact MeasureTheory.Measure.pi.isAddHaarMeasure _
  have h2 : (volume : Measure (Fin n → Fin r → ℂ)).IsAddHaarMeasure := by
    rw [MeasureTheory.volume_pi]
    exact MeasureTheory.Measure.pi.isAddHaarMeasure _
  unfold WR
  rw [MeasureTheory.volume_pi]
  exact MeasureTheory.Measure.pi.isAddHaarMeasure _

end Classical

/- English proof (translation)
Establish `h1 : a * conj a = 1`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]`. Evaluate the numerical expressions. Rewrite using `[map_mul]`. Take the linear combination `(x * conj y) * h1`.
-/
theorem mul_conj_phase {a : ℂ} (ha : ‖a‖ = 1) (x y : ℂ) : a * x * conj (a * y) = x * conj y := by
  have h1 : a * conj a = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]
    norm_num
  rw [map_mul]
  linear_combination (x * conj y) * h1

/- English proof (translation)
Introduce `D S T C μ 𝓕 hcov f f' hf hf'`. Unfold `IsCovolOne at hcov`. Take `⟨hμ, h𝓕, h1⟩` from `hcov`. Take `⟨R, hRc, hpc, hpadd, hRv, hRreal, hfp, hfin0, -, -⟩` from `GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C`. Establish `hstdfg : (stdL D.host.E S.rank).FG`.

Unfold `stdL`. Conclude with `Submodule.fg_span (Set.finite_range _)`. Take `⟨hA1, hA2, hA3, -, hA5, hA6⟩` from `GlobalTheory.T.completedTensorLattice_strongApprox_open_compact D S T C (stdL D.host.E S.rank) C.X.Λ ⟨hstdfg, span_stdL⟩ ⟨C.X.Λ_fg, C.X.Λ_span⟩`. Take `⟨-, -, hTh⟩` from `GlobalTheory.T.thetaFunction_space_heisenberg_laws D S T C`. Take `⟨-, -, -, -, -, Nf, hNf, hfN⟩` from `hTh f hf`.

Take `⟨-, -, -, -, -, Nf', hNf', hfN'⟩` from `hTh f' hf'`. Establish `hψ : ∀ x, ‖C.ψ x‖ = 1` using `C.std.1.2.1`. Use `set A := hatA S T (tens (stdL D.host.E S.rank) C.X.Λ) with hAdef`. Use `⟨Nf * Nf', Nat.mul_pos hNf hNf', fun N hN hdvd => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `hdvd`.

Establish `hfU : ∀ u ∈ A, C.rho (N • u) f = f`. Introduce `u hu`. Establish `e : N • u = Nf • ((Nf' * k) • u)` using `by rw [smul_smul, hk, mul_assoc]`. Rewrite using `[e]`. Conclude with `hfN _ (A.nsmul_mem hu _)`.

Establish `hf'U : ∀ u ∈ A, C.rho (N • u) f' = f'`. Introduce `u hu`. Establish `e : N • u = Nf' • ((Nf * k) • u)`. Rewrite using `[smul_smul, hk]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hfN' _ (A.nsmul_mem hu _)`. Use `set h : WO S T → ℂ := fun w => f w * conj (f' w) with hhdef`. Establish `hstep : ∀ w₀ w, C.rho w₀ f = f → C.rho w₀ f' = f' → h (w + w₀) = h w`.

Introduce `w₀ w e e'`. Establish `a1` using `congrFun e w`. Establish `a2` using `congrFun e' w`. Simplify using `only [Ctx.rho, heisO] at a1 a2`. Simplify using `only [hhdef]`.

Use `conv_rhs => rw [← a1, ← a2]`. Rewrite using `[mul_conj_phase (hψ _)]`. Establish `hΓ : ∀ γ ∈ ratL T S, ∀ w, h (γ + w) = h w`. Introduce and unpack `_ ⟨z, rfl⟩ w`. Establish `q1` using `hf.quasi z w`.

Establish `q2` using `hf'.quasi z w`. Simplify using `only [hhdef]`. Express the relevant statement in the definitionally equal form `f (ratW T S z + w) * conj (f' (ratW T S z + w)) = _`. Rewrite using `[q1, q2, mul_conj_phase (hψ _)]`. Use `set U : AddSubgroup (WO S T) := A.map (DistribSMul.toAddMonoidHom (WO S T) N) with hUdef`.

Establish `hmemU : ∀ x, x ∈ U ↔ ∃ u ∈ A, N • u = x` using `fun x => AddSubgroup.mem_map`. Establish `hhU : ∀ u ∈ U, ∀ w, h (w + u) = h w`. Introduce `x hx w`. Take `⟨u, hu, rfl⟩` from `(hmemU x).mp hx`. Conclude with `hstep _ w (hfU u hu) (hf'U u hu)`.

Use `set p : WO S T →+ WR C.X S.rank := AddMonoidHom.mk' C.realPt hpadd with hpdef`. Establish `hpapp : ∀ w, p w = C.realPt w` using `fun w => rfl`. Establish `hfinsmul : ∀ u ∈ A, C.realPt (N • u) = 0`. Introduce `u hu`. Rewrite using `[← hpapp, map_nsmul, hpapp, hfin0 u (hA3 u hu).1, smul_zero]`.

Establish `hRemb : ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, R (embR C.X y) = ratW T S yᵀ - finW S T y`. Introduce `y`. Establish `e1` using `hRreal _ (real_rat_sub y)`. Establish `e2 : C.realPt (ratW T S yᵀ - finW S T y) = embR C.X y`. Rewrite using `[← hpapp, map_sub, hpapp, hpapp, realPt_ratW, hfin0 _ (fin_finW y), sub_zero]`.

Rewrite `e1` using `[e2]`. Then use the resulting hypothesis. Establish `hmemT : ∀ w, w ∈ tube p R U ↔ ∃ u ∈ A, N • u = w - R (C.realPt w)` using `fun w => (mem_tube p R U w).trans (hmemU _)`. Establish `hO : IsOpen (tube p R U : Set (WO S T))`. Use `hA5 N hN using 1` and compare the differences between its conclusion and the goal. Use extensionality with `w`.

Simplify using `only [SetLike.mem_coe, Set.mem_ofPred_eq]`. Rewrite using `[hmemT]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, e⟩`. Use `⟨u, hu, ?_⟩` and prove the remaining obligations.

Rewrite using `[show w - N • u = R (C.realPt w) by rw [e]; abel]`. Conclude with `(hRv _).1`. Introduce and unpack `⟨u, hu, hr⟩`. Use `⟨u, hu, ?_⟩` and prove the remaining obligations. Establish `e1` using `hRreal _ hr`.

Establish `e2 : C.realPt (w - N • u) = C.realPt w`. Rewrite using `[← hpapp, map_sub, hpapp, hpapp, hfinsmul u hu, sub_zero]`. Rewrite `e1` using `[e2]`. Rewrite using `[e1]`. Normalize the expressions using the abelian group laws.

Establish `hcov' : ∀ w, ∃ γ ∈ ratL T S, γ + w ∈ tube p R U`. Introduce `w`. Take `⟨y, hy⟩` from `hA1 _ (hfp w)`. Take `⟨-, hsplit⟩` from `hA3 _ hy`. Take `⟨y', -, u', hu', e⟩` from `hsplit N hN`.

Use `⟨-(ratW T S (y + y')ᵀ), (ratL T S).neg_mem ⟨(y + y')ᵀ, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hmemT]`. Use `⟨u', hu', ?_⟩` and prove the remaining obligations. Establish `e3 : C.realPt (-(ratW T S (y + y')ᵀ) + w) = -embR C.X (y + y') + C.realPt w`. Rewrite using `[← hpapp, map_add, map_neg, hpapp, hpapp, realPt_ratW]`.

Rewrite using `[e3, map_add, map_neg, hRemb, finW_add]`. Rewrite using `[show N • u' = w - R (C.realPt w) - finW S T y - finW S T y' by rw [e]; abel]`. Normalize the expressions using the abelian group laws. Establish `hinj : ∀ γ ∈ ratL T S, γ ∈ U → γ = 0`. Introduce and unpack `_ ⟨z, rfl⟩ hzU`.

Take `⟨u, hu, e⟩` from `(hmemU _).mp hzU`. Express the relevant statement in the definitionally equal form `ratW T S z = 0`. Establish `e' : N • u = ratW T S z` using `e`. Establish `e1 : embR C.X zᵀ = 0`. Rewrite using `[← realPt_ratW C zᵀ, Matrix.transpose_transpose, ← e', hfinsmul u hu]`.

Establish `e2` using `eq_zero_of_embR C.X e1`. Rewrite using `[← Matrix.transpose_transpose z, e2]`. Use extensionality with `i j`. Simplify using `[ratW]`. Establish `hL : ∀ v, v ∈ latR C.X S.rank N ↔ ∃ γ ∈ ratL T S, γ ∈ tube p R U ∧ p γ = v`.

Introduce `v`. Rewrite using `[mem_latR_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Use `⟨ratW T S (N • y)ᵀ, ⟨_, rfl⟩, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hmemT]`. Use `⟨finW S T y, (hA2 y).mpr ((GlobalTheory.SW.TensLat.mem_tens_stdL C.X.Λ y).mpr hy), ?_⟩` and prove the remaining obligations. Rewrite using `[realPt_ratW, hRemb, finW_nsmul]`. Normalize the expressions using the abelian group laws. Use `show C.realPt _ = _`.

Rewrite using `[realPt_ratW, embR_smul]`. Introduce and unpack `⟨_, ⟨z, rfl⟩, hzt, rfl⟩`. Take `⟨y, rfl⟩ : ∃ y, z = yᵀ` from `⟨zᵀ, (Matrix.transpose_transpose z).symm⟩`. Express the relevant statement in the definitionally equal form `ratW T S yᵀ ∈ tube p R U at hzt`. Rewrite `hzt` using `[hmemT, realPt_ratW, hRemb]`.

Take `⟨u, hu, e⟩` from `hzt`. Establish `e2 : finW S T y = N • u`. Rewrite using `[e]`. Normalize the expressions using the abelian group laws. Establish `hNE : (N : D.host.E) ≠ 0` using `by exact_mod_cast hN.ne'`.

Establish `hy3 : N • ((N : D.host.E)⁻¹ • y) = y`. Rewrite using `[← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, mul_inv_cancel₀ hNE, one_smul]`. Establish `e3 : finW S T ((N : D.host.E)⁻¹ • y) = u`. Apply `nsmul_cancel hN` to reduce the goal to its premises. Rewrite using `[← finW_nsmul, hy3, e2]`.

Establish `hmem` using `(GlobalTheory.SW.TensLat.mem_tens_stdL C.X.Λ _).mp ((hA2 _).mp (by rw [e3]; exact hu))`. Use `⟨(N : D.host.E)⁻¹ • y, hmem, ?_⟩` and prove the remaining obligations. Use `show C.realPt (ratW T S yᵀ) = N • embR C.X ((N : D.host.E)⁻¹ • y)`. Rewrite using `[realPt_ratW, ← embR_smul, hy3]`. Establish `hUc : IsCompact (U : Set (WO S T))`.

Rewrite using `[hUdef, AddSubgroup.coe_map]`. Conclude with `hA6.image (show Continuous (DistribSMul.toAddMonoidHom (WO S T) N) from continuous_nsmul N)`. Take `⟨hTG, hLC, hSC, hT2, hdisc, -⟩` from `GlobalTheory.AdelicMatrixLattice.lattice D T S`. Use `hT2` as an intermediate fact. Use `hdisc` as an intermediate fact.

Use `hSC` as an intermediate fact. Establish `: BorelSpace (WO S T)` using `⟨rfl⟩`. Establish `: Countable (ratL T S)` using `GlobalTheory.countable_of_discrete_addSubgroup (ratL T S)`. Use `haar_WR C.X (n := S.rank)` as an intermediate fact. Use `hμ` as an intermediate fact.

Establish `hLdisc : DiscreteTopology (latR C.X S.rank N)` using `discrete_image (p := p) hRc hUc (ratL T S) (latR C.X S.rank N) (fun v hv => (hL v).mp hv)`. Take `⟨Fd0, -, -, hFd0⟩` from `GlobalTheory.exists_isAddFundamentalDomain_addSubgroup (latR C.X S.rank N)`. Use `⟨⟨Fd0, hFd0 volume⟩, fun Fd hFd F hF => ?_⟩` and prove the remaining obligations. Establish `hcont : Continuous h` using `hf.cont.mul (Complex.continuous_conj.comp hf'.cont)`. Establish `key` using `integral_eq_mean (p := p) (R := R) (U := U) hpc hRc (fun v => (hRv v).2) hUc hO μ volume (ratL T S) (latR C.X S.rank N) hL hcov' hinj h𝓕 h1 hFd hcont hΓ hhU`.

Establish `hFR : (fun v => h (R v)) = F`. Use function extensionality and compare the values at `v`. Use `hF (R v) (hRv v).1` as an intermediate fact. Rewrite `this` using `[(hRv v).2]`. Conclude with `this`.

Use `show ∫ w in 𝓕, h w ∂μ = _`. Rewrite using `[key, hFR]`.
-/
theorem ipO_eq_mean : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f', C.IsTh f → C.IsTh f' → ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, 0 < N → N₀ ∣ N → (∃ Fd : Set (WR C.X S.rank), IsAddFundamentalDomain (latR C.X S.rank N) Fd volume) ∧ ∀ Fd : Set (WR C.X S.rank), IsAddFundamentalDomain (latR C.X S.rank N) Fd volume → ∀ F : WR C.X S.rank → ℂ, (∀ w, IsRealPt w → f w * conj (f' w) = F (C.realPt w)) → ipO μ 𝓕 f f' = ((volume Fd).toReal : ℂ)⁻¹ * ∫ v in Fd, F v := by
  intro D S T C μ 𝓕 hcov f f' hf hf'
  unfold IsCovolOne at hcov
  obtain ⟨hμ, h𝓕, h1⟩ := hcov
  obtain ⟨R, hRc, hpc, hpadd, hRv, hRreal, hfp, hfin0, -, -⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  have hstdfg : (stdL D.host.E S.rank).FG := by
    unfold stdL
    exact Submodule.fg_span (Set.finite_range _)
  obtain ⟨hA1, hA2, hA3, -, hA5, hA6⟩ := GlobalTheory.T.completedTensorLattice_strongApprox_open_compact D S T C (stdL D.host.E S.rank) C.X.Λ
    ⟨hstdfg, span_stdL⟩ ⟨C.X.Λ_fg, C.X.Λ_span⟩
  obtain ⟨-, -, hTh⟩ := GlobalTheory.T.thetaFunction_space_heisenberg_laws D S T C
  obtain ⟨-, -, -, -, -, Nf, hNf, hfN⟩ := hTh f hf
  obtain ⟨-, -, -, -, -, Nf', hNf', hfN'⟩ := hTh f' hf'
  have hψ : ∀ x, ‖C.ψ x‖ = 1 := C.std.1.2.1
  set A := hatA S T (tens (stdL D.host.E S.rank) C.X.Λ) with hAdef
  refine ⟨Nf * Nf', Nat.mul_pos hNf hNf', fun N hN hdvd => ?_⟩
  obtain ⟨k, hk⟩ := hdvd
  have hfU : ∀ u ∈ A, C.rho (N • u) f = f := by
    intro u hu
    have e : N • u = Nf • ((Nf' * k) • u) := by rw [smul_smul, hk, mul_assoc]
    rw [e]
    exact hfN _ (A.nsmul_mem hu _)
  have hf'U : ∀ u ∈ A, C.rho (N • u) f' = f' := by
    intro u hu
    have e : N • u = Nf' • ((Nf * k) • u) := by
      rw [smul_smul, hk]
      congr 1
      ring
    rw [e]
    exact hfN' _ (A.nsmul_mem hu _)
  set h : WO S T → ℂ := fun w => f w * conj (f' w) with hhdef
  have hstep : ∀ w₀ w, C.rho w₀ f = f → C.rho w₀ f' = f' → h (w + w₀) = h w := by
    intro w₀ w e e'
    have a1 := congrFun e w
    have a2 := congrFun e' w
    simp only [Ctx.rho, heisO] at a1 a2
    simp only [hhdef]
    conv_rhs => rw [← a1, ← a2]
    rw [mul_conj_phase (hψ _)]
  have hΓ : ∀ γ ∈ ratL T S, ∀ w, h (γ + w) = h w := by
    rintro _ ⟨z, rfl⟩ w
    have q1 := hf.quasi z w
    have q2 := hf'.quasi z w
    simp only [hhdef]
    change f (ratW T S z + w) * conj (f' (ratW T S z + w)) = _
    rw [q1, q2, mul_conj_phase (hψ _)]
  set U : AddSubgroup (WO S T) := A.map (DistribSMul.toAddMonoidHom (WO S T) N) with hUdef
  have hmemU : ∀ x, x ∈ U ↔ ∃ u ∈ A, N • u = x := fun x => AddSubgroup.mem_map
  have hhU : ∀ u ∈ U, ∀ w, h (w + u) = h w := by
    intro x hx w
    obtain ⟨u, hu, rfl⟩ := (hmemU x).mp hx
    exact hstep _ w (hfU u hu) (hf'U u hu)
  set p : WO S T →+ WR C.X S.rank := AddMonoidHom.mk' C.realPt hpadd with hpdef
  have hpapp : ∀ w, p w = C.realPt w := fun w => rfl
  have hfinsmul : ∀ u ∈ A, C.realPt (N • u) = 0 := by
    intro u hu
    rw [← hpapp, map_nsmul, hpapp, hfin0 u (hA3 u hu).1, smul_zero]
  have hRemb : ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E,
      R (embR C.X y) = ratW T S yᵀ - finW S T y := by
    intro y
    have e1 := hRreal _ (real_rat_sub y)
    have e2 : C.realPt (ratW T S yᵀ - finW S T y) = embR C.X y := by
      rw [← hpapp, map_sub, hpapp, hpapp, realPt_ratW, hfin0 _ (fin_finW y), sub_zero]
    rwa [e2] at e1
  have hmemT : ∀ w, w ∈ tube p R U ↔ ∃ u ∈ A, N • u = w - R (C.realPt w) :=
    fun w => (mem_tube p R U w).trans (hmemU _)
  have hO : IsOpen (tube p R U : Set (WO S T)) := by
    convert hA5 N hN using 1
    ext w
    simp only [SetLike.mem_coe, Set.mem_ofPred_eq]
    rw [hmemT]
    constructor
    · rintro ⟨u, hu, e⟩
      refine ⟨u, hu, ?_⟩
      rw [show w - N • u = R (C.realPt w) by rw [e]; abel]
      exact (hRv _).1
    · rintro ⟨u, hu, hr⟩
      refine ⟨u, hu, ?_⟩
      have e1 := hRreal _ hr
      have e2 : C.realPt (w - N • u) = C.realPt w := by
        rw [← hpapp, map_sub, hpapp, hpapp, hfinsmul u hu, sub_zero]
      rw [e2] at e1
      rw [e1]
      abel
  have hcov' : ∀ w, ∃ γ ∈ ratL T S, γ + w ∈ tube p R U := by
    intro w
    obtain ⟨y, hy⟩ := hA1 _ (hfp w)
    obtain ⟨-, hsplit⟩ := hA3 _ hy
    obtain ⟨y', -, u', hu', e⟩ := hsplit N hN
    refine ⟨-(ratW T S (y + y')ᵀ), (ratL T S).neg_mem ⟨(y + y')ᵀ, rfl⟩, ?_⟩
    rw [hmemT]
    refine ⟨u', hu', ?_⟩
    have e3 : C.realPt (-(ratW T S (y + y')ᵀ) + w) = -embR C.X (y + y') + C.realPt w := by
      rw [← hpapp, map_add, map_neg, hpapp, hpapp, realPt_ratW]
    rw [e3, map_add, map_neg, hRemb, finW_add]
    rw [show N • u' = w - R (C.realPt w) - finW S T y - finW S T y' by rw [e]; abel]
    abel
  have hinj : ∀ γ ∈ ratL T S, γ ∈ U → γ = 0 := by
    rintro _ ⟨z, rfl⟩ hzU
    obtain ⟨u, hu, e⟩ := (hmemU _).mp hzU
    change ratW T S z = 0
    have e' : N • u = ratW T S z := e
    have e1 : embR C.X zᵀ = 0 := by
      rw [← realPt_ratW C zᵀ, Matrix.transpose_transpose, ← e', hfinsmul u hu]
    have e2 := eq_zero_of_embR C.X e1
    rw [← Matrix.transpose_transpose z, e2]
    ext i j
    simp [ratW]
  have hL : ∀ v, v ∈ latR C.X S.rank N ↔ ∃ γ ∈ ratL T S, γ ∈ tube p R U ∧ p γ = v := by
    intro v
    rw [mem_latR_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨ratW T S (N • y)ᵀ, ⟨_, rfl⟩, ?_, ?_⟩
      · rw [hmemT]
        refine ⟨finW S T y, (hA2 y).mpr ((GlobalTheory.SW.TensLat.mem_tens_stdL C.X.Λ y).mpr hy), ?_⟩
        rw [realPt_ratW, hRemb, finW_nsmul]
        abel
      · show C.realPt _ = _
        rw [realPt_ratW, embR_smul]
    · rintro ⟨_, ⟨z, rfl⟩, hzt, rfl⟩
      obtain ⟨y, rfl⟩ : ∃ y, z = yᵀ := ⟨zᵀ, (Matrix.transpose_transpose z).symm⟩
      change ratW T S yᵀ ∈ tube p R U at hzt
      rw [hmemT, realPt_ratW, hRemb] at hzt
      obtain ⟨u, hu, e⟩ := hzt
      have e2 : finW S T y = N • u := by
        rw [e]
        abel
      have hNE : (N : D.host.E) ≠ 0 := by exact_mod_cast hN.ne'
      have hy3 : N • ((N : D.host.E)⁻¹ • y) = y := by
        rw [← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, mul_inv_cancel₀ hNE, one_smul]
      have e3 : finW S T ((N : D.host.E)⁻¹ • y) = u := by
        apply nsmul_cancel hN
        rw [← finW_nsmul, hy3, e2]
      have hmem := (GlobalTheory.SW.TensLat.mem_tens_stdL C.X.Λ _).mp ((hA2 _).mp (by rw [e3]; exact hu))
      refine ⟨(N : D.host.E)⁻¹ • y, hmem, ?_⟩
      show C.realPt (ratW T S yᵀ) = N • embR C.X ((N : D.host.E)⁻¹ • y)
      rw [realPt_ratW, ← embR_smul, hy3]
  have hUc : IsCompact (U : Set (WO S T)) := by
    rw [hUdef, AddSubgroup.coe_map]
    exact hA6.image (show Continuous (DistribSMul.toAddMonoidHom (WO S T) N) from continuous_nsmul N)
  obtain ⟨hTG, hLC, hSC, hT2, hdisc, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have := hT2
  have := hdisc
  have := hSC
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have : Countable (ratL T S) := GlobalTheory.countable_of_discrete_addSubgroup (ratL T S)
  have := haar_WR C.X (n := S.rank)
  have := hμ
  have hLdisc : DiscreteTopology (latR C.X S.rank N) :=
    discrete_image (p := p) hRc hUc (ratL T S) (latR C.X S.rank N) (fun v hv => (hL v).mp hv)
  obtain ⟨Fd0, -, -, hFd0⟩ := GlobalTheory.exists_isAddFundamentalDomain_addSubgroup (latR C.X S.rank N)
  refine ⟨⟨Fd0, hFd0 volume⟩, fun Fd hFd F hF => ?_⟩
  have hcont : Continuous h := hf.cont.mul (Complex.continuous_conj.comp hf'.cont)
  have key := integral_eq_mean (p := p) (R := R) (U := U) hpc hRc (fun v => (hRv v).2) hUc hO μ volume
    (ratL T S) (latR C.X S.rank N) hL hcov' hinj h𝓕 h1 hFd hcont hΓ hhU
  have hFR : (fun v => h (R v)) = F := by
    funext v
    have := hF (R v) (hRv v).1
    rw [(hRv v).2] at this
    exact this
  show ∫ w in 𝓕, h w ∂μ = _
  rw [key, hFR]

end GlobalTheory.Ker.TorusMean
