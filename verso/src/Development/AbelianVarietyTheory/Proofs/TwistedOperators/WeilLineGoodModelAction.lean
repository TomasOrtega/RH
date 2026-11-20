import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelPolynomial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfTensEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSmulSemi

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM Filter Topology
open scoped SchwartzMap GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical

noncomputable section

namespace GlobalTheory.ArchJointCont

/- English proof (translation)
Use `haveI : BarrelledSpace ℂ 𝓢(V, ℂ) := GlobalTheory.schwartzMap_barrelledSpace V`. Use `(schwartz_withSeminorms ℂ V ℂ).continuous_of_continuous_comp A fun i => ?_` and prove the remaining obligations. Use `set p : Seminorm ℂ 𝓢(V, ℂ) := schwartzSeminormFamily ℂ V ℂ i`. Establish `hp : Continuous p` using `(schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i`. Set `j₀ : 𝓢(V, ℂ) →ₗ[ℂ] GlobalTheory.DiffDecay.WithSemi p` to `LinearMap.id`.

Establish `hj : Continuous j₀`. Use `continuous_of_continuousAt_zero j₀ ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]`. Use `hp.tendsto 0` as an intermediate fact. Rewrite `this` using `[map_zero]`.

Conclude with `this`. Set `j : 𝓢(V, ℂ) →L[ℂ] GlobalTheory.DiffDecay.WithSemi p` to `⟨j₀, hj⟩`. Establish `hnorm : ∀ x, ‖j x‖ = p x` using `fun x => rfl`. Use `Seminorm.continuous_of_lowerSemicontinuous _ fun f₀ y hy => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `y < p (A f₀) at hy`.

Break down `lt_or_ge y 0 with hy0 | hy0` into its components or cases. Conclude with `Eventually.of_forall fun f => lt_of_lt_of_le hy0 (apply_nonneg _ _)`. Establish `hex : ∃ L : StrongDual ℂ (GlobalTheory.DiffDecay.WithSemi p), y * ‖L‖ < ‖L (j (A f₀))‖`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`.

Establish `h1 : ‖NormedSpace.inclusionInDoubleDual ℂ (GlobalTheory.DiffDecay.WithSemi p) (j (A f₀))‖ ≤ y` using `ContinuousLinearMap.opNorm_le_bound _ hy0 fun L => by`. Rewrite using `[NormedSpace.dual_def]`. Conclude with `hne L`. Rewrite `h1` using `[show NormedSpace.inclusionInDoubleDual ℂ (GlobalTheory.DiffDecay.WithSemi p) (j (A f₀)) = NormedSpace.inclusionInDoubleDualLi ℂ (j (A f₀)) from rfl, LinearIsometry.norm_map, hnorm]`. Conclude with `absurd hy (not_lt.2 h1)`.

Take `⟨L, hL⟩` from `hex`. Establish `hc : Continuous fun f => ‖L (j (A f))‖` using `(h (L.comp j)).norm`. Use `filter_upwards [(hc.tendsto f₀).eventually_const_lt hL] with f hf`. Express the relevant statement in the definitionally equal form `y < p (A f)`. Establish `h2 : ‖L (j (A f))‖ ≤ ‖L‖ * p (A f)` using `by rw [← hnorm]; exact L.le_opNorm _`.

Establish `h4 : y * ‖L‖ < ‖L‖ * p (A f)` using `lt_of_lt_of_le hf h2`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Use polynomial arithmetic with `[norm_nonneg L]`.
-/
theorem continuous_of_weak {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (A : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ)) (h : ∀ T : 𝓢(V, ℂ) →L[ℂ] ℂ, Continuous fun f => T (A f)) : Continuous A := by
  haveI : BarrelledSpace ℂ 𝓢(V, ℂ) := GlobalTheory.schwartzMap_barrelledSpace V
  refine (schwartz_withSeminorms ℂ V ℂ).continuous_of_continuous_comp A fun i => ?_
  set p : Seminorm ℂ 𝓢(V, ℂ) := schwartzSeminormFamily ℂ V ℂ i
  have hp : Continuous p := (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i
  let j₀ : 𝓢(V, ℂ) →ₗ[ℂ] GlobalTheory.DiffDecay.WithSemi p := LinearMap.id
  have hj : Continuous j₀ := by
    refine continuous_of_continuousAt_zero j₀ ?_
    rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
    have := hp.tendsto 0
    rw [map_zero] at this
    exact this
  let j : 𝓢(V, ℂ) →L[ℂ] GlobalTheory.DiffDecay.WithSemi p := ⟨j₀, hj⟩
  have hnorm : ∀ x, ‖j x‖ = p x := fun x => rfl
  refine Seminorm.continuous_of_lowerSemicontinuous _ fun f₀ y hy => ?_
  change y < p (A f₀) at hy
  rcases lt_or_ge y 0 with hy0 | hy0
  · exact Eventually.of_forall fun f => lt_of_lt_of_le hy0 (apply_nonneg _ _)
  have hex : ∃ L : StrongDual ℂ (GlobalTheory.DiffDecay.WithSemi p), y * ‖L‖ < ‖L (j (A f₀))‖ := by
    by_contra hne
    push_neg at hne
    have h1 : ‖NormedSpace.inclusionInDoubleDual ℂ (GlobalTheory.DiffDecay.WithSemi p) (j (A f₀))‖ ≤ y :=
      ContinuousLinearMap.opNorm_le_bound _ hy0 fun L => by
        rw [NormedSpace.dual_def]; exact hne L
    rw [show NormedSpace.inclusionInDoubleDual ℂ (GlobalTheory.DiffDecay.WithSemi p) (j (A f₀)) =
      NormedSpace.inclusionInDoubleDualLi ℂ (j (A f₀)) from rfl, LinearIsometry.norm_map, hnorm] at h1
    exact absurd hy (not_lt.2 h1)
  obtain ⟨L, hL⟩ := hex
  have hc : Continuous fun f => ‖L (j (A f))‖ := (h (L.comp j)).norm
  filter_upwards [(hc.tendsto f₀).eventually_const_lt hL] with f hf
  change y < p (A f)
  have h2 : ‖L (j (A f))‖ ≤ ‖L‖ * p (A f) := by rw [← hnorm]; exact L.le_opNorm _
  have h4 : y * ‖L‖ < ‖L‖ * p (A f) := lt_of_lt_of_le hf h2
  by_contra hcon
  push_neg at hcon
  nlinarith [norm_nonneg L]

/- English proof (translation)
Set `lift : (κ → mixedEmbedding.mixedSpace F) → (κ → AF F)` to `fun y i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0)`. Set `sl : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ)` to `LinearMap.funLeft ℂ ℂ lift`. Set `co : SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ)` to `{ toFun := fun f => ⇑f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Establish `hco : Function.Injective co` using `DFunLike.coe_injective`. Set `e` to `LinearEquiv.ofInjective co hco`.

Take `⟨T₂, hT₂⟩` from `LinearMap.exists_extend (T.toLinearMap ∘ₗ e.symm.toLinearMap)`. Establish `hT₂f : ∀ f : SInf F κ, T₂ ⇑f = T f` using `fun f => by`. Use `congrArg (fun m => m (e f)) hT₂` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_coe] at this`. Rewrite `this` using `[LinearEquiv.ofInjective_apply]`.

Conclude with `this`. Establish `hsl : ∀ (f : SInf F κ) g, sl (pureA F ⇑f g) = g 0 • ⇑f` using `fun f g => by`. Use function extensionality and compare the values at `y`. Use `show pureA F ⇑f g (lift y) = g 0 * f y`. Simplify using `only [pureA, lift, RingEquiv.apply_symm_apply]`.

Rewrite using `[mul_comm]`. Both sides reduce to the same expression. Use `⟨T₂ ∘ₗ sl, fun g _ => ⟨g 0 • T, fun f => ?_⟩, fun f g => ?_⟩` and prove the remaining obligations. Simplify using `[hsl, hT₂f]`. Simplify using `[hsl, hT₂f]`.
-/
theorem exists_adm (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (T : SInf F κ →L[ℂ] ℂ) :
    ∃ l ∈ (adeleClass F).adm κ, ∀ (f : SInf F κ) (g : (κ → IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) → ℂ),
      l (pureA F ⇑f g) = g 0 * T f := by
  let lift : (κ → mixedEmbedding.mixedSpace F) → (κ → AF F) := fun y i =>
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0)
  let sl : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) := LinearMap.funLeft ℂ ℂ lift
  let co : SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) :=
    { toFun := fun f => ⇑f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hco : Function.Injective co := DFunLike.coe_injective
  let e := LinearEquiv.ofInjective co hco
  obtain ⟨T₂, hT₂⟩ := LinearMap.exists_extend (T.toLinearMap ∘ₗ e.symm.toLinearMap)
  have hT₂f : ∀ f : SInf F κ, T₂ ⇑f = T f := fun f => by
    have := congrArg (fun m => m (e f)) hT₂
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      ContinuousLinearMap.coe_coe] at this
    rw [LinearEquiv.ofInjective_apply] at this
    exact this
  have hsl : ∀ (f : SInf F κ) g, sl (pureA F ⇑f g) = g 0 • ⇑f := fun f g => by
    funext y
    show pureA F ⇑f g (lift y) = g 0 * f y
    simp only [pureA, lift, RingEquiv.apply_symm_apply]
    rw [mul_comm]
    rfl
  refine ⟨T₂ ∘ₗ sl, fun g _ => ⟨g 0 • T, fun f => ?_⟩, fun f g => ?_⟩
  · simp [hsl, hT₂f]
  · simp [hsl, hT₂f]

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hψ _hM hW γ hγ r hr0 hR h k h₀ hk hh`. Establish `hs` using `IsUWeilPair.isUSplitting hW`. Set `δ : ℝ → UA σ Y.J × UA σ Wd.J` to `fun t => (γ (Multiplicative.ofAdd t), 1)`. Establish `hδc : Continuous δ` using `(hγ.1.comp continuous_ofAdd).prodMk continuous_const`. Establish `hδ0 : δ 0 = 1` using `by show (γ (Multiplicative.ofAdd 0), 1) = 1`.

Rewrite using `[ofAdd_zero, map_one]`. Both sides reduce to the same expression. Establish `hδm : ∀ s t, δ (s + t) = δ s * δ t` using `fun s t => by show (γ (Multiplicative.ofAdd (s + t)), 1) = (γ (Multiplicative.ofAdd s), 1) * (γ (Multiplicative.ofAdd t), 1)`. Rewrite using `[ofAdd_add, map_mul, Prod.mk_mul_mk, one_mul]`. Establish `ex` using `fun f => GlobalTheory.ArchLinePair.exists_orbit_pair hP M ψ χX χW om hψ hW δ hδc hδ0 hδm (fun t => hγ.2 _) (fun t u _ => by simp [δ, mat]) f`.

Use `choose c g hc0 hslope hact using ex`. Establish `hrr : ∀ x z, At (evI F) z → r (x + z) = r x` using `(hR 0).1`. Establish `hinj` using `GlobalTheory.ArchCancel.eq_of_tens_eq F r hrr ⟨0, hr0⟩`. Establish `hA : ∀ t (f : SInf F (Fin n × Fin d)), om (δ t) (tens (evI F) ⇑f r) = tens (evI F) ⇑(c f t) r` using `fun t f => hact f t r (hR f)`. Establish `tadd : ∀ f g : SInf F (Fin n × Fin d), tens (evI F) ⇑(f + g) r = tens (evI F) ⇑f r + tens (evI F) ⇑g r`.

Introduce `f g`. Use function extensionality and compare the values at `x`. Simplify using `[tens, add_mul]`. Establish `tsmul : ∀ (a : ℂ) (f : SInf F (Fin n × Fin d)), tens (evI F) ⇑(a • f) r = a • tens (evI F) ⇑f r`. Introduce `a f`.

Use function extensionality and compare the values at `x`. Simplify using `[tens, mul_assoc]`. Set `A : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)` to `fun t => { toFun := fun f => c f t map_add' := fun f g => hinj _ _ (by rw [← hA, tadd, map_add, hA, hA, tadd]) map_smul' := fun a f => hinj _ _ (by rw [← hA, tsmul, map_smul, hA, RingHom.id_apply, tsmul]) }`. Establish `hAf : ∀ t f, A t f = c f t` using `fun _ _ => rfl`. Establish `hmul : ∀ s t f, c f (s + t) = c (c f t) s` using `fun s t f => hinj _ _ (by`.

Rewrite using `[← hA (s + t) f, ← hA s (c f t), ← hA t f, hδm, map_mul, Module.End.mul_apply])`. Establish `hcont0 : ∀ f, Tendsto (fun s => c f s) (𝓝 0) (𝓝 f)`. Introduce `f`. Establish `h1 : Tendsto (fun s : ℝ => s • (s⁻¹ • (c f s - f))) (𝓝[≠] 0) (𝓝 ((0 : ℝ) • g f))` using `(tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul (hslope f)`. Rewrite `h1` using `[zero_smul]`.

Establish `h2 : Tendsto (fun s => c f s) (𝓝[≠] 0) (𝓝 f)`. Establish `h1'` using `h1.add_const f`. Rewrite `h1'` using `[zero_add]`. Use `h1'.congr' (eventually_nhdsWithin_of_forall fun s hs => ?_)` and prove the remaining obligations. Rewrite using `[smul_smul, mul_inv_cancel₀ hs, one_smul, sub_add_cancel]`.

Establish `h3 : ContinuousAt (fun s => c f s) 0`. Rewrite using `[← continuousWithinAt_compl_self, ContinuousWithinAt, hc0]`. Conclude with `h2`. Establish `h4` using `h3.tendsto`. Rewrite `h4` using `[hc0]`. Then use the resulting hypothesis.

Establish `hcont : ∀ f, Continuous fun s => c f s`. Introduce `f`. Use `continuous_iff_continuousAt.2 fun t₀ => ?_` and prove the remaining obligations. Establish `ht : Tendsto (fun s : ℝ => s - t₀) (𝓝 t₀) (𝓝 0)`. Establish `h5` using `(continuous_sub_right t₀).tendsto t₀`.

Rewrite `h5` using `[sub_self]`. Then use the resulting hypothesis. Use `((hcont0 (c f t₀)).comp ht).congr fun s => ?_` and prove the remaining obligations. Use `show c (c f t₀) (s - t₀) = c f s`. Rewrite using `[← hmul, sub_add_cancel]`. Set `g₀` to `GlobalTheory.ArchLocality.intInd (F := F) (Fin n × Fin d)`.

Establish `hg₀ : g₀ ∈ SB _` using `GlobalTheory.ArchLocality.intInd_mem _`. Establish `hg₀0 : g₀ 0 = 1`. Simplify using `only [g₀, GlobalTheory.ArchLocality.intInd]`. Rewrite using `[Set.indicator_of_mem (show (0 : Fin n × Fin d → IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ∈ Set.pi Set.univ fun _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) from fun i _ => zero_mem (GroundTheory.Global.integralFiniteAd …`. Both sides reduce to the same expression.

Set `r₀ : (Fin n × Fin d → AF F) → ℂ` to `fun x => g₀ fun i => (x i).2`. Establish `hrr₀ : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x`. Introduce `x z hz`. Use `congrArg g₀ (funext fun i => ?_)` and prove the remaining obligations. Use `show (x i).2 + (z i).2 = (x i).2`.

Rewrite using `[GlobalTheory.ArchLocality.snd_eq_zero_of_at hz i, add_zero]`. Establish `hR₀ : ∀ f : SInf F (Fin n × Fin d), Rest (evI F) ⇑f r₀` using `fun f => ⟨hrr₀, Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩⟩`. Establish `hAcont : ∀ t, Continuous (A t)`. Introduce `t`. Use `continuous_of_weak (A t) fun T => ?_` and prove the remaining obligations.

Take `⟨l, hl, hlf⟩` from `exists_adm F T`. Take `⟨T', hT'⟩` from `hs.adm (δ t) l hl g₀ hg₀`. Use `T'.continuous.congr fun f => ?_` and prove the remaining obligations. Establish `e1 : om (δ t) (pureA F ⇑f g₀) = pureA F ⇑(c f t) g₀` using `hact f t r₀ (hR₀ f)`. Establish `e2` using `hT' f`.

Rewrite `e2` using `[LinearMap.comp_apply, e1, hlf, hg₀0, one_mul]`. Conclude with `e2.symm`. Set `𝓕 : Set.Icc (-1 : ℝ) 1 → SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)` to `fun i => ⟨A i, hAcont i⟩`. Use `haveI : BarrelledSpace ℂ (SInf F (Fin n × Fin d)) := GlobalTheory.schwartzMap_barrelledSpace _`. Establish `hq` using `schwartz_withSeminorms ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ`.

Establish `hUE : UniformEquicontinuous ((↑) ∘ 𝓕)` using `hq.banach_steinhaus fun q x => by`. Establish `hc : Continuous fun t : ℝ => schwartzSeminormFamily ℂ _ ℂ q (c x t)` using `(hq.continuous_seminorm q).comp (hcont x)`. Use `(isCompact_Icc (a := (-1 : ℝ)) (b := 1)).bddAbove_image hc.continuousOn` as an intermediate fact. Rewrite `this` using `[Set.image_eq_range]`. Conclude with `this`.

Establish `hk' : ∀ t, k t = c (h t) t` using `fun t => hinj _ _ ((hk t).symm.trans (hA t (h t)))`. Establish `h1 : Tendsto (fun t => A t (h t - h₀)) (𝓝 0) (𝓝 0)`. Establish `hE` using `hUE.equicontinuous 0`. Introduce `U hU`. Establish `hU' : {p : SInf F (Fin n × Fin d) × SInf F (Fin n × Fin d) | p.2 - p.1 ∈ U} ∈ uniformity (SInf F (Fin n × Fin d))`.

Rewrite using `[uniformity_eq_comap_nhds_zero]`. Conclude with `⟨U, hU, fun p hp => hp⟩`. Establish `ev` using `hE _ hU'`. Establish `hz : Tendsto (fun t => h t - h₀) (𝓝 0) (𝓝 0)` using `by simpa using hh.sub_const h₀`. Establish `ev3 : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Set.Icc (-1 : ℝ) 1` using `Icc_mem_nhds (by norm_num) (by norm_num)`.

Use `Filter.mem_map.2 ?_` and prove the remaining obligations. Use `filter_upwards [hz.eventually ev, ev3] with t ht ht'`. Use `ht ⟨t, ht'⟩` as an intermediate fact. Simplify `this` using `[𝓕]`. Establish `h2 : Tendsto (fun t => A t (h t - h₀) + c h₀ t) (𝓝 0) (𝓝 (0 + h₀))` using `h1.add (hcont0 h₀)`.

Rewrite `h2` using `[zero_add]`. Use `h2.congr fun t => ?_` and prove the remaining obligations. Rewrite using `[hk' t, map_sub]`. Use `show c (h t) t - c h₀ t + c h₀ t = c (h t) t`. Conclude with `sub_add_cancel _ _`.
-/
theorem tendsto_line : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Y, ∀ (r : (Fin n × Fin d → AF F) → ℂ), r 0 ≠ 0 →
    (∀ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r) →
    ∀ (h k : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (h₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
    (∀ t : ℝ, om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (h t) r) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (k t) r) →
    Filter.Tendsto h (nhds 0) (nhds h₀) → Filter.Tendsto k (nhds 0) (nhds h₀) := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hψ _hM hW γ hγ r hr0 hR h k h₀ hk hh
  have hs := IsUWeilPair.isUSplitting hW
  let δ : ℝ → UA σ Y.J × UA σ Wd.J := fun t => (γ (Multiplicative.ofAdd t), 1)
  have hδc : Continuous δ := (hγ.1.comp continuous_ofAdd).prodMk continuous_const
  have hδ0 : δ 0 = 1 := by
    show (γ (Multiplicative.ofAdd 0), 1) = 1
    rw [ofAdd_zero, map_one]; rfl
  have hδm : ∀ s t, δ (s + t) = δ s * δ t := fun s t => by
    show (γ (Multiplicative.ofAdd (s + t)), 1) = (γ (Multiplicative.ofAdd s), 1) * (γ (Multiplicative.ofAdd t), 1)
    rw [ofAdd_add, map_mul, Prod.mk_mul_mk, one_mul]
  have ex := fun f => GlobalTheory.ArchLinePair.exists_orbit_pair hP M ψ χX χW om hψ hW δ hδc hδ0 hδm (fun t => hγ.2 _)
    (fun t u _ => by simp [δ, mat]) f
  choose c g hc0 hslope hact using ex
  have hrr : ∀ x z, At (evI F) z → r (x + z) = r x := (hR 0).1
  have hinj := GlobalTheory.ArchCancel.eq_of_tens_eq F r hrr ⟨0, hr0⟩
  have hA : ∀ t (f : SInf F (Fin n × Fin d)), om (δ t) (tens (evI F) ⇑f r) = tens (evI F) ⇑(c f t) r :=
    fun t f => hact f t r (hR f)
  have tadd : ∀ f g : SInf F (Fin n × Fin d),
      tens (evI F) ⇑(f + g) r = tens (evI F) ⇑f r + tens (evI F) ⇑g r := by
    intro f g; funext x; simp [tens, add_mul]
  have tsmul : ∀ (a : ℂ) (f : SInf F (Fin n × Fin d)), tens (evI F) ⇑(a • f) r = a • tens (evI F) ⇑f r := by
    intro a f; funext x; simp [tens, mul_assoc]
  let A : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) := fun t =>
    { toFun := fun f => c f t
      map_add' := fun f g => hinj _ _ (by rw [← hA, tadd, map_add, hA, hA, tadd])
      map_smul' := fun a f => hinj _ _ (by rw [← hA, tsmul, map_smul, hA, RingHom.id_apply, tsmul]) }
  have hAf : ∀ t f, A t f = c f t := fun _ _ => rfl
  have hmul : ∀ s t f, c f (s + t) = c (c f t) s := fun s t f => hinj _ _ (by
    rw [← hA (s + t) f, ← hA s (c f t), ← hA t f, hδm, map_mul, Module.End.mul_apply])
  have hcont0 : ∀ f, Tendsto (fun s => c f s) (𝓝 0) (𝓝 f) := by
    intro f
    have h1 : Tendsto (fun s : ℝ => s • (s⁻¹ • (c f s - f))) (𝓝[≠] 0) (𝓝 ((0 : ℝ) • g f)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul (hslope f)
    rw [zero_smul] at h1
    have h2 : Tendsto (fun s => c f s) (𝓝[≠] 0) (𝓝 f) := by
      have h1' := h1.add_const f
      rw [zero_add] at h1'
      refine h1'.congr' (eventually_nhdsWithin_of_forall fun s hs => ?_)
      rw [smul_smul, mul_inv_cancel₀ hs, one_smul, sub_add_cancel]
    have h3 : ContinuousAt (fun s => c f s) 0 := by
      rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hc0]; exact h2
    have h4 := h3.tendsto
    rwa [hc0] at h4
  have hcont : ∀ f, Continuous fun s => c f s := by
    intro f
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    have ht : Tendsto (fun s : ℝ => s - t₀) (𝓝 t₀) (𝓝 0) := by
      have h5 := (continuous_sub_right t₀).tendsto t₀
      rwa [sub_self] at h5
    refine ((hcont0 (c f t₀)).comp ht).congr fun s => ?_
    show c (c f t₀) (s - t₀) = c f s
    rw [← hmul, sub_add_cancel]
  let g₀ := GlobalTheory.ArchLocality.intInd (F := F) (Fin n × Fin d)
  have hg₀ : g₀ ∈ SB _ := GlobalTheory.ArchLocality.intInd_mem _
  have hg₀0 : g₀ 0 = 1 := by
    simp only [g₀, GlobalTheory.ArchLocality.intInd]
    rw [Set.indicator_of_mem (show (0 : Fin n × Fin d → IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ∈ Set.pi Set.univ
      fun _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) from
        fun i _ => zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F))]
    rfl
  let r₀ : (Fin n × Fin d → AF F) → ℂ := fun x => g₀ fun i => (x i).2
  have hrr₀ : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := by
    intro x z hz
    refine congrArg g₀ (funext fun i => ?_)
    show (x i).2 + (z i).2 = (x i).2
    rw [GlobalTheory.ArchLocality.snd_eq_zero_of_at hz i, add_zero]
  have hR₀ : ∀ f : SInf F (Fin n × Fin d), Rest (evI F) ⇑f r₀ := fun f =>
    ⟨hrr₀, Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩⟩
  have hAcont : ∀ t, Continuous (A t) := by
    intro t
    refine continuous_of_weak (A t) fun T => ?_
    obtain ⟨l, hl, hlf⟩ := exists_adm F T
    obtain ⟨T', hT'⟩ := hs.adm (δ t) l hl g₀ hg₀
    refine T'.continuous.congr fun f => ?_
    have e1 : om (δ t) (pureA F ⇑f g₀) = pureA F ⇑(c f t) g₀ := hact f t r₀ (hR₀ f)
    have e2 := hT' f
    rw [LinearMap.comp_apply, e1, hlf, hg₀0, one_mul] at e2
    exact e2.symm
  let 𝓕 : Set.Icc (-1 : ℝ) 1 → SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d) := fun i => ⟨A i, hAcont i⟩
  haveI : BarrelledSpace ℂ (SInf F (Fin n × Fin d)) := GlobalTheory.schwartzMap_barrelledSpace _
  have hq := schwartz_withSeminorms ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ
  have hUE : UniformEquicontinuous ((↑) ∘ 𝓕) := hq.banach_steinhaus fun q x => by
    have hc : Continuous fun t : ℝ => schwartzSeminormFamily ℂ _ ℂ q (c x t) :=
      (hq.continuous_seminorm q).comp (hcont x)
    have := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).bddAbove_image hc.continuousOn
    rw [Set.image_eq_range] at this
    exact this
  have hk' : ∀ t, k t = c (h t) t := fun t => hinj _ _ ((hk t).symm.trans (hA t (h t)))
  have h1 : Tendsto (fun t => A t (h t - h₀)) (𝓝 0) (𝓝 0) := by
    have hE := hUE.equicontinuous 0
    intro U hU
    have hU' : {p : SInf F (Fin n × Fin d) × SInf F (Fin n × Fin d) | p.2 - p.1 ∈ U} ∈
        uniformity (SInf F (Fin n × Fin d)) := by
      rw [uniformity_eq_comap_nhds_zero]; exact ⟨U, hU, fun p hp => hp⟩
    have ev := hE _ hU'
    have hz : Tendsto (fun t => h t - h₀) (𝓝 0) (𝓝 0) := by simpa using hh.sub_const h₀
    have ev3 : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Set.Icc (-1 : ℝ) 1 := Icc_mem_nhds (by norm_num) (by norm_num)
    refine Filter.mem_map.2 ?_
    filter_upwards [hz.eventually ev, ev3] with t ht ht'
    have := ht ⟨t, ht'⟩
    simpa [𝓕] using this
  have h2 : Tendsto (fun t => A t (h t - h₀) + c h₀ t) (𝓝 0) (𝓝 (0 + h₀)) := h1.add (hcont0 h₀)
  rw [zero_add] at h2
  refine h2.congr fun t => ?_
  rw [hk' t, map_sub]
  show c (h t) t - c h₀ t + c h₀ t = c (h t) t
  exact sub_add_cancel _ _

end GlobalTheory.ArchJointCont
