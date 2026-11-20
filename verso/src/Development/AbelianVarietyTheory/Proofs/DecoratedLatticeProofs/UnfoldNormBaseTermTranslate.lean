import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnitaryOrbitActionTransitiveWithStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralUnfoldSumTransitiveOrbitStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFundamentalDomainProdOfKernelImageStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRationalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

/- English proof (translation)
Simplify using `only [GQ, HFinIn, HFin, Subgroup.mem_subgroupOf] at hγ`. Take `⟨u, -, hu⟩` from `hγ`. Conclude with `⟨u.1, (congrArg Units.val hu).symm⟩`.
-/
theorem mt_mem_GQ_rat' {D : D7} (V : HSp D) {γ : GA D V} (hγ : γ ∈ GQ V) :
    ∃ M : Matrix (Fin V.rank) (Fin V.rank) D.host.E, mt V γ = rat M := by
  simp only [GQ, HFinIn, HFin, Subgroup.mem_subgroupOf] at hγ
  obtain ⟨u, -, hu⟩ := hγ
  exact ⟨u.1, (congrArg Units.val hu).symm⟩

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vW x₀ hx G Φ hG hΦ 𝓐 𝓑 h𝓐 h𝓑 g`. Take `⟨a1, a2, a3, a4, a5, a6, a7⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V`. Take `⟨b1, b2, b3, b4, b5, b6, b7⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W`. Take `⟨c1, c2, c3, c4⟩` from `GlobalTheory.Mem.TrueRecord.top_NFlag V (GlobalTheory.MixPer.isIsoSub_e d)`. Take `⟨hN1, hN2, hN3⟩` from `vN.unit`.

Use `haveI := vW.haar`. Use `haveI : SFinite vN.ν := inferInstance`. Use `haveI : SFinite vW.μ := inferInstance`. Take `⟨act, y₀, hy₀, hrel, htrans, hstab1, hstab2⟩` from `GlobalTheory.T.flagUnitaryOrbitAction_transitive_with_stabilizer D V V₀ W ρ d x₀ hx`. Use `letI := act`.

Use `haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable`. Use `haveI : Countable (Matrix (Fin W.rank) (Fin ρ) D.host.E) := inferInstanceAs (Countable (Fin _ → Fin _ → _))`. Use `haveI hΓc : Countable ((NFlagQ V d.e).prod (GQ W)) := Function.Injective.countable (f := fun γ : (NFlagQ V d.e).prod (GQ W) => ((⟨γ.1.1, (Subgroup.mem_prod.1 γ.2).1⟩ : NFlagQ V d.e), (⟨γ.1.2, (Subgroup.mem_prod.1 γ.2).2⟩ : GQ W))) fun a b h => by`. Simplify using `only [Prod.mk.injEq, Subtype.mk.injEq] at h`. Conclude with `Subtype.ext (Prod.ext h.1 h.2)`.

Use `haveI : Countable ((MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀).map (Subgroup.subtype _)) := (Subgroup.inclusion_injective (Subgroup.map_subtype_le (MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀))).countable`. Establish `hF : IsFundamentalDomain ((NFlagQ V d.e).prod (GQ W)) (vN.𝓝 ×ˢ vW.𝓕) (vN.ν.prod vW.μ)`. Use `GlobalTheory.T.isFundamentalDomain_prod_of_kernel_image _ _ vN.ν vW.μ _ vN.𝓝 vW.𝓕 ?_ ?_` and prove the remaining obligations. Establish `hc : ((NFlagQ V d.e).prod (GQ W)).comap (MonoidHom.inl (flagN d) (GA D W)) = NFlagQ V d.e`. Use extensionality with `n`.

Simplify using `only [Subgroup.mem_comap, MonoidHom.inl_apply, Subgroup.mem_prod, one_mem, and_true]`. Rewrite using `[hc]`. Conclude with `hN2`. Establish `hc : ((NFlagQ V d.e).prod (GQ W)).map (MonoidHom.snd (flagN d) (GA D W)) = GQ W`. Use extensionality with `h`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, hp, rfl⟩`. Conclude with `(Subgroup.mem_prod.1 hp).2`. Introduce `hh`. Conclude with `⟨(1, h), Subgroup.mem_prod.2 ⟨one_mem _, hh⟩, rfl⟩`.

Rewrite using `[hc]`. Conclude with `vW.fund`. Establish `hG' : IsFundamentalDomain ((MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀).map (Subgroup.subtype _)) (𝓐 ×ˢ 𝓑) (vN.ν.prod vW.μ)`. Use `GlobalTheory.T.isFundamentalDomain_prod_of_kernel_image _ _ vN.ν vW.μ _ 𝓐 𝓑 ?_ ?_` and prove the remaining obligations. Rewrite using `[hstab1]`.

Conclude with `h𝓐`. Rewrite using `[hstab2]`. Conclude with `h𝓑`. Establish `hmeas : ∀ y : Orb W x₀, Measurable fun p : flagN d × GA D W => G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1`. Introduce `y`.

Establish `t4` using `(GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS Φ hΦ).2.2.2.1 y.1`. Use `Continuous.measurable ?_` and prove the remaining obligations. Use `(hG.2.1.comp continuous_snd).mul ?_` and prove the remaining obligations. Conclude with `t4.comp (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk continuous_snd)`. Establish `hinv : ∀ (γ : (NFlagQ V d.e).prod (GQ W)) (y : Orb W x₀) (p : flagN d × GA D W), G ((γ : flagN d × GA D W) * p).2 * term ψ d W vS (om (((γ : flagN d × GA D W) * p).1.1 * g, ((γ : flagN d × GA D W) * p).2) Φ) (γ • y).1 = G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1`.

Introduce `γ y p`. Establish `hmem` using `Subgroup.mem_prod.1 γ.2`. Establish `hq1 : ((γ.1.1 : flagN d) : GA D V) ∈ GQ V` using `hmem.1`. Establish `hq2 : γ.1.2 ∈ GQ W` using `hmem.2`. Take `⟨M, hM⟩` from `mt_mem_GQ_rat' W hq2`.

Establish `hΨ` using `hω.om_pres (p.1.1 * g, p.2) Φ hΦ`. Establish `hΨ'` using `hω.om_pres (1, γ.1.2) _ hΨ`. Establish `key : term ψ d W vS (om ((γ.1.1 : GA D V) * p.1.1 * g, γ.1.2 * p.2) Φ) (γ • y).1 = term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1`. Establish `hsplit : ((γ.1.1 : GA D V) * p.1.1 * g, γ.1.2 * p.2) = (((γ.1.1 : GA D V), 1) * ((1 : GA D V), γ.1.2)) * (p.1.1 * g, p.2)`. Apply the tactic sequence `ext <;> simp [mul_assoc]`.

Rewrite using `[hsplit, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]`. Establish `t2` using `(GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS _ hΨ').2.1`. Establish `t3` using `(GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS _ hΨ).2.2.1`. Establish `e1 : (rat (M * y.1) : Mx D W.rank ρ) = rat (γ • y).1 ⬝ blockX d (γ.1.1 : GA D V)`. Rewrite using `[hrel γ y, hM, rat_mul]`.

Rewrite using `[t2 _ hq1 γ.1.1.2 (γ • y).1 (M * y.1) e1, t3 _ hq2 (M * y.1) y.1 (by rw [hM, rat_mul])]`. Establish `hGG : G (γ.1.2 * p.2) = G p.2` using `hG.1 _ hq2 p.2`. Use `show G (γ.1.2 * p.2) * term ψ d W vS (om ((γ.1.1 : GA D V) * p.1.1 * g, γ.1.2 * p.2) Φ) (γ • y).1 = _`. Conclude with `congrArg₂ (· * ·) hGG key`. Take `⟨hl, -⟩` from `GlobalTheory.T.lintegral_unfold_sum_transitive_orbit (flagN d × GA D W) (vN.ν.prod vW.μ) ((NFlagQ V d.e).prod (GQ W)) (Orb W x₀) y₀ htrans (vN.𝓝 ×ˢ vW.𝓕) (𝓐 ×ˢ 𝓑) hF hG' (fun y p => G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1) hmeas hinv`.

Simplify using `only [hy₀] at hl`. Conclude with `hl`.
-/
theorem unfold_norm_base_term_translate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ (𝓐 : Set (flagN d)) (𝓑 : Set (GA D W)), IsFundamentalDomain ((GQ V ⊓ radX d).subgroupOf (flagN d)) 𝓐 vN.ν → IsFundamentalDomain (GQ W ⊓ Rgrp W (rat x₀) : Subgroup (GA D W)) 𝓑 vW.μ → ∀ g : GA D V, ∫⁻ p in 𝓐 ×ˢ 𝓑, ‖G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) x₀‖ₑ ∂(vN.ν.prod vW.μ) = ∫⁻ p in vN.𝓝 ×ˢ vW.𝓕, ∑' y : Orb W x₀, ‖G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1‖ₑ ∂(vN.ν.prod vW.μ) := by
  intro D ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vW x₀ hx G Φ hG hΦ 𝓐 𝓑 h𝓐 h𝓑 g
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (GlobalTheory.MixPer.isIsoSub_e d)
  obtain ⟨hN1, hN2, hN3⟩ := vN.unit
  haveI := vW.haar
  haveI : SFinite vN.ν := inferInstance
  haveI : SFinite vW.μ := inferInstance
  obtain ⟨act, y₀, hy₀, hrel, htrans, hstab1, hstab2⟩ := GlobalTheory.T.flagUnitaryOrbitAction_transitive_with_stabilizer D V V₀ W ρ d x₀ hx
  letI := act
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin W.rank) (Fin ρ) D.host.E) := inferInstanceAs (Countable (Fin _ → Fin _ → _))
  haveI hΓc : Countable ((NFlagQ V d.e).prod (GQ W)) := Function.Injective.countable
    (f := fun γ : (NFlagQ V d.e).prod (GQ W) => ((⟨γ.1.1, (Subgroup.mem_prod.1 γ.2).1⟩ : NFlagQ V d.e),
      (⟨γ.1.2, (Subgroup.mem_prod.1 γ.2).2⟩ : GQ W)))
    fun a b h => by
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      exact Subtype.ext (Prod.ext h.1 h.2)
  haveI : Countable ((MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀).map (Subgroup.subtype _)) :=
    (Subgroup.inclusion_injective (Subgroup.map_subtype_le (MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀))).countable
  have hF : IsFundamentalDomain ((NFlagQ V d.e).prod (GQ W)) (vN.𝓝 ×ˢ vW.𝓕) (vN.ν.prod vW.μ) := by
    refine GlobalTheory.T.isFundamentalDomain_prod_of_kernel_image _ _ vN.ν vW.μ _ vN.𝓝 vW.𝓕 ?_ ?_
    · have hc : ((NFlagQ V d.e).prod (GQ W)).comap (MonoidHom.inl (flagN d) (GA D W)) = NFlagQ V d.e := by
        ext n
        simp only [Subgroup.mem_comap, MonoidHom.inl_apply, Subgroup.mem_prod, one_mem, and_true]
      rw [hc]; exact hN2
    · have hc : ((NFlagQ V d.e).prod (GQ W)).map (MonoidHom.snd (flagN d) (GA D W)) = GQ W := by
        ext h
        constructor
        · rintro ⟨p, hp, rfl⟩
          exact (Subgroup.mem_prod.1 hp).2
        · intro hh
          exact ⟨(1, h), Subgroup.mem_prod.2 ⟨one_mem _, hh⟩, rfl⟩
      rw [hc]; exact vW.fund
  have hG' : IsFundamentalDomain ((MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀).map (Subgroup.subtype _))
      (𝓐 ×ˢ 𝓑) (vN.ν.prod vW.μ) := by
    refine GlobalTheory.T.isFundamentalDomain_prod_of_kernel_image _ _ vN.ν vW.μ _ 𝓐 𝓑 ?_ ?_
    · rw [hstab1]; exact h𝓐
    · rw [hstab2]; exact h𝓑
  have hmeas : ∀ y : Orb W x₀, Measurable fun p : flagN d × GA D W =>
      G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1 := by
    intro y
    have t4 := (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS Φ hΦ).2.2.2.1 y.1
    refine Continuous.measurable ?_
    refine (hG.2.1.comp continuous_snd).mul ?_
    exact t4.comp (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk continuous_snd)
  have hinv : ∀ (γ : (NFlagQ V d.e).prod (GQ W)) (y : Orb W x₀) (p : flagN d × GA D W),
      G ((γ : flagN d × GA D W) * p).2 *
        term ψ d W vS (om (((γ : flagN d × GA D W) * p).1.1 * g, ((γ : flagN d × GA D W) * p).2) Φ) (γ • y).1 =
      G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1 := by
    intro γ y p
    have hmem := Subgroup.mem_prod.1 γ.2
    have hq1 : ((γ.1.1 : flagN d) : GA D V) ∈ GQ V := hmem.1
    have hq2 : γ.1.2 ∈ GQ W := hmem.2
    obtain ⟨M, hM⟩ := mt_mem_GQ_rat' W hq2
    have hΨ := hω.om_pres (p.1.1 * g, p.2) Φ hΦ
    have hΨ' := hω.om_pres (1, γ.1.2) _ hΨ
    have key : term ψ d W vS (om ((γ.1.1 : GA D V) * p.1.1 * g, γ.1.2 * p.2) Φ) (γ • y).1 =
        term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1 := by
      have hsplit : ((γ.1.1 : GA D V) * p.1.1 * g, γ.1.2 * p.2) =
          (((γ.1.1 : GA D V), 1) * ((1 : GA D V), γ.1.2)) * (p.1.1 * g, p.2) := by
        ext <;> simp [mul_assoc]
      rw [hsplit, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      have t2 := (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS _ hΨ').2.1
      have t3 := (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS _ hΨ).2.2.1
      have e1 : (rat (M * y.1) : Mx D W.rank ρ) = rat (γ • y).1 ⬝ blockX d (γ.1.1 : GA D V) := by
        rw [hrel γ y, hM, rat_mul]
      rw [t2 _ hq1 γ.1.1.2 (γ • y).1 (M * y.1) e1, t3 _ hq2 (M * y.1) y.1 (by rw [hM, rat_mul])]
    have hGG : G (γ.1.2 * p.2) = G p.2 := hG.1 _ hq2 p.2
    show G (γ.1.2 * p.2) *
        term ψ d W vS (om ((γ.1.1 : GA D V) * p.1.1 * g, γ.1.2 * p.2) Φ) (γ • y).1 = _
    exact congrArg₂ (· * ·) hGG key
  obtain ⟨hl, -⟩ := GlobalTheory.T.lintegral_unfold_sum_transitive_orbit (flagN d × GA D W) (vN.ν.prod vW.μ) ((NFlagQ V d.e).prod (GQ W)) (Orb W x₀) y₀ htrans
    (vN.𝓝 ×ˢ vW.𝓕) (𝓐 ×ˢ 𝓑) hF hG'
    (fun y p => G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1) hmeas hinv
  simp only [hy₀] at hl
  exact hl

end GlobalTheory.Unf
