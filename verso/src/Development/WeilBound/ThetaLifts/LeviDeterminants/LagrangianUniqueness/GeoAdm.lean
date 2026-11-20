import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.ExistsScaledIntegralLatticeSubset
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.IndicatorCosetScaledIntegralEqRestrictedProductStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace PositivityTheory.ThKF0.GeoAdm
open GlobalTheory.EvAdm
open scoped Classical

/- English proof (translation)
Conclude with `PositivityTheory.Mix.T.indicator_coset_scaledIntegral_eq_restrictedProduct`.
-/
theorem boxS : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F) (r : κ → FiniteAdeleRing (𝓞 F) F), a ≠ 0 →
    ∃ φ : ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) ∧
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      ∀ y : κ → FiniteAdeleRing (𝓞 F) F, Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) y =
        ∏ᶠ v, φ v fun i => evalV F v (y i) := by
  exact PositivityTheory.Mix.T.indicator_coset_scaledIntegral_eq_restrictedProduct

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
Establish `hg' : IsLocallyConstant g ∧ HasCompactSupport g` using `hg`. Take `⟨hlc, hcs⟩` from `hg'`. Establish `hK : IsCompact (tsupport g)` using `hcs`. Establish `hW : ∀ x : κ → FiniteAdeleRing (𝓞 F) F, ∃ W ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F), ∀ u ∈ W, ∀ w ∈ W, g (x + u + w) = g x`. Introduce `x`.

Establish `h1 : {y | g y = g x} ∈ 𝓝 x` using `(hlc.isOpen_fiber (g x)).mem_nhds rfl`. Establish `h2 : (fun u => x + u) ⁻¹' {y | g y = g x} ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F)` using `(continuous_const_add x).continuousAt.preimage_mem_nhds (by simpa using h1)`. Take `⟨W, hW0, hWW⟩` from `exists_nhds_zero_half h2`. Conclude with `⟨W, hW0, fun u hu w hw => by simpa [add_assoc] using hWW u hu w hw⟩`. Use `choose W hW0 hWg using hW`.

Take `⟨t, -, ht⟩` from `hK.elim_nhds_subcover (fun x => {y | y - x ∈ W x}) (fun x _ => (continuous_sub_right x).continuousAt.preimage_mem_nhds (by simpa using hW0 x))`. Establish `hV : (⋂ x ∈ t, W x) ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F)` using `(Filter.biInter_finset_mem t).2 fun x _ => hW0 x`. Establish `hkey : ∀ y ∈ tsupport g, ∀ z ∈ ⋂ x ∈ t, W x, g (y + z) = g y`. Introduce `y hy z hz`. Take `⟨x, hx, hyx⟩` from `Set.mem_iUnion₂.1 (ht hy)`.

Establish `hzx : z ∈ W x` using `Set.mem_iInter₂.1 hz x hx`. Establish `e1` using `hWg x (y - x) hyx z hzx`. Establish `e2` using `hWg x (y - x) hyx 0 (mem_of_mem_nhds (hW0 x))`. Simplify using `only [add_sub_cancel, add_zero] at e1 e2`. Rewrite using `[e1, e2]`.

Establish `hV' : (fun z : κ → FiniteAdeleRing (𝓞 F) F => -z) ⁻¹' (⋂ x ∈ t, W x) ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F)` using `continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hV)`. Take `⟨a, ha, hsub⟩` from `PositivityTheory.Mix.exists_scaled_integral_lattice_subset F κ _ (Filter.inter_mem hV hV')`. Use `⟨a, ha, fun y z hz => ?_⟩` and prove the remaining obligations. Establish `hz'` using `hsub hz`. Distinguish the cases in `hy : y ∈ tsupport g`.

Conclude with `hkey y hy z hz'.1`. Distinguish the cases in `hyz : y + z ∈ tsupport g`. Establish `h3` using `hkey (y + z) hyz (-z) hz'.2`. Establish `h4 : g y = g (y + z)` using `by simpa using h3`. Conclude with `h4.symm`.

Rewrite using `[image_eq_zero_of_notMem_tsupport hyz, image_eq_zero_of_notMem_tsupport hy]`.
-/
theorem exists_invariant {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ a : F, a ≠ 0 ∧ ∀ x, ∀ z ∈ scaledInt F κ a, g (x + z) = g x := by
  have hg' : IsLocallyConstant g ∧ HasCompactSupport g := hg
  obtain ⟨hlc, hcs⟩ := hg'
  have hK : IsCompact (tsupport g) := hcs
  have hW : ∀ x : κ → FiniteAdeleRing (𝓞 F) F, ∃ W ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F),
      ∀ u ∈ W, ∀ w ∈ W, g (x + u + w) = g x := by
    intro x
    have h1 : {y | g y = g x} ∈ 𝓝 x := (hlc.isOpen_fiber (g x)).mem_nhds rfl
    have h2 : (fun u => x + u) ⁻¹' {y | g y = g x} ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) :=
      (continuous_const_add x).continuousAt.preimage_mem_nhds (by simpa using h1)
    obtain ⟨W, hW0, hWW⟩ := exists_nhds_zero_half h2
    exact ⟨W, hW0, fun u hu w hw => by simpa [add_assoc] using hWW u hu w hw⟩
  choose W hW0 hWg using hW
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x => {y | y - x ∈ W x}) (fun x _ =>
    (continuous_sub_right x).continuousAt.preimage_mem_nhds (by simpa using hW0 x))
  have hV : (⋂ x ∈ t, W x) ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) :=
    (Filter.biInter_finset_mem t).2 fun x _ => hW0 x
  have hkey : ∀ y ∈ tsupport g, ∀ z ∈ ⋂ x ∈ t, W x, g (y + z) = g y := by
    intro y hy z hz
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hy)
    have hzx : z ∈ W x := Set.mem_iInter₂.1 hz x hx
    have e1 := hWg x (y - x) hyx z hzx
    have e2 := hWg x (y - x) hyx 0 (mem_of_mem_nhds (hW0 x))
    simp only [add_sub_cancel, add_zero] at e1 e2
    rw [e1, e2]
  have hV' : (fun z : κ → FiniteAdeleRing (𝓞 F) F => -z) ⁻¹' (⋂ x ∈ t, W x) ∈
      𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) :=
    continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨a, ha, hsub⟩ := PositivityTheory.Mix.exists_scaled_integral_lattice_subset F κ _ (Filter.inter_mem hV hV')
  refine ⟨a, ha, fun y z hz => ?_⟩
  have hz' := hsub hz
  by_cases hy : y ∈ tsupport g
  · exact hkey y hy z hz'.1
  · by_cases hyz : y + z ∈ tsupport g
    · have h3 := hkey (y + z) hyz (-z) hz'.2
      have h4 : g y = g (y + z) := by simpa using h3
      exact h4.symm
    · rw [image_eq_zero_of_notMem_tsupport hyz, image_eq_zero_of_notMem_tsupport hy]

/- English proof (translation)
Take `⟨a, ha, hinv⟩` from `exists_invariant hg`. Establish `hg' : IsLocallyConstant g ∧ HasCompactSupport g` using `hg`. Establish `hK : IsCompact (tsupport g)` using `hg'.2`. Establish `hopen : IsOpen ((scaledInt F κ a : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)) : Set (κ → FiniteAdeleRing (𝓞 F) F))` using `GlobalTheory.EvAdm.isOpen_scaledInt a`. Take `⟨t, -, ht⟩` from `hK.elim_nhds_subcover (fun x => {y | y - x ∈ scaledInt F κ a}) (fun x _ => (continuous_sub_right x).continuousAt.preimage_mem_nhds (hopen.mem_nhds (by simp)))`.

Use `⟨a, ha, (t.image (fun x => (QuotientAddGroup.mk x : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ scaledInt F κ a))).image Quotient.out, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `y`. Establish `hmem : ∀ q : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ scaledInt F κ a, y - Quotient.out q ∈ scaledInt F κ a ↔ (QuotientAddGroup.mk y : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ scaledInt F κ a) = q`. Introduce `q`. Establish `hq : (QuotientAddGroup.mk (Quotient.out q) : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ scaledInt F κ a) = q` using `Quotient.out_eq' q`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← (scaledInt F κ a).neg_mem_iff, neg_sub, sub_eq_neg_add]`. Use `_ ↔ (QuotientAddGroup.mk y : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ scaledInt F κ a) = QuotientAddGroup.mk (Quotient.out q) := QuotientAddGroup.eq.symm`. Use `_ ↔ _ := by rw [hq]`. Rewrite using `[Finset.sum_apply, Finset.sum_image (by intro q _ q' _ h; exact Quotient.out_injective h)]`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, Set.indicator_apply, Set.mem_ofPred_eq, hmem, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_ite_eq]`. Use `split_ifs with hy`. Establish `h1` using `hinv (Quotient.out (QuotientAddGroup.mk y : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ scaledInt F κ a)) (y - Quotient.out (QuotientAddGroup.mk y : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ scaledInt F κ a)) ((hmem _).2 rfl)`. Simplify using `using h1`.

Assume the negation of the conclusion as `hne`. Establish `hyK : y ∈ tsupport g` using `subset_tsupport g hne`. Take `⟨x, hx, hyx⟩` from `Set.mem_iUnion₂.1 (ht hyK)`. Apply `hy` to reduce the goal to its premises. Use `Finset.mem_image.2 ⟨x, hx, ?_⟩` and prove the remaining obligations.

Rewrite using `[QuotientAddGroup.eq, neg_add_eq_sub]`. Conclude with `hyx`.
-/
theorem exists_sum_cosets {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ a : F, a ≠ 0 ∧ ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F),
      g = ∑ r ∈ R, g r • Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) := by
  obtain ⟨a, ha, hinv⟩ := exists_invariant hg
  have hg' : IsLocallyConstant g ∧ HasCompactSupport g := hg
  have hK : IsCompact (tsupport g) := hg'.2
  have hopen : IsOpen ((scaledInt F κ a : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)) :
      Set (κ → FiniteAdeleRing (𝓞 F) F)) := GlobalTheory.EvAdm.isOpen_scaledInt a
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x => {y | y - x ∈ scaledInt F κ a}) (fun x _ =>
    (continuous_sub_right x).continuousAt.preimage_mem_nhds
      (hopen.mem_nhds (by simp)))
  refine ⟨a, ha, (t.image (fun x => (QuotientAddGroup.mk x :
    (κ → FiniteAdeleRing (𝓞 F) F) ⧸ scaledInt F κ a))).image Quotient.out, ?_⟩
  funext y
  have hmem : ∀ q : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ scaledInt F κ a,
      y - Quotient.out q ∈ scaledInt F κ a ↔
        (QuotientAddGroup.mk y : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ scaledInt F κ a) = q := by
    intro q
    have hq : (QuotientAddGroup.mk (Quotient.out q) :
        (κ → FiniteAdeleRing (𝓞 F) F) ⧸ scaledInt F κ a) = q := Quotient.out_eq' q
    calc y - Quotient.out q ∈ scaledInt F κ a ↔ -y + Quotient.out q ∈ scaledInt F κ a := by
          rw [← (scaledInt F κ a).neg_mem_iff, neg_sub, sub_eq_neg_add]
      _ ↔ (QuotientAddGroup.mk y : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ scaledInt F κ a) =
          QuotientAddGroup.mk (Quotient.out q) := QuotientAddGroup.eq.symm
      _ ↔ _ := by rw [hq]
  rw [Finset.sum_apply, Finset.sum_image (by intro q _ q' _ h; exact Quotient.out_injective h)]
  simp only [Pi.smul_apply, smul_eq_mul, Set.indicator_apply, Set.mem_ofPred_eq, hmem, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hy
  · have h1 := hinv (Quotient.out (QuotientAddGroup.mk y :
        (κ → FiniteAdeleRing (𝓞 F) F) ⧸ scaledInt F κ a)) (y - Quotient.out (QuotientAddGroup.mk y :
        (κ → FiniteAdeleRing (𝓞 F) F) ⧸ scaledInt F κ a)) ((hmem _).2 rfl)
    simpa using h1
  · by_contra hne
    have hyK : y ∈ tsupport g := subset_tsupport g hne
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hyK)
    apply hy
    refine Finset.mem_image.2 ⟨x, hx, ?_⟩
    rw [QuotientAddGroup.eq, neg_add_eq_sub]
    exact hyx

/- English proof (translation)
Take `⟨a, ha, R, hR⟩` from `exists_sum_cosets hg`. Use `choose ψ hψSB hψcof hψeq using fun r => boxS F κ a r ha`. Use `⟨R.card, fun k => g (R.equivFin.symm k), fun k => ψ (R.equivFin.symm k), fun k v => hψSB _ v, fun k => hψcof _, ?_⟩` and prove the remaining obligations. Establish `key : ∀ r, Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) = fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, ψ r v fun i => evalV F v (y i)` using `fun r => funext (hψeq r)`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[key r]`. Use `_ = _ := by`. Rewrite using `[← Finset.sum_coe_sort R]`. Conclude with `(Equiv.sum_comp R.equivFin.symm (fun r : R => g r • fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, ψ r v fun i => evalV F v (y i))).symm`.
-/
theorem exists_sum_finprod {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (φ : Fin m → ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ),
      (∀ k v, φ k v ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) ∧
      (∀ k, ∀ᶠ v in cofinite, φ k v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      g = ∑ k, c k • fun y => ∏ᶠ v, φ k v fun i => evalV F v (y i) := by
  obtain ⟨a, ha, R, hR⟩ := exists_sum_cosets hg
  choose ψ hψSB hψcof hψeq using fun r => boxS F κ a r ha
  refine ⟨R.card, fun k => g (R.equivFin.symm k), fun k => ψ (R.equivFin.symm k),
    fun k v => hψSB _ v, fun k => hψcof _, ?_⟩
  have key : ∀ r, Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) =
      fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, ψ r v fun i => evalV F v (y i) := fun r => funext (hψeq r)
  calc g = ∑ r ∈ R, g r • Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) := hR
    _ = ∑ r ∈ R, g r • fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, ψ r v fun i => evalV F v (y i) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [key r]
    _ = _ := by
        rw [← Finset.sum_coe_sort R]
        exact (Equiv.sum_comp R.equivFin.symm
          (fun r : R => g r • fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, ψ r v fun i => evalV F v (y i))).symm

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hM hM₁ hev l hl`. Take `⟨-, -, hstd, -, -⟩` from `hM`. Take `⟨-, -, hstd₁, -, -⟩` from `hM₁`. Take `⟨ei, ev, -, hev_v, hpure⟩` from `hev.loc`. Simplify using `only [GlobalTheory.WeilM.adeleClass, Set.mem_ofPred_eq] at hl ⊢`.

Introduce `g hg`. Take `⟨m, c, φ, hφ, hcof, hgeq⟩` from `exists_sum_finprod hg`. Establish `hcofM : ∀ k, ∀ᶠ v in cofinite, φ k v = M.vac v` using `fun k => (hcof k).mp (hstd.mono fun v h1 h2 => h2.trans h1.symm)`. Use `set H : Fin m → (Fin n₁ × Fin d₁ → FiniteAdeleRing (𝓞 F) F) → ℂ := fun k y => ∏ᶠ v, ev v (φ k v) fun i => evalV F v (y i) with hHdef`. Establish `hH : ∀ k, H k ∈ GlobalTheory.WeilM.SB (Fin n₁ × Fin d₁ → FiniteAdeleRing (𝓞 F) F)`.

Introduce `k`. Establish `hSB : ∀ v : HeightOneSpectrum (𝓞 F), ev v (φ k v) ∈ GlobalTheory.WeilM.SB (Fin n₁ × Fin d₁ → Fv F v)` using `fun v => by`. Rewrite using `[← (hev_v v).2]`. Conclude with `Submodule.mem_map_of_mem (hφ k v)`. Establish `hc : ∀ᶠ v in cofinite, ev v (φ k v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1` using `((hcofM k).and hstd₁).mono fun v h => by rw [h.1, (hev_v v).1, h.2]`.

Use `show IsLocallyConstant (H k) ∧ HasCompactSupport (H k)`. Conclude with `⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV (fun v => ev v (φ k v)) hSB hc, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod (fun v => ev v (φ k v)) hSB hc⟩`. Use `choose T hT using fun k => hl (H k) (hH k)`. Establish `hsplit : ∀ f : SchwartzMap (Fin n × Fin d → NumberField.mixedEmbedding.mixedSpace F) ℂ, GlobalTheory.WeilM.pureA F (⇑f) g = ∑ k, c k • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k)`. Introduce `f`.

Use function extensionality and compare the values at `x`. Rewrite using `[hgeq]`. Simplify using `only [GlobalTheory.WeilM.pureA, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm]`.

Both sides reduce to the same expression. Use `⟨∑ k, c k • (T k).comp ei, fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, hsplit f, map_sum, map_sum, ContinuousLinearMap.sum_apply]`. Simplify using `only [map_smul, smul_eq_mul, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[hpure f (φ k) (hφ k) (hcofM k), ← hT k (ei f)]`. Use `congr 2`.
-/
theorem comp_mem_adm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ)
    (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E)))
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e →
      ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hM hM₁ hev l hl
  obtain ⟨-, -, hstd, -, -⟩ := hM
  obtain ⟨-, -, hstd₁, -, -⟩ := hM₁
  obtain ⟨ei, ev, -, hev_v, hpure⟩ := hev.loc
  simp only [GlobalTheory.WeilM.adeleClass, Set.mem_ofPred_eq] at hl ⊢
  intro g hg
  obtain ⟨m, c, φ, hφ, hcof, hgeq⟩ := exists_sum_finprod hg
  have hcofM : ∀ k, ∀ᶠ v in cofinite, φ k v = M.vac v := fun k =>
    (hcof k).mp (hstd.mono fun v h1 h2 => h2.trans h1.symm)
  set H : Fin m → (Fin n₁ × Fin d₁ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
    fun k y => ∏ᶠ v, ev v (φ k v) fun i => evalV F v (y i) with hHdef
  have hH : ∀ k, H k ∈ GlobalTheory.WeilM.SB (Fin n₁ × Fin d₁ → FiniteAdeleRing (𝓞 F) F) := by
    intro k
    have hSB : ∀ v : HeightOneSpectrum (𝓞 F),
        ev v (φ k v) ∈ GlobalTheory.WeilM.SB (Fin n₁ × Fin d₁ → Fv F v) := fun v => by
      rw [← (hev_v v).2]
      exact Submodule.mem_map_of_mem (hφ k v)
    have hc : ∀ᶠ v in cofinite, ev v (φ k v) =
        Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
      ((hcofM k).and hstd₁).mono fun v h => by rw [h.1, (hev_v v).1, h.2]
    show IsLocallyConstant (H k) ∧ HasCompactSupport (H k)
    exact ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV (fun v => ev v (φ k v)) hSB hc,
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod (fun v => ev v (φ k v)) hSB hc⟩
  choose T hT using fun k => hl (H k) (hH k)
  have hsplit : ∀ f : SchwartzMap (Fin n × Fin d → NumberField.mixedEmbedding.mixedSpace F) ℂ,
      GlobalTheory.WeilM.pureA F (⇑f) g = ∑ k, c k • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k) := by
    intro f
    funext x
    rw [hgeq]
    simp only [GlobalTheory.WeilM.pureA, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm]
    rfl
  refine ⟨∑ k, c k • (T k).comp ei, fun f => ?_⟩
  rw [LinearMap.comp_apply, hsplit f, map_sum, map_sum, ContinuousLinearMap.sum_apply]
  simp only [map_smul, smul_eq_mul, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hpure f (φ k) (hφ k) (hcofM k), ← hT k (ei f)]
  congr 2

end PositivityTheory.ThKF0.GeoAdm

end
