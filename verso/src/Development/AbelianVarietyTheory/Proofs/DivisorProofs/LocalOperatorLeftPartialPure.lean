import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductMemSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOperatorParametricExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFunctionFactorizableSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatSumSplitTensorStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section
namespace GlobalTheory.DblEval.PartLStr

/- English proof (translation)
Establish `hc : Continuous fun p : (κ → X) × (κ' → X) => Sum.elim p.1 p.2` using `continuous_pi fun k => by`. Consider the cases of `k`. Use `exacts [(continuous_apply _).comp continuous_fst, (continuous_apply _).comp continuous_snd]`. Use `⟨(ha.1.comp_continuous (f := fun z : κ ⊕ κ' → X => z ∘ Sum.inl) (by fun_prop)).mul (hb.1.comp_continuous (f := fun z : κ ⊕ κ' → X => z ∘ Sum.inr) (by fun_prop)), ?_⟩` and prove the remaining obligations. Use `HasCompactSupport.intro ((ha.2.isCompact.prod hb.2.isCompact).image hc) fun z hz => ?_` and prove the remaining obligations.

Distinguish the cases in `h1 : z ∘ Sum.inl ∈ tsupport a`. Distinguish the cases in `h2 : z ∘ Sum.inr ∈ tsupport b`. Conclude with `absurd ⟨(z ∘ Sum.inl, z ∘ Sum.inr), ⟨h1, h2⟩, Sum.elim_comp_inl_inr z⟩ hz`. Simplify using `only [image_eq_zero_of_notMem_tsupport h2, mul_zero]`. Simplify using `only [image_eq_zero_of_notMem_tsupport h1, zero_mul]`.
-/
theorem mul_blocks_mem_SB {X : Type} [TopologicalSpace X] [T2Space X] {κ κ' : Type} {a : (κ → X) → ℂ} {b : (κ' → X) → ℂ}
    (ha : a ∈ SB (κ → X)) (hb : b ∈ SB (κ' → X)) :
    (fun z : κ ⊕ κ' → X => a (z ∘ Sum.inl) * b (z ∘ Sum.inr)) ∈ SB (κ ⊕ κ' → X) := by
  have hc : Continuous fun p : (κ → X) × (κ' → X) => Sum.elim p.1 p.2 :=
    continuous_pi fun k => by
      cases k
      exacts [(continuous_apply _).comp continuous_fst, (continuous_apply _).comp continuous_snd]
  refine ⟨(ha.1.comp_continuous (f := fun z : κ ⊕ κ' → X => z ∘ Sum.inl) (by fun_prop)).mul
    (hb.1.comp_continuous (f := fun z : κ ⊕ κ' → X => z ∘ Sum.inr) (by fun_prop)), ?_⟩
  refine HasCompactSupport.intro ((ha.2.isCompact.prod hb.2.isCompact).image hc) fun z hz => ?_
  by_cases h1 : z ∘ Sum.inl ∈ tsupport a
  · by_cases h2 : z ∘ Sum.inr ∈ tsupport b
    · exact absurd ⟨(z ∘ Sum.inl, z ∘ Sum.inr), ⟨h1, h2⟩, Sum.elim_comp_inl_inr z⟩ hz
    · simp only [image_eq_zero_of_notMem_tsupport h2, mul_zero]
  · simp only [image_eq_zero_of_notMem_tsupport h1, zero_mul]

/- English proof (translation)
Apply the tactic sequence `funext k; cases k <;> rfl`.
-/
theorem glue_sumComm {R κ κ' : Type} (a : κ' → R) (x : κ → R) :
    GlobalTheory.ThK.Adapt.glue (Equiv.sumComm κ κ') a x = Sum.elim x a := by
  funext k; cases k <;> rfl

/- English proof (translation)
Introduce `F _ _ κ κ₁ κ' _ _ _ e he`. Use `haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F`. Take `⟨ei, ev, hSB, hstd, hpure⟩` from `he`. Set `eq₀ : (κ ⊕ κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) × (κ' → mixedEmbedding.mixedSpace F)` to `(LinearEquiv.sumArrowLequivProdArrow κ κ' ℝ _).toContinuousLinearEquiv`. Set `eq₁ : (κ₁ ⊕ κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ₁ → mixedEmbedding.mixedSpace F) × (κ' → mixedEmbedding.mixedSpace F)` to `(LinearEquiv.sumArrowLequivProdArrow κ₁ κ' ℝ _).toContinuousLinearEquiv`.

Take `⟨P₀, hP₀⟩` from `GlobalTheory.T.schwartz_operator_parametric_extension (V' := κ' → mixedEmbedding.mixedSpace F) ei`. Set `P : SInf F (κ ⊕ κ') →L[ℂ] SInf F (κ₁ ⊕ κ')` to `(SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eq₁).comp (P₀.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eq₀.symm))`. Establish `hP : ∀ (f : SInf F (κ ⊕ κ')) (y : κ₁ → mixedEmbedding.mixedSpace F) (x' : κ' → mixedEmbedding.mixedSpace F) (h : SInf F κ), (∀ x, h x = f (Sum.elim x x')) → P f (Sum.elim y x') = ei h y`. Introduce `f y x' h hh`. Establish `h1 : eq₁ (Sum.elim y x') = (y, x')` using `rfl`.

Simplify using `only [P, ContinuousLinearMap.comp_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, h1]`. Conclude with `hP₀ _ x' h (fun x => (hh x).trans rfl) y`. Use `⟨P, fun g hg => ?_⟩` and prove the remaining obligations. Establish `hE : ∀ (z : AF F) (v : Pl F), evFin F v z = evalV F v z.2` using `fun _ _ => rfl`. Take `⟨m, a, b, ha, hb, hab⟩` from `GlobalTheory.T.schwartz_bruhat_sum_split_tensor g hg`.

Use `choose n φ hφSB hφstd hφ using fun k => GlobalTheory.T.adelic_schwartz_function_factorizable_sum (a k) (ha k)`. Set `g₁ : (κ₁ ⊕ κ' → Af F) → ℂ` to `∑ k, ∑ j : Fin (n k), fun z => (∏ᶠ v, ev v (φ k j v) fun i => evalV F v (z (Sum.inl i))) * b k (z ∘ Sum.inr)`. Establish `hev : ∀ k j, ∀ᶠ v in cofinite, ev v (φ k j v) = stdInd F κ₁ v` using `fun k j => by filter_upwards [hstd, hφstd k j] with v h1 h2`. Rewrite using `[h2, h1]`. Use `⟨g₁, Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun j _ => mul_blocks_mem_SB (GlobalTheory.AdelicCoordSB.finprod_mem_SB F κ₁ _ (fun v => hSB v _ (hφSB k j v)) (hev k j)) (hb k), ?_⟩` and prove the remaining obligations.

Introduce `f`. Use function extensionality and compare the values at `y`. Take `⟨T, hT⟩` from `GlobalTheory.ThK.Adapt.exists_slice (κ := κ ⊕ κ') (κ₁ := κ) (Equiv.sumComm κ κ') (fun i => evI F (y (Sum.inr i)))`. Establish `hh : ∀ x, T f x = f (Sum.elim x fun i => evI F (y (Sum.inr i)))` using `fun x => by`. Rewrite using `[hT, glue_sumComm]`.

Establish `hslice : (fun x : κ → AF F => pureA F f g (Sum.elim x (y ∘ Sum.inr))) = ∑ k, ∑ j : Fin (n k), b k (fun i => (y (Sum.inr i)).2) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (T f) (φ k j)`. Use function extensionality and compare the values at `x`. Establish `e1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (Sum.elim x (y ∘ Sum.inr) i).1) = Sum.elim (fun i => evI F (x i)) fun i => evI F (y (Sum.inr i))`. Apply the tactic sequence `funext i; cases i <;> rfl`. Establish `e2 : (fun i => (Sum.elim x (y ∘ Sum.inr) i).2) = Sum.elim (fun i => (x i).2) fun i => (y (Sum.inr i)).2`.

Apply the tactic sequence `funext i; cases i <;> rfl`. Simplify using `only [pureA, e1, e2, hab, hφ, ← hh, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [hE]`. Expand and normalize the polynomial expressions, which then agree.

Establish `ey : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1) = Sum.elim (fun i => evI F (y (Sum.inl i))) fun i => evI F (y (Sum.inr i))`. Apply the tactic sequence `funext i; cases i <;> rfl`. Use `show e (fun x => pureA F f g (Sum.elim x (y ∘ Sum.inr))) (y ∘ Sum.inl) = pureA F (P f) g₁ y`. Rewrite using `[hslice]`. Simplify using `only [map_sum, map_smul, hpure (T f) _ (hφSB _ _) (hφstd _ _), pureA, ey, hP f _ _ (T f) hh, g₁, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [hE, Function.comp_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_partL_pureA : ∀ {F : Type} [Field F] [NumberField F] {κ κ₁ κ' : Type} [Fintype κ] [Fintype κ₁] [Fintype κ']
    (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ), IsLocOp e →
    ∃ P : SInf F (κ ⊕ κ') →L[ℂ] SInf F (κ₁ ⊕ κ'), ∀ g ∈ SB (κ ⊕ κ' → Af F), ∃ g₁ ∈ SB (κ₁ ⊕ κ' → Af F),
      ∀ f : SInf F (κ ⊕ κ'), partL e (pureA F f g) = pureA F (P f) g₁ := by
  intro F _ _ κ κ₁ κ' _ _ _ e he
  classical
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  obtain ⟨ei, ev, hSB, hstd, hpure⟩ := he
  let eq₀ : (κ ⊕ κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) × (κ' → mixedEmbedding.mixedSpace F) :=
    (LinearEquiv.sumArrowLequivProdArrow κ κ' ℝ _).toContinuousLinearEquiv
  let eq₁ : (κ₁ ⊕ κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ₁ → mixedEmbedding.mixedSpace F) × (κ' → mixedEmbedding.mixedSpace F) :=
    (LinearEquiv.sumArrowLequivProdArrow κ₁ κ' ℝ _).toContinuousLinearEquiv
  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.schwartz_operator_parametric_extension (V' := κ' → mixedEmbedding.mixedSpace F) ei
  let P : SInf F (κ ⊕ κ') →L[ℂ] SInf F (κ₁ ⊕ κ') := (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eq₁).comp
    (P₀.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eq₀.symm))
  have hP : ∀ (f : SInf F (κ ⊕ κ')) (y : κ₁ → mixedEmbedding.mixedSpace F) (x' : κ' → mixedEmbedding.mixedSpace F)
      (h : SInf F κ), (∀ x, h x = f (Sum.elim x x')) → P f (Sum.elim y x') = ei h y := by
    intro f y x' h hh
    have h1 : eq₁ (Sum.elim y x') = (y, x') := rfl
    simp only [P, ContinuousLinearMap.comp_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, h1]
    exact hP₀ _ x' h (fun x => (hh x).trans rfl) y
  refine ⟨P, fun g hg => ?_⟩
  have hE : ∀ (z : AF F) (v : Pl F), evFin F v z = evalV F v z.2 := fun _ _ => rfl
  obtain ⟨m, a, b, ha, hb, hab⟩ := GlobalTheory.T.schwartz_bruhat_sum_split_tensor g hg
  choose n φ hφSB hφstd hφ using fun k => GlobalTheory.T.adelic_schwartz_function_factorizable_sum (a k) (ha k)
  let g₁ : (κ₁ ⊕ κ' → Af F) → ℂ := ∑ k, ∑ j : Fin (n k), fun z =>
    (∏ᶠ v, ev v (φ k j v) fun i => evalV F v (z (Sum.inl i))) * b k (z ∘ Sum.inr)
  have hev : ∀ k j, ∀ᶠ v in cofinite, ev v (φ k j v) = stdInd F κ₁ v := fun k j => by
    filter_upwards [hstd, hφstd k j] with v h1 h2
    rw [h2, h1]
  refine ⟨g₁, Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun j _ =>
    mul_blocks_mem_SB (GlobalTheory.AdelicCoordSB.finprod_mem_SB F κ₁ _ (fun v => hSB v _ (hφSB k j v)) (hev k j)) (hb k), ?_⟩
  intro f
  funext y
  obtain ⟨T, hT⟩ := GlobalTheory.ThK.Adapt.exists_slice (κ := κ ⊕ κ') (κ₁ := κ) (Equiv.sumComm κ κ')
    (fun i => evI F (y (Sum.inr i)))
  have hh : ∀ x, T f x = f (Sum.elim x fun i => evI F (y (Sum.inr i))) := fun x => by
    rw [hT, glue_sumComm]
  have hslice : (fun x : κ → AF F => pureA F f g (Sum.elim x (y ∘ Sum.inr))) =
      ∑ k, ∑ j : Fin (n k), b k (fun i => (y (Sum.inr i)).2) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (T f) (φ k j) := by
    funext x
    have e1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (Sum.elim x (y ∘ Sum.inr) i).1) =
        Sum.elim (fun i => evI F (x i)) fun i => evI F (y (Sum.inr i)) := by
      funext i; cases i <;> rfl
    have e2 : (fun i => (Sum.elim x (y ∘ Sum.inr) i).2) = Sum.elim (fun i => (x i).2) fun i => (y (Sum.inr i)).2 := by
      funext i; cases i <;> rfl
    simp only [pureA, e1, e2, hab, hφ, ← hh, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hE]
    ring
  have ey : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1) =
      Sum.elim (fun i => evI F (y (Sum.inl i))) fun i => evI F (y (Sum.inr i)) := by
    funext i; cases i <;> rfl
  show e (fun x => pureA F f g (Sum.elim x (y ∘ Sum.inr))) (y ∘ Sum.inl) = pureA F (P f) g₁ y
  rw [hslice]
  simp only [map_sum, map_smul, hpure (T f) _ (hφSB _ _) (hφstd _ _), pureA, ey,
    hP f _ _ (T f) hh, g₁, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [hE, Function.comp_def]
  ring
end GlobalTheory.DblEval.PartLStr

end
