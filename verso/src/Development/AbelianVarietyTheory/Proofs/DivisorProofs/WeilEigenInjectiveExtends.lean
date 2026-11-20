import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.EvInj

/- English proof (translation)
Rewrite using `[finprod_def]`. Use `split_ifs`. Conclude with `Finset.prod_ne_zero_iff.2 fun i _ => h i`. Conclude with `one_ne_zero`.
-/
theorem finprod_ne_zero' {ι : Type} {g : ι → ℂ} (h : ∀ i, g i ≠ 0) : ∏ᶠ i, g i ≠ 0 := by
  classical
  rw [finprod_def]
  split_ifs
  · exact Finset.prod_ne_zero_iff.2 fun i _ => h i
  · exact one_ne_zero

/- English proof (translation)
Establish `hS` using `Filter.eventually_cofinite.1 hstd`. Use `set S := hS.toFinset`. Establish `hpt : ∀ v, ∃ y : κ → Fv F v, φ v y ≠ 0` using `fun v => by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Conclude with `hne v (funext hc)`. Use `choose pt hpt using hpt`. Set `yf : κ → Af F` to `fun i => ∑ v ∈ S, GlobalTheory.AdelicU.singleFin v (pt v i)`. Establish `hyf : ∀ w i, evalV F w (yf i) = if w ∈ S then pt w i else 0`. Introduce `w i`.

Simplify using `only [yf, map_sum]`. Use `split_ifs with hw`. Rewrite using `[Finset.sum_eq_single w]`. Conclude with `GlobalTheory.AdelicU.evalV_singleFin_self w _`. Introduce `b _ hb`.

Conclude with `GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hb) _`. Introduce `h`. Conclude with `absurd hw h`. Use `Finset.sum_eq_zero fun b hb => ?_` and prove the remaining obligations. Conclude with `GlobalTheory.AdelicU.evalV_singleFin_ne (by rintro rfl; exact hw hb) _`.

Use extensionality with `a`. Set `x : κ → AF F` to `fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i), yf i)`. Establish `hI : (fun i => evI F (x i)) = a`. Use function extensionality and compare the values at `i`. Use `show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i)) = a i`.

Conclude with `RingEquiv.apply_symm_apply _ _`. Establish `hF : ∀ w, (fun i => GlobalTheory.AdelicU.evFin F w (x i)) = fun i => if w ∈ S then pt w i else 0`. Introduce `w`. Use function extensionality and compare the values at `i`. Conclude with `hyf w i`.

Establish `hc : ∏ᶠ v, φ v (fun i => GlobalTheory.AdelicU.evFin F v (x i)) ≠ 0`. Use `finprod_ne_zero' fun v => ?_` and prove the remaining obligations. Rewrite using `[hF v]`. Distinguish the cases in `hv : v ∈ S`. Simplify using `only [hv, if_true]`.

Conclude with `hpt v`. Simplify using `only [hv, if_false]`. Establish `: φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1`. Assume the negation of the conclusion as `hc'`. Conclude with `hv (hS.mem_toFinset.2 hc')`.

Rewrite using `[this, Set.indicator_of_mem (by intro i; exact zero_mem _)]`. Conclude with `one_ne_zero`. Establish `e` using `congrFun h0 x`. Express the relevant statement in the definitionally equal form `f (fun i => evI F (x i)) * ∏ᶠ v, φ v (fun i => GlobalTheory.AdelicU.evFin F v (x i)) = 0 at e`. Rewrite `e` using `[hI]`.

Simplify using `using (mul_eq_zero.1 e).resolve_right hc`.
-/
theorem eq_zero_of_pure_eq_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (hne : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (h0 : pure f φ = 0) : f = 0 := by
  classical
  have hS := Filter.eventually_cofinite.1 hstd
  set S := hS.toFinset
  have hpt : ∀ v, ∃ y : κ → Fv F v, φ v y ≠ 0 := fun v => by
    by_contra hc
    push_neg at hc
    exact hne v (funext hc)
  choose pt hpt using hpt
  let yf : κ → Af F := fun i => ∑ v ∈ S, GlobalTheory.AdelicU.singleFin v (pt v i)
  have hyf : ∀ w i, evalV F w (yf i) = if w ∈ S then pt w i else 0 := by
    intro w i
    simp only [yf, map_sum]
    split_ifs with hw
    · rw [Finset.sum_eq_single w]
      · exact GlobalTheory.AdelicU.evalV_singleFin_self w _
      · intro b _ hb; exact GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hb) _
      · intro h; exact absurd hw h
    · refine Finset.sum_eq_zero fun b hb => ?_
      exact GlobalTheory.AdelicU.evalV_singleFin_ne (by rintro rfl; exact hw hb) _
  ext a
  let x : κ → AF F := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i), yf i)
  have hI : (fun i => evI F (x i)) = a := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i)) = a i
    exact RingEquiv.apply_symm_apply _ _
  have hF : ∀ w, (fun i => GlobalTheory.AdelicU.evFin F w (x i)) = fun i => if w ∈ S then pt w i else 0 := by
    intro w; funext i; exact hyf w i
  have hc : ∏ᶠ v, φ v (fun i => GlobalTheory.AdelicU.evFin F v (x i)) ≠ 0 := by
    refine finprod_ne_zero' fun v => ?_
    rw [hF v]
    by_cases hv : v ∈ S
    · simp only [hv, if_true]; exact hpt v
    · simp only [hv, if_false]
      have : φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
        by_contra hc'; exact hv (hS.mem_toFinset.2 hc')
      rw [this, Set.indicator_of_mem (by intro i; exact zero_mem _)]
      exact one_ne_zero
  have e := congrFun h0 x
  change f (fun i => evI F (x i)) * ∏ᶠ v, φ v (fun i => GlobalTheory.AdelicU.evFin F v (x i)) = 0 at e
  rw [hI] at e
  simpa using (mul_eq_zero.1 e).resolve_right hc

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M M₁ hM e hinj ei ev _ hev`. Use `(injective_iff_map_eq_zero ei).2 fun f hf => ?_` and prove the remaining obligations. Establish `hSB : ∀ v, M.vac v ∈ SB (Fin n × Fin d → Fv F v)` using `fun v => (hM.vac v).1`. Establish `hmem : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac ∈ schA F (Fin n × Fin d)` using `GlobalTheory.TensUniq.pure_mem_schA f M.vac hSB hM.std`. Establish `h1 : e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) = e 0`.

Rewrite using `[hev f M.vac hSB (Filter.Eventually.of_forall fun _ => rfl), hf, map_zero]`. Use function extensionality and compare the values at `x`. Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]`. Establish `h2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac = 0` using `hinj hmem (schA F (Fin n × Fin d)).zero_mem h1`. Conclude with `eq_zero_of_pure_eq_zero f M.vac (fun v => (hM.vac v).2.1) hM.std h2`.
-/
theorem ei_injective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W), M.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, Set.InjOn e (schA F (Fin n × Fin d) : Set _) → ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)) (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), (∀ v, ev v (M.vac v) = M₁.vac v) → (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)) → Function.Injective ei := by
  intro F E _ _ _ _ _ σ B n d X W M M₁ hM e hinj ei ev _ hev
  refine (injective_iff_map_eq_zero ei).2 fun f hf => ?_
  have hSB : ∀ v, M.vac v ∈ SB (Fin n × Fin d → Fv F v) := fun v => (hM.vac v).1
  have hmem : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac ∈ schA F (Fin n × Fin d) :=
    GlobalTheory.TensUniq.pure_mem_schA f M.vac hSB hM.std
  have h1 : e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) = e 0 := by
    rw [hev f M.vac hSB (Filter.Eventually.of_forall fun _ => rfl), hf, map_zero]
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  have h2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac = 0 :=
    hinj hmem (schA F (Fin n × Fin d)).zero_mem h1
  exact eq_zero_of_pure_eq_zero f M.vac (fun v => (hM.vac v).2.1) hM.std h2

end GlobalTheory.EvInj
