import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChangeBij

open GlobalTheory.SympChange

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

/- English proof (translation)
Establish `h1 : (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Simplify using `only [spAct, h1, Matrix.one_mulVec]`. Both sides reduce to the same expression.
-/
theorem spAct_one' {R : Type} [CommRing R] [Algebra F R] (w : (κ → R) × (κ → R)) :
    spAct (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) w = w := by
  have h1 : (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  simp only [spAct, h1, Matrix.one_mulVec]
  rfl

/- English proof (translation)
Establish `h : Sum.elim (spAct G' w).1 (spAct G' w).2 = G'.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2`. Apply the tactic sequence `funext i; cases i <;> rfl`. Use `conv_rhs => rw [spAct, h]`. Simplify using `only [spAct, Matrix.map_mul (f := algebraMap F R), Matrix.mulVec_mulVec]`.
-/
theorem spAct_mul' {R : Type} [CommRing R] [Algebra F R] (G G' : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (w : (κ → R) × (κ → R)) :
    spAct (G * G') w = spAct G (spAct G' w) := by
  have h : Sum.elim (spAct G' w).1 (spAct G' w).2 = G'.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2 := by
    funext i; cases i <;> rfl
  conv_rhs => rw [spAct, h]
  simp only [spAct, Matrix.map_mul (f := algebraMap F R), Matrix.mulVec_mulVec]

variable [NumberField F]

def HasOpB (ψ : AddChar (AF F) ℂ) (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop :=
  ∃ (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    Function.Surjective ei ∧ (∀ Φ ∈ schA F κ, e Φ ∈ schA F κ) ∧
    (∀ w, ∀ Φ ∈ schA F κ, e (schr ψ w Φ) = schr ψ (spAct G w) (e Φ)) ∧
    (∀ v, (SB _).map (ev v) = SB _) ∧ (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = 0 → φ = 0) ∧
    (∀ v w, ∀ φ ∈ SB (κ → Fv F v),
      ev v (schr (GlobalTheory.LatVac.psiAt ψ v) w φ) = schr (GlobalTheory.LatVac.psiAt ψ v) (spAct G w) (ev v φ)) ∧
    (∀ᶠ v in cofinite, ev v (indO v) = indO v) ∧
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = indO v) →
      e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)) ∧
    Set.BijOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ))

/- English proof (translation)
Use `⟨LinearMap.id, ContinuousLinearMap.id ℂ _, fun _ => LinearMap.id, Function.surjective_id, fun Φ h => h, fun w Φ _ => by simp [spAct_one'], fun v => Submodule.map_id _, fun v φ _ h => h, fun v w φ _ => by simp [spAct_one'], Filter.Eventually.of_forall fun v => rfl, fun f φ _ _ => …` and prove the remaining obligations. Simplify using `using Set.bijOn_id (schA F κ : Set ((κ → AF F) → ℂ))`.
-/
theorem hasOpB_one (ψ : AddChar (AF F) ℂ) : HasOpB (κ := κ) ψ 1 := by
  refine ⟨LinearMap.id, ContinuousLinearMap.id ℂ _, fun _ => LinearMap.id, Function.surjective_id, fun Φ h => h,
    fun w Φ _ => by simp [spAct_one'], fun v => Submodule.map_id _, fun v φ _ h => h, fun v w φ _ => by simp [spAct_one'],
    Filter.Eventually.of_forall fun v => rfl, fun f φ _ _ => rfl, ?_⟩
  simpa using Set.bijOn_id (schA F κ : Set ((κ → AF F) → ℂ))

/- English proof (translation)
Take `⟨e, ei, ev, hs, hm, hh, hSB, hi, hl, hind, hp, hb⟩` from `hG`. Take `⟨e', ei', ev', hs', hm', hh', hSB', hi', hl', hind', hp', hb'⟩` from `hG'`. Establish `hmem : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev' v φ ∈ SB (κ → Fv F v)` using `fun v φ hφ => by`. Rewrite using `[← hSB' v]`. Conclude with `Submodule.mem_map_of_mem hφ`.

Use `⟨e ∘ₗ e', ei.comp ei', fun v => ev v ∘ₗ ev' v, hs.comp hs', fun Φ h => hm _ (hm' _ h), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `w Φ hΦ`. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[hh' w Φ hΦ, hh _ _ (hm' _ hΦ), spAct_mul']`. Introduce `v`.

Rewrite using `[Submodule.map_comp, hSB', hSB]`. Introduce `v φ hφ h0`. Conclude with `hi' v φ hφ (hi v _ (hmem v φ hφ) h0)`. Introduce `v w φ hφ`. Simplify using `only [LinearMap.comp_apply]`.

Rewrite using `[hl' v w φ hφ, hl v _ _ (hmem v φ hφ), spAct_mul']`. Use `filter_upwards [hind, hind'] with v h1 h2`. Simplify using `only [LinearMap.comp_apply, h2, h1]`. Introduce `f φ hφ hφv`. Simplify using `only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]`.

Rewrite using `[hp' f φ hφ hφv, hp _ _ (fun v => hmem v _ (hφ v))]`. Use `filter_upwards [hφv, hind'] with v h1 h2`. Rewrite using `[h1, h2]`. Rewrite using `[LinearMap.coe_comp]`. Conclude with `hb.comp hb'`.
-/
theorem hasOpB_mul {ψ : AddChar (AF F) ℂ} {G G' : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hG : HasOpB ψ G) (hG' : HasOpB ψ G') :
    HasOpB ψ (G * G') := by
  obtain ⟨e, ei, ev, hs, hm, hh, hSB, hi, hl, hind, hp, hb⟩ := hG
  obtain ⟨e', ei', ev', hs', hm', hh', hSB', hi', hl', hind', hp', hb'⟩ := hG'
  have hmem : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev' v φ ∈ SB (κ → Fv F v) := fun v φ hφ => by
    rw [← hSB' v]; exact Submodule.mem_map_of_mem hφ
  refine ⟨e ∘ₗ e', ei.comp ei', fun v => ev v ∘ₗ ev' v, hs.comp hs', fun Φ h => hm _ (hm' _ h), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w Φ hΦ
    simp only [LinearMap.comp_apply]
    rw [hh' w Φ hΦ, hh _ _ (hm' _ hΦ), spAct_mul']
  · intro v
    rw [Submodule.map_comp, hSB', hSB]
  · intro v φ hφ h0
    exact hi' v φ hφ (hi v _ (hmem v φ hφ) h0)
  · intro v w φ hφ
    simp only [LinearMap.comp_apply]
    rw [hl' v w φ hφ, hl v _ _ (hmem v φ hφ), spAct_mul']
  · filter_upwards [hind, hind'] with v h1 h2
    simp only [LinearMap.comp_apply, h2, h1]
  · intro f φ hφ hφv
    simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [hp' f φ hφ hφv, hp _ _ (fun v => hmem v _ (hφ v))]
    filter_upwards [hφv, hind'] with v h1 h2
    rw [h1, h2]
  · rw [LinearMap.coe_comp]
    exact hb.comp hb'

/- English proof (translation)
Introduce `G hG` and use `Submonoid.closure_induction (fun x hx => hgen x hx) (hasOpB_one ψ) (fun _ _ _ _ hx hy => hasOpB_mul hx hy) hG`.
-/
theorem hasOpB_of_mem_closure {ψ : AddChar (AF F) ℂ} (hgen : ∀ G ∈ gens (F := F) (κ := κ), HasOpB ψ G) :
    ∀ G ∈ Submonoid.closure (gens (F := F) (κ := κ)), HasOpB ψ G := fun G hG =>
  Submonoid.closure_induction (fun x hx => hgen x hx) (hasOpB_one ψ) (fun _ _ _ _ hx hy => hasOpB_mul hx hy) hG

/- English proof (translation)
The claim follows from `Set.InvOn.bijOn (f' := e') ⟨fun Φ h => h1 Φ h, fun Φ h => h2 Φ h⟩ (fun Φ h => hm Φ h) (fun Φ h => hm' Φ h)`.
-/
theorem bijOn_of_inv (e e' : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) (hm : ∀ Φ ∈ schA F κ, e Φ ∈ schA F κ)
    (hm' : ∀ Φ ∈ schA F κ, e' Φ ∈ schA F κ) (h1 : ∀ Φ ∈ schA F κ, e' (e Φ) = Φ) (h2 : ∀ Φ ∈ schA F κ, e (e' Φ) = Φ) :
    Set.BijOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) :=
  Set.InvOn.bijOn (f' := e') ⟨fun Φ h => h1 Φ h, fun Φ h => h2 Φ h⟩ (fun Φ h => hm Φ h) (fun Φ h => hm' Φ h)

end GlobalTheory.SympChangeBij
