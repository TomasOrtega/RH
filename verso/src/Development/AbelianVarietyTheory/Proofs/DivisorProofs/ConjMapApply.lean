import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DoublingEv

def conjMap {X Y : Type} (T : (X → ℂ) →ₗ[ℂ] (Y → ℂ)) : (X → ℂ) →ₗ[ℂ] (Y → ℂ) where
  toFun φ := star (T (star φ))
  map_add' φ φ' := by rw [star_add, map_add, star_add]
  map_smul' c φ := by rw [star_smul, map_smul, star_smul, star_star]; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjMap_apply {X Y : Type} (T : (X → ℂ) →ₗ[ℂ] (Y → ℂ)) (φ : X → ℂ) :
    conjMap T φ = star (T (star φ)) := rfl

variable {R : Type}

def partR {κ κ' κ₁' : Type} (T : ((κ' → R) → ℂ) →ₗ[ℂ] ((κ₁' → R) → ℂ)) :
    ((κ ⊕ κ' → R) → ℂ) →ₗ[ℂ] ((κ ⊕ κ₁' → R) → ℂ) where
  toFun Φ s := T (fun x₂ => Φ (Sum.elim (s ∘ Sum.inl) x₂)) (s ∘ Sum.inr)
  map_add' Φ Ψ := by funext s; exact congrFun (map_add T (fun x₂ => Φ (Sum.elim (s ∘ Sum.inl) x₂)) (fun x₂ => Ψ (Sum.elim (s ∘ Sum.inl) x₂))) _
  map_smul' c Φ := by funext s; exact congrFun (map_smul T c (fun x₂ => Φ (Sum.elim (s ∘ Sum.inl) x₂))) _

def partL {κ κ₁ κ' : Type} (T : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) :
    ((κ ⊕ κ' → R) → ℂ) →ₗ[ℂ] ((κ₁ ⊕ κ' → R) → ℂ) where
  toFun Φ s := T (fun x₁ => Φ (Sum.elim x₁ (s ∘ Sum.inr))) (s ∘ Sum.inl)
  map_add' Φ Ψ := by funext s; exact congrFun (map_add T (fun x₁ => Φ (Sum.elim x₁ (s ∘ Sum.inr))) (fun x₁ => Ψ (Sum.elim x₁ (s ∘ Sum.inr)))) _
  map_smul' c Φ := by funext s; exact congrFun (map_smul T c (fun x₁ => Φ (Sum.elim x₁ (s ∘ Sum.inr)))) _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem partR_apply {κ κ' κ₁' : Type} (T : ((κ' → R) → ℂ) →ₗ[ℂ] ((κ₁' → R) → ℂ)) (Φ : (κ ⊕ κ' → R) → ℂ)
    (s : κ ⊕ κ₁' → R) : partR (κ := κ) T Φ s = T (fun x₂ => Φ (Sum.elim (s ∘ Sum.inl) x₂)) (s ∘ Sum.inr) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem partL_apply {κ κ₁ κ' : Type} (T : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) (Φ : (κ ⊕ κ' → R) → ℂ)
    (s : κ₁ ⊕ κ' → R) : partL (κ' := κ') T Φ s = T (fun x₁ => Φ (Sum.elim x₁ (s ∘ Sum.inr))) (s ∘ Sum.inl) := rfl

def evDbl {κ κ₁ : Type} (e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) :
    ((κ ⊕ κ → R) → ℂ) →ₗ[ℂ] ((κ₁ ⊕ κ₁ → R) → ℂ) :=
  partL e ∘ₗ partR (conjMap e)

/- English proof (translation)
Simplify using `only [evDbl, LinearMap.comp_apply, partL_apply, partR_apply, Sum.elim_comp_inl, Sum.elim_comp_inr]`.
-/
theorem evDbl_apply {κ κ₁ : Type} (e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) (Φ : (κ ⊕ κ → R) → ℂ)
    (s : κ₁ ⊕ κ₁ → R) : evDbl e Φ s =
      e (fun x₁ => conjMap e (fun x₂ => Φ (Sum.elim x₁ x₂)) (s ∘ Sum.inr)) (s ∘ Sum.inl) := by
  simp only [evDbl, LinearMap.comp_apply, partL_apply, partR_apply, Sum.elim_comp_inl, Sum.elim_comp_inr]

/- English proof (translation)
Use function extensionality and compare the values at `s`. Rewrite using `[evDbl_apply]`. Establish `h1 : ∀ x₁ : κ → R, (fun x₂ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) = φ₁ x₁ • φ₂` using `fun x₁ => by`. Use function extensionality and compare the values at `x₂`. Simplify using `[boxFun]`.

Establish `h2 : (fun x₁ => conjMap e (fun x₂ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) (s ∘ Sum.inr)) = conjMap e φ₂ (s ∘ Sum.inr) • φ₁`. Use function extensionality and compare the values at `x₁`. Rewrite using `[h1, map_smul]`. Simplify using `[mul_comm]`. Rewrite using `[h2, map_smul]`.

Simplify using `[boxFun, mul_comm]`.
-/
theorem evDbl_boxFun {κ κ₁ : Type} (e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) (φ₁ φ₂ : (κ → R) → ℂ) :
    evDbl e (boxFun φ₁ φ₂) = boxFun (e φ₁) (conjMap e φ₂) := by
  funext s
  rw [evDbl_apply]
  have h1 : ∀ x₁ : κ → R, (fun x₂ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) = φ₁ x₁ • φ₂ := fun x₁ => by
    funext x₂; simp [boxFun]
  have h2 : (fun x₁ => conjMap e (fun x₂ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) (s ∘ Sum.inr)) =
      conjMap e φ₂ (s ∘ Sum.inr) • φ₁ := by
    funext x₁; rw [h1, map_smul]; simp [mul_comm]
  rw [h2, map_smul]
  simp [boxFun, mul_comm]

section Tame

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

def IsTame {κ κ' : Type} [Fintype κ] [Fintype κ'] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) : Prop :=
  ∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ (ι : Type) (_ : Fintype ι)
    (P : ι → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ' → mixedEmbedding.mixedSpace F) ℂ)
    (g' : ι → (κ' → FiniteAdeleRing (𝓞 F) F) → ℂ), (∀ j, g' j ∈ SB (κ' → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, T (pureA F f g) = ∑ j, pureA F (P j f) (g' j)

variable {F}

/- English proof (translation)
Introduce `g hg` and use `⟨Unit, inferInstance, fun _ => ContinuousLinearMap.id ℂ _, fun _ => g, fun _ => hg, fun f => by simp⟩`.
-/
theorem isTame_id {κ : Type} [Fintype κ] : IsTame F (LinearMap.id : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) :=
  fun g hg => ⟨Unit, inferInstance, fun _ => ContinuousLinearMap.id ℂ _, fun _ => g, fun _ => hg, fun f => by simp⟩

/- English proof (translation)
Introduce `g hg`. Take `⟨ι, _, P, g', hg', hP⟩` from `hT g hg`. Use `choose ι' inst P' g'' hg'' hP' using fun j => hT' (g' j) (hg' j)`. Use `letI : ∀ j, Fintype (ι' j) := inst`. Use `⟨Σ j, ι' j, inferInstance, fun p => (P' p.1 p.2).comp (P p.1), fun p => g'' p.1 p.2, fun p => hg'' p.1 p.2, fun f => ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.comp_apply, hP, map_sum, Fintype.sum_sigma]`. Conclude with `Finset.sum_congr rfl fun j _ => hP' j (P j f)`.
-/
theorem IsTame.comp {κ κ' κ'' : Type} [Fintype κ] [Fintype κ'] [Fintype κ'']
    {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)} {T' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)}
    (hT : IsTame F T) (hT' : IsTame F T') : IsTame F (T' ∘ₗ T) := by
  intro g hg
  obtain ⟨ι, _, P, g', hg', hP⟩ := hT g hg
  choose ι' inst P' g'' hg'' hP' using fun j => hT' (g' j) (hg' j)
  letI : ∀ j, Fintype (ι' j) := inst
  refine ⟨Σ j, ι' j, inferInstance, fun p => (P' p.1 p.2).comp (P p.1), fun p => g'' p.1 p.2,
    fun p => hg'' p.1 p.2, fun f => ?_⟩
  rw [LinearMap.comp_apply, hP, map_sum, Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun j _ => hP' j (P j f)

/- English proof (translation)
Introduce `φ hφ`. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, g, hg, rfl⟩` from `hx`. Take `⟨ι, _, P, g', hg', hP⟩` from `hT g hg`.

Rewrite using `[hP]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨P j f, g' j, hg' j, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem IsTame.mapsTo {κ κ' : Type} [Fintype κ] [Fintype κ'] {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    (hT : IsTame F T) : ∀ φ ∈ schA F κ, T φ ∈ schA F κ' := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    obtain ⟨ι, _, P, g', hg', hP⟩ := hT g hg
    rw [hP]
    exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨P j f, g' j, hg' j, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/- English proof (translation)
Introduce `g hg`. Take `⟨ι, _, P, g', hg', hP⟩` from `hT g hg`. Use `choose L hL using fun j => hl (g' j) (hg' j)`. Use `⟨∑ j, (L j).comp (P j), fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, hP, map_sum, ContinuousLinearMap.sum_apply]`.

Conclude with `Finset.sum_congr rfl fun j _ => hL j (P j f)`.
-/
theorem IsTame.comp_adm {κ κ' : Type} [Fintype κ] [Fintype κ'] {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    (hT : IsTame F T) {l : ((κ' → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm κ') :
    l ∘ₗ T ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨ι, _, P, g', hg', hP⟩ := hT g hg
  choose L hL using fun j => hl (g' j) (hg' j)
  refine ⟨∑ j, (L j).comp (P j), fun f => ?_⟩
  rw [LinearMap.comp_apply, hP, map_sum, ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => hL j (P j f)

end Tame

end GlobalTheory.DoublingEv
