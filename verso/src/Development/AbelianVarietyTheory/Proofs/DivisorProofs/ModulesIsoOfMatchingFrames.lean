import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSecOn

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB GlobalTheory.FlagZ GlobalTheory
open GlobalTheory.LB (homOfLinear homOfLinear_app le_iSup_inf)
open GlobalTheory.Twist (resM resM_resM app_resM sec_ext_of_cover exists_sec_of_cover isIso_of_cover)

namespace GlobalTheory.VB

/- English proof (translation)
Take `⟨a, rfl⟩` from `(h₁ V hV).2 s`. Simplify using `only [Fintype.linearCombination_apply, map_sum, map_smul, IsFrame.equiv_resM_frame, Scheme.Modules.Hom.app_smul, app_resM, h]`.
-/
theorem IsFrame.app_equiv_of_app_eq {X : Scheme.{0}} {F₁ F₂ E : X.Modules} (m₁ : F₁ ⟶ E)
    (m₂ : F₂ ⟶ E) {ι : Type} [Fintype ι] {U V : X.Opens} {s₁ : ι → Γ(F₁, U)} {s₂ : ι → Γ(F₂, U)}
    (h₁ : IsFrame s₁) (h₂ : IsFrame s₂) (h : ∀ j, m₁.app U (s₁ j) = m₂.app U (s₂ j))
    (hV : V ≤ U) (s : Γ(F₁, V)) : m₂.app V (h₁.equiv h₂ hV s) = m₁.app V s := by
  obtain ⟨a, rfl⟩ := (h₁ V hV).2 s
  simp only [Fintype.linearCombination_apply, map_sum, map_smul, IsFrame.equiv_resM_frame,
    Scheme.Modules.Hom.app_smul, app_resM, h]

/- English proof (translation)
Introduce `X F₁ F₂ E m₁ m₂ _ r H`. Use `choose U s₁ s₂ hx h₁ h₂ h using H`. Establish `hU : ⨆ x, U x = ⊤` using `top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩`. Establish `inj (V : X.Opens) : Function.Injective (m₂.app V)` using `QCoh.injective_app_of_mono m₂ V`. Establish `loc (x : X) {V : X.Opens} (hV : V ≤ U x) (s : Γ(F₁, V)) : m₂.app V ((h₁ x).equiv (h₂ x) hV s) = m₁.app V s` using `(h₁ x).app_equiv_of_app_eq m₁ m₂ (h₂ x) (h x) hV s`.

Establish `ex (V : X.Opens) (s : Γ(F₁, V)) : ∃ t : Γ(F₂, V), m₂.app V t = m₁.app V s`. Take `⟨t, ht⟩` from `exists_sec_of_cover (F := F₂) (fun x => V ⊓ U x) (fun _ => inf_le_left) (le_iSup_inf hU V) (fun x => (h₁ x).equiv (h₂ x) inf_le_right (resM F₁ inf_le_left s)) fun x y => inj _ (by`. Rewrite using `[app_resM, app_resM, loc, loc, app_resM, app_resM, resM_resM, resM_resM])`. Use `⟨t, sec_ext_of_cover (fun x => V ⊓ U x) (fun _ => inf_le_left) (le_iSup_inf hU V) fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← app_resM, ht, loc, app_resM]`.

Use `choose φ hφ using ex`. Set `ψ (V : X.Opens) : Γ(F₁, V) →ₗ[Γ(X, V)] Γ(F₂, V)` to `{ toFun := φ V map_add' := fun s t => inj V (by rw [map_add, hφ, hφ, hφ, map_add]) map_smul' := fun a s => inj V (by`. Rewrite using `[RingHom.id_apply, Scheme.Modules.Hom.app_smul, hφ, hφ, Scheme.Modules.Hom.app_smul]) }`. Set `e : F₁ ⟶ F₂` to `homOfLinear ψ fun {V W} hW s => inj W (by`. Express the relevant statement in the definitionally equal form `m₂.app W (φ W (resM F₁ hW s)) = m₂.app W (resM F₂ hW (φ V s))`.

Rewrite using `[hφ, app_resM, app_resM, hφ])`. Establish `he (V : X.Opens) (s : Γ(F₁, V)) : e.app V s = φ V s` using `rfl`. Use `haveI : IsIso e := isIso_of_cover e hU fun x W hW => by`. Establish `: (e.app W : Γ(F₁, W) → Γ(F₂, W)) = (h₁ x).equiv (h₂ x) hW`. Use function extensionality and compare the values at `fun s => inj W (by rw [he, hφ, loc])`.

Rewrite using `[this]`. Conclude with `((h₁ x).equiv (h₂ x) hW).bijective`. Use `⟨asIso e, ?_⟩` and prove the remaining obligations. Use extensionality with `V s`. Conclude with `hφ V s`.
-/
theorem exists_iso_of_frames_app_eq :
    ∀ {X : Scheme.{0}} {F₁ F₂ E : X.Modules} (m₁ : F₁ ⟶ E) (m₂ : F₂ ⟶ E) [Mono m₂] (r : ℕ),
    (∀ x : X, ∃ (U : X.Opens) (s₁ : Fin r → Γ(F₁, U)) (s₂ : Fin r → Γ(F₂, U)), x ∈ U ∧ IsFrame s₁ ∧ IsFrame s₂ ∧
      ∀ j, m₁.app U (s₁ j) = m₂.app U (s₂ j)) →
    ∃ e : F₁ ≅ F₂, e.hom ≫ m₂ = m₁ := by
  intro X F₁ F₂ E m₁ m₂ _ r H
  choose U s₁ s₂ hx h₁ h₂ h using H
  have hU : ⨆ x, U x = ⊤ := top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩
  have inj (V : X.Opens) : Function.Injective (m₂.app V) := QCoh.injective_app_of_mono m₂ V
  have loc (x : X) {V : X.Opens} (hV : V ≤ U x) (s : Γ(F₁, V)) :
      m₂.app V ((h₁ x).equiv (h₂ x) hV s) = m₁.app V s :=
    (h₁ x).app_equiv_of_app_eq m₁ m₂ (h₂ x) (h x) hV s
  have ex (V : X.Opens) (s : Γ(F₁, V)) : ∃ t : Γ(F₂, V), m₂.app V t = m₁.app V s := by
    obtain ⟨t, ht⟩ := exists_sec_of_cover (F := F₂) (fun x => V ⊓ U x) (fun _ => inf_le_left)
      (le_iSup_inf hU V)
      (fun x => (h₁ x).equiv (h₂ x) inf_le_right (resM F₁ inf_le_left s)) fun x y => inj _ (by
        rw [app_resM, app_resM, loc, loc, app_resM, app_resM, resM_resM, resM_resM])
    refine ⟨t, sec_ext_of_cover (fun x => V ⊓ U x) (fun _ => inf_le_left) (le_iSup_inf hU V)
      fun x => ?_⟩
    rw [← app_resM, ht, loc, app_resM]
  choose φ hφ using ex
  let ψ (V : X.Opens) : Γ(F₁, V) →ₗ[Γ(X, V)] Γ(F₂, V) :=
    { toFun := φ V
      map_add' := fun s t => inj V (by rw [map_add, hφ, hφ, hφ, map_add])
      map_smul' := fun a s => inj V (by
        rw [RingHom.id_apply, Scheme.Modules.Hom.app_smul, hφ, hφ, Scheme.Modules.Hom.app_smul]) }
  let e : F₁ ⟶ F₂ := homOfLinear ψ fun {V W} hW s => inj W (by
    change m₂.app W (φ W (resM F₁ hW s)) = m₂.app W (resM F₂ hW (φ V s))
    rw [hφ, app_resM, app_resM, hφ])
  have he (V : X.Opens) (s : Γ(F₁, V)) : e.app V s = φ V s := rfl
  haveI : IsIso e := isIso_of_cover e hU fun x W hW => by
    have : (e.app W : Γ(F₁, W) → Γ(F₂, W)) = (h₁ x).equiv (h₂ x) hW :=
      funext fun s => inj W (by rw [he, hφ, loc])
    rw [this]
    exact ((h₁ x).equiv (h₂ x) hW).bijective
  refine ⟨asIso e, ?_⟩
  ext V s
  exact hφ V s

end GlobalTheory.VB
