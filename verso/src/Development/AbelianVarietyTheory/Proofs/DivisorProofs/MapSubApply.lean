import Mathlib

namespace GlobalTheory.LinearMapDifferenceFormula

open AdicCompletion

/- English proof (translation)
Proceed by induction on `y using AdicCompletion.induction_on with`. Consider the case `h a`. Use extensionality with `n`. Simplify using the standard rewrite rules.
-/
theorem map_sub_apply {A : Type} [CommRing A] (J : Ideal A) {M P : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup P] [Module A P] (h k : M →ₗ[A] P) (y : AdicCompletion J M) :
    AdicCompletion.map J (h - k) y = AdicCompletion.map J h y - AdicCompletion.map J k y := by
  induction y using AdicCompletion.induction_on with
  | h a =>
    ext n
    simp

/- English proof (translation)
Introduce `A _ _ J N M _ _ _ _ _ f Γ _ g hf hfix`. Use `haveI : Fintype Γ := Fintype.ofFinite Γ`. Use `⟨AdicCompletion.map_injective J hf, ?_⟩` and prove the remaining obligations. Set `φ : M →ₗ[A] (Γ → M)` to `LinearMap.pi (fun σ => g σ - LinearMap.id)`. Set `ψ : M →ₗ[A] LinearMap.range φ` to `φ.rangeRestrict`.

Establish `hψs : Function.Surjective ψ` using `LinearMap.surjective_rangeRestrict φ`. Establish `hφ0 : ∀ x, φ x = 0 ↔ ∀ σ, g σ x = x`. Introduce `x`. Simplify using `only [φ, funext_iff, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, Pi.zero_apply, sub_eq_zero]`. Establish `hex : Function.Exact f ψ`.

Introduce `x`. Establish `: ψ x = 0 ↔ φ x = 0`. Simplify using `[ψ, Subtype.ext_iff]`. Rewrite using `[this, hφ0, ← hfix]`. Both sides reduce to the same expression.

Establish `hE` using `AdicCompletion.map_exact (I := J) hf hex hψs`. Establish `hinj : Function.Injective (AdicCompletion.map J (LinearMap.range φ).subtype)` using `AdicCompletion.map_injective J (Submodule.injective_subtype _)`. Establish `hcomp : (LinearMap.range φ).subtype ∘ₗ ψ = φ`. Use extensionality with `x`. Simplify using `[ψ]`.

Introduce `y`. Rewrite using `[LinearMap.mem_range, ← Set.mem_range, ← hE y]`. Establish `h1 : AdicCompletion.map J ψ y = 0 ↔ AdicCompletion.map J φ y = 0`. Establish `e : AdicCompletion.map J φ y = AdicCompletion.map J (LinearMap.range φ).subtype (AdicCompletion.map J ψ y)`. Rewrite using `[AdicCompletion.map_comp_apply, hcomp]`.

Rewrite using `[e]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h, _root_.map_zero]`. Introduce `h; exact hinj (by rw [h, _root_.map_zero])`.

Rewrite using `[h1]`. Establish `hpi : AdicCompletion.map J φ y = 0 ↔ ∀ σ, AdicCompletion.map J (LinearMap.proj σ) (AdicCompletion.map J φ y) = 0`. Prove the components needed by the constructor for the conclusion. Introduce `h σ`. Rewrite using `[h, _root_.map_zero]`.

Introduce `h`. Apply `(AdicCompletion.piEquivOfFintype J (fun _ : Γ => M)).injective` to reduce the goal to its premises. Rewrite using `[_root_.map_zero, AdicCompletion.piEquivOfFintype_apply]`. Use function extensionality and compare the values at `σ`. Conclude with `h σ`.

Rewrite using `[hpi]`. Use `forall_congr' fun σ => ?_` and prove the remaining obligations. Rewrite using `[AdicCompletion.map_comp_apply]`. Establish `: (LinearMap.proj σ : (Γ → M) →ₗ[A] M) ∘ₗ φ = g σ - LinearMap.id`. Use extensionality with `x`.

Simplify using `[φ]`. Rewrite using `[this, map_sub_apply, AdicCompletion.map_id, LinearMap.id_apply, sub_eq_zero]`.
-/
theorem main : ∀ (A : Type) [inst : CommRing A] [IsNoetherianRing A] (J : Ideal A) (N M : Type) [inst_2 : AddCommGroup N] [inst_3 : Module A N] [inst_4 : AddCommGroup M] [inst_5 : Module A M] [Module.Finite A M] (f : N →ₗ[A] M) (Γ : Type) [Finite Γ] (g : Γ → M →ₗ[A] M), Function.Injective (⇑f : N → M) → (∀ (x : M), x ∈ LinearMap.range f ↔ ∀ (σ : Γ), (g σ : M → M) x = x) → Function.Injective (⇑(AdicCompletion.map J f) : AdicCompletion J N → AdicCompletion J M) ∧ ∀ (y : AdicCompletion J M), y ∈ LinearMap.range (AdicCompletion.map J f) ↔ ∀ (σ : Γ), (AdicCompletion.map J (g σ) : AdicCompletion J M → AdicCompletion J M) y = y := by
  intro A _ _ J N M _ _ _ _ _ f Γ _ g hf hfix
  classical
  haveI : Fintype Γ := Fintype.ofFinite Γ
  refine ⟨AdicCompletion.map_injective J hf, ?_⟩

  let φ : M →ₗ[A] (Γ → M) := LinearMap.pi (fun σ => g σ - LinearMap.id)
  let ψ : M →ₗ[A] LinearMap.range φ := φ.rangeRestrict
  have hψs : Function.Surjective ψ := LinearMap.surjective_rangeRestrict φ
  have hφ0 : ∀ x, φ x = 0 ↔ ∀ σ, g σ x = x := by
    intro x
    simp only [φ, funext_iff, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply,
      Pi.zero_apply, sub_eq_zero]
  have hex : Function.Exact f ψ := by
    intro x
    have : ψ x = 0 ↔ φ x = 0 := by
      simp [ψ, Subtype.ext_iff]
    rw [this, hφ0, ← hfix]
    rfl
  have hE := AdicCompletion.map_exact (I := J) hf hex hψs
  have hinj : Function.Injective (AdicCompletion.map J (LinearMap.range φ).subtype) :=
    AdicCompletion.map_injective J (Submodule.injective_subtype _)
  have hcomp : (LinearMap.range φ).subtype ∘ₗ ψ = φ := by
    ext x; simp [ψ]
  intro y
  rw [LinearMap.mem_range, ← Set.mem_range, ← hE y]
  have h1 : AdicCompletion.map J ψ y = 0 ↔ AdicCompletion.map J φ y = 0 := by
    have e : AdicCompletion.map J φ y = AdicCompletion.map J (LinearMap.range φ).subtype (AdicCompletion.map J ψ y) := by
      rw [AdicCompletion.map_comp_apply, hcomp]
    rw [e]
    constructor
    · intro h; rw [h, _root_.map_zero]
    · intro h; exact hinj (by rw [h, _root_.map_zero])
  rw [h1]
  have hpi : AdicCompletion.map J φ y = 0 ↔ ∀ σ, AdicCompletion.map J (LinearMap.proj σ) (AdicCompletion.map J φ y) = 0 := by
    constructor
    · intro h σ; rw [h, _root_.map_zero]
    · intro h
      apply (AdicCompletion.piEquivOfFintype J (fun _ : Γ => M)).injective
      rw [_root_.map_zero, AdicCompletion.piEquivOfFintype_apply]
      funext σ
      exact h σ
  rw [hpi]
  refine forall_congr' fun σ => ?_
  rw [AdicCompletion.map_comp_apply]
  have : (LinearMap.proj σ : (Γ → M) →ₗ[A] M) ∘ₗ φ = g σ - LinearMap.id := by
    ext x; simp [φ]
  rw [this, map_sub_apply, AdicCompletion.map_id, LinearMap.id_apply, sub_eq_zero]

end GlobalTheory.LinearMapDifferenceFormula
