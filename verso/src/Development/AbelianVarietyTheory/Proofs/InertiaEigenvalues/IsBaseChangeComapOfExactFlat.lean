import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory

/- English proof (translation)
Use `set N₀ := N₁.comap (j.restrictScalars A) with hN₀`. Set `ι : N₀ →ₗ[A] N₁` to `(j.restrictScalars A).restrict (fun x hx => hx)`. Set `f : N₁ →ₗ[A] N₂` to `(q.restrictScalars A).restrict hN`. Establish `hιv : ∀ y : N₀, (ι y : D₁) = j y` using `fun _ => rfl`. Establish `hfv : ∀ y : N₁, (f y : D₂) = q y` using `fun _ => rfl`.

Establish `hι : Function.Injective ι`. Introduce `x y hxy`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `hj` to reduce the goal to its premises. Use `congrArg Subtype.val hxy` as an intermediate fact.

Simplify `this` using `[ι]`. Establish `hιf : Function.Exact ι f`. Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Establish `hy' : q (y : D₁) = 0`. Use `congrArg Subtype.val hy` as an intermediate fact. Rewrite `this` using `[hfv]`. Then use the resulting hypothesis. Take `⟨x, hx⟩` from `(hex (y : D₁)).1 hy'`. Use `⟨⟨x, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `show j x ∈ N₁`. Rewrite using `[hx]`. Conclude with `y.2`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify `hx` using `[ι]`.

Introduce and unpack `⟨x, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [f, ι, LinearMap.restrict_apply, LinearMap.restrictScalars_apply, ZeroMemClass.coe_zero]`. Conclude with `(hex (j x)).2 ⟨x, rfl⟩`. Establish `hιT : Function.Injective (LinearMap.lTensor E ι)` using `Module.Flat.lTensor_preserves_injective_linearMap ι hι`.

Establish `hfT : Function.Exact (LinearMap.lTensor E ι) (LinearMap.lTensor E f)` using `Module.Flat.lTensor_exact E hιf`. Set `Φ : E ⊗[A] N₀ →ₗ[E] D₀` to `N₀.subtype.liftBaseChange E`. Establish `hcomm₁ : ∀ t : E ⊗[A] N₀, j (Φ t) = h₁.equiv (LinearMap.lTensor E ι t)`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul x y => simp [Φ, IsBaseChange.equiv_tmul, hιv]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Establish `hcomm₂ : ∀ t : E ⊗[A] N₁, h₂.equiv (LinearMap.lTensor E f t) = q (h₁.equiv t)`. Introduce `t`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp [IsBaseChange.equiv_tmul, hfv]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Establish `hΦi : Function.Injective Φ`.

Introduce `s t hst`. Apply `hιT` to reduce the goal to its premises. Apply `h₁.equiv.injective` to reduce the goal to its premises. Rewrite using `[← hcomm₁, ← hcomm₁, hst]`. Establish `hΦs : Function.Surjective Φ`.

Introduce `d`. Take `⟨t, ht⟩` from `h₁.equiv.surjective (j d)`. Establish `h0 : LinearMap.lTensor E f t = 0`. Apply `h₂.equiv.injective` to reduce the goal to its premises. Rewrite using `[hcomm₂, ht, map_zero]`.

Conclude with `(hex (j d)).2 ⟨d, rfl⟩`. Take `⟨s, hs⟩` from `(hfT t).1 h0`. Use `⟨s, hj ?_⟩` and prove the remaining obligations. Rewrite using `[hcomm₁, hs, ht]`. Use `IsBaseChange.of_equiv (LinearEquiv.ofBijective Φ ⟨hΦi, hΦs⟩) ?_` and prove the remaining obligations.

Introduce `x`. Use `show Φ (1 ⊗ₜ x) = x`. Simplify using `[Φ, LinearMap.liftBaseChange_tmul]`.
-/
theorem isBaseChange_comap_of_exact (A E : Type) [CommRing A] [CommRing E] [Algebra A E]
    [Module.Flat A E] (D₀ D₁ D₂ : Type) [AddCommGroup D₀] [AddCommGroup D₁] [AddCommGroup D₂]
    [Module E D₀] [Module E D₁] [Module E D₂] [Module A D₀] [Module A D₁] [Module A D₂]
    [IsScalarTower A E D₀] [IsScalarTower A E D₁] [IsScalarTower A E D₂]
    (j : D₀ →ₗ[E] D₁) (q : D₁ →ₗ[E] D₂) (N₁ : Submodule A D₁) (N₂ : Submodule A D₂)
    (hj : Function.Injective j) (hex : Function.Exact j q) (_hq : Function.Surjective q)
    (h₁ : IsBaseChange E N₁.subtype) (h₂ : IsBaseChange E N₂.subtype)
    (hN : ∀ x ∈ N₁, q x ∈ N₂) :
    IsBaseChange E (N₁.comap (j.restrictScalars A)).subtype := by
  set N₀ := N₁.comap (j.restrictScalars A) with hN₀
  let ι : N₀ →ₗ[A] N₁ := (j.restrictScalars A).restrict (fun x hx => hx)
  let f : N₁ →ₗ[A] N₂ := (q.restrictScalars A).restrict hN
  have hιv : ∀ y : N₀, (ι y : D₁) = j y := fun _ => rfl
  have hfv : ∀ y : N₁, (f y : D₂) = q y := fun _ => rfl
  have hι : Function.Injective ι := by
    intro x y hxy
    apply Subtype.ext
    apply hj
    have := congrArg Subtype.val hxy
    simpa [ι] using this
  have hιf : Function.Exact ι f := by
    intro y
    constructor
    · intro hy
      have hy' : q (y : D₁) = 0 := by
        have := congrArg Subtype.val hy
        rwa [hfv] at this
      obtain ⟨x, hx⟩ := (hex (y : D₁)).1 hy'
      refine ⟨⟨x, ?_⟩, ?_⟩
      · show j x ∈ N₁
        rw [hx]; exact y.2
      · apply Subtype.ext
        simpa [ι] using hx
    · rintro ⟨x, rfl⟩
      apply Subtype.ext
      simp only [f, ι, LinearMap.restrict_apply, LinearMap.restrictScalars_apply,
        ZeroMemClass.coe_zero]
      exact (hex (j x)).2 ⟨x, rfl⟩
  have hιT : Function.Injective (LinearMap.lTensor E ι) :=
    Module.Flat.lTensor_preserves_injective_linearMap ι hι
  have hfT : Function.Exact (LinearMap.lTensor E ι) (LinearMap.lTensor E f) :=
    Module.Flat.lTensor_exact E hιf
  let Φ : E ⊗[A] N₀ →ₗ[E] D₀ := N₀.subtype.liftBaseChange E
  have hcomm₁ : ∀ t : E ⊗[A] N₀, j (Φ t) = h₁.equiv (LinearMap.lTensor E ι t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [Φ, IsBaseChange.equiv_tmul, hιv]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hcomm₂ : ∀ t : E ⊗[A] N₁, h₂.equiv (LinearMap.lTensor E f t) = q (h₁.equiv t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [IsBaseChange.equiv_tmul, hfv]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hΦi : Function.Injective Φ := by
    intro s t hst
    apply hιT
    apply h₁.equiv.injective
    rw [← hcomm₁, ← hcomm₁, hst]
  have hΦs : Function.Surjective Φ := by
    intro d
    obtain ⟨t, ht⟩ := h₁.equiv.surjective (j d)
    have h0 : LinearMap.lTensor E f t = 0 := by
      apply h₂.equiv.injective
      rw [hcomm₂, ht, map_zero]
      exact (hex (j d)).2 ⟨d, rfl⟩
    obtain ⟨s, hs⟩ := (hfT t).1 h0
    refine ⟨s, hj ?_⟩
    rw [hcomm₁, hs, ht]
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective Φ ⟨hΦi, hΦs⟩) ?_
  intro x
  show Φ (1 ⊗ₜ x) = x
  simp [Φ, LinearMap.liftBaseChange_tmul]

end GlobalTheory
