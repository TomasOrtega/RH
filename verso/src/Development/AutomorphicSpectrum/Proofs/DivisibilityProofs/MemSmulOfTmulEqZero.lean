import Mathlib

open CategoryTheory TensorProduct ChangeOfRings

namespace GlobalTheory.CompanionTheory.ModuleReduction

/- English proof (translation)
Establish `hex : Function.Exact (LinearMap.mulLeft A ξ) g`. Introduce `a`. Rewrite using `[hk a]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, rfl⟩`.

Conclude with `⟨b, rfl⟩`. Introduce and unpack `⟨b, rfl⟩`. Conclude with `⟨b, rfl⟩`. Establish `hex'` using `rTensor_exact N hex hg`. Establish `h1 : (LinearMap.rTensor N g) ((1 : A) ⊗ₜ[A] m) = 0`.

Simplify using `using h`. Take `⟨t, ht⟩` from `(hex' _).1 h1`. Establish `key : ∀ t : A ⊗[A] N, TensorProduct.lid A N (LinearMap.rTensor N (LinearMap.mulLeft A ξ) t) = ξ • TensorProduct.lid A N t`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a n => simp [mul_smul]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy, smul_add]`. Use `⟨TensorProduct.lid A N t, ?_⟩` and prove the remaining obligations. Rewrite using `[← key, ht]`.

Simplify using the standard rewrite rules.
-/
theorem mem_smul_of_tmul_eq_zero {A Q N : Type} [CommRing A] [AddCommGroup Q] [Module A Q]
    [AddCommGroup N] [Module A N] (g : A →ₗ[A] Q) (hg : Function.Surjective g) (ξ : A)
    (hk : ∀ a, g a = 0 ↔ ∃ b, a = ξ * b) (m : N) (h : g 1 ⊗ₜ[A] m = 0) :
    ∃ n : N, m = ξ • n := by
  have hex : Function.Exact (LinearMap.mulLeft A ξ) g := by
    intro a
    rw [hk a]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨b, rfl⟩
  have hex' := rTensor_exact N hex hg
  have h1 : (LinearMap.rTensor N g) ((1 : A) ⊗ₜ[A] m) = 0 := by
    simpa using h
  obtain ⟨t, ht⟩ := (hex' _).1 h1
  have key : ∀ t : A ⊗[A] N, TensorProduct.lid A N (LinearMap.rTensor N (LinearMap.mulLeft A ξ) t)
      = ξ • TensorProduct.lid A N t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a n => simp [mul_smul]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  refine ⟨TensorProduct.lid A N t, ?_⟩
  rw [← key, ht]
  simp

/- English proof (translation)
Set `Q` to `(ModuleCat.restrictScalars θ).obj (ModuleCat.of O O)`. Set `one : Q` to `(1 : O)`. Set `g : A →ₗ[A] Q` to `LinearMap.toSpanSingleton A Q one`. Establish `hgθ : ∀ a, (g a : O) = θ a` using `fun a => mul_one (θ a)`. Establish `hsm : ∀ (X : 𝒞) (a : A) (m : M.obj X), (1 : O) ⊗ₜ[A,θ] (a • m) = (θ a) ⊗ₜ[A,θ] m`.

Introduce `X a m`. Establish `h` using `TensorProduct.smul_tmul (R := A) (R' := A) a one m`. Establish `e : a • one = (θ a : O)` using `hgθ a`. Rewrite `h` using `[e]`. Conclude with `h.symm`.

Set `r : ∀ X : 𝒞, M.obj X →ₛₗ[θ] (M ⋙ ModuleCat.extendScalars θ).obj X` to `fun X => { toFun := fun m => (1 : O) ⊗ₜ[A,θ] m map_add' := fun a b => TensorProduct.tmul_add _ _ _ map_smul' := fun a m => by`. Use `(hsm X a m).trans ?_` and prove the remaining obligations. Use `ModuleCat.ExtendScalars.smul_tmul θ (M := M.obj X) (θ a) (1 : O) m` as an intermediate fact. Rewrite `this` using `[mul_one]`. Conclude with `this.symm }`.

Use `⟨M ⋙ ModuleCat.extendScalars θ, r, fun X => ⟨?_, fun m => ⟨?_, ?_⟩⟩, ?_⟩` and prove the remaining obligations. Introduce `y`. Express the relevant statement in the definitionally equal form `Q ⊗[A] (M.obj X) at y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, map_zero _⟩`.

Consider the case `tmul o n`. Take `⟨a, ha⟩` from `hθ o`. Use `⟨a • n, ?_⟩` and prove the remaining obligations. Use `(hsm X a n).trans ?_` and prove the remaining obligations. Rewrite using `[ha]`.

Both sides reduce to the same expression. Consider the case `add x y hx hy`. Take `⟨u, hu⟩` from `hx`. Take `⟨v, hv⟩` from `hy`. Use `⟨u + v, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, hu, hv]`. Both sides reduce to the same expression. Introduce `h`. Use `mem_smul_of_tmul_eq_zero g ?_ ξ ?_ m ?_` and prove the remaining obligations. Introduce `q`.

Take `⟨a, ha⟩` from `hθ q`. Conclude with `⟨a, (hgθ a).trans ha⟩`. Introduce `a`. Establish `: g a = 0 ↔ θ a = 0`. Rewrite using `[← hgθ a]`.

Both sides reduce to the same expression. Rewrite using `[this, ← RingHom.mem_ker, hker, Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, rfl⟩`. Conclude with `⟨b, mul_comm _ _⟩`.

Introduce and unpack `⟨b, rfl⟩`. Conclude with `⟨b, mul_comm _ _⟩`. Establish `e : g 1 = one` using `one_smul A one`. Rewrite using `[e]`. Conclude with `h`.

Introduce and unpack `⟨n, rfl⟩`. Establish `: θ ξ = 0`. Rewrite using `[← RingHom.mem_ker, hker]`. Conclude with `Ideal.mem_span_singleton_self ξ`. Express the relevant statement in the definitionally equal form `(1 : O) ⊗ₜ[A,θ] (ξ • n) = 0`.

Rewrite using `[hsm X ξ n, this]`. Conclude with `TensorProduct.zero_tmul (R := A) Q n`. Introduce `X Y f m`. Both sides reduce to the same expression.
-/
theorem exists_reduction (A O : Type) [CommRing A] [CommRing O] (θ : A →+* O)
    (hθ : Function.Surjective θ) (ξ : A) (hker : RingHom.ker θ = Ideal.span {ξ})
    (𝒞 : Type 1) [CategoryTheory.Category.{0} 𝒞] (M : CategoryTheory.Functor 𝒞 (ModuleCat.{0} A)) :
    ∃ (D : CategoryTheory.Functor 𝒞 (ModuleCat.{0} O)) (r : ∀ X : 𝒞, M.obj X →ₛₗ[θ] D.obj X),
      (∀ X, Function.Surjective (r X) ∧ ∀ m, r X m = 0 ↔ ∃ n, m = ξ • n) ∧
      ∀ (X Y : 𝒞) (f : X ⟶ Y) (m : M.obj X), D.map f (r X m) = r Y (M.map f m) := by
  let Q := (ModuleCat.restrictScalars θ).obj (ModuleCat.of O O)
  let one : Q := (1 : O)
  let g : A →ₗ[A] Q := LinearMap.toSpanSingleton A Q one
  have hgθ : ∀ a, (g a : O) = θ a := fun a => mul_one (θ a)
  have hsm : ∀ (X : 𝒞) (a : A) (m : M.obj X),
      (1 : O) ⊗ₜ[A,θ] (a • m) = (θ a) ⊗ₜ[A,θ] m := by
    intro X a m
    have h := TensorProduct.smul_tmul (R := A) (R' := A) a one m
    have e : a • one = (θ a : O) := hgθ a
    rw [e] at h
    exact h.symm
  let r : ∀ X : 𝒞, M.obj X →ₛₗ[θ] (M ⋙ ModuleCat.extendScalars θ).obj X := fun X =>
    { toFun := fun m => (1 : O) ⊗ₜ[A,θ] m
      map_add' := fun a b => TensorProduct.tmul_add _ _ _
      map_smul' := fun a m => by
        refine (hsm X a m).trans ?_
        have := ModuleCat.ExtendScalars.smul_tmul θ (M := M.obj X) (θ a) (1 : O) m
        rw [mul_one] at this
        exact this.symm }
  refine ⟨M ⋙ ModuleCat.extendScalars θ, r, fun X => ⟨?_, fun m => ⟨?_, ?_⟩⟩, ?_⟩
  · intro y
    change Q ⊗[A] (M.obj X) at y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul o n =>
      obtain ⟨a, ha⟩ := hθ o
      refine ⟨a • n, ?_⟩
      refine (hsm X a n).trans ?_
      rw [ha]
      rfl
    | add x y hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      refine ⟨u + v, ?_⟩
      rw [map_add, hu, hv]
      rfl
  · intro h
    refine mem_smul_of_tmul_eq_zero g ?_ ξ ?_ m ?_
    · intro q
      obtain ⟨a, ha⟩ := hθ q
      exact ⟨a, (hgθ a).trans ha⟩
    · intro a
      have : g a = 0 ↔ θ a = 0 := by
        rw [← hgθ a]
        rfl
      rw [this, ← RingHom.mem_ker, hker, Ideal.mem_span_singleton']
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨b, mul_comm _ _⟩
      · rintro ⟨b, rfl⟩
        exact ⟨b, mul_comm _ _⟩
    · have e : g 1 = one := one_smul A one
      rw [e]
      exact h
  · rintro ⟨n, rfl⟩
    have : θ ξ = 0 := by
      rw [← RingHom.mem_ker, hker]
      exact Ideal.mem_span_singleton_self ξ
    change (1 : O) ⊗ₜ[A,θ] (ξ • n) = 0
    rw [hsm X ξ n, this]
    exact TensorProduct.zero_tmul (R := A) Q n
  · intro X Y f m
    rfl

end GlobalTheory.CompanionTheory.ModuleReduction
