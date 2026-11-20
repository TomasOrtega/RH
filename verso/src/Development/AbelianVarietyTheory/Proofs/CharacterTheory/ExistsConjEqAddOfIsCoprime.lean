import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

/- English proof (translation)
Establish `hpow : ∀ (n : ℕ) (x : V), f ((a ^ n) x) = (b ^ n) (f x)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro x`. Simplify using the standard rewrite rules.

Consider the case `succ n ih => intro x`. Rewrite using `[pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]`. Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `monomial n c => simp [aeval_monomial, hpow]`.
-/
theorem intertwine_aeval_apply {F : Type} [Field F] {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W]
    [Module F W] (f : V →ₗ[F] W) (a : Module.End F V) (b : Module.End F W) (h : ∀ x, f (a x) = b (f x))
    (p : F[X]) (x : V) : f (aeval a p x) = aeval b p (f x) := by
  have hpow : ∀ (n : ℕ) (x : V), f ((a ^ n) x) = (b ^ n) (f x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c => simp [aeval_monomial, hpow]

/- English proof (translation)
Take `⟨a, b, hab⟩` from `hc`. Use `set p₁ := LinearMap.charpoly (g.restrict hg) with hp₁`. Use `set p₂ := LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx)) with hp₂`. Establish `h1 : ∀ y ∈ A, aeval g p₁ y = 0`. Introduce `y hy`.

Use `intertwine_aeval_apply A.subtype (g.restrict hg) g (fun x => rfl) p₁ ⟨y, hy⟩` as an intermediate fact. Rewrite `this` using `[hp₁, LinearMap.aeval_self_charpoly]`. Simplify using `using this.symm`. Establish `h2 : ∀ y, aeval g p₂ y ∈ A`. Introduce `y`.

Use `intertwine_aeval_apply A.mkQ g (A.mapQ A g (fun x hx => hg x hx)) (fun x => rfl) p₂ y` as an intermediate fact. Rewrite `this` using `[hp₂, LinearMap.aeval_self_charpoly]`. Simplify using `using this`. Use extensionality with `x`. Establish `hx : x = aeval g p₁ (aeval g a x) + aeval g p₂ (aeval g b x)`.

Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← LinearMap.add_apply, ← map_add, mul_comm p₁, mul_comm p₂, hab]`. Simplify using the standard rewrite rules. Rewrite using `[hx, map_add, hu.2 _ (h2 _), intertwine_aeval_apply u g g hug, h1 _ (hu.1 _)]`. Simplify using the standard rewrite rules.
-/
theorem nilRad_eq_zero_of_commute {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A)
    (hc : IsCoprime (LinearMap.charpoly (g.restrict hg))
      (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))))
    (u : Module.End F V) (hu : u ∈ nilRad A) (hug : ∀ x, u (g x) = g (u x)) : u = 0 := by
  obtain ⟨a, b, hab⟩ := hc
  set p₁ := LinearMap.charpoly (g.restrict hg) with hp₁
  set p₂ := LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx)) with hp₂
  have h1 : ∀ y ∈ A, aeval g p₁ y = 0 := by
    intro y hy
    have := intertwine_aeval_apply A.subtype (g.restrict hg) g (fun x => rfl) p₁ ⟨y, hy⟩
    rw [hp₁, LinearMap.aeval_self_charpoly] at this
    simpa using this.symm
  have h2 : ∀ y, aeval g p₂ y ∈ A := by
    intro y
    have := intertwine_aeval_apply A.mkQ g (A.mapQ A g (fun x hx => hg x hx)) (fun x => rfl) p₂ y
    rw [hp₂, LinearMap.aeval_self_charpoly] at this
    simpa using this
  ext x
  have hx : x = aeval g p₁ (aeval g a x) + aeval g p₂ (aeval g b x) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← LinearMap.add_apply, ← map_add,
      mul_comm p₁, mul_comm p₂, hab]
    simp
  rw [hx, map_add, hu.2 _ (h2 _), intertwine_aeval_apply u g g hug, h1 _ (hu.1 _)]
  simp

/- English proof (translation)
Introduce `F _ _ V _ _ _ A g hg hc h hh`. Set `N : Submodule F (Module.End F V)` to `{ carrier := nilRad A add_mem' := fun {a b} ha hb => ⟨fun x => A.add_mem (ha.1 x) (hb.1 x), fun x hx => by`. Simplify using `[ha.2 x hx, hb.2 x hx]⟩`. Use the proof step `zero_mem' := ⟨fun x => A.zero_mem, fun x _ => rfl⟩`. Use the proof step `smul_mem' := fun c a ha => ⟨fun x => A.smul_mem c (ha.1 x), fun x hx => by simp [ha.2 x hx]⟩ }`.

Set `D : Module.End F V →ₗ[F] Module.End F V` to `LinearMap.mulRight F g - LinearMap.mulLeft F g`. Establish `hD : ∀ u x, D u x = u (g x) - g (u x)` using `fun u x => rfl`. Establish `hDN : ∀ u ∈ N, D u ∈ N`. Introduce `u hu`. Use `⟨fun x => ?_, fun x hx => ?_⟩` and prove the remaining obligations.

Rewrite using `[hD]`. Conclude with `A.sub_mem (hu.1 _) (hg _ (hu.1 _))`. Rewrite using `[hD, hu.2 _ hx, hu.2 _ (hg _ hx)]`. Simplify using the standard rewrite rules. Establish `hinj : Function.Injective (D.restrict hDN)`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `u hu`. Apply `Subtype.ext` to reduce the goal to its premises. Use `nilRad_eq_zero_of_commute A g hg hc u.1 u.2 fun x => ?_` and prove the remaining obligations. Establish `h0 : D u.1 = 0` using `congrArg Subtype.val hu`.

Use `hD u.1 x` as an intermediate fact. Rewrite `this` using `[h0]`. Conclude with `sub_eq_zero.1 this.symm`. Take `⟨u, hu⟩` from `LinearMap.surjective_of_injective hinj ⟨h, hh⟩`. Establish `hu' : D u.1 = h` using `congrArg Subtype.val hu`.

Take `⟨u, huA, hu0⟩` from `u`. Establish `huu : ∀ x, u (u x) = 0` using `fun x => hu0 _ (huA x)`. Use `⟨LinearEquiv.ofLinearMap (1 + u) (1 - u) ?_ ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Simplify using `[huu]`.

Use extensionality with `x`. Simplify using `[huu]`. Use extensionality with `x`. Establish `h3 : u (g (u x)) = 0` using `hu0 _ (hg _ (huA x))`. Establish `h4 : h x = u (g x) - g (u x)` using `by rw [← hu']; rfl`.

Simplify using `[LinearEquiv.conj_apply, h3, h4]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_conj_eq_add_of_isCoprime : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A),
    IsCoprime (LinearMap.charpoly (g.restrict hg)) (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))) →
    ∀ h ∈ nilRad A, ∃ e : V ≃ₗ[F] V, e.conj g = g + h := by
  intro F _ _ V _ _ _ A g hg hc h hh
  let N : Submodule F (Module.End F V) :=
    { carrier := nilRad A
      add_mem' := fun {a b} ha hb => ⟨fun x => A.add_mem (ha.1 x) (hb.1 x), fun x hx => by
        simp [ha.2 x hx, hb.2 x hx]⟩
      zero_mem' := ⟨fun x => A.zero_mem, fun x _ => rfl⟩
      smul_mem' := fun c a ha => ⟨fun x => A.smul_mem c (ha.1 x), fun x hx => by simp [ha.2 x hx]⟩ }
  let D : Module.End F V →ₗ[F] Module.End F V := LinearMap.mulRight F g - LinearMap.mulLeft F g
  have hD : ∀ u x, D u x = u (g x) - g (u x) := fun u x => rfl
  have hDN : ∀ u ∈ N, D u ∈ N := by
    intro u hu
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · rw [hD]; exact A.sub_mem (hu.1 _) (hg _ (hu.1 _))
    · rw [hD, hu.2 _ hx, hu.2 _ (hg _ hx)]; simp
  have hinj : Function.Injective (D.restrict hDN) := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    apply Subtype.ext
    refine nilRad_eq_zero_of_commute A g hg hc u.1 u.2 fun x => ?_
    have h0 : D u.1 = 0 := congrArg Subtype.val hu
    have := hD u.1 x
    rw [h0] at this
    exact sub_eq_zero.1 this.symm
  obtain ⟨u, hu⟩ := LinearMap.surjective_of_injective hinj ⟨h, hh⟩
  have hu' : D u.1 = h := congrArg Subtype.val hu
  obtain ⟨u, huA, hu0⟩ := u
  have huu : ∀ x, u (u x) = 0 := fun x => hu0 _ (huA x)
  refine ⟨LinearEquiv.ofLinearMap (1 + u) (1 - u) ?_ ?_, ?_⟩
  · ext x; simp [huu]
  · ext x; simp [huu]
  · ext x
    have h3 : u (g (u x)) = 0 := hu0 _ (hg _ (huA x))
    have h4 : h x = u (g x) - g (u x) := by rw [← hu']; rfl
    simp [LinearEquiv.conj_apply, h3, h4]
    abel

end GlobalTheory.CuspGL
