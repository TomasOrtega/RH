import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.AlgCoproduct

/- English proof (translation)
Introduce `A _ B _ _ n`. Proceed by induction on `n with`. Consider the case `zero`. Use `⟨A, inferInstance, inferInstance, fun i => i.elim0, ?_⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion.

Introduce `T _ x y _`. Conclude with `⟨x, by ext a; rfl, fun i => i.elim0⟩`. Introduce `T _ z z' h _`. Conclude with `h`. Consider the case `succ n ih`.

Take `⟨K, _, _, ι, hι⟩` from `ih`. Use `⟨B ⊗[A] K, inferInstance, inferInstance, Fin.cons Algebra.TensorProduct.includeLeft (fun i => (Algebra.TensorProduct.includeRight).comp (ι i)), ?_⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `T _ x y hy`. Take `⟨z, hz, hzi⟩` from `hι.ex T x (fun i => y i.succ) (fun i => hy i.succ)`.

Use `letI : Algebra A T := x.toAlgebra`. Set `f : B →ₐ[A] T` to `{ y 0 with commutes' := fun a => RingHom.congr_fun (hy 0) a }`. Set `g : K →ₐ[A] T` to `{ z with commutes' := fun a => RingHom.congr_fun hz a }`. Use `⟨(Algebra.TensorProduct.productMap f g).toRingHom, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `a`.

Conclude with `(Algebra.TensorProduct.productMap f g).commutes a`. Introduce `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Use extensionality with `b`. Simplify using `[f, g]`.

Use extensionality with `b`. Use `RingHom.congr_fun (hzi j) b` as an intermediate fact. Simplify `this` using `[f, g]`. Introduce `T _ z z' h hi`. Establish `hB : ∀ b : B, z (b ⊗ₜ[A] 1) = z' (b ⊗ₜ[A] 1)` using `fun b => by`.

Simplify using `using RingHom.congr_fun (hi 0) b`. Establish `hK : (z.comp (Algebra.TensorProduct.includeRight : K →ₐ[A] B ⊗[A] K).toRingHom) = z'.comp (Algebra.TensorProduct.includeRight : K →ₐ[A] B ⊗[A] K).toRingHom`. Use `hι.uniq T _ _ ?_ (fun i => ?_)` and prove the remaining obligations. Use extensionality with `a`. Use `RingHom.congr_fun h a` as an intermediate fact.

Simplify `this` using `[Algebra.TensorProduct.algebraMap_apply]`. Use extensionality with `b`. Simplify using `using RingHom.congr_fun (hi i.succ) b`. Use `RingHom.ext fun t => ?_` and prove the remaining obligations. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul b k`. Establish `h1 : b ⊗ₜ[A] k = (b ⊗ₜ[A] (1 : K)) * ((1 : B) ⊗ₜ[A] k)` using `by simp`. Establish `h2 : z ((1 : B) ⊗ₜ[A] k) = z' ((1 : B) ⊗ₜ[A] k)` using `RingHom.congr_fun hK k`. Rewrite using `[h1, map_mul, map_mul, hB, h2]`.

Consider the case `add a b ha hb => simp [ha, hb]`.
-/
theorem exists_isWP : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (n : ℕ),
    ∃ (K : Type) (_ : CommRing K) (_ : Algebra A K) (ι : Fin n → (B →ₐ[A] K)), IsWP ι := by
  intro A _ B _ _ n
  induction n with
  | zero =>
    refine ⟨A, inferInstance, inferInstance, fun i => i.elim0, ?_⟩
    constructor
    · intro T _ x y _
      exact ⟨x, by ext a; rfl, fun i => i.elim0⟩
    · intro T _ z z' h _
      exact h
  | succ n ih =>
    obtain ⟨K, _, _, ι, hι⟩ := ih
    refine ⟨B ⊗[A] K, inferInstance, inferInstance,
      Fin.cons Algebra.TensorProduct.includeLeft
        (fun i => (Algebra.TensorProduct.includeRight).comp (ι i)), ?_⟩
    constructor
    · intro T _ x y hy
      obtain ⟨z, hz, hzi⟩ := hι.ex T x (fun i => y i.succ) (fun i => hy i.succ)
      letI : Algebra A T := x.toAlgebra
      let f : B →ₐ[A] T := { y 0 with commutes' := fun a => RingHom.congr_fun (hy 0) a }
      let g : K →ₐ[A] T := { z with commutes' := fun a => RingHom.congr_fun hz a }
      refine ⟨(Algebra.TensorProduct.productMap f g).toRingHom, ?_, ?_⟩
      · ext a
        exact (Algebra.TensorProduct.productMap f g).commutes a
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · ext b
          simp [f, g]
        · ext b
          have := RingHom.congr_fun (hzi j) b
          simpa [f, g] using this
    · intro T _ z z' h hi
      have hB : ∀ b : B, z (b ⊗ₜ[A] 1) = z' (b ⊗ₜ[A] 1) := fun b => by
        simpa using RingHom.congr_fun (hi 0) b
      have hK : (z.comp (Algebra.TensorProduct.includeRight : K →ₐ[A] B ⊗[A] K).toRingHom) =
          z'.comp (Algebra.TensorProduct.includeRight : K →ₐ[A] B ⊗[A] K).toRingHom := by
        refine hι.uniq T _ _ ?_ (fun i => ?_)
        · ext a
          have := RingHom.congr_fun h a
          simpa [Algebra.TensorProduct.algebraMap_apply] using this
        · ext b
          simpa using RingHom.congr_fun (hi i.succ) b
      refine RingHom.ext fun t => ?_
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b k =>
        have h1 : b ⊗ₜ[A] k = (b ⊗ₜ[A] (1 : K)) * ((1 : B) ⊗ₜ[A] k) := by simp
        have h2 : z ((1 : B) ⊗ₜ[A] k) = z' ((1 : B) ⊗ₜ[A] k) := RingHom.congr_fun hK k
        rw [h1, map_mul, map_mul, hB, h2]
      | add a b ha hb => simp [ha, hb]

end GlobalTheory.CompanionTheory.AlgCoproduct
