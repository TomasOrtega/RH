import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximationStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealPropertiesStatement

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

/- English proof (translation)
Simplify using `only [hermA, Pi.add_apply, add_mul, Finset.sum_add_distrib]`.
-/
theorem hermA_add_left {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → RA F E) :
    hermA c G (x + x') y = hermA c G x y + hermA c G x' y := by
  simp only [hermA, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hermA, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]`.
-/
theorem hermA_neg_left {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → RA F E) :
    hermA c G (-x) y = - hermA c G x y := by
  simp only [hermA, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

/- English proof (translation)
Simplify using `only [hermA, fv, sg, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sum, map_one, mul_one]`. Both sides reduce to the same expression.
-/
theorem hermA_tmul_fv {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (t : FiniteAdeleRing (𝓞 F) F) (x y : Fin n → E) :
    hermA c G (fun i => t ⊗ₜ[F] x i) (fv F y) = t ⊗ₜ[F] (∑ a, ∑ b, x a * G a b * c (y b)) := by
  simp only [hermA, fv, sg, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    TensorProduct.tmul_sum, map_one, mul_one]
  rfl

/- English proof (translation)
Introduce `F E _ _ _ _ _ n L c G J hfg hspan _ _ _ _ hL z`. Establish `back : ∀ w ∈ hat F (L : Set (Fin n → E)), ∀ y ∈ L, hermA c G w (fv F y) ∈ hat1 F (J : Set E)`. Introduce `w hw y hy`. Proceed by induction on `hw using AddSubgroup.closure_induction with`. Consider the case `mem w hw`.

Take `⟨t, ht, x, hx, rfl⟩` from `hw`. Rewrite using `[hermA_tmul_fv]`. Conclude with `AddSubgroup.subset_closure ⟨t, ht, _, (hL x).2 hx y hy, rfl⟩`. Consider the case `zero`. Establish `: hermA c G 0 (fv F y) = 0` using `by simp [hermA]`.

Rewrite using `[this]`. Conclude with `zero_mem _`. Consider the case `add w w' _ _ h h' => rw [hermA_add_left]`. Conclude with `add_mem h h'`. Consider the case `neg w _ h => rw [hermA_neg_left]`.

Conclude with `neg_mem h`. Use `⟨fun hz => ?_, fun hz => back z hz⟩` and prove the remaining obligations. Take `⟨h1, -, h3, -⟩` from `GlobalTheory.T.adelicCompletion_rational_points_and_approximation F E n L hfg hspan`. Take `⟨x, hx⟩` from `h3 z`. Establish `hxL : x ∈ L`.

Use `(hL x).1 fun y hy => ?_` and prove the remaining obligations. Establish `h` using `sub_mem (hz y hy) (back _ hx y hy)`. Establish `e : hermA c G z (fv F y) - hermA c G (z - fv F x) (fv F y) = hermA c G (fv F x) (fv F y)`. Rewrite using `[sub_eq_add_neg z, hermA_add_left, hermA_neg_left]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h` using `[e]`. Establish `e2` using `hermA_tmul_fv c G (1 : FiniteAdeleRing (𝓞 F) F) x y`. Conclude with `((GlobalTheory.T.adelicCompletion_fractionalIdeal_properties_alt F E).2.1 J _).1 (e2 ▸ h)`. Use `add_mem hx ((h1 x).2 hxL)` as an intermediate fact. Simplify using `using this`.
-/
theorem hat_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (J : FractionalIdeal (𝓞 E)⁰ E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ x, c (c x) = x) → (∀ a b, c (G a b) = G b a) → G.det ≠ 0 → J ≠ 0 → (∀ v : Fin n → E, (∀ y ∈ L, (∑ a, ∑ b, v a * G a b * c (y b)) ∈ J) ↔ v ∈ L) → ∀ z : Fin n → RA F E, (∀ y ∈ L, hermA c G z (fv F y) ∈ hat1 F (J : Set E)) ↔ z ∈ (hat F (L : Set (Fin n → E))) := by
  intro F E _ _ _ _ _ n L c G J hfg hspan _ _ _ _ hL z
  have back : ∀ w ∈ hat F (L : Set (Fin n → E)), ∀ y ∈ L,
      hermA c G w (fv F y) ∈ hat1 F (J : Set E) := by
    intro w hw y hy
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hw
      rw [hermA_tmul_fv]
      exact AddSubgroup.subset_closure ⟨t, ht, _, (hL x).2 hx y hy, rfl⟩
    | zero =>
      have : hermA c G 0 (fv F y) = 0 := by simp [hermA]
      rw [this]; exact zero_mem _
    | add w w' _ _ h h' => rw [hermA_add_left]; exact add_mem h h'
    | neg w _ h => rw [hermA_neg_left]; exact neg_mem h
  refine ⟨fun hz => ?_, fun hz => back z hz⟩
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.T.adelicCompletion_rational_points_and_approximation F E n L hfg hspan
  obtain ⟨x, hx⟩ := h3 z
  have hxL : x ∈ L := by
    refine (hL x).1 fun y hy => ?_
    have h := sub_mem (hz y hy) (back _ hx y hy)
    have e : hermA c G z (fv F y) - hermA c G (z - fv F x) (fv F y)
        = hermA c G (fv F x) (fv F y) := by
      rw [sub_eq_add_neg z, hermA_add_left, hermA_neg_left]; ring
    rw [e] at h
    have e2 := hermA_tmul_fv c G (1 : FiniteAdeleRing (𝓞 F) F) x y
    exact ((GlobalTheory.T.adelicCompletion_fractionalIdeal_properties_alt F E).2.1 J _).1 (e2 ▸ h)
  have := add_mem hx ((h1 x).2 hxL)
  simpa using this

end GlobalTheory.AdLat
