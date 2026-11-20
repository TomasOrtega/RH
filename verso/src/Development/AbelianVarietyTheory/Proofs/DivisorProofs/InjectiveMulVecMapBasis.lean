import Mathlib

namespace GlobalTheory.BasisLeftInverse

/- English proof (translation)
Establish `hinj : Function.Injective B.mulVec` using `Matrix.mulVec_injective_iff.2 h`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (Matrix.toLin' B) (LinearMap.ker_eq_bot.2 hinj)`. Use `⟨LinearMap.toMatrix' g, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.toMatrix'_toLin' B, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]`.
-/
theorem exists_left_inv {E : Type} [Field E] {n d : ℕ} (B : Matrix (Fin n) (Fin d) E)
    (h : LinearIndependent E B.col) : ∃ C : Matrix (Fin d) (Fin n) E, C * B = 1 := by
  have hinj : Function.Injective B.mulVec := Matrix.mulVec_injective_iff.2 h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' B) (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' B, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

/- English proof (translation)
Set `B : Matrix (Fin n) (Fin (Module.finrank E V)) E` to `Matrix.of fun k i => ((Module.finBasis E V i : V) : Fin n → E) k`. Establish `hB : LinearIndependent E B.col` using `(Module.finBasis E V).linearIndependent.map' V.subtype (Submodule.ker_subtype V)`. Take `⟨C, hC⟩` from `exists_left_inv B hB`. Establish `hC' : C.map τ * B.map τ = 1`. Rewrite using `[← Matrix.map_mul, hC, Matrix.map_one τ (map_zero τ) (map_one τ)]`.

Express the relevant statement in the definitionally equal form `Function.Injective (B.map τ).mulVec`. Introduce `v w hvw`. Establish `h1 : Matrix.mulVec (C.map τ * B.map τ) v = Matrix.mulVec (C.map τ * B.map τ) w`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hvw]`. Rewrite `h1` using `[hC', Matrix.one_mulVec, Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
theorem injective_mulVec_map_basis {E : Type} [Field E] {n : ℕ} (V : Submodule E (Fin n → E))
    (τ : E →+* ℂ) :
    Function.Injective (Matrix.mulVec (Matrix.of fun (k : Fin n) (i : Fin (Module.finrank E V)) =>
      τ (((Module.finBasis E V i : V) : Fin n → E) k))) := by
  let B : Matrix (Fin n) (Fin (Module.finrank E V)) E :=
    Matrix.of fun k i => ((Module.finBasis E V i : V) : Fin n → E) k
  have hB : LinearIndependent E B.col :=
    (Module.finBasis E V).linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  obtain ⟨C, hC⟩ := exists_left_inv B hB
  have hC' : C.map τ * B.map τ = 1 := by
    rw [← Matrix.map_mul, hC, Matrix.map_one τ (map_zero τ) (map_one τ)]
  change Function.Injective (B.map τ).mulVec
  intro v w hvw
  have h1 : Matrix.mulVec (C.map τ * B.map τ) v = Matrix.mulVec (C.map τ * B.map τ) w := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hvw]
  rwa [hC', Matrix.one_mulVec, Matrix.one_mulVec] at h1

end GlobalTheory.BasisLeftInverse
