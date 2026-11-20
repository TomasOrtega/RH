import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly

namespace UpperTheory.Gal.W2

/- English proof (translation)
Introduce `V _ _ _ d hd τ G A hτ hG`. Set `e : V ≃ₗ[ℂ] (Fin d → ℂ)` to `τ.linearEquivOfInjective hτ (by simp [hd])`. Set `b : Module.Basis (Fin d) ℂ V` to `(Pi.basisFun ℂ (Fin d)).map e.symm`. Establish `hM : LinearMap.toMatrix b b G = A`. Use extensionality with `i j`.

Rewrite using `[LinearMap.toMatrix_apply]`. Establish `h1 : b j = e.symm (Pi.single j 1)` using `by simp [b]`. Establish `h2 : ∀ v, b.repr v i = e v i` using `fun v => by simp [b, Pi.basisFun_repr]`. Rewrite using `[h2, h1]`. Express the relevant statement in the definitionally equal form `τ (G (e.symm (Pi.single j 1))) i = A i j`.

Rewrite using `[hG]`. Establish `h3 : τ (e.symm (Pi.single j 1)) = Pi.single j 1`. Rewrite using `[← LinearMap.linearEquivOfInjective_apply hτ (by simp [hd])]`. Conclude with `e.apply_symm_apply _`. Rewrite using `[h3, Matrix.mulVec_single_one]`.

Both sides reduce to the same expression. Rewrite using `[← hM, LinearMap.charpoly_toMatrix]`.
-/
theorem conjCharpoly_of : ConjCharpoly := by
  intro V _ _ _ d hd τ G A hτ hG
  let e : V ≃ₗ[ℂ] (Fin d → ℂ) := τ.linearEquivOfInjective hτ (by simp [hd])
  let b : Module.Basis (Fin d) ℂ V := (Pi.basisFun ℂ (Fin d)).map e.symm
  have hM : LinearMap.toMatrix b b G = A := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have h1 : b j = e.symm (Pi.single j 1) := by simp [b]
    have h2 : ∀ v, b.repr v i = e v i := fun v => by simp [b, Pi.basisFun_repr]
    rw [h2, h1]
    change τ (G (e.symm (Pi.single j 1))) i = A i j
    rw [hG]
    have h3 : τ (e.symm (Pi.single j 1)) = Pi.single j 1 := by
      rw [← LinearMap.linearEquivOfInjective_apply hτ (by simp [hd])]
      exact e.apply_symm_apply _
    rw [h3, Matrix.mulVec_single_one]
    rfl
  rw [← hM, LinearMap.charpoly_toMatrix]

end UpperTheory.Gal.W2
