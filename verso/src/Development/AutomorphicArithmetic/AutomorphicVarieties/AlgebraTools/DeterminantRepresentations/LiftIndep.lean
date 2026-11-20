import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg

open Polynomial UpperTheory.V.W

/- English proof (translation)
Introduce `A G _ _ d hd B _ _ σ τ p q x z hxz`. Set `S : Finset G` to `x.coeff.support ∪ z.coeff.support`. Set `w : MonoidAlgebra (MvPolynomial G A) G` to `∑ g ∈ S, MonoidAlgebra.single g (MvPolynomial.X g)`. Set `φ : MvPolynomial G A →ₐ[A] MvPolynomial σ A` to `MvPolynomial.aeval fun g => x.coeff g`. Set `ψ : MvPolynomial G A →ₐ[A] MvPolynomial τ A` to `MvPolynomial.aeval fun g => z.coeff g`.

Establish `hx : MonoidAlgebra.mapRingHom G (φ : MvPolynomial G A →+* MvPolynomial σ A) w = x`. Use extensionality with `g`. Distinguish the cases in `hg : g ∈ S`. Simplify using `[w, φ, map_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply, hg]`. Establish `h0 : x.coeff g = 0`.

Assume the negation of the conclusion as `h`. Conclude with `hg (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr h))`. Simplify using `[w, φ, map_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply, hg, h0]`. Establish `hz : MonoidAlgebra.mapRingHom G (ψ : MvPolynomial G A →+* MvPolynomial τ A) w = z`. Use extensionality with `g`.

Distinguish the cases in `hg : g ∈ S`. Simplify using `[w, ψ, map_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply, hg]`. Establish `h0 : z.coeff g = 0`. Assume the negation of the conclusion as `h`. Conclude with `hg (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr h))`.

Simplify using `[w, ψ, map_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply, hg, h0]`. Establish `key : p.comp φ = q.comp ψ`. Use `MvPolynomial.algHom_ext fun g => ?_` and prove the remaining obligations. Establish `h` using `congrArg (fun y : MonoidAlgebra B G => y.coeff g) hxz`. Simplify `h` using `[φ, ψ]`.

Combine the equalities or inequalities in the displayed calculation. Express the relevant statement in the definitionally equal form `q (ψ (d G w)) = q (d τ z)`. Rewrite using `[← hd, hz]`.
-/
theorem UpperTheory.V.AlgebraTools.Det.liftIndep :
    ∀ {A G : Type} [CommRing A] [Group G] (d : ∀ σ : Type, MonoidAlgebra (MvPolynomial σ A) G →* MvPolynomial σ A),
    (∀ (σ τ : Type) (f : MvPolynomial σ A →ₐ[A] MvPolynomial τ A) (x : MonoidAlgebra (MvPolynomial σ A) G),
      d τ (MonoidAlgebra.mapRingHom G (f : MvPolynomial σ A →+* MvPolynomial τ A) x) = f (d σ x)) →
    ∀ (B : Type) [CommRing B] [Algebra A B] (σ τ : Type) (p : MvPolynomial σ A →ₐ[A] B) (q : MvPolynomial τ A →ₐ[A] B)
      (x : MonoidAlgebra (MvPolynomial σ A) G) (z : MonoidAlgebra (MvPolynomial τ A) G),
      MonoidAlgebra.mapRingHom G (p : MvPolynomial σ A →+* B) x = MonoidAlgebra.mapRingHom G (q : MvPolynomial τ A →+* B) z →
      p (d σ x) = q (d τ z) := by
  intro A G _ _ d hd B _ _ σ τ p q x z hxz
  classical
  let S : Finset G := x.coeff.support ∪ z.coeff.support
  let w : MonoidAlgebra (MvPolynomial G A) G := ∑ g ∈ S, MonoidAlgebra.single g (MvPolynomial.X g)
  let φ : MvPolynomial G A →ₐ[A] MvPolynomial σ A := MvPolynomial.aeval fun g => x.coeff g
  let ψ : MvPolynomial G A →ₐ[A] MvPolynomial τ A := MvPolynomial.aeval fun g => z.coeff g
  have hx : MonoidAlgebra.mapRingHom G (φ : MvPolynomial G A →+* MvPolynomial σ A) w = x := by
    ext g
    by_cases hg : g ∈ S
    · simp [w, φ, map_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply, hg]
    · have h0 : x.coeff g = 0 := by
        by_contra h
        exact hg (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr h))
      simp [w, φ, map_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply, hg, h0]
  have hz : MonoidAlgebra.mapRingHom G (ψ : MvPolynomial G A →+* MvPolynomial τ A) w = z := by
    ext g
    by_cases hg : g ∈ S
    · simp [w, ψ, map_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply, hg]
    · have h0 : z.coeff g = 0 := by
        by_contra h
        exact hg (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr h))
      simp [w, ψ, map_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply, hg, h0]
  have key : p.comp φ = q.comp ψ := by
    refine MvPolynomial.algHom_ext fun g => ?_
    have h := congrArg (fun y : MonoidAlgebra B G => y.coeff g) hxz
    simpa [φ, ψ] using h
  calc p (d σ x) = p (φ (d G w)) := by rw [← hd, hx]
    _ = (p.comp φ) (d G w) := rfl
    _ = (q.comp ψ) (d G w) := by rw [key]
    _ = q (d τ z) := by
      change q (ψ (d G w)) = q (d τ z)
      rw [← hd, hz]
