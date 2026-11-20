import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws

/- English proof (translation)
Use `revert i`. Evaluate the decidable proposition.
-/
private theorem nc_wt_self (i : Fin 4) : wt i i = 0 := by revert i; decide

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem nc_apply {R : Type} [CommRing R] (t : Rˣ × Rˣ) (X : M4 R) (i j : Fin 4) :
    tconj t X i j = (wv t (wt i j) : R) * X i j := rfl

/- English proof (translation)
Rewrite using `[nc_apply, nc_wt_self]`. Simplify using `[wv]`.
-/
private theorem nc_diag {R : Type} [CommRing R] (t : Rˣ × Rˣ) (X : M4 R) (i : Fin 4) : tconj t X i i = X i i := by
  rw [nc_apply, nc_wt_self]; simp [wv]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [nc_apply, Matrix.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem nc_smul {R : Type} [CommRing R] (t : Rˣ × Rˣ) (c : R) (X : M4 R) : tconj t (c • X) = c • tconj t X := by
  ext i j
  simp only [nc_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end UpperTheory.V.Ws

/- English proof (translation)
Introduce `O Γ _ _ _ Φ Λ _ _ a R _ _ _ D t h`. Take `⟨-, -, -, -, -, -, -, -, hmul, hone, hadj, -, -⟩` from `grp R`. Set `r' : Γ →* M4 R` to `{ toFun := fun g => tconj t (D.r g) map_one' := by rw [map_one, hone] map_mul' := fun g k => by rw [map_mul, hmul] }`. Establish `hr : ∀ g, r' g = tconj t (D.r g)` using `fun _ => rfl`. Use `⟨⟨r', D.ψ⟩, ⟨⟨fun g => ?_, fun g hg => ?_, fun i j hij => ?_⟩, fun i j N => ?_, h.contψ, fun g i => ?_, fun g i j hij hτ => ?_, h.redψ⟩, hr, rfl⟩` and prove the remaining obligations.

Use `h.rep.mult g` as an intermediate fact. Unfold `IsGSp at *`. Use `show adj (tconj t (D.r g)) * tconj t (D.r g) = _`. Rewrite using `[hadj, ← hmul, this, nc_smul, hone]`. Use `show tconj t (D.r g) = 1`.

Rewrite using `[h.rep.kill g hg, hone]`. Use `show tconj t (D.r Φ.g0) i j = 0`. Rewrite using `[nc_apply, h.rep.nrm hij, mul_zero]`. Conclude with `(h.cont i j N).comp fun x => Ideal.Quotient.mk _ (wv t (wt i j) : R) * x`. Use `show res Λ R (tconj t (D.r g) i i) = _`.

Rewrite using `[nc_diag, h.diag]`. Use `show tconj t (D.r g) i j ∈ _`. Rewrite using `[nc_apply]`. Conclude with `Ideal.mul_mem_left _ _ (h.off g i j hij hτ)`.
-/
theorem UpperTheory.V.Ws.sxNearConj :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} (t : Rˣ × Rˣ), Φ.Near a 0 D → ∃ D' : RD Φ R, Φ.Near a 0 D' ∧ (∀ g, D'.r g = tconj t (D.r g)) ∧ D'.ψ = D.ψ := by
  intro O Γ _ _ _ Φ Λ _ _ a R _ _ _ D t h
  obtain ⟨-, -, -, -, -, -, -, -, hmul, hone, hadj, -, -⟩ := grp R
  let r' : Γ →* M4 R :=
    { toFun := fun g => tconj t (D.r g)
      map_one' := by rw [map_one, hone]
      map_mul' := fun g k => by rw [map_mul, hmul] }
  have hr : ∀ g, r' g = tconj t (D.r g) := fun _ => rfl
  refine ⟨⟨r', D.ψ⟩, ⟨⟨fun g => ?_, fun g hg => ?_, fun i j hij => ?_⟩, fun i j N => ?_, h.contψ, fun g i => ?_,
    fun g i j hij hτ => ?_, h.redψ⟩, hr, rfl⟩
  · have := h.rep.mult g
    unfold IsGSp at *
    show adj (tconj t (D.r g)) * tconj t (D.r g) = _
    rw [hadj, ← hmul, this, nc_smul, hone]
  · show tconj t (D.r g) = 1
    rw [h.rep.kill g hg, hone]
  · show tconj t (D.r Φ.g0) i j = 0
    rw [nc_apply, h.rep.nrm hij, mul_zero]
  · exact (h.cont i j N).comp fun x => Ideal.Quotient.mk _ (wv t (wt i j) : R) * x
  · show res Λ R (tconj t (D.r g) i i) = _
    rw [nc_diag, h.diag]
  · show tconj t (D.r g) i j ∈ _
    rw [nc_apply]
    exact Ideal.mul_mem_left _ _ (h.off g i j hij hτ)
