import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws

/- English proof (translation)
Evaluate the decidable proposition. A detailed English derivation is pending.
-/
private theorem nc_wt_self (i : Fin 4) : wt i i = 0 := by revert i; decide

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem nc_apply {R : Type} [CommRing R] (t : Rˣ × Rˣ) (X : M4 R) (i j : Fin 4) :
    tconj t X i j = (wv t (wt i j) : R) * X i j := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem nc_diag {R : Type} [CommRing R] (t : Rˣ × Rˣ) (X : M4 R) (i : Fin 4) : tconj t X i i = X i i := by
  rw [nc_apply, nc_wt_self]; simp [wv]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem nc_smul {R : Type} [CommRing R] (t : Rˣ × Rˣ) (c : R) (X : M4 R) : tconj t (c • X) = c • tconj t X := by
  ext i j
  simp only [nc_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end UpperTheory.V.Ws

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
