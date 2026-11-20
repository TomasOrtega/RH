import Mathlib

namespace AevalSpecializationAlgHom

open MvPolynomial

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Treat this case separately. Extract witnesses or component facts from the available result. Split into cases according to the possible forms of the given data. Treat this case separately. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Take a linear combination of the given relations to obtain the conclusion. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem key {Ω : Type} [Field Ω] [Algebra ℚ Ω] {σ : Type} (τ : σ → Ω) (F : MvPolynomial σ ℚ)
    {E : Type} [CommRing E] [Algebra ℚ E] (u : σ → E) (hF : aeval τ F ≠ (0 : Ω))
    (v : E) (hv : v * aeval u F = 1) (P : MvPolynomial (Option σ) ℚ) :
    ∃ (N : ℕ) (G : MvPolynomial σ ℚ),
      aeval (fun o => Option.elim o (aeval τ F)⁻¹ τ) P * (aeval τ F) ^ N = aeval τ G ∧
      aeval (fun o => Option.elim o v u) P * (aeval u F) ^ N = aeval u G := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, by simp, by simp⟩
  | add p q hp hq =>
    obtain ⟨N1, G1, h1, h1'⟩ := hp
    obtain ⟨N2, G2, h2, h2'⟩ := hq
    refine ⟨N1 + N2, G1 * F ^ N2 + G2 * F ^ N1, ?_, ?_⟩
    · simp only [map_add, map_mul, map_pow, ← h1, ← h2]; ring
    · simp only [map_add, map_mul, map_pow, ← h1', ← h2']; ring
  | mul_X p o hp =>
    obtain ⟨N, G, h1, h1'⟩ := hp
    cases o with
    | none =>
      refine ⟨N + 1, G, ?_, ?_⟩
      · simp only [map_mul, aeval_X, Option.elim_none]
        rw [← h1, pow_succ]
        field_simp
      · simp only [map_mul, aeval_X, Option.elim_none]
        rw [← h1', pow_succ]
        linear_combination (aeval (fun o => Option.elim o v u) p * aeval u F ^ N) * hv
    | some i =>
      refine ⟨N, G * X i, ?_, ?_⟩
      · simp only [map_mul, aeval_X, Option.elim_some, ← h1]; ring
      · simp only [map_mul, aeval_X, Option.elim_some, ← h1']; ring

end AevalSpecializationAlgHom

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Substitute using the available equality. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.Yde9.main :
    ∀ (Ω : Type) [inst : Field Ω] [inst_1 : Algebra ℚ Ω] (σ : Type) (τ : σ → Ω) (F : MvPolynomial σ ℚ) (S : Subalgebra ℚ Ω)
      (E : Type) [inst_2 : CommRing E] [inst_3 : Algebra ℚ E] (u : σ → E),
      (MvPolynomial.aeval τ : MvPolynomial σ ℚ → Ω) F ≠ (0 : Ω) →
        S = Algebra.adjoin ℚ (Insert.insert ((MvPolynomial.aeval τ : MvPolynomial σ ℚ → Ω) F)⁻¹ (Set.range τ)) →
          (∀ (G : MvPolynomial σ ℚ),
              (MvPolynomial.aeval τ : MvPolynomial σ ℚ → Ω) G = (0 : Ω) →
                (MvPolynomial.aeval u : MvPolynomial σ ℚ → E) G = (0 : E)) →
            IsUnit ((MvPolynomial.aeval u : MvPolynomial σ ℚ → E) F) →
              ∃ (φ : ↥S →ₐ[ℚ] E),
                ∀ (G : MvPolynomial σ ℚ) (s : ↥S),
                  (↑s : Ω) = (MvPolynomial.aeval τ : MvPolynomial σ ℚ → Ω) G →
                    (φ : ↥S → E) s = (MvPolynomial.aeval u : MvPolynomial σ ℚ → E) G := by
  intro Ω _ _ σ τ F S E _ _ u hF hS hker hU
  obtain ⟨w, hw⟩ := hU
  set v : E := ((w⁻¹ : Eˣ) : E) with hvdef
  have hv : v * MvPolynomial.aeval u F = 1 := by rw [← hw]; simp [v]
  set τ' : Option σ → Ω := fun o => Option.elim o (MvPolynomial.aeval τ F)⁻¹ τ with hτ'
  set u' : Option σ → E := fun o => Option.elim o v u with hu'
  have hS' : S = (MvPolynomial.aeval τ').range := by
    rw [hS, ← Algebra.adjoin_range_eq_range_aeval, Option.range_eq]
    rfl
  subst hS'
  have hsurj := AlgHom.rangeRestrict_surjective (MvPolynomial.aeval τ' : MvPolynomial (Option σ) ℚ →ₐ[ℚ] Ω)
  have hK : ∀ P ∈ RingHom.ker (MvPolynomial.aeval τ' : MvPolynomial (Option σ) ℚ →ₐ[ℚ] Ω).rangeRestrict,
      (MvPolynomial.aeval u') P = 0 := by
    intro P hP
    rw [RingHom.mem_ker] at hP
    have hP' : MvPolynomial.aeval τ' P = 0 := congrArg Subtype.val hP
    obtain ⟨N, G, h1, h1'⟩ := AevalSpecializationAlgHom.key τ F u hF v hv P
    have h0 : MvPolynomial.aeval τ G = 0 := by
      rw [← h1]; simp only [τ'] at hP'; simp [hP']
    have h2 := hker G h0
    rw [h2] at h1'
    have hunit : IsUnit (MvPolynomial.aeval u F ^ N) := by
      rw [← hw]; exact (w.isUnit).pow N
    exact (hunit.mul_left_eq_zero).mp h1'
  let e := Ideal.quotientKerAlgEquivOfSurjective hsurj
  let L := Ideal.Quotient.liftₐ (RingHom.ker (MvPolynomial.aeval τ' : MvPolynomial (Option σ) ℚ →ₐ[ℚ] Ω).rangeRestrict) (MvPolynomial.aeval u') hK
  refine ⟨L.comp e.symm.toAlgHom, ?_⟩
  intro G s hs
  have hs' : s = (MvPolynomial.aeval τ').rangeRestrict (MvPolynomial.rename some G) := by
    apply Subtype.ext
    rw [hs]
    simp [MvPolynomial.aeval_rename]
    rfl
  rw [hs']
  have he : e.symm ((MvPolynomial.aeval τ').rangeRestrict (MvPolynomial.rename some G)) =
      Ideal.Quotient.mk _ (MvPolynomial.rename some G) :=
    Ideal.quotientKerAlgEquivOfSurjective_symm_apply hsurj _
  change L (e.symm ((MvPolynomial.aeval τ').rangeRestrict (MvPolynomial.rename some G))) = _
  rw [he]
  change MvPolynomial.aeval u' (MvPolynomial.rename some G) = _
  rw [MvPolynomial.aeval_rename]
  rfl
