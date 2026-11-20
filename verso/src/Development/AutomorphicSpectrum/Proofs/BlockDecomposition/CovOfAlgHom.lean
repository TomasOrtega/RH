import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.CovMono

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Proceed by induction.

Treat this case separately. Treat this case separately. Treat this case separately. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem cov_self (p : ℕ) (A : Type) [CommRing A] (r : ℕ → A) : Cov p r A := by
  intro K₁ K₀ _ _ _ _ _ _ d _ z hz k
  obtain ⟨w, hw⟩ := hz
  have key : z = d (TensorProduct.lid A K₁ w) := by
    have h1 : TensorProduct.lid A K₀ (d.lTensor A w) = d (TensorProduct.lid A K₁ w) := by
      clear hw
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => simp
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [hw] at h1
    simpa using h1
  rw [key, ← map_smul]
  exact ⟨_, rfl⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Proceed by induction.

Treat this case separately. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem cov_of_algHom (p : ℕ) (A : Type) [CommRing A] (r : ℕ → A)
    (B : Type) [CommRing B] [Algebra A B] (B₁ : Type) [CommRing B₁] [Algebra A B₁]
    (φ : B →ₐ[A] B₁) (h : Cov p r B₁) : Cov p r B := by
  intro K₁ K₀ _ _ _ _ hK₁ hK₀ d hd z hz k
  obtain ⟨w, hw⟩ := hz
  refine h K₁ K₀ hK₁ hK₀ d hd z ⟨φ.toLinearMap.rTensor K₁ w, ?_⟩ k
  have h1 : φ.toLinearMap.rTensor K₀ (d.lTensor B w) = d.lTensor B₁ (φ.toLinearMap.rTensor K₁ w) := by
    clear hw
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [← h1, hw]
  simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem cov_mono : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A), Cov p r A ∧ ∀ (B : Type) [CommRing B] [Algebra A B] (B₁ : Type) [CommRing B₁] [Algebra A B₁] (φ : B →ₐ[A] B₁), Cov p r B₁ → Cov p r B := by
  intro p _ A _ r
  exact ⟨cov_self p A r, fun B _ _ B₁ _ _ φ h => cov_of_algHom p A r B B₁ φ h⟩

end GlobalTheory.CompanionTheory.CovMono
