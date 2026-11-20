import ReciprocityTheory.SemistableReduction.IntCoresB

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory MvPolynomial

def blockSlice {B n : ℕ} (b : Fin B) (p : Fin B → Fin n → ℂ) :
    Fin B × Fin n → MvPolynomial (Fin n) ℂ :=
  fun q => if q.1 = b then X q.2 else C (p q.1 q.2)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem blockSlice_isHomogeneous {B n : ℕ} {a : Fin B → ℕ} {f : MvPolynomial (Fin B × Fin n) ℂ}
    (hf : IsMultiHomogeneous a f) (b : Fin B) (p : Fin B → Fin n → ℂ) :
    (bind₁ (blockSlice b p) f).IsHomogeneous (a b) := by
  rw [f.as_sum, map_sum]
  apply IsHomogeneous.sum
  intro s hs
  rw [bind₁_monomial]
  have hdeg : ∀ q, (blockSlice b p q).IsHomogeneous (if q.1 = b then 1 else 0) := by
    intro q; unfold blockSlice; split_ifs
    · exact isHomogeneous_X _ _
    · exact isHomogeneous_C _ _
  have hprod := IsHomogeneous.prod s.support (fun q => blockSlice b p q ^ s q)
    (fun q => (if q.1 = b then 1 else 0) * s q) (fun q _ => (hdeg q).pow (s q))
  have hsum : ∑ q ∈ s.support, (if q.1 = b then 1 else 0) * s q = a b := by
    rw [Finset.sum_subset (Finset.subset_univ _)
      (fun q _ hq => by simp [Finsupp.notMem_support_iff.1 hq])]
    rw [← hf s hs b, Fintype.sum_prod_type]
    simp [ite_mul]
  rw [← zero_add (a b), ← hsum]
  exact (isHomogeneous_C _ _).mul hprod

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem eval_blockSlice {B n : ℕ} (f : MvPolynomial (Fin B × Fin n) ℂ) (b : Fin B)
    (p : Fin B → Fin n → ℂ) (w : Fin n → ℂ) :
    eval w (bind₁ (blockSlice b p) f) = eval (fun q => Function.update p b w q.1 q.2) f := by
  have hφ : (fun q => eval₂Hom (RingHom.id ℂ) w (blockSlice b p q)) =
      fun q => Function.update p b w q.1 q.2 := by
    funext q
    by_cases hq : q.1 = b
    · simp [blockSlice, hq]
    · simp [blockSlice, hq]
  show eval₂Hom (RingHom.id ℂ) w (bind₁ _ f) = _
  rw [eval₂Hom_bind₁, hφ]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Supply the required witnesses or components. Consider separately whether the proposition holds or fails.

Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sphereLogIntegrable_holds (hSJ : SJStatement) : SphereLogIntegrableStatement := by
  intro B n a f _ hf
  set F : (Fin B → Fin n → ℂ) → ℂ := fun p => eval (fun q => p q.1 q.2) f with hFdef
  have hF : BlockPoly B n a F := by
    refine ⟨(continuous_eval f).comp (continuous_pi fun q =>
      (continuous_apply q.2).comp (continuous_apply q.1)), fun b p => ?_⟩
    exact ⟨_, blockSlice_isHomogeneous hf b p, fun w => (eval_blockSlice f b p w).symm⟩
  by_cases hz : ∃ z0, onSpheres F z0 ≠ 0
  · obtain ⟨z0, hz0⟩ := hz
    exact (blockPoly_claim hSJ n B a F hF z0 hz0).1
  · simp only [not_exists, not_not] at hz
    have : (fun z : BlockSphere B n => Real.log ‖eval (blockPoint z) f‖) = fun _ => 0 := by
      funext z
      have h0 : eval (blockPoint z) f = 0 := hz z
      rw [h0, norm_zero, Real.log_zero]
    rw [this]
    exact integrable_zero _ _ _

end ReciprocityTheory.MultiplicativeHeights
