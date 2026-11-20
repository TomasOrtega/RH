import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormAlmostAll

open Matrix Polynomial NumberField IsDedekindDomain UpperTheory.ConvolutionTheory.D
open scoped TensorProduct

section

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ} (σ : R ≃ₐ[k] R)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
private theorem sg_succ (m : ℕ) (x : GL (Fin n) R) : sg (σ ^ (m + 1)) x = sg (σ ^ m) (sg σ x) := by
  rw [pow_succ]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
private theorem sg_succ' (m : ℕ) (x : GL (Fin n) R) : sg (σ ^ (m + 1)) x = sg σ (sg (σ ^ m) x) := by
  rw [pow_succ']
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem sg_one (x : GL (Fin n) R) : sg (1 : R ≃ₐ[k] R) x = x := rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem nm_succ (m : ℕ) (δ : GL (Fin n) R) : nm σ (m + 1) δ = nm σ m δ * sg (σ ^ m) δ := by
  simp [nm, List.range_succ]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem nm_conj (m : ℕ) (x δ : GL (Fin n) R) : nm σ m (sgConj σ x δ) = x⁻¹ * nm σ m δ * sg (σ ^ m) x := by
  induction m with
  | zero => simp [nm, sg_one]
  | succ m ih =>
    rw [nm_succ, nm_succ, ih, sgConj, map_mul, map_mul, map_inv, sg_succ]
    group

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem sg_nm (m : ℕ) (δ : GL (Fin n) R) : sg σ (nm σ m δ) = δ⁻¹ * nm σ m δ * sg (σ ^ m) δ := by
  induction m with
  | zero => simp [nm, sg_one]
  | succ m ih =>
    rw [nm_succ, map_mul, ih, ← sg_succ']
    group

end

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem UpperTheory.ConvolutionTheory.D.nmPoly :
    UpperTheory.ConvolutionTheory.D.NmPoly := by
  intro k R _ _ _ σ q h n δ
  refine ⟨?_, fun x => by rw [nm_conj, h.pow, sg_one]⟩
  have e : (cp (nm σ q δ)).map (σ : R →+* R) = cp (nm σ q δ) := by
    have h1 := sg_nm σ q δ
    rw [h.pow, sg_one] at h1
    have h2 : cp (sg σ (nm σ q δ)) = (cp (nm σ q δ)).map (σ : R →+* R) := Matrix.charpoly_map _ _
    rw [← h2, h1, cp, cp, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
  have hl : cp (nm σ q δ) ∈ Polynomial.lifts (algebraMap k R) := (Polynomial.lifts_iff_coeff_lifts _).2 fun i =>
    h.fix _ (by simpa [Polynomial.coeff_map] using congrArg (fun p => Polynomial.coeff p i) e)
  obtain ⟨p, hp⟩ := hl
  exact ⟨p, Polynomial.monic_of_injective h.inj (by rw [show p.map (algebraMap k R) = _ from hp]; exact Matrix.charpoly_monic _), hp.symm⟩
