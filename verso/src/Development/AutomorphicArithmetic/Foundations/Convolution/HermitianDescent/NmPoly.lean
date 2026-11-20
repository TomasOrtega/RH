import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormAlmostAll

open Matrix Polynomial NumberField IsDedekindDomain UpperTheory.ConvolutionTheory.D
open scoped TensorProduct

section

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ} (σ : R ≃ₐ[k] R)

/- English proof (translation)
Rewrite using `[pow_succ]`. Both sides reduce to the same expression.
-/
private theorem sg_succ (m : ℕ) (x : GL (Fin n) R) : sg (σ ^ (m + 1)) x = sg (σ ^ m) (sg σ x) := by
  rw [pow_succ]
  rfl

/- English proof (translation)
Rewrite using `[pow_succ']`. Both sides reduce to the same expression.
-/
private theorem sg_succ' (m : ℕ) (x : GL (Fin n) R) : sg (σ ^ (m + 1)) x = sg σ (sg (σ ^ m) x) := by
  rw [pow_succ']
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem sg_one (x : GL (Fin n) R) : sg (1 : R ≃ₐ[k] R) x = x := rfl

/- English proof (translation)
Simplify using `[nm, List.range_succ]`.
-/
private theorem nm_succ (m : ℕ) (δ : GL (Fin n) R) : nm σ (m + 1) δ = nm σ m δ * sg (σ ^ m) δ := by
  simp [nm, List.range_succ]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [nm, sg_one]`. Consider the case `succ m ih`. Rewrite using `[nm_succ, nm_succ, ih, sgConj, map_mul, map_mul, map_inv, sg_succ]`. Use `group`.
-/
private theorem nm_conj (m : ℕ) (x δ : GL (Fin n) R) : nm σ m (sgConj σ x δ) = x⁻¹ * nm σ m δ * sg (σ ^ m) x := by
  induction m with
  | zero => simp [nm, sg_one]
  | succ m ih =>
    rw [nm_succ, nm_succ, ih, sgConj, map_mul, map_mul, map_inv, sg_succ]
    group

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [nm, sg_one]`. Consider the case `succ m ih`. Rewrite using `[nm_succ, map_mul, ih, ← sg_succ']`. Use `group`.
-/
private theorem sg_nm (m : ℕ) (δ : GL (Fin n) R) : sg σ (nm σ m δ) = δ⁻¹ * nm σ m δ * sg (σ ^ m) δ := by
  induction m with
  | zero => simp [nm, sg_one]
  | succ m ih =>
    rw [nm_succ, map_mul, ih, ← sg_succ']
    group

end

/- English proof (translation)
Introduce `k R _ _ _ σ q h n δ`. Use `⟨?_, fun x => by rw [nm_conj, h.pow, sg_one]⟩` and prove the remaining obligations. Establish `e : (cp (nm σ q δ)).map (σ : R →+* R) = cp (nm σ q δ)`. Establish `h1` using `sg_nm σ q δ`. Rewrite `h1` using `[h.pow, sg_one]`.

Establish `h2 : cp (sg σ (nm σ q δ)) = (cp (nm σ q δ)).map (σ : R →+* R)` using `Matrix.charpoly_map _ _`. Rewrite using `[← h2, h1, cp, cp, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']`. Establish `hl : cp (nm σ q δ) ∈ Polynomial.lifts (algebraMap k R)` using `(Polynomial.lifts_iff_coeff_lifts _).2 fun i => h.fix _ (by simpa [Polynomial.coeff_map] using congrArg (fun p => Polynomial.coeff p i) e)`. Take `⟨p, hp⟩` from `hl`. Conclude with `⟨p, Polynomial.monic_of_injective h.inj (by rw [show p.map (algebraMap k R) = _ from hp]; exact Matrix.charpoly_monic _), hp.symm⟩`.
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
