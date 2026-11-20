import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.OrdExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LagTriangular
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LagNeZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CoiConjSingle

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Establish `h : (g : Matrix (Fin n) (Fin n) C) * (f a * M * f b) * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) = single a a 1 * ((g : Matrix (Fin n) (Fin n) C) * M * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) * single b b 1`. Rewrite using `[← hg a, ← hg b]`. Simplify using `only [mul_assoc, Units.inv_mul_cancel_left]`. Rewrite using `[h, Matrix.mul_single_apply_same, Matrix.single_mul_apply_same, one_mul, mul_one]`.
-/
private theorem entry_of_conj {C : Type} [CommRing C] {n : ℕ} (g : GL (Fin n) C) (f : Fin n → Matrix (Fin n) (Fin n) C)
    (hg : ∀ i, (g : Matrix (Fin n) (Fin n) C) * f i * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) = single i i 1)
    (M : Matrix (Fin n) (Fin n) C) (a b : Fin n) :
    ((g : Matrix (Fin n) (Fin n) C) * M * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) a b =
      ((g : Matrix (Fin n) (Fin n) C) * (f a * M * f b) * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) a b := by
  have h : (g : Matrix (Fin n) (Fin n) C) * (f a * M * f b) * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) =
      single a a 1 * ((g : Matrix (Fin n) (Fin n) C) * M * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) *
        single b b 1 := by
    rw [← hg a, ← hg b]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  rw [h, Matrix.mul_single_apply_same, Matrix.single_mul_apply_same, one_mul, mul_one]

/- English proof (translation)
Introduce `H C _ _ _ n r ψ g₀ hu hc ho`. Establish `h0` using `UpperTheory.V.AlgebraTools.ord_ext (R := C) r (fun i => (Units.coeHom C).comp (ψ i)) (fun g => by`. Use `ho g` as an intermediate fact. Unfold `ordProd at this`. Simplify `this)` using `only [Algebra.algebraMap_eq_smul_one, MonoidHom.comp_apply, Units.coeHom_apply]`.

Take `⟨h1, h2, h3⟩` from `UpperTheory.V.AlgebraTools.lag_triangular (MonoidAlgebra.lift C (Matrix (Fin n) (Fin n) C) H r) (fun i => MonoidAlgebra.lift C C H ((Units.coeHom C).comp (ψ i))) (MonoidAlgebra.of C H g₀) h0 (fun i j hij => by simpa using hu i j hij)`. Simplify using `only [MonoidAlgebra.lift_of, MonoidHom.comp_apply, Units.coeHom_apply] at h1 h2 h3`. Establish `h4` using `UpperTheory.V.AlgebraTools.lag_ne_zero (fun i => (ψ i g₀ : C)) (r g₀) hu (by rw [← Matrix.charpoly_map, hc])`. Take `⟨g, hg⟩` from `UpperTheory.V.AlgebraTools.coi_conj_single _ h1 h4`. Use `⟨g, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩` and prove the remaining obligations.

Establish `h5` using `h2 (MonoidAlgebra.of C H s) i j hij`. Rewrite `h5` using `[MonoidAlgebra.lift_of]`. Establish `h6` using `entry_of_conj g _ hg (r s) i j`. Rewrite `h6` using `[h5, mul_zero, zero_mul]`. Conclude with `h6`.

Establish `h5` using `h3 (MonoidAlgebra.of C H s) i`. Rewrite `h5` using `[MonoidAlgebra.lift_of, MonoidAlgebra.lift_of]`. Establish `h6` using `entry_of_conj g _ hg (r s) i i`. Rewrite `h6` using `[h5, mul_smul_comm, smul_mul_assoc, hg]`. Use `h6.trans ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Fr.flag_loc :
    ∀ {H C : Type} [Group H] [CommRing C] [IsLocalRing C] {n : ℕ} (r : H →* Matrix (Fin n) (Fin n) C) (ψ : Fin n → H →* Cˣ) (g₀ : H), (∀ i j, i ≠ j → IsUnit ((ψ i g₀ : C) - ψ j g₀)) → ((r g₀).map (residue C)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (residue C (ψ i g₀))) → (∀ g, ordProd r (fun i s => (ψ i s : C)) g = 0) → UpperTheory.V.W.HasFlag r.toHomUnits ψ := by
  intro H C _ _ _ n r ψ g₀ hu hc ho
  have h0 := UpperTheory.V.AlgebraTools.ord_ext (R := C) r (fun i => (Units.coeHom C).comp (ψ i)) (fun g => by
    have := ho g
    unfold ordProd at this
    simpa only [Algebra.algebraMap_eq_smul_one, MonoidHom.comp_apply, Units.coeHom_apply] using this)
  obtain ⟨h1, h2, h3⟩ := UpperTheory.V.AlgebraTools.lag_triangular (MonoidAlgebra.lift C (Matrix (Fin n) (Fin n) C) H r)
    (fun i => MonoidAlgebra.lift C C H ((Units.coeHom C).comp (ψ i))) (MonoidAlgebra.of C H g₀) h0
    (fun i j hij => by simpa using hu i j hij)
  simp only [MonoidAlgebra.lift_of, MonoidHom.comp_apply, Units.coeHom_apply] at h1 h2 h3
  have h4 := UpperTheory.V.AlgebraTools.lag_ne_zero (fun i => (ψ i g₀ : C)) (r g₀) hu (by rw [← Matrix.charpoly_map, hc])
  obtain ⟨g, hg⟩ := UpperTheory.V.AlgebraTools.coi_conj_single _ h1 h4
  refine ⟨g, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
  · have h5 := h2 (MonoidAlgebra.of C H s) i j hij
    rw [MonoidAlgebra.lift_of] at h5
    have h6 := entry_of_conj g _ hg (r s) i j
    rw [h5, mul_zero, zero_mul] at h6
    exact h6
  · have h5 := h3 (MonoidAlgebra.of C H s) i
    rw [MonoidAlgebra.lift_of, MonoidAlgebra.lift_of] at h5
    have h6 := entry_of_conj g _ hg (r s) i i
    rw [h5, mul_smul_comm, smul_mul_assoc, hg] at h6
    refine h6.trans ?_
    simp
