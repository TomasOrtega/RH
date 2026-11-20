import Mathlib
import GroundTheory.AutomorphicForms.Cartan

namespace GlobalTheory.CompanionTheory.Dblock.CartanDVR

open Matrix

/- English proof (translation)
Introduce `R K _ _ _ _ _ _ n ϖ hϖ g hg`. Establish `hinj : Function.Injective (algebraMap R K)` using `IsFractionRing.injective R K`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) (fun p : Fin n × Fin n => g p.1 p.2)`. Establish `hb0 : (b : R) ≠ 0` using `nonZeroDivisors.ne_zero b.2`. Use `choose A' hA' using hb`.

Set `A : Matrix (Fin n) (Fin n) R` to `Matrix.of fun i j => A' (i, j)`. Establish `hAg : A.map (algebraMap R K) = algebraMap R K (b : R) • g`. Use extensionality with `i j`. Simplify `hA' (i, j)` using `[A, Algebra.smul_def]`. Establish `hbK : algebraMap R K (b : R) ≠ 0` using `fun h => hb0 (hinj (by simpa using h))`.

Establish `hA : A.det ≠ 0`. Introduce `h`. Establish `h1 : (A.map (algebraMap R K)).det = 0`. Use `RingHom.map_det (algebraMap R K) A` as an intermediate fact. Rewrite `this` using `[h, map_zero]`.

Simplify using `using this.symm`. Rewrite `h1` using `[hAg, Matrix.det_smul]`. Conclude with `(mul_ne_zero (pow_ne_zero _ hbK) hg.ne_zero) h1`. Take `⟨P, Q, e, he, hPQ⟩` from `GroundTheory.Automorphic.Cartan.exists_eq_mul_diagonal_pow_mul hϖ A hA`. Take `⟨c, w, hw⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ`.

Establish `hϖK : algebraMap R K ϖ ≠ 0` using `fun h => hϖ.ne_zero (hinj (by simpa using h))`. Establish `hwK : algebraMap R K (w : R) ≠ 0` using `fun h => w.ne_zero (hinj (by simpa using h))`. Establish `hPd : IsUnit (P : Matrix (Fin n) (Fin n) R).det` using `(Matrix.isUnit_iff_isUnit_det _).1 P.isUnit`. Establish `hQd : IsUnit (Q : Matrix (Fin n) (Fin n) R).det` using `(Matrix.isUnit_iff_isUnit_det _).1 Q.isUnit`. Use `⟨((w⁻¹ : Rˣ) : R) • (P : Matrix (Fin n) (Fin n) R), Q, fun i => (e i : ℤ) - c, ?_, hQd, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.det_smul]`. Conclude with `((Units.isUnit _).pow _).mul hPd`. Introduce `i j hij`. Use `he hij` as an intermediate fact. Simplify using `only`.

Use linear arithmetic over natural numbers and integers. Establish `hwinv : algebraMap R K ((w⁻¹ : Rˣ) : R) = (algebraMap R K (w : R))⁻¹`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← map_mul]`. Simplify using the standard rewrite rules.

Establish `hdiag : Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ ((e i : ℤ) - c)) = ((algebraMap R K ϖ) ^ c)⁻¹ • (Matrix.diagonal (fun i => ϖ ^ e i)).map (algebraMap R K)`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[zpow_sub₀ hϖK, div_eq_mul_inv, mul_comm]`.

Simplify using `[Matrix.diagonal_apply_ne _ hij]`. Establish `hmap : A.map (algebraMap R K) = (P : Matrix (Fin n) (Fin n) R).map (algebraMap R K) * (Matrix.diagonal (fun i => ϖ ^ e i)).map (algebraMap R K) * (Q : Matrix (Fin n) (Fin n) R).map (algebraMap R K)`. Rewrite using `[hPQ]`. Simplify using `only [Matrix.map_mul]`. Establish `hsm : (((w⁻¹ : Rˣ) : R) • (P : Matrix (Fin n) (Fin n) R)).map (algebraMap R K) = (algebraMap R K (w : R))⁻¹ • (P : Matrix (Fin n) (Fin n) R).map (algebraMap R K)`.

Use extensionality with `i j`. Simplify using `[hwinv]`. Rewrite using `[hsm, hdiag, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, smul_smul, ← hmap, hAg, smul_smul, hw]`. Establish `: (algebraMap R K (w : R))⁻¹ * ((algebraMap R K ϖ) ^ c)⁻¹ * algebraMap R K ((w : R) * ϖ ^ c) = 1`. Rewrite using `[map_mul, map_pow]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this, one_smul]`.
-/
theorem cartan_exists : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] (n : ℕ) (ϖ : R), Irreducible ϖ →
    ∀ g : Matrix (Fin n) (Fin n) K, IsUnit g.det →
      ∃ (u v : Matrix (Fin n) (Fin n) R) (a : Fin n → ℤ), IsUnit u.det ∧ IsUnit v.det ∧ Antitone a ∧
        g = u.map (algebraMap R K) * Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (a i)) *
          v.map (algebraMap R K) := by
  intro R K _ _ _ _ _ _ n ϖ hϖ g hg
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun p : Fin n × Fin n => g p.1 p.2)
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
  choose A' hA' using hb
  let A : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => A' (i, j)
  have hAg : A.map (algebraMap R K) = algebraMap R K (b : R) • g := by
    ext i j
    simpa [A, Algebra.smul_def] using hA' (i, j)
  have hbK : algebraMap R K (b : R) ≠ 0 := fun h => hb0 (hinj (by simpa using h))
  have hA : A.det ≠ 0 := by
    intro h
    have h1 : (A.map (algebraMap R K)).det = 0 := by
      have := RingHom.map_det (algebraMap R K) A
      rw [h, map_zero] at this
      simpa using this.symm
    rw [hAg, Matrix.det_smul] at h1
    exact (mul_ne_zero (pow_ne_zero _ hbK) hg.ne_zero) h1
  obtain ⟨P, Q, e, he, hPQ⟩ := GroundTheory.Automorphic.Cartan.exists_eq_mul_diagonal_pow_mul hϖ A hA
  obtain ⟨c, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hϖK : algebraMap R K ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (by simpa using h))
  have hwK : algebraMap R K (w : R) ≠ 0 := fun h => w.ne_zero (hinj (by simpa using h))
  have hPd : IsUnit (P : Matrix (Fin n) (Fin n) R).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 P.isUnit
  have hQd : IsUnit (Q : Matrix (Fin n) (Fin n) R).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 Q.isUnit
  refine ⟨((w⁻¹ : Rˣ) : R) • (P : Matrix (Fin n) (Fin n) R), Q, fun i => (e i : ℤ) - c, ?_, hQd, ?_, ?_⟩
  · rw [Matrix.det_smul]
    exact ((Units.isUnit _).pow _).mul hPd
  · intro i j hij
    have := he hij
    simp only
    omega
  · have hwinv : algebraMap R K ((w⁻¹ : Rˣ) : R) = (algebraMap R K (w : R))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul]
      simp
    have hdiag : Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ ((e i : ℤ) - c)) =
        ((algebraMap R K ϖ) ^ c)⁻¹ • (Matrix.diagonal (fun i => ϖ ^ e i)).map (algebraMap R K) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [zpow_sub₀ hϖK, div_eq_mul_inv, mul_comm]
      · simp [Matrix.diagonal_apply_ne _ hij]
    have hmap : A.map (algebraMap R K) = (P : Matrix (Fin n) (Fin n) R).map (algebraMap R K) *
        (Matrix.diagonal (fun i => ϖ ^ e i)).map (algebraMap R K) *
        (Q : Matrix (Fin n) (Fin n) R).map (algebraMap R K) := by
      rw [hPQ]
      simp only [Matrix.map_mul]
    have hsm : (((w⁻¹ : Rˣ) : R) • (P : Matrix (Fin n) (Fin n) R)).map (algebraMap R K) =
        (algebraMap R K (w : R))⁻¹ • (P : Matrix (Fin n) (Fin n) R).map (algebraMap R K) := by
      ext i j
      simp [hwinv]
    rw [hsm, hdiag, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, smul_smul, ← hmap, hAg,
      smul_smul, hw]
    have : (algebraMap R K (w : R))⁻¹ * ((algebraMap R K ϖ) ^ c)⁻¹ *
        algebraMap R K ((w : R) * ϖ ^ c) = 1 := by
      rw [map_mul, map_pow]
      field_simp
    rw [this, one_smul]

end GlobalTheory.CompanionTheory.Dblock.CartanDVR
