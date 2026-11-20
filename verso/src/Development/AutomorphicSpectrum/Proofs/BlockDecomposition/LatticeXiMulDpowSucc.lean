import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit

set_option autoImplicit false

noncomputable section

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatDp

/- English proof (translation)
Establish `hi : ((i : ℚ) + 1) ≠ 0` using `by positivity`. Establish `hf : (i.factorial : ℚ) ≠ 0` using `by exact_mod_cast i.factorial_ne_zero`. Establish `key : ((i : B) + 1) * ((((i + 1).factorial : ℚ)⁻¹) • η ^ (i + 1)) = ((i.factorial : ℚ)⁻¹) • η ^ (i + 1)`. Establish `h1 : ((i : B) + 1) = algebraMap ℚ B ((i : ℚ) + 1)` using `by simp`. Rewrite using `[h1, ← Algebra.smul_def, smul_smul]`.

Use `congr 1`. Rewrite using `[Nat.factorial_succ]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_assoc c ((i : B) + 1), key, mul_assoc c η]`.

Simplify using `only [Algebra.mul_smul_comm, pow_succ]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_divPow_succ {B : Type} [CommRing B] [Algebra ℚ B] (c η : B) (i : ℕ) :
    (c * η) * (((i.factorial : ℚ)⁻¹) • η ^ i) =
      (c * ((i : B) + 1)) * ((((i + 1).factorial : ℚ)⁻¹) • η ^ (i + 1)) := by
  have hi : ((i : ℚ) + 1) ≠ 0 := by positivity
  have hf : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have key : ((i : B) + 1) * ((((i + 1).factorial : ℚ)⁻¹) • η ^ (i + 1)) =
      ((i.factorial : ℚ)⁻¹) • η ^ (i + 1) := by
    have h1 : ((i : B) + 1) = algebraMap ℚ B ((i : ℚ) + 1) := by simp
    rw [h1, ← Algebra.smul_def, smul_smul]
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  rw [mul_assoc c ((i : B) + 1), key, mul_assoc c η]
  simp only [Algebra.mul_smul_comm, pow_succ]
  congr 2
  ring

/- English proof (translation)
Establish `h0 : ((l : ℚ) ^ M) ≠ 0` using `pow_ne_zero _ (by exact_mod_cast hl)`. Establish `h1 : ((l : B) ^ M) = algebraMap ℚ B ((l : ℚ) ^ M)` using `by simp`. Rewrite using `[h1, ← Algebra.smul_def, smul_smul, mul_inv_cancel₀ h0, one_smul]`.
-/
theorem natPow_mul_inv_smul {B : Type} [CommRing B] [Algebra ℚ B] (x : B) (l M : ℕ) (hl : l ≠ 0) :
    (l : B) ^ M * ((((l : ℚ) ^ M)⁻¹) • x) = x := by
  have h0 : ((l : ℚ) ^ M) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl)
  have h1 : ((l : B) ^ M) = algebraMap ℚ B ((l : ℚ) ^ M) := by simp
  rw [h1, ← Algebra.smul_def, smul_smul, mul_inv_cancel₀ h0, one_smul]

/- English proof (translation)
Establish `h` using `mul_divPow_succ ((l : B) ^ M) ((((l : ℚ) ^ M)⁻¹) • x) i`. Rewrite `h` using `[natPow_mul_inv_smul x l M hl]`. Then use the resulting hypothesis.
-/
theorem mul_divPow_eq_elem {B : Type} [CommRing B] [Algebra ℚ B] (x : B) (l M : ℕ) (hl : l ≠ 0) (i : ℕ) :
    x * (((i.factorial : ℚ)⁻¹) • ((((l : ℚ) ^ M)⁻¹) • x) ^ i) =
      ((l : B) ^ M * ((i : B) + 1)) *
        ((((i + 1).factorial : ℚ)⁻¹) • ((((l : ℚ) ^ M)⁻¹) • x) ^ (i + 1)) := by
  have h := mul_divPow_succ ((l : B) ^ M) ((((l : ℚ) ^ M)⁻¹) • x) i
  rwa [natPow_mul_inv_smul x l M hl] at h

/- English proof (translation)
Introduce `W B _ _ _ f ξ l M hl i`. Simplify using `only [Lat.dpE, Lat.η]`. Conclude with `mul_divPow_eq_elem (f ξ) l M hl i`.
-/
theorem mul_divPow_eq : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W)
    (l M : ℕ), l ≠ 0 → ∀ i : ℕ,
    f ξ * Lat.dpE f ξ l M i = ((l : B) ^ M * ((i : B) + 1)) * Lat.dpE f ξ l M (i + 1) := by
  intro W B _ _ _ f ξ l M hl i
  simp only [Lat.dpE, Lat.η]
  exact mul_divPow_eq_elem (f ξ) l M hl i

end GlobalTheory.CompanionTheory.LatDp
