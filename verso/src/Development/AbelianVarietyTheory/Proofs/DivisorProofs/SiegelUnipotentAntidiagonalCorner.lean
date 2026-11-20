import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
open GlobalTheory.WeilM
open scoped Matrix

namespace GlobalTheory.SiegelUnip
open Matrix

variable {R : Type} [CommRing R] {n : ℕ}

abbrev adR (n : ℕ) (R : Type) [CommRing R] : Matrix (Fin n) (Fin n ⊕ Fin n) R := fromCols 1 (-1)

abbrev adC (n : ℕ) (R : Type) [CommRing R] : Matrix (Fin n ⊕ Fin n) (Fin n) R := fromRows 1 (-1)

abbrev dgC (n : ℕ) (R : Type) [CommRing R] : Matrix (Fin n ⊕ Fin n) (Fin n) R := diagCols (Fin n)

/- English proof (translation)
Simplify using `[diagCols, fromCols_mul_fromRows]`.
-/
theorem adR_mul_dgC : adR n R * dgC n R = 0 := by
  simp [diagCols, fromCols_mul_fromRows]

/- English proof (translation)
Simplify using `[fromCols_mul_fromRows, two_smul]`.
-/
theorem adR_mul_adC : adR n R * adC n R = 2 • (1 : Matrix (Fin n) (Fin n) R) := by
  simp [fromCols_mul_fromRows, two_smul]

/- English proof (translation)
Rewrite using `[dbl, dgC, diagCols, fromBlocks_mul_fromRows, adC, fromRows_mul]`. Simplify using the standard rewrite rules.
-/
theorem dbl_mul_dgC (J₀ : Matrix (Fin n) (Fin n) R) : dbl J₀ * dgC n R = adC n R * J₀ := by
  rw [dbl, dgC, diagCols, fromBlocks_mul_fromRows, adC, fromRows_mul]
  simp

/- English proof (translation)
Rewrite using `[dbl, dgC, diagCols, transpose_fromRows, fromCols_mul_fromBlocks, adR, mul_fromCols]`. Simplify using the standard rewrite rules.
-/
theorem dgC_tr_mul_dbl (J₀ : Matrix (Fin n) (Fin n) R) : (dgC n R)ᵀ * dbl J₀ = J₀ * adR n R := by
  rw [dbl, dgC, diagCols, transpose_fromRows, fromCols_mul_fromBlocks, adR, mul_fromCols]
  simp

/- English proof (translation)
Rewrite using `[dgC_tr_mul_dbl, Matrix.mul_assoc, adR_mul_dgC, Matrix.mul_zero]`.
-/
theorem dgC_tr_dbl_dgC (J₀ : Matrix (Fin n) (Fin n) R) : (dgC n R)ᵀ * dbl J₀ * dgC n R = 0 := by
  rw [dgC_tr_mul_dbl, Matrix.mul_assoc, adR_mul_dgC, Matrix.mul_zero]

/- English proof (translation)
Simplify using `[adR, adC, transpose_fromCols]`.
-/
theorem adR_tr : (adR n R)ᵀ = adC n R := by
  simp [adR, adC, transpose_fromCols]

/- English proof (translation)
Rewrite using `[dgC, diagCols, fromRows_map, Matrix.map_one _ (map_zero c) (map_one c)]`.
-/
theorem dgC_map {R₀ : Type} [CommRing R₀] [Algebra R₀ R] (c : R →ₐ[R₀] R) : (dgC n R).map c = dgC n R := by
  rw [dgC, diagCols, fromRows_map, Matrix.map_one _ (map_zero c) (map_one c)]

/- English proof (translation)
Rewrite using `[adR, fromCols_map, Matrix.map_neg _ (map_neg c), Matrix.map_one _ (map_zero c) (map_one c)]`.
-/
theorem adR_map {R₀ : Type} [CommRing R₀] [Algebra R₀ R] (c : R →ₐ[R₀] R) : (adR n R).map c = adR n R := by
  rw [adR, fromCols_map, Matrix.map_neg _ (map_neg c), Matrix.map_one _ (map_zero c) (map_one c)]

end GlobalTheory.SiegelUnip

open Matrix GlobalTheory.SiegelUnip in

/- English proof (translation)
Introduce `R₀ R _ _ _ _ c n J₀ x hx`. Use `set N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := dgC n R * x * adR n R with hN`. Establish `hNN : N * N = 0`. Rewrite using `[hN, show dgC n R * x * adR n R * (dgC n R * x * adR n R) = dgC n R * x * (adR n R * dgC n R) * x * adR n R by`. Simplify using `only [Matrix.mul_assoc], adR_mul_dgC, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]`.

Establish `hsq : (⅟(2 : R) • N) * (⅟(2 : R) • N) = 0`. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, hNN, smul_zero, smul_zero]`. Establish `hPQ : (1 + ⅟(2 : R) • N) * (1 - ⅟(2 : R) • N) = 1`. Rewrite using `[add_mul, one_mul, mul_sub, mul_one, hsq]`. Normalize the expressions using the abelian group laws.

Establish `hQP : (1 - ⅟(2 : R) • N) * (1 + ⅟(2 : R) • N) = 1`. Rewrite using `[sub_mul, one_mul, mul_add, mul_one, hsq]`. Normalize the expressions using the abelian group laws. Establish `hc2 : c (⅟(2 : R)) = ⅟(2 : R)`. Use `(invOf_eq_right_inv ?_).symm` and prove the remaining obligations.

Use `congrArg c (mul_invOf_self (2 : R))` as an intermediate fact. Rewrite `this` using `[map_mul, map_ofNat, map_one]`. Then use the resulting hypothesis. Establish `hNc : N.map c = dgC n R * x.map c * adR n R`. Express the relevant statement in the definitionally equal form `(dgC n R * x * adR n R).map (c.toRingHom : R → R) = _`. Rewrite using `[Matrix.map_mul, Matrix.map_mul]`.

Conclude with `congrArg₂ _ (congrArg₂ _ (dgC_map c) rfl) (adR_map c)`. Establish `hPc : (1 + ⅟(2 : R) • N).map c = 1 + ⅟(2 : R) • (dgC n R * x.map c * adR n R)`. Rewrite using `[Matrix.map_add _ (map_add c), Matrix.map_one _ (map_zero c) (map_one c), ← hNc]`. Use `congr 1`. Use extensionality with `i j`.

Simplify using `[hc2]`. Establish `hNt : Nᵀ = adC n R * xᵀ * (dgC n R)ᵀ`. Rewrite using `[hN, transpose_mul, transpose_mul, adR_tr, Matrix.mul_assoc]`. Establish `hmem : (1 + ⅟(2 : R) • N)ᵀ * dbl J₀ * (1 + ⅟(2 : R) • N).map c = dbl J₀`. Rewrite using `[hPc, transpose_add, transpose_one, transpose_smul, hNt]`.

Establish `e1 : dbl J₀ * (dgC n R * x.map c * adR n R) = adC n R * (J₀ * x.map c) * adR n R`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, dbl_mul_dgC]`. Simplify using `only [Matrix.mul_assoc]`. Establish `e2 : adC n R * xᵀ * (dgC n R)ᵀ * dbl J₀ = adC n R * (xᵀ * J₀) * adR n R`. Rewrite using `[Matrix.mul_assoc, dgC_tr_mul_dbl]`.

Simplify using `only [Matrix.mul_assoc]`. Establish `e3 : adC n R * xᵀ * (dgC n R)ᵀ * dbl J₀ * (dgC n R * x.map c * adR n R) = 0`. Rewrite using `[show adC n R * xᵀ * (dgC n R)ᵀ * dbl J₀ * (dgC n R * x.map c * adR n R) = adC n R * xᵀ * ((dgC n R)ᵀ * dbl J₀ * dgC n R) * x.map c * adR n R by simp only [Matrix.mul_assoc], dgC_tr_dbl_dgC]`. Simplify using the standard rewrite rules. Establish `e4 : adC n R * (J₀ * x.map c) * adR n R + adC n R * (xᵀ * J₀) * adR n R = 0`.

Rewrite using `[← Matrix.add_mul, ← Matrix.mul_add, add_comm, hx, Matrix.mul_zero, Matrix.zero_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul]`. Normalize the expressions using the abelian group laws. Use `_ = dbl J₀ + ⅟(2 : R) • (adC n R * (J₀ * x.map c) * adR n R + adC n R * (xᵀ * J₀) * adR n R) := by`.

Rewrite using `[e3, e1, e2, smul_zero, add_zero, smul_add, add_assoc]`. Use `_ = dbl J₀ := by rw [e4, smul_zero, add_zero]`. Set `u : GL (Fin n ⊕ Fin n) R` to `⟨1 + ⅟(2 : R) • N, 1 - ⅟(2 : R) • N, hPQ, hQP⟩`. Use `⟨⟨u, hmem⟩, ?_, fun h => ?_⟩` and prove the remaining obligations. Establish `hp : ((⟨u, hmem⟩ : UG c (dbl J₀)) : GL (Fin n ⊕ Fin n) R).1 = 1 + ⅟(2 : R) • N` using `rfl`.

Rewrite using `[hp]`. Establish `hpd : N * dgC n R = 0` using `by rw [hN, Matrix.mul_assoc, adR_mul_dgC, Matrix.mul_zero]`. Establish `key : ((1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) + ⅟(2 : R) • N) * dgC n R = dgC n R * (1 : Matrix (Fin n) (Fin n) R)`. Rewrite using `[Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hpd, smul_zero, add_zero, Matrix.mul_one]`. Conclude with `key`.

Establish `hp : ((⟨u, hmem⟩ : UG c (dbl J₀)) : GL (Fin n ⊕ Fin n) R).1 = 1 + ⅟(2 : R) • N` using `rfl`. Rewrite using `[hp]`. Establish `e : adR n R * (h * N) * adC n R = (2 : R) • (adR n R * h * dgC n R * x)`. Rewrite using `[hN, show adR n R * (h * (dgC n R * x * adR n R)) * adC n R = adR n R * h * dgC n R * x * (adR n R * adC n R) by`. Simplify using `only [Matrix.mul_assoc], adR_mul_adC, Matrix.mul_smul, Matrix.mul_one, two_smul, two_smul]`.

Rewrite using `[mul_add, mul_one, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, e, smul_smul, invOf_mul_self, one_smul, Matrix.mul_assoc (adR n R) h]`. Both sides reduce to the same expression.
-/
theorem GlobalTheory.siegel_unip_corner : ∀ {R₀ R : Type} [CommRing R₀] [CommRing R] [Algebra R₀ R] [Invertible (2 : R)] (c : R →ₐ[R₀] R) {n : ℕ} (J₀ : Matrix (Fin n) (Fin n) R) (x : Matrix (Fin n) (Fin n) R), xᵀ * J₀ + J₀ * x.map c = 0 → ∃ p : UG c (dbl J₀), (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) * diagCols (Fin n) = diagCols (Fin n) * (1 : Matrix (Fin n) (Fin n) R) ∧ ∀ h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R, Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * (h * p.1.1) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) = Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * h * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) + Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * h * diagCols (Fin n) * x := by
  intro R₀ R _ _ _ _ c n J₀ x hx
  set N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := dgC n R * x * adR n R with hN
  have hNN : N * N = 0 := by
    rw [hN, show dgC n R * x * adR n R * (dgC n R * x * adR n R) = dgC n R * x * (adR n R * dgC n R) * x * adR n R by
      simp only [Matrix.mul_assoc], adR_mul_dgC, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]
  have hsq : (⅟(2 : R) • N) * (⅟(2 : R) • N) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hNN, smul_zero, smul_zero]
  have hPQ : (1 + ⅟(2 : R) • N) * (1 - ⅟(2 : R) • N) = 1 := by
    rw [add_mul, one_mul, mul_sub, mul_one, hsq]; abel
  have hQP : (1 - ⅟(2 : R) • N) * (1 + ⅟(2 : R) • N) = 1 := by
    rw [sub_mul, one_mul, mul_add, mul_one, hsq]; abel
  have hc2 : c (⅟(2 : R)) = ⅟(2 : R) := by
    refine (invOf_eq_right_inv ?_).symm
    have := congrArg c (mul_invOf_self (2 : R))
    rwa [map_mul, map_ofNat, map_one] at this
  have hNc : N.map c = dgC n R * x.map c * adR n R := by
    change (dgC n R * x * adR n R).map (c.toRingHom : R → R) = _
    rw [Matrix.map_mul, Matrix.map_mul]
    exact congrArg₂ _ (congrArg₂ _ (dgC_map c) rfl) (adR_map c)
  have hPc : (1 + ⅟(2 : R) • N).map c = 1 + ⅟(2 : R) • (dgC n R * x.map c * adR n R) := by
    rw [Matrix.map_add _ (map_add c), Matrix.map_one _ (map_zero c) (map_one c), ← hNc]
    congr 1
    ext i j
    simp [hc2]
  have hNt : Nᵀ = adC n R * xᵀ * (dgC n R)ᵀ := by
    rw [hN, transpose_mul, transpose_mul, adR_tr, Matrix.mul_assoc]
  have hmem : (1 + ⅟(2 : R) • N)ᵀ * dbl J₀ * (1 + ⅟(2 : R) • N).map c = dbl J₀ := by
    rw [hPc, transpose_add, transpose_one, transpose_smul, hNt]
    have e1 : dbl J₀ * (dgC n R * x.map c * adR n R) = adC n R * (J₀ * x.map c) * adR n R := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, dbl_mul_dgC]; simp only [Matrix.mul_assoc]
    have e2 : adC n R * xᵀ * (dgC n R)ᵀ * dbl J₀ = adC n R * (xᵀ * J₀) * adR n R := by
      rw [Matrix.mul_assoc, dgC_tr_mul_dbl]; simp only [Matrix.mul_assoc]
    have e3 : adC n R * xᵀ * (dgC n R)ᵀ * dbl J₀ * (dgC n R * x.map c * adR n R) = 0 := by
      rw [show adC n R * xᵀ * (dgC n R)ᵀ * dbl J₀ * (dgC n R * x.map c * adR n R) =
        adC n R * xᵀ * ((dgC n R)ᵀ * dbl J₀ * dgC n R) * x.map c * adR n R by simp only [Matrix.mul_assoc],
        dgC_tr_dbl_dgC]
      simp
    have e4 : adC n R * (J₀ * x.map c) * adR n R + adC n R * (xᵀ * J₀) * adR n R = 0 := by
      rw [← Matrix.add_mul, ← Matrix.mul_add, add_comm, hx, Matrix.mul_zero, Matrix.zero_mul]
    calc (1 + ⅟(2 : R) • (adC n R * xᵀ * (dgC n R)ᵀ)) * dbl J₀ * (1 + ⅟(2 : R) • (dgC n R * x.map c * adR n R))
        = dbl J₀ + ⅟(2 : R) • (dbl J₀ * (dgC n R * x.map c * adR n R)) +
          ⅟(2 : R) • (adC n R * xᵀ * (dgC n R)ᵀ * dbl J₀) +
          (⅟(2 : R) * ⅟(2 : R)) • (adC n R * xᵀ * (dgC n R)ᵀ * dbl J₀ * (dgC n R * x.map c * adR n R)) := by
          simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul]; abel
      _ = dbl J₀ + ⅟(2 : R) • (adC n R * (J₀ * x.map c) * adR n R + adC n R * (xᵀ * J₀) * adR n R) := by
          rw [e3, e1, e2, smul_zero, add_zero, smul_add, add_assoc]
      _ = dbl J₀ := by rw [e4, smul_zero, add_zero]
  let u : GL (Fin n ⊕ Fin n) R := ⟨1 + ⅟(2 : R) • N, 1 - ⅟(2 : R) • N, hPQ, hQP⟩
  refine ⟨⟨u, hmem⟩, ?_, fun h => ?_⟩
  · have hp : ((⟨u, hmem⟩ : UG c (dbl J₀)) : GL (Fin n ⊕ Fin n) R).1 = 1 + ⅟(2 : R) • N := rfl
    rw [hp]
    have hpd : N * dgC n R = 0 := by rw [hN, Matrix.mul_assoc, adR_mul_dgC, Matrix.mul_zero]
    have key : ((1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) + ⅟(2 : R) • N) * dgC n R =
        dgC n R * (1 : Matrix (Fin n) (Fin n) R) := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hpd, smul_zero, add_zero, Matrix.mul_one]
    exact key
  · have hp : ((⟨u, hmem⟩ : UG c (dbl J₀)) : GL (Fin n ⊕ Fin n) R).1 = 1 + ⅟(2 : R) • N := rfl
    rw [hp]
    have e : adR n R * (h * N) * adC n R = (2 : R) • (adR n R * h * dgC n R * x) := by
      rw [hN, show adR n R * (h * (dgC n R * x * adR n R)) * adC n R = adR n R * h * dgC n R * x * (adR n R * adC n R) by
        simp only [Matrix.mul_assoc], adR_mul_adC, Matrix.mul_smul, Matrix.mul_one, two_smul, two_smul]
    rw [mul_add, mul_one, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, e, smul_smul,
      invOf_mul_self, one_smul, Matrix.mul_assoc (adR n R) h]
    rfl
