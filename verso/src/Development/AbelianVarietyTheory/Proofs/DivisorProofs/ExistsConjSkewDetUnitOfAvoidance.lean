import Mathlib
open scoped Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `F R _ _ _ _ c hcc hcF e H ρ hρ hcρ n J₀ ε hJ hdet D C x₀ hx₀`. Take `⟨e', he'⟩ : ∃ a : R, a = ((ε : ℤ) : R)` from `⟨_, rfl⟩`. Rewrite `hJ` using `[← he']`. Establish `hee : e' * e' = 1`. Rewrite using `[he', ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]`.

Establish `hce : c e' = e'` using `by rw [he']; exact map_intCast c _`. Establish `h2 : (2 : R) * ⅟2 = 1` using `mul_invOf_self 2`. Establish `hc2 : c (⅟2 : R) = ⅟2`. Establish `h1 : c (⅟2 : R) * 2 = 1`. Use `congrArg c (invOf_mul_self (2 : R))` as an intermediate fact.

Rewrite `this` using `[map_mul, map_ofNat, map_one]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation. Take `⟨r, hr'⟩ : ∃ a : R, a = ↑hρ.unit⁻¹` from `⟨_, rfl⟩`. Establish `hr : ρ * r = 1` using `by rw [hr']; exact hρ.mul_val_inv`. Establish `hcr : c r = -r`.

Establish `h1 : c r * (-ρ) = 1` using `by rw [← hcρ, ← map_mul, mul_comm, hr, map_one]`. Take the linear combination `(-r) * h1 + (-c r) * hr`. Establish `hKdet : IsUnit (J₀ᵀ).det` using `by rw [Matrix.det_transpose]; exact hdet`. Establish `hLK : J₀ᵀ⁻¹ * J₀ᵀ = 1` using `Matrix.nonsing_inv_mul _ hKdet`. Establish `hLtJ : (J₀ᵀ⁻¹)ᵀ * J₀ = 1`.

Establish `: J₀ * (J₀ᵀ⁻¹)ᵀ = 1`. Use `congrArg Matrix.transpose hLK` as an intermediate fact. Rewrite `this` using `[Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one]`. Then use the resulting hypothesis. Conclude with `mul_eq_one_comm.mp this`. Establish `hJLc : J₀ * (J₀ᵀ⁻¹).map c = e' • 1`.

Establish `h1 : (J₀ᵀ⁻¹).map c * (e' • J₀) = 1`. Use `congrArg c.mapMatrix hLK` as an intermediate fact. Rewrite `this` using `[map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.transpose_map, hJ]`. Conclude with `this`. Establish `h3 : (e' • J₀) * (J₀ᵀ⁻¹).map c = 1` using `mul_eq_one_comm.mp h1`.

Rewrite `h3` using `[Matrix.smul_mul]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨M₀, hM₀⟩ : ∃ M : Matrix (Fin n) (Fin n) R, M = J₀ᵀ * x₀` from `⟨_, rfl⟩`. Take `⟨v, hv'⟩ : ∃ M : Matrix (Fin n) (Fin n) R, M = (⅟2 : R) • (M₀ - Matrix.of fun i j => e' * c (M₀ j i))` from `⟨_, rfl⟩`. Take `⟨w, hw'⟩ : ∃ M : Matrix (Fin n) (Fin n) R, M = (r * ⅟2) • (M₀ + Matrix.of fun i j => e' * c (M₀ j i))` from `⟨_, rfl⟩`.

Establish `hv : ∀ i j, v j i + e' * c (v i j) = 0`. Introduce `i j`. Simplify using `only [hv', Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, smul_eq_mul, map_mul, map_sub, hc2, hce, hcc]`. Take the linear combination `(-(⅟2 : R) * M₀ j i) * hee`. Establish `hw : ∀ i j, w j i + e' * c (w i j) = 0`.

Introduce `i j`. Simplify using `only [hw', Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, smul_eq_mul, map_mul, map_add, hc2, hce, hcc, hcr]`. Take the linear combination `(-(r * ⅟2) * M₀ j i) * hee`. Establish `hsum : v + ρ • w = M₀`. Use extensionality with `i j`.

Simplify using `only [hv', hw', Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, smul_eq_mul]`. Take the linear combination `((⅟2 : R) * (M₀ i j + e' * c (M₀ j i))) * hr + M₀ i j * h2`. Establish `hcond : ∀ s, c s = s → (J₀ᵀ⁻¹ * (v + s • w))ᵀ * J₀ + J₀ * (J₀ᵀ⁻¹ * (v + s • w)).map c = 0`. Introduce `s hs`. Establish `e1 : (J₀ᵀ⁻¹ * (v + s • w))ᵀ * J₀ = (v + s • w)ᵀ`.

Rewrite using `[Matrix.transpose_mul, Matrix.mul_assoc, hLtJ, Matrix.mul_one]`. Establish `e2 : J₀ * (J₀ᵀ⁻¹ * (v + s • w)).map c = e' • (v + s • w).map c`. Rewrite using `[Matrix.map_mul, ← Matrix.mul_assoc, hJLc, Matrix.smul_mul, Matrix.one_mul]`. Rewrite using `[e1, e2]`. Use extensionality with `i j`.

Simplify using `only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_add, map_mul, hs, Matrix.zero_apply]`. Take the linear combination `hv i j + s * hw i j`. Take `⟨ψ, hψ⟩ : ∃ p : Polynomial R, p = ((D + C * J₀ᵀ⁻¹ * v).map Polynomial.C + (Polynomial.X : Polynomial R) • (C * J₀ᵀ⁻¹ * w).map Polynomial.C).det` from `⟨_, rfl⟩`. Establish `hev : ∀ s, ψ.eval s = (D + C * (J₀ᵀ⁻¹ * (v + s • w))).det`. Introduce `s`.

Establish `hre : D + C * (J₀ᵀ⁻¹ * (v + s • w)) = (D + C * J₀ᵀ⁻¹ * v) + s • (C * J₀ᵀ⁻¹ * w)`. Simplify using `only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc, add_assoc]`. Rewrite using `[hre, hψ, ← Polynomial.coe_evalRingHom, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`.

Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]`. Establish `hρev : ψ.eval ρ = (D + C * x₀).det`. Rewrite using `[hev, hsum, hM₀, ← Matrix.mul_assoc J₀ᵀ⁻¹, hLK, Matrix.one_mul]`. Establish `hne : ∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0`. Introduce `Ω _ φ hφ h0`.

Establish `h1` using `congrArg (Polynomial.eval (φ ρ)) h0`. Rewrite `h1` using `[Polynomial.eval_map, Polynomial.eval₂_at_apply, Polynomial.eval_zero, hρev]`. Establish `hu` using `hx₀.map φ`. Rewrite `hu` using `[map_add, map_mul, map_sub, map_one, hφ, one_mul, sub_self, add_zero, h1]`. Conclude with `not_isUnit_zero hu`.

Take `⟨t, ht⟩` from `H ψ hne`. Use `⟨J₀ᵀ⁻¹ * (v + algebraMap F R t • w), hcond _ (hcF t), ?_⟩` and prove the remaining obligations. Rewrite `ht` using `[hev]`. Then use the resulting hypothesis.
-/
theorem exists_conj_skew_det_unit_of_avoidance :
  ∀ {F R : Type} [Field F] [CommRing R] [Algebra F R] [Invertible (2 : R)] (c : R →+* R), (∀ r, c (c r) = r) → (∀ t : F, c (algebraMap F R t) = algebraMap F R t) → ∀ (e : R), (∀ ψ : Polynomial R, (∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0) → ∃ t : F, IsUnit (e * ψ.eval (algebraMap F R t) + (1 - e))) → ∀ (ρ : R), IsUnit ρ → c ρ = -ρ → ∀ {n : ℕ} (J₀ : Matrix (Fin n) (Fin n) R) (ε : ℤˣ), (J₀.map c)ᵀ = ((ε : ℤ) : R) • J₀ → IsUnit J₀.det → ∀ (D C x₀ : Matrix (Fin n) (Fin n) R), IsUnit (e * (D + C * x₀).det + (1 - e)) → ∃ x : Matrix (Fin n) (Fin n) R, xᵀ * J₀ + J₀ * x.map c = 0 ∧ IsUnit (e * (D + C * x).det + (1 - e)) := by
  intro F R _ _ _ _ c hcc hcF e H ρ hρ hcρ n J₀ ε hJ hdet D C x₀ hx₀
  obtain ⟨e', he'⟩ : ∃ a : R, a = ((ε : ℤ) : R) := ⟨_, rfl⟩
  rw [← he'] at hJ
  have hee : e' * e' = 1 := by
    rw [he', ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hce : c e' = e' := by rw [he']; exact map_intCast c _
  have h2 : (2 : R) * ⅟2 = 1 := mul_invOf_self 2
  have hc2 : c (⅟2 : R) = ⅟2 := by
    have h1 : c (⅟2 : R) * 2 = 1 := by
      have := congrArg c (invOf_mul_self (2 : R))
      rwa [map_mul, map_ofNat, map_one] at this
    calc c (⅟2 : R) = c (⅟2) * (2 * ⅟2) := by rw [h2, mul_one]
      _ = ⅟2 := by rw [← mul_assoc, h1, one_mul]
  obtain ⟨r, hr'⟩ : ∃ a : R, a = ↑hρ.unit⁻¹ := ⟨_, rfl⟩
  have hr : ρ * r = 1 := by rw [hr']; exact hρ.mul_val_inv
  have hcr : c r = -r := by
    have h1 : c r * (-ρ) = 1 := by rw [← hcρ, ← map_mul, mul_comm, hr, map_one]
    linear_combination (-r) * h1 + (-c r) * hr
  have hKdet : IsUnit (J₀ᵀ).det := by rw [Matrix.det_transpose]; exact hdet
  have hLK : J₀ᵀ⁻¹ * J₀ᵀ = 1 := Matrix.nonsing_inv_mul _ hKdet
  have hLtJ : (J₀ᵀ⁻¹)ᵀ * J₀ = 1 := by
    have : J₀ * (J₀ᵀ⁻¹)ᵀ = 1 := by
      have := congrArg Matrix.transpose hLK
      rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
    exact mul_eq_one_comm.mp this
  have hJLc : J₀ * (J₀ᵀ⁻¹).map c = e' • 1 := by
    have h1 : (J₀ᵀ⁻¹).map c * (e' • J₀) = 1 := by
      have := congrArg c.mapMatrix hLK
      rw [map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.transpose_map, hJ] at this
      exact this
    have h3 : (e' • J₀) * (J₀ᵀ⁻¹).map c = 1 := mul_eq_one_comm.mp h1
    rw [Matrix.smul_mul] at h3
    calc J₀ * (J₀ᵀ⁻¹).map c = (e' * e') • (J₀ * (J₀ᵀ⁻¹).map c) := by rw [hee, one_smul]
      _ = e' • (e' • (J₀ * (J₀ᵀ⁻¹).map c)) := by rw [mul_smul]
      _ = e' • 1 := by rw [h3]
  obtain ⟨M₀, hM₀⟩ : ∃ M : Matrix (Fin n) (Fin n) R, M = J₀ᵀ * x₀ := ⟨_, rfl⟩
  obtain ⟨v, hv'⟩ : ∃ M : Matrix (Fin n) (Fin n) R,
      M = (⅟2 : R) • (M₀ - Matrix.of fun i j => e' * c (M₀ j i)) := ⟨_, rfl⟩
  obtain ⟨w, hw'⟩ : ∃ M : Matrix (Fin n) (Fin n) R,
      M = (r * ⅟2) • (M₀ + Matrix.of fun i j => e' * c (M₀ j i)) := ⟨_, rfl⟩
  have hv : ∀ i j, v j i + e' * c (v i j) = 0 := by
    intro i j
    simp only [hv', Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, smul_eq_mul, map_mul,
      map_sub, hc2, hce, hcc]
    linear_combination (-(⅟2 : R) * M₀ j i) * hee
  have hw : ∀ i j, w j i + e' * c (w i j) = 0 := by
    intro i j
    simp only [hw', Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, smul_eq_mul, map_mul,
      map_add, hc2, hce, hcc, hcr]
    linear_combination (-(r * ⅟2) * M₀ j i) * hee
  have hsum : v + ρ • w = M₀ := by
    ext i j
    simp only [hv', hw', Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply,
      smul_eq_mul]
    linear_combination ((⅟2 : R) * (M₀ i j + e' * c (M₀ j i))) * hr + M₀ i j * h2
  have hcond : ∀ s, c s = s →
      (J₀ᵀ⁻¹ * (v + s • w))ᵀ * J₀ + J₀ * (J₀ᵀ⁻¹ * (v + s • w)).map c = 0 := by
    intro s hs
    have e1 : (J₀ᵀ⁻¹ * (v + s • w))ᵀ * J₀ = (v + s • w)ᵀ := by
      rw [Matrix.transpose_mul, Matrix.mul_assoc, hLtJ, Matrix.mul_one]
    have e2 : J₀ * (J₀ᵀ⁻¹ * (v + s • w)).map c = e' • (v + s • w).map c := by
      rw [Matrix.map_mul, ← Matrix.mul_assoc, hJLc, Matrix.smul_mul, Matrix.one_mul]
    rw [e1, e2]
    ext i j
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply,
      smul_eq_mul, map_add, map_mul, hs, Matrix.zero_apply]
    linear_combination hv i j + s * hw i j
  obtain ⟨ψ, hψ⟩ : ∃ p : Polynomial R, p = ((D + C * J₀ᵀ⁻¹ * v).map Polynomial.C +
      (Polynomial.X : Polynomial R) • (C * J₀ᵀ⁻¹ * w).map Polynomial.C).det := ⟨_, rfl⟩
  have hev : ∀ s, ψ.eval s = (D + C * (J₀ᵀ⁻¹ * (v + s • w))).det := by
    intro s
    have hre : D + C * (J₀ᵀ⁻¹ * (v + s • w)) = (D + C * J₀ᵀ⁻¹ * v) + s • (C * J₀ᵀ⁻¹ * w) := by
      simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc, add_assoc]
    rw [hre, hψ, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C]
  have hρev : ψ.eval ρ = (D + C * x₀).det := by
    rw [hev, hsum, hM₀, ← Matrix.mul_assoc J₀ᵀ⁻¹, hLK, Matrix.one_mul]
  have hne : ∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0 := by
    intro Ω _ φ hφ h0
    have h1 := congrArg (Polynomial.eval (φ ρ)) h0
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, Polynomial.eval_zero, hρev] at h1
    have hu := hx₀.map φ
    rw [map_add, map_mul, map_sub, map_one, hφ, one_mul, sub_self, add_zero, h1] at hu
    exact not_isUnit_zero hu
  obtain ⟨t, ht⟩ := H ψ hne
  refine ⟨J₀ᵀ⁻¹ * (v + algebraMap F R t • w), hcond _ (hcF t), ?_⟩
  rwa [hev] at ht

end GlobalTheory
