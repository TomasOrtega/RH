import Mathlib
open scoped Matrix

namespace GlobalTheory

open Polynomial in

/- English proof (translation)
Introduce `F R _ _ _ e he hψ n D C P Q hDPCQ`. Establish `hev : ∀ (s : R) (M : Matrix (Fin n) (Fin n) R[X]), M.det.eval s = (M.map (Polynomial.eval s)).det`. Introduce `s M`. Rewrite using `[← Polynomial.coe_evalRingHom, RingHom.map_det]`. Both sides reduce to the same expression.

Establish `hcoeff : ((1 + (X : R[X]) • D.map Polynomial.C).det).coeff 0 = 1`. Rewrite using `[coeff_zero_eq_eval_zero, hev]`. Establish `: (1 + (X : R[X]) • D.map Polynomial.C).map (Polynomial.eval 0) = 1`. Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h]`.

Rewrite using `[this, Matrix.det_one]`. Use `set ψ : R[X] := (-P).charpoly * (1 + (X : R[X]) • D.map Polynomial.C).det with hψdef`. Establish `hne : ∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0`. Introduce `Ω _ φ _`. Rewrite using `[hψdef, Polynomial.map_mul]`.

Use `mul_ne_zero ?_ ?_` and prove the remaining obligations. Rewrite using `[← Matrix.charpoly_map]`. Conclude with `(Matrix.charpoly_monic _).ne_zero`. Introduce `h`. Establish `h0` using `congrArg (fun f : Polynomial Ω => f.coeff 0) h`.

Simplify using `only [Polynomial.coeff_map, hcoeff, map_one, Polynomial.coeff_zero] at h0`. Conclude with `one_ne_zero h0`. Take `⟨t, ht⟩` from `hψ ψ hne`. Take `⟨s, hs⟩ : ∃ s : R, s = algebraMap F R t` from `⟨_, rfl⟩`. Rewrite `ht` using `[← hs]`.

Take `⟨P', hP2⟩ : ∃ P' : Matrix (Fin n) (Fin n) R, P' = s • (1 : Matrix (Fin n) (Fin n) R) + P` from `⟨_, rfl⟩`. Take `⟨p, hpdef⟩ : ∃ p : R, p = P'.det` from `⟨_, rfl⟩`. Take `⟨q, hqdef⟩ : ∃ q : R, q = (1 + s • D).det` from `⟨_, rfl⟩`. Establish `hψs : ψ.eval s = p * q`. Rewrite using `[hψdef, Polynomial.eval_mul, Matrix.eval_charpoly, hev, hpdef, hqdef, hP2]`.

Use `congr 2`. Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h]`. Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h] <;> ring`.

Rewrite `ht` using `[hψs]`. Take `⟨w, hw⟩` from `ht.exists_right_inv`. Establish `hp : p * (e * q * w) = e`. Take the linear combination `(w - p * q * w) * he + e * hw`. Establish `hq : q * (e * p * w) = e`.

Take the linear combination `(w - p * q * w) * he + e * hw`. Establish `hpow : ∀ k : ℕ, e ^ k * e = e`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ih => rw [pow_succ, mul_assoc, he, ih]`. Use `⟨(e * q * w) • (Q * P'.adjugate), ?_⟩` and prove the remaining obligations. Use `set M : Matrix (Fin n) (Fin n) R := D + C * ((e * q * w) • (Q * P'.adjugate)) with hM`. Establish `hxP : ((e * q * w) • (Q * P'.adjugate)) * P' = e • Q`. Rewrite using `[Matrix.smul_mul, Matrix.mul_assoc, Matrix.adjugate_mul, ← hpdef, Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm (e * q * w) p, hp]`.

Establish `hMP : e • (M * P') = e • (1 + s • D)`. Rewrite using `[hM, Matrix.add_mul, Matrix.mul_assoc, hxP, Matrix.mul_smul, smul_add, smul_smul, he, hP2, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, ← smul_add, add_assoc, hDPCQ, add_comm]`. Establish `hdet` using `congrArg Matrix.det hMP`. Rewrite `hdet` using `[Matrix.det_smul, Matrix.det_smul, Matrix.det_mul, Fintype.card_fin, ← hpdef, ← hqdef]`. Establish `hab : M.det * (e ^ n * p * (e * p * w)) = e`.

Combine the equalities or inequalities in the displayed calculation. Use `isUnit_iff_exists_inv.mpr ⟨e * (e ^ n * p * (e * p * w)) + (1 - e), ?_⟩` and prove the remaining obligations. Take the linear combination `(M.det * (e ^ n * p * (e * p * w)) - M.det - (e ^ n * p * (e * p * w)) + 2) * he + e * hab`.
-/
theorem exists_corner_unit_of_right_inverse :
    ∀ {F R : Type} [Field F] [CommRing R] [Algebra F R] (e : R), e * e = e →
      (∀ ψ : Polynomial R, (∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0) →
        ∃ t : F, IsUnit (e * ψ.eval (algebraMap F R t) + (1 - e))) →
      ∀ {n : ℕ} (D C P Q : Matrix (Fin n) (Fin n) R), D * P + C * Q = 1 →
        ∃ x : Matrix (Fin n) (Fin n) R, IsUnit (e * (D + C * x).det + (1 - e)) := by
  intro F R _ _ _ e he hψ n D C P Q hDPCQ

  have hev : ∀ (s : R) (M : Matrix (Fin n) (Fin n) R[X]),
      M.det.eval s = (M.map (Polynomial.eval s)).det := by
    intro s M
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    rfl
  have hcoeff : ((1 + (X : R[X]) • D.map Polynomial.C).det).coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero, hev]
    have : (1 + (X : R[X]) • D.map Polynomial.C).map (Polynomial.eval 0) = 1 := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [this, Matrix.det_one]
  set ψ : R[X] := (-P).charpoly * (1 + (X : R[X]) • D.map Polynomial.C).det with hψdef
  have hne : ∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0 := by
    intro Ω _ φ _
    rw [hψdef, Polynomial.map_mul]
    refine mul_ne_zero ?_ ?_
    · rw [← Matrix.charpoly_map]
      exact (Matrix.charpoly_monic _).ne_zero
    · intro h
      have h0 := congrArg (fun f : Polynomial Ω => f.coeff 0) h
      simp only [Polynomial.coeff_map, hcoeff, map_one, Polynomial.coeff_zero] at h0
      exact one_ne_zero h0
  obtain ⟨t, ht⟩ := hψ ψ hne
  obtain ⟨s, hs⟩ : ∃ s : R, s = algebraMap F R t := ⟨_, rfl⟩
  rw [← hs] at ht
  obtain ⟨P', hP2⟩ : ∃ P' : Matrix (Fin n) (Fin n) R, P' = s • (1 : Matrix (Fin n) (Fin n) R) + P :=
    ⟨_, rfl⟩
  obtain ⟨p, hpdef⟩ : ∃ p : R, p = P'.det := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q : R, q = (1 + s • D).det := ⟨_, rfl⟩
  have hψs : ψ.eval s = p * q := by
    rw [hψdef, Polynomial.eval_mul, Matrix.eval_charpoly, hev, hpdef, hqdef, hP2]
    congr 2
    · ext i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    · ext i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h] <;> ring
  rw [hψs] at ht
  obtain ⟨w, hw⟩ := ht.exists_right_inv

  have hp : p * (e * q * w) = e := by
    linear_combination (w - p * q * w) * he + e * hw
  have hq : q * (e * p * w) = e := by
    linear_combination (w - p * q * w) * he + e * hw
  have hpow : ∀ k : ℕ, e ^ k * e = e := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_assoc, he, ih]
  refine ⟨(e * q * w) • (Q * P'.adjugate), ?_⟩
  set M : Matrix (Fin n) (Fin n) R := D + C * ((e * q * w) • (Q * P'.adjugate)) with hM
  have hxP : ((e * q * w) • (Q * P'.adjugate)) * P' = e • Q := by
    rw [Matrix.smul_mul, Matrix.mul_assoc, Matrix.adjugate_mul, ← hpdef, Matrix.mul_smul, Matrix.mul_one,
      smul_smul, mul_comm (e * q * w) p, hp]
  have hMP : e • (M * P') = e • (1 + s • D) := by
    rw [hM, Matrix.add_mul, Matrix.mul_assoc, hxP, Matrix.mul_smul, smul_add, smul_smul, he, hP2,
      Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, ← smul_add, add_assoc, hDPCQ, add_comm]
  have hdet := congrArg Matrix.det hMP
  rw [Matrix.det_smul, Matrix.det_smul, Matrix.det_mul, Fintype.card_fin, ← hpdef, ← hqdef] at hdet
  have hab : M.det * (e ^ n * p * (e * p * w)) = e := by
    calc M.det * (e ^ n * p * (e * p * w)) = (e ^ n * (M.det * p)) * (e * p * w) := by ring
      _ = (e ^ n * q) * (e * p * w) := by rw [hdet]
      _ = e ^ n * e := by rw [mul_assoc, hq]
      _ = e := hpow n
  refine isUnit_iff_exists_inv.mpr ⟨e * (e ^ n * p * (e * p * w)) + (1 - e), ?_⟩
  linear_combination (M.det * (e ^ n * p * (e * p * w)) - M.det - (e ^ n * p * (e * p * w)) + 2) * he + e * hab

end GlobalTheory
