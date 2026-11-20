import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.TraceNilStep

namespace Bl.IdempotentTraceVanishing

/- English proof (translation)
Rewrite using `[Polynomial.aeval_eq_sum_range, Matrix.trace_sum]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.trace_smul]`. Break down `Nat.eq_zero_or_pos i with rfl | hi` into its components or cases. Rewrite using `[hp, zero_smul]`.

Rewrite using `[h i hi, smul_zero]`.
-/
private lemma trace_aeval_eq_zero {K : Type} [Field K] {a : ℕ} (M : Matrix (Fin a) (Fin a) K)
    (h : ∀ m : ℕ, 0 < m → Matrix.trace (M ^ m) = 0) (p : Polynomial K) (hp : p.coeff 0 = 0) :
    Matrix.trace (Polynomial.aeval M p) = 0 := by
  rw [Polynomial.aeval_eq_sum_range, Matrix.trace_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Matrix.trace_smul]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [hp, zero_smul]
  · rw [h i hi, smul_zero]

/- English proof (translation)
Establish `hf : IsIdempotentElem (Matrix.toLin' E)` using `by show Matrix.toLin' E * Matrix.toLin' E = Matrix.toLin' E`. Rewrite using `[Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hE]`. Establish `htf : LinearMap.trace K _ (Matrix.toLin' E) = 0`. Rewrite using `[Matrix.trace_toLin'_eq, ht]`. Establish `h0` using `LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hf htf`.

Conclude with `Matrix.toLin'.injective (by rw [h0, map_zero])`.
-/
private lemma idem_eq_zero {K : Type} [Field K] [CharZero K] {a : ℕ}
    (E : Matrix (Fin a) (Fin a) K) (hE : E * E = E) (ht : Matrix.trace E = 0) : E = 0 := by
  have hf : IsIdempotentElem (Matrix.toLin' E) := by
    show Matrix.toLin' E * Matrix.toLin' E = Matrix.toLin' E
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hE]
  have htf : LinearMap.trace K _ (Matrix.toLin' E) = 0 := by
    rw [Matrix.trace_toLin'_eq, ht]
  have h0 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hf htf
  exact Matrix.toLin'.injective (by rw [h0, map_zero])

/- English proof (translation)
Use `set r : Polynomial K := Polynomial.X * M.charpoly with hr`. Establish `hr0 : r ≠ 0` using `mul_ne_zero Polynomial.X_ne_zero M.charpoly_monic.ne_zero`. Establish `hrM : Polynomial.aeval M r = 0`. Rewrite using `[hr, map_mul, Matrix.aeval_self_charpoly, mul_zero]`. Take `⟨q, hq, hndvd⟩` from `r.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hr0 0`.

Use `set k := r.rootMultiplicity 0 with hk`. Rewrite `hq`, `hndvd` using `[map_zero, sub_zero]`. Establish `hkpos : 0 < k`. Rewrite using `[hk, Polynomial.rootMultiplicity_pos hr0]`. Simplify using `[hr]`.

Establish `hcop : IsCoprime (Polynomial.X ^ k) q` using `((Polynomial.irreducible_X).coprime_iff_not_dvd.2 hndvd).pow_left`. Take `⟨u, v, huv⟩` from `hcop`. Establish `hE : Polynomial.aeval M (u * Polynomial.X ^ k) * Polynomial.aeval M (u * Polynomial.X ^ k) = Polynomial.aeval M (u * Polynomial.X ^ k)`. Establish `h1 : (1 : Matrix (Fin a) (Fin a) K) - Polynomial.aeval M (u * Polynomial.X ^ k) = Polynomial.aeval M (v * q)`. Rewrite using `[sub_eq_iff_eq_add', ← map_add, huv, map_one]`.

Establish `h2 : Polynomial.aeval M (u * Polynomial.X ^ k) * (1 - Polynomial.aeval M (u * Polynomial.X ^ k)) = 0`. Rewrite using `[h1, ← map_mul]`. Establish `: u * Polynomial.X ^ k * (v * q) = (u * v) * r` using `by rw [hq]; ring`. Rewrite using `[this, map_mul, hrM, mul_zero]`. Rewrite `h2` using `[mul_sub, mul_one, sub_eq_zero]`.

Conclude with `h2.symm`. Establish `ht : Matrix.trace (Polynomial.aeval M (u * Polynomial.X ^ k)) = 0`. Apply `trace_aeval_eq_zero M h` to reduce the goal to its premises. Rewrite using `[Polynomial.coeff_mul_X_pow', if_neg (by omega)]`. Establish `hE0` using `idem_eq_zero _ hE ht`.

Use `⟨k, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[huv, map_one, mul_one]`. Use `_ = Polynomial.aeval M (Polynomial.X ^ k * (u * Polynomial.X ^ k + v * q)) := by`. Rewrite using `[map_mul, map_pow, Polynomial.aeval_X]`.

Use `_ = Polynomial.aeval M (Polynomial.X ^ k * (u * Polynomial.X ^ k)) + Polynomial.aeval M (v * r) := by`. Establish `hpoly : Polynomial.X ^ k * (u * Polynomial.X ^ k + v * q) = Polynomial.X ^ k * (u * Polynomial.X ^ k) + v * r` using `by rw [hq]; ring`. Rewrite using `[hpoly, map_add]`. Use `_ = M ^ k * Polynomial.aeval M (u * Polynomial.X ^ k) + Polynomial.aeval M (v * r) := by`. Rewrite using `[map_mul (Polynomial.aeval M) (Polynomial.X ^ k), map_pow, Polynomial.aeval_X]`.

Use `_ = 0 := by rw [hE0, mul_zero, map_mul, hrM, mul_zero, add_zero]`.
-/
private lemma key {K : Type} [Field K] [CharZero K] {a : ℕ} (M : Matrix (Fin a) (Fin a) K)
    (h : ∀ m : ℕ, 0 < m → Matrix.trace (M ^ m) = 0) : IsNilpotent M := by
  classical
  set r : Polynomial K := Polynomial.X * M.charpoly with hr
  have hr0 : r ≠ 0 := mul_ne_zero Polynomial.X_ne_zero M.charpoly_monic.ne_zero
  have hrM : Polynomial.aeval M r = 0 := by
    rw [hr, map_mul, Matrix.aeval_self_charpoly, mul_zero]
  obtain ⟨q, hq, hndvd⟩ := r.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hr0 0
  set k := r.rootMultiplicity 0 with hk
  rw [map_zero, sub_zero] at hq hndvd
  have hkpos : 0 < k := by
    rw [hk, Polynomial.rootMultiplicity_pos hr0]
    simp [hr]
  have hcop : IsCoprime (Polynomial.X ^ k) q :=
    ((Polynomial.irreducible_X).coprime_iff_not_dvd.2 hndvd).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  have hE : Polynomial.aeval M (u * Polynomial.X ^ k) * Polynomial.aeval M (u * Polynomial.X ^ k)
      = Polynomial.aeval M (u * Polynomial.X ^ k) := by
    have h1 : (1 : Matrix (Fin a) (Fin a) K) - Polynomial.aeval M (u * Polynomial.X ^ k)
        = Polynomial.aeval M (v * q) := by
      rw [sub_eq_iff_eq_add', ← map_add, huv, map_one]
    have h2 : Polynomial.aeval M (u * Polynomial.X ^ k) *
        (1 - Polynomial.aeval M (u * Polynomial.X ^ k)) = 0 := by
      rw [h1, ← map_mul]
      have : u * Polynomial.X ^ k * (v * q) = (u * v) * r := by rw [hq]; ring
      rw [this, map_mul, hrM, mul_zero]
    rw [mul_sub, mul_one, sub_eq_zero] at h2
    exact h2.symm
  have ht : Matrix.trace (Polynomial.aeval M (u * Polynomial.X ^ k)) = 0 := by
    apply trace_aeval_eq_zero M h
    rw [Polynomial.coeff_mul_X_pow', if_neg (by omega)]
  have hE0 := idem_eq_zero _ hE ht
  refine ⟨k, ?_⟩
  calc M ^ k = M ^ k * Polynomial.aeval M (u * Polynomial.X ^ k + v * q) := by
        rw [huv, map_one, mul_one]
    _ = Polynomial.aeval M (Polynomial.X ^ k * (u * Polynomial.X ^ k + v * q)) := by
        rw [map_mul, map_pow, Polynomial.aeval_X]
    _ = Polynomial.aeval M (Polynomial.X ^ k * (u * Polynomial.X ^ k)) + Polynomial.aeval M (v * r) := by
        have hpoly : Polynomial.X ^ k * (u * Polynomial.X ^ k + v * q)
            = Polynomial.X ^ k * (u * Polynomial.X ^ k) + v * r := by rw [hq]; ring
        rw [hpoly, map_add]
    _ = M ^ k * Polynomial.aeval M (u * Polynomial.X ^ k) + Polynomial.aeval M (v * r) := by
        rw [map_mul (Polynomial.aeval M) (Polynomial.X ^ k), map_pow, Polynomial.aeval_X]
    _ = 0 := by rw [hE0, mul_zero, map_mul, hrM, mul_zero, add_zero]

/- English proof (translation)
Introduce `K _ _ a M h`. Conclude with `key M h`.
-/
theorem goal1 :
  PI.SSAscent.UnitaryGroupMassFormula.TraceNilStep := by
  intro K _ _ a M h
  exact key M h

end Bl.IdempotentTraceVanishing
