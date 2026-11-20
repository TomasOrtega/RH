import Mathlib

namespace GlobalTheory.InjectiveAlgebraMapTorsionFree

variable (p : ℕ) [Fact (Nat.Prime p)]

/- English proof (translation)
Assume the negation of the conclusion as `hinj`. Establish `hker : RingHom.ker (algebraMap ℤ_[p] D) ≠ ⊥` using `fun h => hinj ((RingHom.injective_iff_ker_eq_bot _).mpr h)`. Take `⟨n, hn⟩` from `PadicInt.ideal_eq_span_pow_p hker`. Establish `hmem : (p : ℤ_[p]) ^ n ∈ RingHom.ker (algebraMap ℤ_[p] D)`. Rewrite using `[hn]`.

Conclude with `Ideal.mem_span_singleton_self _`. Rewrite `hmem` using `[RingHom.mem_ker, map_pow, map_natCast]`. Conclude with `hp (pow_eq_zero_iff'.mp hmem).1`.
-/
theorem algebraMap_injective_of_ne (D : Type) [CommRing D] [IsDomain D] [Algebra ℤ_[p] D]
    (hp : (p : D) ≠ 0) : Function.Injective (algebraMap ℤ_[p] D) := by
  by_contra hinj
  have hker : RingHom.ker (algebraMap ℤ_[p] D) ≠ ⊥ := fun h =>
    hinj ((RingHom.injective_iff_ker_eq_bot _).mpr h)
  obtain ⟨n, hn⟩ := PadicInt.ideal_eq_span_pow_p hker
  have hmem : (p : ℤ_[p]) ^ n ∈ RingHom.ker (algebraMap ℤ_[p] D) := by
    rw [hn]
    exact Ideal.mem_span_singleton_self _
  rw [RingHom.mem_ker, map_pow, map_natCast] at hmem
  exact hp (pow_eq_zero_iff'.mp hmem).1

/- English proof (translation)
The claim follows from `Module.isTorsionFree_iff_algebraMap_injective.mpr h`.
-/
theorem isTorsionFree_of_injective {R S : Type} [CommRing R] [CommRing S] [IsDomain R]
    [IsDomain S] [Algebra R S] (h : Function.Injective (algebraMap R S)) :
    Module.IsTorsionFree R S :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr h

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p), PadicAlgCl.norm_extends]`. Simplify using `using PadicInt.norm_le_one a`.
-/
theorem norm_algebraMap_le (a : ℤ_[p]) : ‖algebraMap ℤ_[p] (PadicAlgCl p) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p), PadicAlgCl.norm_extends]
  simpa using PadicInt.norm_le_one a

/- English proof (translation)
Use `haveI : IsUltrametricDist (PadicAlgCl p) := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (PadicAlgCl.isNonarchimedean p)`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Take `⟨q, hqm, hq⟩` from `hx`. Rewrite `hq` using `[hqm.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum]`.

Simplify using `only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at hq`. Establish `hxn : x ^ q.natDegree = -∑ i ∈ Finset.range q.natDegree, algebraMap ℤ_[p] (PadicAlgCl p) (q.coeff i) * x ^ i` using `eq_neg_of_add_eq_zero_left hq`. Break down `Nat.eq_zero_or_pos q.natDegree with h0 | hn` into its components or cases. Rewrite `hxn` using `[h0]`. Simplify using `at hxn`.

Establish `hx1 : 1 ≤ ‖x‖` using `h.le`. Establish `hle : ‖∑ i ∈ Finset.range q.natDegree, algebraMap ℤ_[p] (PadicAlgCl p) (q.coeff i) * x ^ i‖ ≤ ‖x‖ ^ (q.natDegree - 1)`. Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg (norm_nonneg _) _)` to reduce the goal to its premises. Introduce `i hi`. Rewrite using `[norm_mul, norm_pow]`.

Establish `hi'` using `Finset.mem_range.mp hi`. Combine the equalities or inequalities in the displayed calculation. Establish `h1 : ‖x‖ ^ q.natDegree ≤ ‖x‖ ^ (q.natDegree - 1)`. Rewrite using `[← norm_pow, hxn, norm_neg]`. Conclude with `hle`.

Establish `h2 : ‖x‖ ^ (q.natDegree - 1) < ‖x‖ ^ q.natDegree` using `pow_lt_pow_right₀ h (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_le_one_of_isIntegral (x : PadicAlgCl p) (hx : IsIntegral ℤ_[p] x) : ‖x‖ ≤ 1 := by
  haveI : IsUltrametricDist (PadicAlgCl p) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (PadicAlgCl.isNonarchimedean p)
  by_contra h
  push_neg at h
  obtain ⟨q, hqm, hq⟩ := hx
  rw [hqm.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum] at hq
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at hq
  have hxn : x ^ q.natDegree =
      -∑ i ∈ Finset.range q.natDegree, algebraMap ℤ_[p] (PadicAlgCl p) (q.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_left hq
  rcases Nat.eq_zero_or_pos q.natDegree with h0 | hn
  · rw [h0] at hxn
    simp at hxn
  have hx1 : 1 ≤ ‖x‖ := h.le
  have hle : ‖∑ i ∈ Finset.range q.natDegree, algebraMap ℤ_[p] (PadicAlgCl p) (q.coeff i) * x ^ i‖ ≤
      ‖x‖ ^ (q.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg (norm_nonneg _) _)
    intro i hi
    rw [norm_mul, norm_pow]
    have hi' := Finset.mem_range.mp hi
    calc ‖algebraMap ℤ_[p] (PadicAlgCl p) (q.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (q.natDegree - 1) :=
          mul_le_mul (norm_algebraMap_le p _) (pow_le_pow_right₀ hx1 (by omega))
            (pow_nonneg (norm_nonneg _) _) zero_le_one
      _ = ‖x‖ ^ (q.natDegree - 1) := one_mul _
  have h1 : ‖x‖ ^ q.natDegree ≤ ‖x‖ ^ (q.natDegree - 1) := by
    rw [← norm_pow, hxn, norm_neg]
    exact hle
  have h2 : ‖x‖ ^ (q.natDegree - 1) < ‖x‖ ^ q.natDegree := pow_lt_pow_right₀ h (by omega)
  linarith

/- English proof (translation)
Establish `hM : Function.Injective (algebraMap ℤ_[p] (PadicAlgCl p))`. Apply `algebraMap_injective_of_ne` to reduce the goal to its premises. Conclude with `(Fact.out : p.Prime).ne_zero` after adjusting the coercions. Use `haveI := isTorsionFree_of_injective (algebraMap_injective_of_ne p D hp)`. Use `haveI := isTorsionFree_of_injective hM`.

Set `φ : D →ₐ[ℤ_[p]] PadicAlgCl p` to `IsAlgClosed.lift`. Use `⟨φ.toRingHom, ?_, fun d => ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.injective_iff_ker_eq_bot]`. Apply `Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[p])` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`.

Introduce `a ha`. Rewrite `ha` using `[Ideal.mem_comap, RingHom.mem_ker]`. Establish `: algebraMap ℤ_[p] (PadicAlgCl p) a = 0`. Rewrite using `[← φ.commutes]`. Conclude with `ha`.

Conclude with `(map_eq_zero_iff _ hM).mp this`. Conclude with `norm_le_one_of_isIntegral p _ ((Algebra.IsIntegral.isIntegral d).map φ)`.
-/
theorem exists_injective_norm_le_one (p : ℕ) [Fact (Nat.Prime p)] (D : Type) [CommRing D]
    [IsDomain D] [Algebra ℤ_[p] D] [Module.Finite ℤ_[p] D] (hp : (p : D) ≠ 0) :
    ∃ φ : D →+* PadicAlgCl p, Function.Injective φ ∧ ∀ d : D, ‖φ d‖ ≤ 1 := by
  have hM : Function.Injective (algebraMap ℤ_[p] (PadicAlgCl p)) := by
    apply algebraMap_injective_of_ne
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  haveI := isTorsionFree_of_injective (algebraMap_injective_of_ne p D hp)
  haveI := isTorsionFree_of_injective hM
  let φ : D →ₐ[ℤ_[p]] PadicAlgCl p := IsAlgClosed.lift
  refine ⟨φ.toRingHom, ?_, fun d => ?_⟩
  · rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[p])
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    have : algebraMap ℤ_[p] (PadicAlgCl p) a = 0 := by
      rw [← φ.commutes]; exact ha
    exact (map_eq_zero_iff _ hM).mp this
  · exact norm_le_one_of_isIntegral p _ ((Algebra.IsIntegral.isIntegral d).map φ)

end GlobalTheory.InjectiveAlgebraMapTorsionFree
