import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
import Formalism.DirichletDensity.DirichletDensityProofs.QuadDiscr

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

section
open Polynomial

/- English proof (translation)
Establish `hdisc : discr K = -(d : ℤ)` using `Formalism.HF.quadDiscr K (-(d : ℤ)) x (by push_cast; exact hx) hadj ((Nat.prime_iff_prime_int.mp hd).neg.squarefree) (by omega)`. Use `⟨hdisc, ?_⟩` and prove the remaining obligations. Establish `hN : (differentIdeal ℤ (𝓞 K)).absNorm = d`. Rewrite using `[absNorm_differentIdeal K, hdisc]`. Simplify using the standard rewrite rules.

Establish `hβ2 : β ^ 2 = -(d : 𝓞 K)`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Establish `: ((β ^ 2 : 𝓞 K) : K) = (β : K) ^ 2` using `by push_cast; rfl`. Rewrite using `[this, hβ, hx]`. Use `push_cast`.

Both sides reduce to the same expression. Establish `hadj' : Algebra.adjoin ℚ {algebraMap (𝓞 K) K β} = ⊤`. Establish `h1 : IsAlgebraic ℚ x` using `Algebra.IsAlgebraic.isAlgebraic x`. Establish `h2` using `IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic h1`. Rewrite `h2` using `[hadj]`.

Use `show Algebra.adjoin ℚ {(β : K)} = ⊤`. Rewrite using `[hβ, ← h2]`. Both sides reduce to the same expression. Establish `hmem` using `aeval_derivative_mem_differentIdeal ℤ ℚ K β hadj'`. Establish `hint : IsIntegral ℤ β` using `Algebra.IsIntegral.isIntegral β`.

Take `⟨r, hr⟩` from `minpoly.isIntegrallyClosed_dvd hint (p := X ^ 2 + C (d : ℤ)) (by simp [hβ2])`. Establish `h2β : 2 * β ∈ differentIdeal ℤ (𝓞 K)`. Use `congrArg (fun p => aeval β (derivative p)) hr` as an intermediate fact. Simplify using `only [derivative_X_pow, derivative_C, derivative_mul, map_add, map_mul, minpoly.aeval, zero_mul, add_zero] at this`. Establish `e : (2 : 𝓞 K) * β = aeval β (derivative (minpoly ℤ β)) * aeval β r`.

Rewrite using `[← this]`. Simplify using `[map_ofNat]`. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_right _ _ hmem`. Establish `hdmem : (d : 𝓞 K) ∈ differentIdeal ℤ (𝓞 K)`.

Use `Ideal.absNorm_mem (differentIdeal ℤ (𝓞 K))` as an intermediate fact. Rewrite `this` using `[hN]`. Then use the resulting hypothesis. Establish `hβmem : β ∈ differentIdeal ℤ (𝓞 K)`. Establish `e : β = (d : 𝓞 K) * β - ((d / 2 : ℕ) : 𝓞 K) * (2 * β)`. Establish `h : (d : 𝓞 K) = 2 * ((d / 2 : ℕ) : 𝓞 K) + 1`.

Establish `: d = 2 * (d / 2) + 1` using `by omega`. Conclude with `this` after adjusting the coercions. Take the linear combination `(-β) * h`. Rewrite using `[e]`. Conclude with `Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hdmem) (Ideal.mul_mem_left _ _ h2β)`.

Establish `hle : span {β} ≤ differentIdeal ℤ (𝓞 K)`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hβmem`. Take `⟨C, hC⟩` from `Ideal.dvd_iff_le.mpr hle`. Establish `hNβ : (span {β}).absNorm ^ 2 = d ^ 2`.

Rewrite using `[← map_pow, Ideal.span_singleton_pow, hβ2, Ideal.absNorm_span_singleton]`. Establish `: (-(d : 𝓞 K)) = algebraMap ℤ (𝓞 K) (-(d : ℤ))` using `by simp`. Rewrite using `[this, Algebra.norm_algebraMap, RingOfIntegers.rank, hrank]`. Simplify using `[Int.natAbs_pow]`. Establish `hNβ' : (span {β}).absNorm = d`.

Conclude with `Nat.pow_left_injective (n := 2) (by norm_num) hNβ`. Establish `hC1 : C.absNorm = 1`. Use `congrArg Ideal.absNorm hC` as an intermediate fact. Rewrite `this` using `[map_mul, hNβ', hN]`. Conclude with `Nat.eq_of_mul_eq_mul_left hd.pos (by rw [mul_one]; exact this.symm)`.

Rewrite `hC1` using `[Ideal.absNorm_eq_one_iff]`. Rewrite using `[hC, hC1, Ideal.mul_top]`.
-/
private theorem diffQuadK (K : Type) [Field K] [NumberField K] (d : ℕ) (hd : d.Prime) (hd4 : d % 4 = 3)
    (x : K) (hx : x ^ 2 = -(d : K)) (hadj : IntermediateField.adjoin ℚ {x} = ⊤)
    (hrank : Module.finrank ℚ K = 2) (β : 𝓞 K) (hβ : (β : K) = x) :
    discr K = -(d : ℤ) ∧ differentIdeal ℤ (𝓞 K) = span {β} := by
  have hdisc : discr K = -(d : ℤ) :=
    Formalism.HF.quadDiscr K (-(d : ℤ)) x (by push_cast; exact hx) hadj
      ((Nat.prime_iff_prime_int.mp hd).neg.squarefree) (by omega)
  refine ⟨hdisc, ?_⟩
  have hN : (differentIdeal ℤ (𝓞 K)).absNorm = d := by
    rw [absNorm_differentIdeal K, hdisc]; simp
  have hβ2 : β ^ 2 = -(d : 𝓞 K) := by
    apply RingOfIntegers.ext
    have : ((β ^ 2 : 𝓞 K) : K) = (β : K) ^ 2 := by push_cast; rfl
    rw [this, hβ, hx]
    push_cast; rfl
  have hadj' : Algebra.adjoin ℚ {algebraMap (𝓞 K) K β} = ⊤ := by
    have h1 : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
    have h2 := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic h1
    rw [hadj] at h2
    show Algebra.adjoin ℚ {(β : K)} = ⊤
    rw [hβ, ← h2]
    rfl
  have hmem := aeval_derivative_mem_differentIdeal ℤ ℚ K β hadj'
  have hint : IsIntegral ℤ β := Algebra.IsIntegral.isIntegral β
  obtain ⟨r, hr⟩ := minpoly.isIntegrallyClosed_dvd hint (p := X ^ 2 + C (d : ℤ))
    (by simp [hβ2])
  have h2β : 2 * β ∈ differentIdeal ℤ (𝓞 K) := by
    have := congrArg (fun p => aeval β (derivative p)) hr
    simp only [derivative_X_pow, derivative_C, derivative_mul, map_add, map_mul,
      minpoly.aeval, zero_mul, add_zero] at this
    have e : (2 : 𝓞 K) * β = aeval β (derivative (minpoly ℤ β)) * aeval β r := by
      rw [← this]; simp [map_ofNat]
    rw [e]
    exact Ideal.mul_mem_right _ _ hmem
  have hdmem : (d : 𝓞 K) ∈ differentIdeal ℤ (𝓞 K) := by
    have := Ideal.absNorm_mem (differentIdeal ℤ (𝓞 K))
    rwa [hN] at this
  have hβmem : β ∈ differentIdeal ℤ (𝓞 K) := by
    have e : β = (d : 𝓞 K) * β - ((d / 2 : ℕ) : 𝓞 K) * (2 * β) := by
      have h : (d : 𝓞 K) = 2 * ((d / 2 : ℕ) : 𝓞 K) + 1 := by
        have : d = 2 * (d / 2) + 1 := by omega
        exact_mod_cast this
      linear_combination (-β) * h
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hdmem) (Ideal.mul_mem_left _ _ h2β)
  have hle : span {β} ≤ differentIdeal ℤ (𝓞 K) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hβmem
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hle
  have hNβ : (span {β}).absNorm ^ 2 = d ^ 2 := by
    rw [← map_pow, Ideal.span_singleton_pow, hβ2, Ideal.absNorm_span_singleton]
    have : (-(d : 𝓞 K)) = algebraMap ℤ (𝓞 K) (-(d : ℤ)) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank, hrank]
    simp [Int.natAbs_pow]
  have hNβ' : (span {β}).absNorm = d := by
    exact Nat.pow_left_injective (n := 2) (by norm_num) hNβ
  have hC1 : C.absNorm = 1 := by
    have := congrArg Ideal.absNorm hC
    rw [map_mul, hNβ', hN] at this
    exact Nat.eq_of_mul_eq_mul_left hd.pos (by rw [mul_one]; exact this.symm)
  rw [Ideal.absNorm_eq_one_iff] at hC1
  rw [hC, hC1, Ideal.mul_top]

end

/- English proof (translation)
Introduce `φ H`. Set `x : H.K` to `⟨H.sqd, H.sqd_mem_K⟩`. Establish `hx : x ^ 2 = -(H.d : H.K)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify `H.sqd_sq` using `[x]`.

Establish `hint : IsIntegral ℤ x`. Use `IsIntegral.of_pow (n := 2) (by norm_num) ?_` and prove the remaining obligations. Rewrite using `[hx]`. Conclude with `(isIntegral_natCast H.d).neg`. Establish `hadj : IntermediateField.adjoin ℚ {x} = ⊤`.

Establish `h' : IntermediateField.lift (@IntermediateField.adjoin ℚ _ H.K _ H.K.algebra' {x}) = IntermediateField.lift (⊤ : @IntermediateField ℚ H.K _ _ H.K.algebra')`. Rewrite using `[IntermediateField.lift_adjoin, IntermediateField.lift_top, Set.image_singleton]`. Both sides reduce to the same expression. Establish `key` using `IntermediateField.lift_injective H.K h'`. Apply the tactic sequence `convert key <;> exact Subsingleton.elim _ _`.

Take `⟨β, hβ⟩ : ∃ β : 𝓞 H.K, (β : H.K) = x` from `⟨⟨x, hint⟩, rfl⟩`. Take `⟨hd, hK⟩` from `diffQuadK H.K H.d H.d_prime H.d_mod_four x hx hadj H.finrank_K β hβ`. Establish `hmap : (differentIdeal ℤ (𝓞 H.K)).map (algebraMap (𝓞 H.K) (𝓞 H.E)) = span {algebraMap (𝓞 H.K) (𝓞 H.E) β}`. Rewrite using `[hK, Ideal.map_span, Set.image_singleton]`. Use `⟨by rw [hd]; simp, algebraMap (𝓞 H.K) (𝓞 H.E) β, ?_, hmap, ?_⟩` and prove the remaining obligations.

Use `show ((β : H.K) : H.E) = H.sqd`. Rewrite using `[hβ]`. Rewrite using `[← hmap]`. Conclude with `differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 H.K) (𝓞 H.E)`.
-/
theorem UpperTheory.HF.discr_K :
    ∀ {φ : Frame} (H : HostAx φ), (discr H.K).natAbs = H.d ∧ ∃ s : 𝓞 H.E, (s : H.E) = H.sqd ∧ (differentIdeal ℤ (𝓞 H.K)).map (algebraMap (𝓞 H.K) (𝓞 H.E)) = span {s} ∧ differentIdeal ℤ (𝓞 H.E) = differentIdeal (𝓞 H.K) (𝓞 H.E) * span {s} := by
  intro φ H
  let x : H.K := ⟨H.sqd, H.sqd_mem_K⟩
  have hx : x ^ 2 = -(H.d : H.K) := by
    apply Subtype.ext
    simpa [x] using H.sqd_sq
  have hint : IsIntegral ℤ x := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hx]
    exact (isIntegral_natCast H.d).neg
  have hadj : IntermediateField.adjoin ℚ {x} = ⊤ := by
    have h' : IntermediateField.lift (@IntermediateField.adjoin ℚ _ H.K _ H.K.algebra' {x}) =
        IntermediateField.lift (⊤ : @IntermediateField ℚ H.K _ _ H.K.algebra') := by
      rw [IntermediateField.lift_adjoin, IntermediateField.lift_top, Set.image_singleton]
      rfl
    have key := IntermediateField.lift_injective H.K h'
    convert key <;> exact Subsingleton.elim _ _
  obtain ⟨β, hβ⟩ : ∃ β : 𝓞 H.K, (β : H.K) = x := ⟨⟨x, hint⟩, rfl⟩
  obtain ⟨hd, hK⟩ := diffQuadK H.K H.d H.d_prime H.d_mod_four x hx hadj H.finrank_K β hβ
  have hmap : (differentIdeal ℤ (𝓞 H.K)).map (algebraMap (𝓞 H.K) (𝓞 H.E)) =
      span {algebraMap (𝓞 H.K) (𝓞 H.E) β} := by
    rw [hK, Ideal.map_span, Set.image_singleton]
  refine ⟨by rw [hd]; simp, algebraMap (𝓞 H.K) (𝓞 H.E) β, ?_, hmap, ?_⟩
  · show ((β : H.K) : H.E) = H.sqd
    rw [hβ]
  · rw [← hmap]
    exact differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 H.K) (𝓞 H.E)
