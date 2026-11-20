import Mathlib

open NumberField IsDedekindDomain

namespace GlobalTheory.RootIdeal

/- English proof (translation)
Set `u : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ` to `Units.mk0 J hJ`. Establish `hpos : 0 < orderOf (ClassGroup.mk K u)` using `orderOf_pos _`. Establish `h1 : ClassGroup.mk K (u ^ orderOf (ClassGroup.mk K u)) = 1`. Rewrite using `[map_pow, pow_orderOf_eq_one]`. Rewrite `h1` using `[ClassGroup.mk_eq_one_iff]`.

Take `⟨x, hx⟩` from `h1.principal`. Establish `hJh : ((u ^ orderOf (ClassGroup.mk K u) : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = J ^ orderOf (ClassGroup.mk K u)`. Simplify using `[u]`. Establish `key : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x = J ^ orderOf (ClassGroup.mk K u)`. Rewrite using `[← hJh]`.

Apply `FractionalIdeal.coeToSubmodule_injective` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[FractionalIdeal.coe_spanSingleton, hx]`. Use `⟨_, x, hpos, ?_, key⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Rewrite `key` using `[FractionalIdeal.spanSingleton_zero]`. Conclude with `pow_ne_zero _ hJ key.symm`.
-/
theorem exists_pow_eq_spanSingleton (K : Type) [Field K] [NumberField K]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hJ : J ≠ 0) :
    ∃ (h : ℕ) (x : K), 0 < h ∧ x ≠ 0 ∧
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x = J ^ h := by
  classical
  let u : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ := Units.mk0 J hJ
  have hpos : 0 < orderOf (ClassGroup.mk K u) := orderOf_pos _
  have h1 : ClassGroup.mk K (u ^ orderOf (ClassGroup.mk K u)) = 1 := by
    rw [map_pow, pow_orderOf_eq_one]
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨x, hx⟩ := h1.principal
  have hJh : ((u ^ orderOf (ClassGroup.mk K u) : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = J ^ orderOf (ClassGroup.mk K u) := by
    simp [u]
  have key : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x =
      J ^ orderOf (ClassGroup.mk K u) := by
    rw [← hJh]
    apply FractionalIdeal.coeToSubmodule_injective
    dsimp only
    rw [FractionalIdeal.coe_spanSingleton, hx]
  refine ⟨_, x, hpos, ?_, key⟩
  rintro rfl
  rw [FractionalIdeal.spanSingleton_zero] at key
  exact pow_ne_zero _ hJ key.symm

/- English proof (translation)
Use `set d : ℕ := ∏ v ∈ r.support, (r v).den with hd`. Establish `hdpos : 0 < d` using `Finset.prod_pos (fun v _ => (r v).pos)`. Establish `hdvd : ∀ v, (r v).den ∣ d`. Introduce `v`. Distinguish the cases in `hv : v ∈ r.support`.

Conclude with `Finset.dvd_prod_of_mem _ hv`. Rewrite using `[Finsupp.notMem_support_iff.mp hv]`. Simplify using the standard rewrite rules. Set `e : HeightOneSpectrum (𝓞 K) →₀ ℤ` to `Finsupp.mapRange (fun q : ℚ => q.num * ((d / q.den : ℕ) : ℤ)) (by simp) r`. Establish `he : ∀ v, ((e v : ℤ) : ℚ) = d * r v`.

Introduce `v`. Simplify using `only [e, Finsupp.mapRange_apply]`. Establish `hden : ((r v).den : ℚ) ≠ 0` using `by exact_mod_cast (r v).pos.ne'`. Rewrite using `[Int.cast_mul, Int.cast_natCast, Nat.cast_div (hdvd v) hden]`. Use `conv_rhs => rw [← Rat.num_div_den (r v)]`.

Clear the denominators using the available nonvanishing facts. Use `set J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K := e.prod (fun v n => ((v.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n) with hJdef`. Establish `hJ0 : J ≠ 0`. Rewrite using `[hJdef, Finsupp.prod, Finset.prod_ne_zero_iff]`. Introduce `v _`.

Conclude with `zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)`. Establish `hcount : ∀ v, FractionalIdeal.count K v J = e v` using `fun v => FractionalIdeal.count_finsuppProd K v e`. Take `⟨h, x, hh, hx0, hxJ⟩` from `exists_pow_eq_spanSingleton K J hJ0`. Use `⟨h * d, x, Nat.mul_pos hh hdpos, hx0, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[hxJ, FractionalIdeal.count_pow, hcount, Int.cast_mul, Int.cast_natCast, he]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_count_spanSingleton_eq_mul (K : Type) [Field K] [NumberField K]
    (r : HeightOneSpectrum (𝓞 K) →₀ ℚ) :
    ∃ (n : ℕ) (x : K), 0 < n ∧ x ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 K),
      ((FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x) : ℤ) : ℚ) = n * r v := by
  classical
  set d : ℕ := ∏ v ∈ r.support, (r v).den with hd
  have hdpos : 0 < d := Finset.prod_pos (fun v _ => (r v).pos)
  have hdvd : ∀ v, (r v).den ∣ d := by
    intro v
    by_cases hv : v ∈ r.support
    · exact Finset.dvd_prod_of_mem _ hv
    · rw [Finsupp.notMem_support_iff.mp hv]
      simp
  let e : HeightOneSpectrum (𝓞 K) →₀ ℤ :=
    Finsupp.mapRange (fun q : ℚ => q.num * ((d / q.den : ℕ) : ℤ)) (by simp) r
  have he : ∀ v, ((e v : ℤ) : ℚ) = d * r v := by
    intro v
    simp only [e, Finsupp.mapRange_apply]
    have hden : ((r v).den : ℚ) ≠ 0 := by exact_mod_cast (r v).pos.ne'
    rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div (hdvd v) hden]
    conv_rhs => rw [← Rat.num_div_den (r v)]
    field_simp
  set J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    e.prod (fun v n => ((v.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n)
    with hJdef
  have hJ0 : J ≠ 0 := by
    rw [hJdef, Finsupp.prod, Finset.prod_ne_zero_iff]
    intro v _
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
  have hcount : ∀ v, FractionalIdeal.count K v J = e v := fun v =>
    FractionalIdeal.count_finsuppProd K v e
  obtain ⟨h, x, hh, hx0, hxJ⟩ := exists_pow_eq_spanSingleton K J hJ0
  refine ⟨h * d, x, Nat.mul_pos hh hdpos, hx0, fun v => ?_⟩
  rw [hxJ, FractionalIdeal.count_pow, hcount, Int.cast_mul, Int.cast_natCast, he]
  push_cast
  ring

end GlobalTheory.RootIdeal
