import Mathlib

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `J using Finset.induction_on with`. Consider the case `empty => exact ⟨fun _ => 0, x, by simp, by simp⟩`. Consider the case `@insert j J hj ih`. Take `⟨m, y, hxy, hy⟩` from `ih`. Establish `hy0 : y ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hx (by simpa using hxy)`. Distinguish the cases in `hp : Prime (π j)`. Take `⟨y', hy', hnd⟩` from `(FiniteMultiplicity.of_not_isUnit hp.not_unit hy0).exists_eq_pow_mul_and_not_dvd`. Use `⟨Function.update m j (multiplicity (π j) y), y', ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.prod_insert hj, Function.update_self]`. Establish `hJ : ∏ i ∈ J, π i ^ Function.update m j (multiplicity (π j) y) i = ∏ i ∈ J, π i ^ m i`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (by rintro rfl; exact hj hi)]`. Rewrite using `[hJ, hxy]`.

Use `conv_lhs => rw [hy']`. Expand and normalize the polynomial expressions, which then agree. Introduce `i hi hpi hdvd`. Break down `Finset.mem_insert.mp hi with rfl | hi` into its components or cases. Conclude with `hnd hdvd`.

Conclude with `hy i hi hpi (hdvd.trans (Dvd.intro_left _ hy'.symm))`. Use `⟨Function.update m j 0, y, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.prod_insert hj, Function.update_self, pow_zero, one_mul]`. Rewrite using `[hxy]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (by rintro rfl; exact hj hi)]`. Introduce `i hi hpi hdvd`. Break down `Finset.mem_insert.mp hi with rfl | hi` into its components or cases. Conclude with `hp hpi`.

Conclude with `hy i hi hpi hdvd`.
-/
theorem strip_prime_factors (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] {n : ℕ}
    (π : Fin n → R) (J : Finset (Fin n)) (x : R) (hx : x ≠ 0) :
    ∃ (m : Fin n → ℕ) (y : R), x = y * ∏ j ∈ J, π j ^ m j ∧
      ∀ j ∈ J, Prime (π j) → ¬ π j ∣ y := by
  induction J using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, x, by simp, by simp⟩
  | @insert j J hj ih =>
    obtain ⟨m, y, hxy, hy⟩ := ih
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hx (by simpa using hxy)
    by_cases hp : Prime (π j)
    · obtain ⟨y', hy', hnd⟩ :=
        (FiniteMultiplicity.of_not_isUnit hp.not_unit hy0).exists_eq_pow_mul_and_not_dvd
      refine ⟨Function.update m j (multiplicity (π j) y), y', ?_, ?_⟩
      · rw [Finset.prod_insert hj, Function.update_self]
        have hJ : ∏ i ∈ J, π i ^ Function.update m j (multiplicity (π j) y) i
            = ∏ i ∈ J, π i ^ m i := by
          refine Finset.prod_congr rfl fun i hi => ?_
          rw [Function.update_of_ne (by rintro rfl; exact hj hi)]
        rw [hJ, hxy]
        conv_lhs => rw [hy']
        ring
      · intro i hi hpi hdvd
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hnd hdvd
        · exact hy i hi hpi (hdvd.trans (Dvd.intro_left _ hy'.symm))
    · refine ⟨Function.update m j 0, y, ?_, ?_⟩
      · rw [Finset.prod_insert hj, Function.update_self, pow_zero, one_mul]
        rw [hxy]
        congr 1
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (by rintro rfl; exact hj hi)]
      · intro i hi hpi hdvd
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hp hpi
        · exact hy i hi hpi hdvd

/- English proof (translation)
Introduce `R _ _ _ _ π J x hx` and use `strip_prime_factors R π J x hx`.
-/
theorem strip_prime_factors_target : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] {n : ℕ} (π : Fin n → R) (J : Finset (Fin n)) (x : R), x ≠ 0 → ∃ (m : Fin n → ℕ) (y : R), x = y * ∏ j ∈ J, π j ^ m j ∧ ∀ j ∈ J, Prime (π j) → ¬ π j ∣ y :=
  fun R _ _ _ _ π J x hx => strip_prime_factors R π J x hx

end GlobalTheory
