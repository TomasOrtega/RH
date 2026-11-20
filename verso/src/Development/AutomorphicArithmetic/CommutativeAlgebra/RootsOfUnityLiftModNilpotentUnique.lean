import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot

noncomputable section
open IsLocalRing UpperTheory.Et

/- English proof (translation)
Establish `hxq : IsUnit (x ^ q)`. Establish `h` using `IsNilpotent.isUnit_add_one hx`. Simplify using `using h`. Establish `hxu : IsUnit x` using `(isUnit_pow_iff hq0).1 hxq`. Establish `h2 : Polynomial.aeval x (Polynomial.derivative (Polynomial.X ^ q - 1 : Polynomial ℤ)) = (q : S) * x ^ (q - 1)`.

Simplify using `[Polynomial.derivative_X_pow]`. Rewrite using `[h2]`. Conclude with `hq.mul (hxu.pow _)`.
-/
private theorem isUnit_aeval_derivative {S : Type} [CommRing S] {q : ℕ} (hq : IsUnit (q : S)) (hq0 : q ≠ 0)
    {x : S} (hx : IsNilpotent (x ^ q - 1)) :
    IsUnit (Polynomial.aeval x (Polynomial.derivative (Polynomial.X ^ q - 1 : Polynomial ℤ))) := by
  have hxq : IsUnit (x ^ q) := by
    have h := IsNilpotent.isUnit_add_one hx
    simpa using h
  have hxu : IsUnit x := (isUnit_pow_iff hq0).1 hxq
  have h2 : Polynomial.aeval x (Polynomial.derivative (Polynomial.X ^ q - 1 : Polynomial ℤ))
      = (q : S) * x ^ (q - 1) := by
    simp [Polynomial.derivative_X_pow]
  rw [h2]
  exact hq.mul (hxu.pow _)

/- English proof (translation)
Introduce `S _ q hq`. Distinguish the cases in `hq0 : q = 0`. Substitute `hq0` using the available equality. Establish `h01 : (0 : S) = 1` using `by simpa using hq`. Establish `: Subsingleton S` using `subsingleton_of_zero_eq_one h01`.

Conclude with `⟨fun x _ => ⟨x, Subsingleton.elim _ _, by simp⟩, fun x y _ _ _ => Subsingleton.elim _ _⟩`. Use `⟨fun x hx => ?_, fun x y hx hy hxy => ?_⟩` and prove the remaining obligations. Take `⟨y, ⟨hy1, hy2⟩, -⟩` from `Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero (P := (Polynomial.X ^ q - 1 : Polynomial ℤ)) (x := x) (by simpa using hx) (isUnit_aeval_derivative hq hq0 hx)`. Use `⟨y, ?_, hy1⟩` and prove the remaining obligations. Simplify `hy2` using `[sub_eq_zero]`.

Establish `hx' : IsNilpotent (x ^ q - 1)` using `by simp [hx]`. Establish `h` using `Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero (P := (Polynomial.X ^ q - 1 : Polynomial ℤ)) (x := x) (by simpa using hx') (isUnit_aeval_derivative hq hq0 hx')`. Conclude with `h.unique ⟨by simp, by simp [hx]⟩ ⟨hxy, by simp [hy]⟩`.
-/
theorem UpperTheory.roots_of_unity_lift_mod_nilpotent_unique :
    ∀ (S : Type) [CommRing S] (q : ℕ), IsUnit (q : S) → (∀ x : S, IsNilpotent (x ^ q - 1) → ∃ y : S, y ^ q = 1 ∧ IsNilpotent (x - y)) ∧
      ∀ x y : S, x ^ q = 1 → y ^ q = 1 → IsNilpotent (x - y) → x = y := by
  intro S _ q hq
  by_cases hq0 : q = 0
  · subst hq0
    have h01 : (0 : S) = 1 := by simpa using hq
    have : Subsingleton S := subsingleton_of_zero_eq_one h01
    exact ⟨fun x _ => ⟨x, Subsingleton.elim _ _, by simp⟩, fun x y _ _ _ => Subsingleton.elim _ _⟩
  refine ⟨fun x hx => ?_, fun x y hx hy hxy => ?_⟩
  · obtain ⟨y, ⟨hy1, hy2⟩, -⟩ := Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero
      (P := (Polynomial.X ^ q - 1 : Polynomial ℤ)) (x := x) (by simpa using hx)
      (isUnit_aeval_derivative hq hq0 hx)
    refine ⟨y, ?_, hy1⟩
    simpa [sub_eq_zero] using hy2
  · have hx' : IsNilpotent (x ^ q - 1) := by simp [hx]
    have h := Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero
      (P := (Polynomial.X ^ q - 1 : Polynomial ℤ)) (x := x) (by simpa using hx')
      (isUnit_aeval_derivative hq hq0 hx')
    exact h.unique ⟨by simp, by simp [hx]⟩ ⟨hxy, by simp [hy]⟩

end
