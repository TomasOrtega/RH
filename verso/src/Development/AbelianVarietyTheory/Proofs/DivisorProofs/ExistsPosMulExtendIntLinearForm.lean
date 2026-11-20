import Mathlib

namespace GlobalTheory

/- English proof (translation)
Take `⟨g, hg⟩` from `(Module.Baer.of_divisible ℚ).extension_property P.subtype P.injective_subtype ((Algebra.linearMap ℤ ℚ).comp f)`. Set `b` to `Module.Free.chooseBasis ℤ F`. Take `⟨⟨d, hd⟩, hint⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) (S := ℚ) (fun i => g (b i))`. Establish `hd0 : d ≠ 0` using `nonZeroDivisors.ne_zero hd`. Use `choose n hn using hint`.

Set `lam : F →ₗ[ℤ] ℤ` to `b.constr ℤ n`. Establish `key : (Algebra.linearMap ℤ ℚ).comp lam = d • g`. Use `b.ext fun i => ?_` and prove the remaining obligations. Simplify `hn i` using `[lam]`. Use `⟨d * d, mul_self_pos.mpr hd0, d • lam, fun x => ?_⟩` and prove the remaining obligations.

Establish `h1` using `LinearMap.congr_fun key x`. Establish `h2` using `LinearMap.congr_fun hg x`. Simplify using `at h1 h2`. Rewrite `h1` using `[h2]`. Establish `h3 : lam x = d * f x` using `by exact_mod_cast h1`.

Simplify using `[h3, mul_assoc]`.
-/
theorem exists_pos_mul_extend_int_linearForm (F : Type) [AddCommGroup F] [Module.Free ℤ F]
    [Module.Finite ℤ F] (P : Submodule ℤ F) (f : P →ₗ[ℤ] ℤ) :
    ∃ c : ℤ, 0 < c ∧ ∃ lam : F →ₗ[ℤ] ℤ, ∀ x : P, lam x = c * f x := by
  classical
  obtain ⟨g, hg⟩ := (Module.Baer.of_divisible ℚ).extension_property P.subtype
    P.injective_subtype ((Algebra.linearMap ℤ ℚ).comp f)
  let b := Module.Free.chooseBasis ℤ F
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (S := ℚ) (fun i => g (b i))
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  choose n hn using hint
  let lam : F →ₗ[ℤ] ℤ := b.constr ℤ n
  have key : (Algebra.linearMap ℤ ℚ).comp lam = d • g := by
    refine b.ext fun i => ?_
    simpa [lam] using hn i
  refine ⟨d * d, mul_self_pos.mpr hd0, d • lam, fun x => ?_⟩
  have h1 := LinearMap.congr_fun key x
  have h2 := LinearMap.congr_fun hg x
  simp at h1 h2
  rw [h2] at h1
  have h3 : lam x = d * f x := by exact_mod_cast h1
  simp [h3, mul_assoc]

end GlobalTheory
