import Mathlib
open Complex Filter Topology

namespace GlobalTheory

/- English proof (translation)
Unfold `LSeries`. Use `congr 1`. Use function extensionality and compare the values at `n`. Simplify using `only [LSeries.term]`. Use `split_ifs with hn`.

Both sides reduce to the same expression. Establish `hn' : (n : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hn`. Establish `key : (n : ℂ) ^ (((2 * (e : ℝ) + s : ℝ)) : ℂ) = (n : ℂ) ^ (e - 1) * (n : ℂ) ^ ((((e + 1 : ℝ) + s : ℝ)) : ℂ)`. Rewrite using `[← Complex.cpow_natCast, ← Complex.cpow_add _ _ hn']`. Use `congr 1`.

Move the coercions through the operations in `[Nat.cast_sub he]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : (n : ℂ) ^ (e - 1) ≠ 0` using `pow_ne_zero _ hn'`. Establish `h2 : (n : ℂ) ^ ((((e + 1 : ℝ) + s : ℝ)) : ℂ) ≠ 0`. Rewrite using `[Ne, Complex.cpow_eq_zero_iff]`.

The claim follows by propositional logic. Rewrite using `[key]`. Clear the denominators using the available nonvanishing facts.
-/
theorem lseries_shift_twist (e : ℕ) (ψ g : ℕ → ℂ) (s : ℝ) (he : 1 ≤ e) :
    LSeries (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) =
      LSeries (fun n => ψ n * g n) ((e + 1 : ℝ) + s : ℝ) := by
  unfold LSeries
  congr 1
  funext n
  simp only [LSeries.term]
  split_ifs with hn
  · rfl
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have key : (n : ℂ) ^ (((2 * (e : ℝ) + s : ℝ)) : ℂ) =
      (n : ℂ) ^ (e - 1) * (n : ℂ) ^ ((((e + 1 : ℝ) + s : ℝ)) : ℂ) := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hn']
    congr 1
    push_cast [Nat.cast_sub he]
    ring
  have h1 : (n : ℂ) ^ (e - 1) ≠ 0 := pow_ne_zero _ hn'
  have h2 : (n : ℂ) ^ ((((e + 1 : ℝ) + s : ℝ)) : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  rw [key]
  field_simp

end GlobalTheory
