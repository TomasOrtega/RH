import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
open UpperHalfPlane CongruenceSubgroup Ad3

namespace GlobalTheory.CompanionTheory.HeckeSum

/- English proof (translation)
Establish `hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / p)) p` using `Complex.isPrimitiveRoot_exp p hp.ne_zero`. Use `set ζ : ℂ := (Complex.exp (2 * Real.pi * Complex.I / p))⁻¹ ^ n with hζ`. Establish `hterm : ∀ b ∈ Finset.range p, Complex.exp (-(2 * Real.pi * Complex.I * n * b / p)) = ζ ^ b`. Introduce `b _`. Rewrite using `[hζ, ← Complex.exp_neg, ← pow_mul, ← Complex.exp_nat_mul]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl hterm]`. Establish `hζp : ζ ^ p = 1`.

Rewrite using `[hζ, ← pow_mul, mul_comm n p, pow_mul, hprim.inv.pow_eq_one, one_pow]`. Use `split_ifs with h`. Establish `h1 : ζ = 1`. Rewrite using `[hζ]`. Conclude with `(hprim.inv.pow_eq_one_iff_dvd n).mpr h`.

Simplify using `[h1]`. Establish `h1 : ζ ≠ 1`. Rewrite using `[hζ]`. Introduce `h1`. Conclude with `h ((hprim.inv.pow_eq_one_iff_dvd n).mp h1)`.

Rewrite using `[geom_sum_eq h1, hζp, sub_self, zero_div]`.
-/
theorem sum_root (p : ℕ) (hp : p.Prime) (n : ℕ) :
    ∑ b ∈ Finset.range p, Complex.exp (-(2 * Real.pi * Complex.I * n * b / p)) =
      if p ∣ n then (p : ℂ) else 0 := by
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / p)) p :=
    Complex.isPrimitiveRoot_exp p hp.ne_zero
  set ζ : ℂ := (Complex.exp (2 * Real.pi * Complex.I / p))⁻¹ ^ n with hζ
  have hterm : ∀ b ∈ Finset.range p,
      Complex.exp (-(2 * Real.pi * Complex.I * n * b / p)) = ζ ^ b := by
    intro b _
    rw [hζ, ← Complex.exp_neg, ← pow_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm]
  have hζp : ζ ^ p = 1 := by
    rw [hζ, ← pow_mul, mul_comm n p, pow_mul, hprim.inv.pow_eq_one, one_pow]
  split_ifs with h
  · have h1 : ζ = 1 := by
      rw [hζ]
      exact (hprim.inv.pow_eq_one_iff_dvd n).mpr h
    simp [h1]
  · have h1 : ζ ≠ 1 := by
      rw [hζ]
      intro h1
      exact h ((hprim.inv.pow_eq_one_iff_dvd n).mp h1)
    rw [geom_sum_eq h1, hζp, sub_self, zero_div]

/- English proof (translation)
Establish `hterm : ∀ n : ℕ, ∑ b ∈ Finset.range p, a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((w b : ℍ) : ℂ)) = if p ∣ n then (p : ℂ) * (a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ) / p)) else 0`. Introduce `n`. Establish `hsplit : ∀ b : ℕ, a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((w b : ℍ) : ℂ)) = a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ) / p) * Complex.exp (-(2 * Real.pi * Complex.I * n * b / p))`. Introduce `b`. Rewrite using `[hw b, mul_assoc (a n), ← Complex.exp_add]`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl fun b _ => hsplit b, ← Finset.mul_sum, sum_root p hp n]`. Apply the tactic sequence `split_ifs <;> ring`. Establish `hL : HasSum (fun n : ℕ => if p ∣ n then (p : ℂ) * (a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ) / p)) else 0) (∑ b ∈ Finset.range p, (f : ℍ → ℂ) (w b))`.

Establish `h` using `hasSum_sum fun b (_ : b ∈ Finset.range p) => hf.exp (w b)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `n`. Conclude with `(hterm n).symm`. Establish `hinj : Function.Injective (fun m : ℕ => p * m)` using `fun x y h => Nat.eq_of_mul_eq_mul_left hp.pos h`.

Establish `hLm : HasSum (fun m : ℕ => (p : ℂ) * (a (p * m) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ)))) (∑ b ∈ Finset.range p, (f : ℍ → ℂ) (w b))`. Establish `h1` using `(hinj.hasSum_iff (f := fun n : ℕ => if p ∣ n then (p : ℂ) * (a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ) / p)) else 0) (a := ∑ b ∈ Finset.range p, (f : ℍ → ℂ) (w b)) ?_).mpr hL`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `m`. Simplify using `only [Function.comp_apply]`.

Rewrite using `[if_pos (dvd_mul_right p m)]`. Use `congr 3`. Rewrite using `[eq_div_iff (Nat.cast_ne_zero.mpr hp.ne_zero)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Introduce `x hx`. Rewrite using `[if_neg]`. Introduce and unpack `⟨m, rfl⟩`. Conclude with `hx ⟨m, rfl⟩`. Establish `h2 : HasSum ((fun m : ℕ => if p ∣ m then a (m / p) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ)) else 0) ∘ (fun n : ℕ => p * n)) ((f : ℍ → ℂ) w')`.

Use `hf.exp w' using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `n`. Simplify using `only [Function.comp_apply]`. Rewrite using `[if_pos (dvd_mul_right p n), Nat.mul_div_cancel_left n hp.pos, hw']`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hw's : HasSum (fun m : ℕ => if p ∣ m then a (m / p) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ)) else 0) ((f : ℍ → ℂ) w')`. Use `(hinj.hasSum_iff ?_).mp h2` and prove the remaining obligations. Introduce `x hx`.

Rewrite using `[if_neg]`. Introduce and unpack `⟨m, rfl⟩`. Conclude with `hx ⟨m, rfl⟩`. Establish `hR` using `((hf.exp z).mul_left (a p)).sub (hw's.mul_left (χ p * (p : ℂ) ^ (k - 1)))`. Establish `key : ∀ m : ℕ, a p * (a m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ))) - χ p * (p : ℂ) ^ (k - 1) * (if p ∣ m then a (m / p) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ)) else 0) = a (p * m) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ( …`.

Introduce `m`. Establish `h` using `he.2.2 p m hp`. Distinguish the cases in `hm : p ∣ m`. Rewrite `h`, the goal using `[if_pos hm]`. Take the linear combination `(Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ))) * h`.

Rewrite `h`, the goal using `[if_neg hm]`. Take the linear combination `(Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ))) * h`. Simplify using `only [key] at hR`. Conclude with `hLm.unique (hR.mul_left (p : ℂ))`.
-/
theorem hecke_sum (k N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N) (k : ℤ)) (a : ℕ → ℂ) (hf : IsForm k N χ f a)
    (he : IsEig k N χ a) (p : ℕ) (hp : p.Prime) (z : ℍ) (w : ℕ → ℍ)
    (hw : ∀ b : ℕ, (w b : ℂ) = ((z : ℂ) - b) / p) (w' : ℍ) (hw' : (w' : ℂ) = p * z) :
    ∑ b ∈ Finset.range p, (f : ℍ → ℂ) (w b) =
      p * (a p * f z - χ p * (p : ℂ) ^ (k - 1) * f w') := by
  have hterm : ∀ n : ℕ, ∑ b ∈ Finset.range p,
      a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((w b : ℍ) : ℂ)) =
      if p ∣ n then (p : ℂ) * (a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ) / p))
      else 0 := by
    intro n
    have hsplit : ∀ b : ℕ,
        a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((w b : ℍ) : ℂ)) =
        a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ) / p) *
          Complex.exp (-(2 * Real.pi * Complex.I * n * b / p)) := by
      intro b
      rw [hw b, mul_assoc (a n), ← Complex.exp_add]
      congr 2
      ring
    rw [Finset.sum_congr rfl fun b _ => hsplit b, ← Finset.mul_sum, sum_root p hp n]
    split_ifs <;> ring
  have hL : HasSum (fun n : ℕ => if p ∣ n then
      (p : ℂ) * (a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ) / p)) else 0)
      (∑ b ∈ Finset.range p, (f : ℍ → ℂ) (w b)) := by
    have h := hasSum_sum fun b (_ : b ∈ Finset.range p) => hf.exp (w b)
    convert h using 1
    funext n
    exact (hterm n).symm
  have hinj : Function.Injective (fun m : ℕ => p * m) := fun x y h =>
    Nat.eq_of_mul_eq_mul_left hp.pos h
  have hLm : HasSum (fun m : ℕ => (p : ℂ) *
      (a (p * m) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ))))
      (∑ b ∈ Finset.range p, (f : ℍ → ℂ) (w b)) := by
    have h1 := (hinj.hasSum_iff (f := fun n : ℕ => if p ∣ n then
      (p : ℂ) * (a n * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ) / p)) else 0)
      (a := ∑ b ∈ Finset.range p, (f : ℍ → ℂ) (w b)) ?_).mpr hL
    · convert h1 using 1
      funext m
      simp only [Function.comp_apply]
      rw [if_pos (dvd_mul_right p m)]
      congr 3
      rw [eq_div_iff (Nat.cast_ne_zero.mpr hp.ne_zero)]
      push_cast
      ring
    · intro x hx
      rw [if_neg]
      rintro ⟨m, rfl⟩
      exact hx ⟨m, rfl⟩
  have h2 : HasSum ((fun m : ℕ => if p ∣ m then
      a (m / p) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ)) else 0) ∘
      (fun n : ℕ => p * n)) ((f : ℍ → ℂ) w') := by
    convert hf.exp w' using 1
    funext n
    simp only [Function.comp_apply]
    rw [if_pos (dvd_mul_right p n), Nat.mul_div_cancel_left n hp.pos, hw']
    congr 2
    push_cast
    ring
  have hw's : HasSum (fun m : ℕ => if p ∣ m then
      a (m / p) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ)) else 0)
      ((f : ℍ → ℂ) w') := by
    refine (hinj.hasSum_iff ?_).mp h2
    intro x hx
    rw [if_neg]
    rintro ⟨m, rfl⟩
    exact hx ⟨m, rfl⟩
  have hR := ((hf.exp z).mul_left (a p)).sub (hw's.mul_left (χ p * (p : ℂ) ^ (k - 1)))
  have key : ∀ m : ℕ, a p * (a m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ))) - χ p * (p : ℂ) ^ (k - 1) *
      (if p ∣ m then a (m / p) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ)) else 0) = a (p * m) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ)) := by
    intro m
    have h := he.2.2 p m hp
    by_cases hm : p ∣ m
    · rw [if_pos hm] at h ⊢
      linear_combination (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ))) * h
    · rw [if_neg hm] at h ⊢
      linear_combination (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (z : ℂ))) * h
  simp only [key] at hR
  exact hLm.unique (hR.mul_left (p : ℂ))

end GlobalTheory.CompanionTheory.HeckeSum
