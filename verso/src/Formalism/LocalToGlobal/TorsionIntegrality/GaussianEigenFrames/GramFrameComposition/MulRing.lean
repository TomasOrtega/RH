import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementB

noncomputable section

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.H (cmL CmOK)
open Formalism.L2.Th1.CM (omegaK)

namespace GramFrameMultiplicativityLemmas

/- English proof (translation)
Establish `hs : 0 < Real.sqrt d` using `Real.sqrt_pos.mpr (by exact_mod_cast hd)`. Establish `him` using `congrArg Complex.im h`. Establish `hre` using `congrArg Complex.re h`. Simplify using `at him hre`. Use `⟨hre, ?_⟩` and prove the remaining obligations.

Break down `him with h1 | h1` into its components or cases. Conclude with `h1`. Conclude with `absurd h1 (by positivity)`.
-/
theorem indep_sqrt {d : ℕ} (hd : 0 < d) (P Q : ℤ)
    (h : (P : ℂ) + (Q : ℂ) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) = 0) : P = 0 ∧ Q = 0 := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  refine ⟨hre, ?_⟩
  rcases him with h1 | h1
  · exact h1
  · exact absurd h1 (by positivity)

/- English proof (translation)
Establish `h : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = (d : ℂ)`. Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]`. Simplify using the standard rewrite rules. Take the linear combination `Complex.I * Complex.I * h + (d : ℂ) * Complex.I_mul_I`.
-/
theorem sqrt_sq (d : ℕ) :
    (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) = -(d : ℂ) := by
  have h : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = (d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]; simp
  linear_combination Complex.I * Complex.I * h + (d : ℂ) * Complex.I_mul_I

/- English proof (translation)
Establish `h1` using `hOK.1`. Establish `h8` using `hOK.2.2.1`. Break down `Int.even_or_odd b with ⟨k, hk⟩ | h` into its components or cases. It suffices to derive a contradiction. Establish `h2 : (d : ℤ) = 4 * ((a : ℤ) * c - k * k)`.

Rewrite `h1` using `[hk]`. Take the linear combination `(-1 : ℤ) * h1`. Generalize the expression as in `(a : ℤ) * c - k * k = X at h2`. Use linear arithmetic over natural numbers and integers. Conclude with `h`.
-/
theorem odd_b {a : ℕ} {b c : ℤ} {d : ℕ} (hOK : CmOK a b c d) : Odd b := by
  have h1 := hOK.1
  have h8 := hOK.2.2.1
  rcases Int.even_or_odd b with ⟨k, hk⟩ | h
  · exfalso
    have h2 : (d : ℤ) = 4 * ((a : ℤ) * c - k * k) := by
      rw [hk] at h1
      linear_combination (-1 : ℤ) * h1
    generalize (a : ℤ) * c - k * k = X at h2
    omega
  · exact h

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨r, hr, hrg⟩` from `Nat.exists_prime_and_dvd hne`. Establish `hg : (r : ℤ) ∣ (Int.gcd (a : ℤ) (Int.gcd b c : ℤ) : ℤ)` using `by exact_mod_cast hrg`. Establish `h1 : (r : ℤ) ∣ (a : ℤ)` using `hg.trans (Int.gcd_dvd_left _ _)`. Establish `h2 : (r : ℤ) ∣ (Int.gcd b c : ℤ)` using `hg.trans (Int.gcd_dvd_right _ _)`.

Establish `h3 : (r : ℤ) ∣ b` using `h2.trans (Int.gcd_dvd_left _ _)`. Establish `h4 : (r : ℤ) ∣ c` using `h2.trans (Int.gcd_dvd_right _ _)`. Take `⟨a', ha'⟩` from `h1`. Take `⟨b', hb'⟩` from `h3`. Take `⟨c', hc'⟩` from `h4`.

Establish `h0` using `hOK.1`. Establish `hdv : ((r * r : ℕ) : ℤ) ∣ (d : ℤ)`. Use `⟨4 * a' * c' - b' * b', ?_⟩` and prove the remaining obligations. Rewrite `h0` using `[ha', hb', hc']`. Use `push_cast`.

Take the linear combination `(-1 : ℤ) * h0`. Establish `hdv' : r * r ∣ d` using `by exact_mod_cast hdv`. Establish `hu` using `(Irreducible.squarefree hOK.2.2.2) r hdv'`. Conclude with `hr.one_lt.ne' (Nat.isUnit_iff.mp hu)`.
-/
theorem gcd_one {a : ℕ} {b c : ℤ} {d : ℕ} (hOK : CmOK a b c d) :
    Int.gcd (a : ℤ) (Int.gcd b c : ℤ) = 1 := by
  by_contra hne
  obtain ⟨r, hr, hrg⟩ := Nat.exists_prime_and_dvd hne
  have hg : (r : ℤ) ∣ (Int.gcd (a : ℤ) (Int.gcd b c : ℤ) : ℤ) := by exact_mod_cast hrg
  have h1 : (r : ℤ) ∣ (a : ℤ) := hg.trans (Int.gcd_dvd_left _ _)
  have h2 : (r : ℤ) ∣ (Int.gcd b c : ℤ) := hg.trans (Int.gcd_dvd_right _ _)
  have h3 : (r : ℤ) ∣ b := h2.trans (Int.gcd_dvd_left _ _)
  have h4 : (r : ℤ) ∣ c := h2.trans (Int.gcd_dvd_right _ _)
  obtain ⟨a', ha'⟩ := h1
  obtain ⟨b', hb'⟩ := h3
  obtain ⟨c', hc'⟩ := h4
  have h0 := hOK.1
  have hdv : ((r * r : ℕ) : ℤ) ∣ (d : ℤ) := by
    refine ⟨4 * a' * c' - b' * b', ?_⟩
    rw [ha', hb', hc'] at h0
    push_cast
    linear_combination (-1 : ℤ) * h0
  have hdv' : r * r ∣ d := by exact_mod_cast hdv
  have hu := (Irreducible.squarefree hOK.2.2.2) r hdv'
  exact hr.one_lt.ne' (Nat.isUnit_iff.mp hu)

/- English proof (translation)
Establish `e1` using `Int.gcd_eq_gcd_ab b c`. Establish `e2` using `Int.gcd_eq_gcd_ab (a : ℤ) (Int.gcd b c : ℤ)`. Rewrite `e2` using `[gcd_one hOK]`. Use `set u := Int.gcdA b c`. Use `set v := Int.gcdB b c`.

Use `set u' := Int.gcdA (a : ℤ) (Int.gcd b c : ℤ)`. Use `set v' := Int.gcdB (a : ℤ) (Int.gcd b c : ℤ)`. Establish `hy : y = (a : ℤ) * (y * u') + (y * b) * (u * v') + (y * c) * (v * v')`. Move the coercions through the operations in `at e2`. Take the linear combination `y * e2 + y * v' * e1`.

Rewrite using `[hy]`. Conclude with `dvd_add (dvd_add (dvd_mul_right _ _) (hb.mul_right _)) (hc.mul_right _)`.
-/
theorem dvd_of_prim {a : ℕ} {b c : ℤ} {d : ℕ} (hOK : CmOK a b c d) (y : ℤ)
    (hb : (a : ℤ) ∣ y * b) (hc : (a : ℤ) ∣ y * c) : (a : ℤ) ∣ y := by
  have e1 := Int.gcd_eq_gcd_ab b c
  have e2 := Int.gcd_eq_gcd_ab (a : ℤ) (Int.gcd b c : ℤ)
  rw [gcd_one hOK] at e2
  set u := Int.gcdA b c
  set v := Int.gcdB b c
  set u' := Int.gcdA (a : ℤ) (Int.gcd b c : ℤ)
  set v' := Int.gcdB (a : ℤ) (Int.gcd b c : ℤ)
  have hy : y = (a : ℤ) * (y * u') + (y * b) * (u * v') + (y * c) * (v * v') := by
    push_cast at e2
    linear_combination y * e2 + y * v' * e1
  rw [hy]
  exact dvd_add (dvd_add (dvd_mul_right _ _) (hb.mul_right _)) (hc.mul_right _)

end GramFrameMultiplicativityLemmas

open GramFrameMultiplicativityLemmas in
/- English proof (translation)
Introduce `a b c d ha hd lam hlam hOK z hz`. Establish `hw1 : (cmL a b d ha hd lam hlam).ω₁ = lam * (a : ℂ)` using `rfl`. Establish `hw2 : (cmL a b d ha hd lam hlam).ω₂ = lam * Formalism.L2.Th1.F.cmTheta b d` using `rfl`. Take `⟨x, y, e1⟩` from `PeriodPair.mem_lattice.mp (hz _ (cmL a b d ha hd lam hlam).ω₁_mem_lattice)`. Take `⟨x', y', e2⟩` from `PeriodPair.mem_lattice.mp (hz _ (cmL a b d ha hd lam hlam).ω₂_mem_lattice)`.

Rewrite `e1`, `e2` using `[hw1, hw2]`. Establish `haC : (a : ℂ) ≠ 0` using `by exact_mod_cast ha.ne'`. Establish `hS` using `sqrt_sq d`. Unfold `Formalism.L2.Th1.F.cmTheta at e1 e2`. Use `set S : ℂ := Complex.I * ((Real.sqrt d : ℝ) : ℂ) with hSdef`.

Establish `f1 : (x : ℂ) * a + y * (((b : ℂ) + S) / 2) = z * a`. Apply `mul_left_cancel₀ hlam` to reduce the goal to its premises. Take the linear combination `e1`. Establish `f2 : (x' : ℂ) * a + y' * (((b : ℂ) + S) / 2) = z * (((b : ℂ) + S) / 2)`. Apply `mul_left_cancel₀ hlam` to reduce the goal to its premises.

Take the linear combination `e2`. Establish `key : (((4 * a * a * x' + 2 * a * y' * b - 2 * x * a * b - y * (b * b - d) : ℤ)) : ℂ) + ((2 * a * y' - 2 * x * a - 2 * y * b : ℤ) : ℂ) * S = 0`. Use `push_cast`. Take the linear combination `4 * (a : ℂ) * f2 - 2 * ((b : ℂ) + S) * f1 + (y : ℂ) * hS`. Take `⟨k1, k2⟩` from `indep_sqrt hd _ _ key`.

Establish `h0` using `hOK.1`. Establish `haZ : (a : ℤ) ≠ 0` using `by exact_mod_cast ha.ne'`. Establish `hb : (a : ℤ) ∣ y * b`. Use `⟨y' - x, ?_⟩` and prove the remaining obligations. Establish `h2 : (2 : ℤ) * (y * b) = 2 * ((a : ℤ) * (y' - x))` using `by linear_combination (-1 : ℤ) * k2`.

Conclude with `mul_left_cancel₀ two_ne_zero h2`. Establish `hc : (a : ℤ) ∣ y * c`. Use `⟨-x', ?_⟩` and prove the remaining obligations. Establish `h2 : (4 * (a : ℤ)) * (y * c) = (4 * (a : ℤ)) * ((a : ℤ) * (-x'))`. Take the linear combination `k1 - b * k2 + y * h0`.

Conclude with `mul_left_cancel₀ (mul_ne_zero four_ne_zero haZ) h2`. Take `⟨y₀, hy₀⟩` from `dvd_of_prim hOK y hb hc`. Take `⟨k, hk⟩` from `odd_b hOK`. Establish `hom : omegaK d = (1 + S) / 2` using `rfl`. Use `⟨x + y₀ * k, y₀, ?_⟩` and prove the remaining obligations.

Rewrite using `[hom]`. Apply `mul_right_cancel₀ haC` to reduce the goal to its premises. Rewrite using `[← f1, hy₀, hk]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem MulRing_proof : MulRing := by
  intro a b c d ha hd lam hlam hOK z hz
  have hw1 : (cmL a b d ha hd lam hlam).ω₁ = lam * (a : ℂ) := rfl
  have hw2 : (cmL a b d ha hd lam hlam).ω₂ = lam * Formalism.L2.Th1.F.cmTheta b d := rfl
  obtain ⟨x, y, e1⟩ := PeriodPair.mem_lattice.mp (hz _ (cmL a b d ha hd lam hlam).ω₁_mem_lattice)
  obtain ⟨x', y', e2⟩ := PeriodPair.mem_lattice.mp (hz _ (cmL a b d ha hd lam hlam).ω₂_mem_lattice)
  rw [hw1, hw2] at e1 e2
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hS := sqrt_sq d
  unfold Formalism.L2.Th1.F.cmTheta at e1 e2
  set S : ℂ := Complex.I * ((Real.sqrt d : ℝ) : ℂ) with hSdef
  have f1 : (x : ℂ) * a + y * (((b : ℂ) + S) / 2) = z * a := by
    apply mul_left_cancel₀ hlam
    linear_combination e1
  have f2 : (x' : ℂ) * a + y' * (((b : ℂ) + S) / 2) = z * (((b : ℂ) + S) / 2) := by
    apply mul_left_cancel₀ hlam
    linear_combination e2
  have key : (((4 * a * a * x' + 2 * a * y' * b - 2 * x * a * b - y * (b * b - d) : ℤ)) : ℂ)
      + ((2 * a * y' - 2 * x * a - 2 * y * b : ℤ) : ℂ) * S = 0 := by
    push_cast
    linear_combination 4 * (a : ℂ) * f2 - 2 * ((b : ℂ) + S) * f1 + (y : ℂ) * hS
  obtain ⟨k1, k2⟩ := indep_sqrt hd _ _ key
  have h0 := hOK.1
  have haZ : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb : (a : ℤ) ∣ y * b := by
    refine ⟨y' - x, ?_⟩
    have h2 : (2 : ℤ) * (y * b) = 2 * ((a : ℤ) * (y' - x)) := by linear_combination (-1 : ℤ) * k2
    exact mul_left_cancel₀ two_ne_zero h2
  have hc : (a : ℤ) ∣ y * c := by
    refine ⟨-x', ?_⟩
    have h2 : (4 * (a : ℤ)) * (y * c) = (4 * (a : ℤ)) * ((a : ℤ) * (-x')) := by
      linear_combination k1 - b * k2 + y * h0
    exact mul_left_cancel₀ (mul_ne_zero four_ne_zero haZ) h2
  obtain ⟨y₀, hy₀⟩ := dvd_of_prim hOK y hb hc
  obtain ⟨k, hk⟩ := odd_b hOK
  have hom : omegaK d = (1 + S) / 2 := rfl
  refine ⟨x + y₀ * k, y₀, ?_⟩
  rw [hom]
  apply mul_right_cancel₀ haC
  rw [← f1, hy₀, hk]
  push_cast
  ring

end Formalism.L2.Th1.GD
