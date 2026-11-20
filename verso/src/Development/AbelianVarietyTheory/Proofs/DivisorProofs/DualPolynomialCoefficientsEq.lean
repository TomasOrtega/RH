import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.PolUnitary

/- English proof (translation)
Establish `h : ∀ n : ℕ, 2 * (n * (n - 1) / 2) + n = n * n`. Introduce `n`. Rewrite using `[Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]`. Consider the cases of `n with`. Consider the case `zero => rfl`.

Consider the case `succ m => simp`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `h (i + j)`. Establish `h2` using `h i`. Establish `h3` using `h j`.

Establish `h4 : (i + j - 1) * i + i = (i + j) * i`. Break down `Nat.eq_zero_or_pos i with rfl | hi` into its components or cases. Simplify using the standard rewrite rules. Take `⟨m, rfl⟩ : ∃ m, i = m + 1` from `⟨i - 1, by omega⟩`. Establish `: m + 1 + j - 1 = m + j` using `by omega`.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem tri_add' (i j : ℕ) : (i + j) * (i + j - 1) / 2 + i * (i - 1) / 2 = j * (j - 1) / 2 + (i + j - 1) * i := by
  have h : ∀ n : ℕ, 2 * (n * (n - 1) / 2) + n = n * n := by
    intro n
    rw [Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]
    cases n with
    | zero => rfl
    | succ m => simp; ring
  have h1 := h (i + j)
  have h2 := h i
  have h3 := h j
  have h4 : (i + j - 1) * i + i = (i + j) * i := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      have : m + 1 + j - 1 = m + j := by omega
      rw [this]; ring
  nlinarith

/- English proof (translation)
Establish `htop : f.coeff r ≠ 0`. Rewrite using `[← hd]`. Conclude with `leadingCoeff_ne_zero.2 hf`. Rewrite using `[coeff_dualPoly_of_le _ _ (by rw [hd]; exact hk), leadingCoeff, hd]`. Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_le hk`.

Rewrite using `[Nat.add_sub_cancel_left, ← pow_mul]`. Establish `e` using `congrArg (fun m => q ^ m) (tri_add' k j)`. Simplify using `only [pow_add] at e`. Establish `e2 : ((-1 : ℂ) ^ k) * (-1) ^ k = 1` using `by rw [← mul_pow]; simp`. Establish `n1 : ((-1 : ℂ) ^ k) ≠ 0` using `pow_ne_zero _ (by simp)`.

Establish `n2 : ((-1 : ℂ) ^ j) ≠ 0` using `pow_ne_zero _ (by simp)`. Establish `n3 : ∀ m : ℕ, q ^ m ≠ 0` using `fun m => pow_ne_zero _ hq`. Rewrite using `[pow_add]`. Generalize the expression as in `(-1 : ℂ) ^ k = u at *`. Generalize the expression as in `(-1 : ℂ) ^ j = v at *`.

Establish `m1` using `n3 ((k + j) * (k + j - 1) / 2)`. Establish `m2` using `n3 (k * (k - 1) / 2)`. Establish `m3` using `n3 (j * (j - 1) / 2)`. Generalize the expression as in `q ^ ((k + j) * (k + j - 1) / 2) = A at *`. Generalize the expression as in `q ^ (k * (k - 1) / 2) = B at *`.

Generalize the expression as in `q ^ (j * (j - 1) / 2) = C' at *`. Generalize the expression as in `q ^ ((k + j - 1) * k) = D at *`. Rewrite using `[div_mul_div_comm, div_eq_div_iff (by simp [n1, n2, m1, m2]) (by simp [n2, m3])]`. Establish `e3` using `inv_mul_cancel₀ htop`. Take the linear combination `(f.coeff j * D * v * C') * e3 - (f.coeff j * v) * e - (f.coeff j * v * A * B) * e2`.
-/
theorem dual_coeff_mul {q : ℂ} (hq : q ≠ 0) {r : ℕ} {f : ℂ[X]} (hf : f ≠ 0) (hd : f.natDegree = r) {k : ℕ} (hk : k ≤ r) :
    (dualPoly (q ^ (r - 1)) f).coeff k / ((-1) ^ k * q ^ (k * (k - 1) / 2)) *
        (f.coeff r / ((-1) ^ r * q ^ (r * (r - 1) / 2))) =
      f.coeff (r - k) / ((-1) ^ (r - k) * q ^ ((r - k) * (r - k - 1) / 2)) := by
  have htop : f.coeff r ≠ 0 := by
    rw [← hd]; exact leadingCoeff_ne_zero.2 hf
  rw [coeff_dualPoly_of_le _ _ (by rw [hd]; exact hk), leadingCoeff, hd]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left, ← pow_mul]
  have e := congrArg (fun m => q ^ m) (tri_add' k j)
  simp only [pow_add] at e
  have e2 : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; simp
  have n1 : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by simp)
  have n2 : ((-1 : ℂ) ^ j) ≠ 0 := pow_ne_zero _ (by simp)
  have n3 : ∀ m : ℕ, q ^ m ≠ 0 := fun m => pow_ne_zero _ hq
  rw [pow_add]
  generalize (-1 : ℂ) ^ k = u at *
  generalize (-1 : ℂ) ^ j = v at *
  have m1 := n3 ((k + j) * (k + j - 1) / 2)
  have m2 := n3 (k * (k - 1) / 2)
  have m3 := n3 (j * (j - 1) / 2)
  generalize q ^ ((k + j) * (k + j - 1) / 2) = A at *
  generalize q ^ (k * (k - 1) / 2) = B at *
  generalize q ^ (j * (j - 1) / 2) = C' at *
  generalize q ^ ((k + j - 1) * k) = D at *
  rw [div_mul_div_comm, div_eq_div_iff (by simp [n1, n2, m1, m2]) (by simp [n2, m3])]
  have e3 := inv_mul_cancel₀ htop
  linear_combination (f.coeff j * D * v * C') * e3 - (f.coeff j * v) * e - (f.coeff j * v * A * B) * e2

/- English proof (translation)
Introduce `q r f a w hq h0 hdeg ha hw hrel k hk`. Establish `hqc : (q : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hq`. Establish `hf : f ≠ 0` using `ne_zero_of_coeff_zero h0`. Take `⟨c, hc⟩ : ∃ c : ℕ → ℂ, ∀ k, c k = f.coeff k / ((-1) ^ k * (q : ℂ) ^ (k * (k - 1) / 2))` from `⟨_, fun _ => rfl⟩`. Establish `hac : ∀ k, a k = star (c k)`.

Introduce `k`. Rewrite using `[ha, hc, coeff_map]`. Simplify using the standard rewrite rules. Establish `key : f.natDegree = r → ∀ k ≤ r, w k * c r = c (r - k)`. Introduce `hd k hk`.

Rewrite using `[hw, hc, hc]`. Conclude with `dual_coeff_mul hqc hf hd hk`. Establish `hc0 : c 0 = 1` using `by rw [hc, h0]; simp`. Break down `hrel with ⟨hr, hrel⟩ | ⟨hr, hrel⟩` into its components or cases. Establish `hcr : c r ≠ 0`.

Introduce `h`. Apply `hr` to reduce the goal to its premises. Rewrite using `[hac, h, star_zero]`. Establish `hd : f.natDegree = r`. Use `le_antisymm hdeg (le_natDegree_of_ne_zero fun h => hcr ?_)` and prove the remaining obligations.

Rewrite using `[hc, h, zero_div]`. Establish `h1` using `congrArg star (hrel k hk)`. Rewrite `h1` using `[star_mul', star_star, hac r, hac (r - k), star_star, star_star, ← key hd k hk]`. Conclude with `mul_right_cancel₀ hcr h1`. Establish `hd : f.natDegree = r`.

Use `le_antisymm hdeg (not_lt.1 fun h => hr ?_)` and prove the remaining obligations. Rewrite using `[hw, coeff_dualPoly_of_lt _ _ h, zero_div]`. Establish `h1` using `key hd r le_rfl`. Rewrite `h1` using `[Nat.sub_self, hc0]`. Establish `h2` using `key hd (r - k) (Nat.sub_le _ _)`.

Rewrite `h2` using `[Nat.sub_sub_self hk, ← hrel k hk, mul_assoc, h1, mul_one]`. Rewrite using `[hac, ← h2, star_star]`.
-/
theorem conj_eq_dual : ∀ (q r : ℕ) (f : ℂ[X]) (a w : ℕ → ℂ), q ≠ 0 → f.coeff 0 = 1 → f.natDegree ≤ r → (∀ k, a k = (f.map (starRingEnd ℂ)).coeff k / ((-1) ^ k * (q : ℂ) ^ (k * (k - 1) / 2))) → (∀ k, w k = (dualPoly ((q : ℂ) ^ (r - 1)) f).coeff k / ((-1) ^ k * (q : ℂ) ^ (k * (k - 1) / 2))) → ((a r ≠ 0 ∧ ∀ k ≤ r, star (a k) * a r = a (r - k)) ∨ (w r ≠ 0 ∧ ∀ k ≤ r, star (w k) * w r = w (r - k))) → ∀ k ≤ r, a k = w k := by
  intro q r f a w hq h0 hdeg ha hw hrel k hk
  have hqc : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have hf : f ≠ 0 := ne_zero_of_coeff_zero h0
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℂ, ∀ k, c k = f.coeff k / ((-1) ^ k * (q : ℂ) ^ (k * (k - 1) / 2)) := ⟨_, fun _ => rfl⟩
  have hac : ∀ k, a k = star (c k) := by
    intro k
    rw [ha, hc, coeff_map]
    simp
  have key : f.natDegree = r → ∀ k ≤ r, w k * c r = c (r - k) := by
    intro hd k hk
    rw [hw, hc, hc]
    exact dual_coeff_mul hqc hf hd hk
  have hc0 : c 0 = 1 := by rw [hc, h0]; simp
  rcases hrel with ⟨hr, hrel⟩ | ⟨hr, hrel⟩
  · have hcr : c r ≠ 0 := by
      intro h
      apply hr
      rw [hac, h, star_zero]
    have hd : f.natDegree = r := by
      refine le_antisymm hdeg (le_natDegree_of_ne_zero fun h => hcr ?_)
      rw [hc, h, zero_div]
    have h1 := congrArg star (hrel k hk)
    rw [star_mul', star_star, hac r, hac (r - k), star_star, star_star, ← key hd k hk] at h1
    exact mul_right_cancel₀ hcr h1
  · have hd : f.natDegree = r := by
      refine le_antisymm hdeg (not_lt.1 fun h => hr ?_)
      rw [hw, coeff_dualPoly_of_lt _ _ h, zero_div]
    have h1 := key hd r le_rfl
    rw [Nat.sub_self, hc0] at h1
    have h2 := key hd (r - k) (Nat.sub_le _ _)
    rw [Nat.sub_sub_self hk, ← hrel k hk, mul_assoc, h1, mul_one] at h2
    rw [hac, ← h2, star_star]

end GlobalTheory.PolUnitary
