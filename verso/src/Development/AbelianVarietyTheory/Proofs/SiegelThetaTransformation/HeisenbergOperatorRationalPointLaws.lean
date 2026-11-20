import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinearStatement

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW

/- English proof (translation)
Use `⟨∏ p : κ × ι, (a p.1 p.2).den, Finset.prod_pos fun p _ => (a p.1 p.2).den_pos, ?_⟩` and prove the remaining obligations. Introduce `k i`. Take `⟨c, hc⟩ : (a k i).den ∣ ∏ p : κ × ι, (a p.1 p.2).den` from `Finset.dvd_prod_of_mem (fun p : κ × ι => (a p.1 p.2).den) (Finset.mem_univ (k, i))`. Establish `: ((∏ p : κ × ι, (a p.1 p.2).den : ℕ) : ℚ) * a k i = algebraMap ℤ ℚ ((c : ℤ) * (a k i).num)`. Rewrite using `[hc]`.

Establish `h` using `Rat.mul_den_eq_num (a k i)`. Simplify using `only [eq_intCast, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]`. Rewrite using `[← h]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `isIntegral_algebraMap`.
-/
theorem heisS_exists_den {κ ι : Type} [Fintype κ] [Fintype ι] (a : Matrix κ ι ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ k i, IsIntegral ℤ ((D : ℚ) * a k i) := by
  classical
  refine ⟨∏ p : κ × ι, (a p.1 p.2).den, Finset.prod_pos fun p _ => (a p.1 p.2).den_pos, ?_⟩
  intro k i
  obtain ⟨c, hc⟩ : (a k i).den ∣ ∏ p : κ × ι, (a p.1 p.2).den :=
    Finset.dvd_prod_of_mem (fun p : κ × ι => (a p.1 p.2).den) (Finset.mem_univ (k, i))
  have : ((∏ p : κ × ι, (a p.1 p.2).den : ℕ) : ℚ) * a k i
      = algebraMap ℤ ℚ ((c : ℤ) * (a k i).num) := by
    rw [hc]
    have h := Rat.mul_den_eq_num (a k i)
    simp only [eq_intCast, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    rw [← h]; ring
  rw [this]
  exact isIntegral_algebraMap

/- English proof (translation)
Take `⟨R, hR, hs, hp⟩` from `h`. Take `⟨D, hD, ha⟩` from `heisS_exists_den a`. Establish `hn : ∀ n : ℕ, IsIntegral ℤ (n : ℚ)` using `fun n => by`. Simplify using `using (isIntegral_algebraMap (R := ℤ) (A := ℚ) (x := (n : ℤ)))`. Use `⟨R * D, Nat.mul_pos hR hD, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x hx k i`. Establish `h1` using `hs x (left_ne_zero_of_mul hx) k i`. Establish `: (((R * D : ℕ) : ℚ) • x) k i = (D : ℚ) * ((R : ℚ) • x) k i`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Nat.cast_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `(hn D).mul h1`. Introduce `x y hy`. Establish `e1 : x + ((R * D : ℕ) : ℚ) • y = x + (R : ℚ) • ((D : ℚ) • y)`. Rewrite using `[smul_smul, Nat.cast_mul]`.

Establish `hy' : IntM ((D : ℚ) • y)` using `fun k i => by`. Simplify using `using (hn D).mul (hy k i)`. Establish `hint : IsIntegral ℤ (∑ k, ∑ i, (R : ℚ) * (y k i * ((D : ℚ) * a k i)))` using `IsIntegral.sum _ fun k _ => IsIntegral.sum _ fun i _ => (hn R).mul ((hy k i).mul (ha k i))`. Take `⟨n, hn'⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hint`. Establish `e2 : (∑ k, (2 * ((x + ((R * D : ℕ) : ℚ) • y) k ⬝ᵥ a k) - a k ⬝ᵥ b k) : ℚ) = (∑ k, (2 * (x k ⬝ᵥ a k) - a k ⬝ᵥ b k) : ℚ) + 2 * n`.

Establish `: (n : ℚ) = ∑ k, ∑ i, (R : ℚ) * (y k i * ((D : ℚ) * a k i))` using `by simpa using hn'`. Rewrite using `[this, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `: (x + ((R * D : ℕ) : ℚ) • y) k ⬝ᵥ a k = x k ⬝ᵥ a k + ∑ i, (R : ℚ) * (y k i * ((D : ℚ) * a k i))`. Simplify using `only [dotProduct, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Nat.cast_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only []`. Rewrite using `[e2, e1, hp x _ hy']`. Use `congr 1`. Rewrite using `[Rat.cast_add, mul_add, Complex.exp_add]`. Establish `: (π : ℂ) * I * ((2 * n : ℚ) : ℂ) = n * (2 * π * I)` using `by push_cast; ring`.

Rewrite using `[this, Complex.exp_int_mul_two_pi_mul_I, mul_one]`.
-/
theorem isSB_mul_char {κ ι : Type} [Fintype κ] [Fintype ι] (a b : Matrix κ ι ℚ)
    (ψ : Matrix κ ι ℚ → ℂ) (h : IsSB ψ) :
    IsSB (fun x : Matrix κ ι ℚ => ψ x *
      cexp (Real.pi * I * ((∑ k, (2 * (x k ⬝ᵥ a k) - a k ⬝ᵥ b k) : ℚ) : ℂ))) := by
  obtain ⟨R, hR, hs, hp⟩ := h
  obtain ⟨D, hD, ha⟩ := heisS_exists_den a
  have hn : ∀ n : ℕ, IsIntegral ℤ (n : ℚ) := fun n => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℚ) (x := (n : ℤ)))
  refine ⟨R * D, Nat.mul_pos hR hD, ?_, ?_⟩
  · intro x hx k i
    have h1 := hs x (left_ne_zero_of_mul hx) k i
    have : (((R * D : ℕ) : ℚ) • x) k i = (D : ℚ) * ((R : ℚ) • x) k i := by
      simp only [Matrix.smul_apply, smul_eq_mul, Nat.cast_mul]; ring
    rw [this]; exact (hn D).mul h1
  · intro x y hy
    have e1 : x + ((R * D : ℕ) : ℚ) • y = x + (R : ℚ) • ((D : ℚ) • y) := by
      rw [smul_smul, Nat.cast_mul]
    have hy' : IntM ((D : ℚ) • y) := fun k i => by
      simpa using (hn D).mul (hy k i)
    have hint : IsIntegral ℤ (∑ k, ∑ i, (R : ℚ) * (y k i * ((D : ℚ) * a k i))) :=
      IsIntegral.sum _ fun k _ => IsIntegral.sum _ fun i _ => (hn R).mul ((hy k i).mul (ha k i))
    obtain ⟨n, hn'⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    have e2 : (∑ k, (2 * ((x + ((R * D : ℕ) : ℚ) • y) k ⬝ᵥ a k) - a k ⬝ᵥ b k) : ℚ)
        = (∑ k, (2 * (x k ⬝ᵥ a k) - a k ⬝ᵥ b k) : ℚ) + 2 * n := by
      have : (n : ℚ) = ∑ k, ∑ i, (R : ℚ) * (y k i * ((D : ℚ) * a k i)) := by simpa using hn'
      rw [this, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have : (x + ((R * D : ℕ) : ℚ) • y) k ⬝ᵥ a k
          = x k ⬝ᵥ a k + ∑ i, (R : ℚ) * (y k i * ((D : ℚ) * a k i)) := by
        simp only [dotProduct, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Nat.cast_mul]; ring
      rw [this]; ring
    simp only []
    rw [e2, e1, hp x _ hy']
    congr 1
    rw [Rat.cast_add, mul_add, Complex.exp_add]
    have : (π : ℂ) * I * ((2 * n : ℚ) : ℂ) = n * (2 * π * I) := by push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/- English proof (translation)
Introduce `κ ι _ _ _ a b φ hφ`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `isSB_mul_char a b _ ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι φ φ hφ hφ).2.2.2.2.2.2.2 b).1`. Introduce `τ hτ ζ`. Unfold `thS`.

Rewrite using `[← tsum_mul_left, ← (Equiv.addRight b).tsum_eq]`. Use `tsum_congr fun y => ?_` and prove the remaining obligations. Simplify using `only [Equiv.coe_addRight, heisS, add_sub_cancel_right]`. Rewrite using `[mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]`. Use `congr 2`.

Rewrite using `[← mul_add, ← mul_add, Rat.cast_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `hq : ∀ u v : ι → ℚ, ((u ⬝ᵥ v : ℚ) : ℂ) = qv u ⬝ᵥ qv v` using `fun u v => by`. Simplify using `[dotProduct, qv]`.

Establish `hadd : qv ((y + b) k) = qv (y k) + qv (b k)`. Use extensionality with `i`. Simplify using `[qv]`. Establish `hsym : qv (b k) ⬝ᵥ τ *ᵥ qv (y k) = qv (y k) ⬝ᵥ τ *ᵥ qv (b k)`. Rewrite using `[dotProduct_mulVec, ← mulVec_transpose, hτ.1.eq, dotProduct_comm]`.

Rewrite using `[Rat.cast_sub, Rat.cast_mul, hq, hq, hadd]`. Simplify using `only [add_dotProduct, dotProduct_add, mulVec_add, hsym, dotProduct_comm (qv (b k)) (qv (a k))]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `a' b'`.

Use function extensionality and compare the values at `x`. Simplify using `only [heisS, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, sub_sub]`. Use `congr 2`. Rewrite using `[← mul_add, ← mul_add, ← Rat.cast_add, ← Rat.cast_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`.

Use `congr 2`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.add_apply, Matrix.sub_apply]`.

Expand and normalize the polynomial expressions, which then agree. Use function extensionality and compare the values at `x`. Simplify using `[heisS, dotProduct]`. Introduce `ψ hψ`. Establish `h1 : IsSB (fun x : Matrix κ ι ℚ => conj (ψ x))` using `(GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι ψ ψ hψ hψ).2.2.2.1`.

Establish `h2` using `(GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι φ _ hφ h1).2.2.1`. Establish `h3` using `((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι _ _ h2 h2).2.2.2.2.2.2.2 b).2`. Unfold `ip`. Use `Eq.trans ?_ h3` and prove the remaining obligations. Use `congr 1`.

Use function extensionality and compare the values at `x`. Simplify using `only [heisS, Pi.mul_apply, map_mul]`. Rewrite using `[← Complex.exp_conj, mul_mul_mul_comm, ← Complex.exp_add]`. Simplify using `only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ratCast]`. Simplify using the standard rewrite rules.
-/
theorem heisS_laws : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (a b : Matrix κ ι ℚ) (φ : Matrix κ ι ℚ → ℂ), IsSB φ → IsSB (heisS a b φ) ∧ (∀ τ ∈ Siegel ι, ∀ ζ, thS (heisS a b φ) τ ζ = cexp (π * I * ∑ k, (qv (b k) ⬝ᵥ τ *ᵥ qv (b k) + 2 * (qv (b k) ⬝ᵥ ζ k) + qv (a k) ⬝ᵥ qv (b k))) * thS φ τ (fun k => ζ k + qv (a k) + τ *ᵥ qv (b k))) ∧ (∀ a' b', heisS a b (heisS a' b' φ) = cexp (π * I * ((∑ k, (a k ⬝ᵥ b' k - a' k ⬝ᵥ b k) : ℚ) : ℂ)) • heisS (a + a') (b + b') φ) ∧ heisS 0 0 φ = φ ∧ ∀ ψ, IsSB ψ → ip (heisS a b φ) (heisS a b ψ) = ip φ ψ := by
  intro κ ι _ _ _ a b φ hφ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact isSB_mul_char a b _ ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι φ φ hφ hφ).2.2.2.2.2.2.2 b).1
  · intro τ hτ ζ
    unfold thS
    rw [← tsum_mul_left, ← (Equiv.addRight b).tsum_eq]
    refine tsum_congr fun y => ?_
    simp only [Equiv.coe_addRight, heisS, add_sub_cancel_right]
    rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
    congr 2
    rw [← mul_add, ← mul_add, Rat.cast_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have hq : ∀ u v : ι → ℚ, ((u ⬝ᵥ v : ℚ) : ℂ) = qv u ⬝ᵥ qv v := fun u v => by
      simp [dotProduct, qv]
    have hadd : qv ((y + b) k) = qv (y k) + qv (b k) := by
      ext i; simp [qv]
    have hsym : qv (b k) ⬝ᵥ τ *ᵥ qv (y k) = qv (y k) ⬝ᵥ τ *ᵥ qv (b k) := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hτ.1.eq, dotProduct_comm]
    rw [Rat.cast_sub, Rat.cast_mul, hq, hq, hadd]
    simp only [add_dotProduct, dotProduct_add, mulVec_add, hsym, dotProduct_comm (qv (b k)) (qv (a k))]
    push_cast; ring
  · intro a' b'
    funext x
    simp only [heisS, Pi.smul_apply, smul_eq_mul]
    rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, sub_sub]
    congr 2
    rw [← mul_add, ← mul_add, ← Rat.cast_add, ← Rat.cast_add, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.add_apply, Matrix.sub_apply]; ring
  · funext x
    simp [heisS, dotProduct]
  · intro ψ hψ
    have h1 : IsSB (fun x : Matrix κ ι ℚ => conj (ψ x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι ψ ψ hψ hψ).2.2.2.1
    have h2 := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι φ _ hφ h1).2.2.1
    have h3 := ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι _ _ h2 h2).2.2.2.2.2.2.2 b).2
    unfold ip
    refine Eq.trans ?_ h3
    congr 1
    funext x
    simp only [heisS, Pi.mul_apply, map_mul]
    rw [← Complex.exp_conj, mul_mul_mul_comm, ← Complex.exp_add]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ratCast]
    simp

end GlobalTheory.SW
