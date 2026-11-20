import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet

open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

/- English proof (translation)
Set `ψ : AddChar (Fin n → B) ℂ` to `{ toFun := fun y => χ (s * ip c y z) map_zero_eq_one' := by simp [ip_zero_left] map_add_eq_mul' := fun x y => by rw [ip_add_left, mul_add, AddChar.map_add_eq_mul] }`. Establish `hψ : ψ ≠ 1`. Introduce `h`. Take `⟨i, hi⟩` from `Function.ne_iff.1 hz`. Establish `hne : s * c (z i) ≠ 0`.

Introduce `h0`. Establish `h1 : c (z i) = 0` using `(hs.mul_right_eq_zero).1 h0`. Apply `hi` to reduce the goal to its premises. Use `congrArg c h1` as an intermediate fact. Simplify `this` using `[hc]`.

Apply `hχ hne` to reduce the goal to its premises. Use extensionality with `u`. Establish `h2 : χ (s * ip c (Pi.single i u) z) = 1` using `DFunLike.congr_fun h (Pi.single i u)`. Establish `h3 : ip c (Pi.single i u) z = u * c (z i)`. Unfold `ip`.

Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules.

Rewrite `h2` using `[h3]`. Rewrite using `[AddChar.mulShift_apply, AddChar.one_apply, ← h2]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Conclude with `AddChar.sum_eq_zero_of_ne_one hψ`.
-/
theorem sum_char_unit_mul_ip_eq_zero {B : Type} [CommRing B] [Fintype B] (c : B →+* B)
    (hc : ∀ u, c (c u) = u) (χ : AddChar B ℂ) (hχ : χ.IsPrimitive) {n : ℕ} {s : B}
    (hs : IsUnit s) {z : Fin n → B} (hz : z ≠ 0) :
    ∑ y : Fin n → B, χ (s * ip c y z) = 0 := by
  let ψ : AddChar (Fin n → B) ℂ :=
    { toFun := fun y => χ (s * ip c y z)
      map_zero_eq_one' := by simp [ip_zero_left]
      map_add_eq_mul' := fun x y => by rw [ip_add_left, mul_add, AddChar.map_add_eq_mul] }
  have hψ : ψ ≠ 1 := by
    intro h
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hz
    have hne : s * c (z i) ≠ 0 := by
      intro h0
      have h1 : c (z i) = 0 := (hs.mul_right_eq_zero).1 h0
      apply hi
      have := congrArg c h1
      simpa [hc] using this
    apply hχ hne
    ext u
    have h2 : χ (s * ip c (Pi.single i u) z) = 1 := DFunLike.congr_fun h (Pi.single i u)
    have h3 : ip c (Pi.single i u) z = u * c (z i) := by
      unfold ip
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    rw [h3] at h2
    rw [AddChar.mulShift_apply, AddChar.one_apply, ← h2]
    congr 1
    ring
  exact AddChar.sum_eq_zero_of_ne_one hψ

/- English proof (translation)
Use `set Q : (Fin n → B) → B := fun y => a * ip c y y + ip c y v with hQ`. Use `set S : ℂ := ∑ y : Fin n → B, χ (Q y) with hS`. Establish `key : ∀ y z : Fin n → B, χ (Q (y + z)) * (starRingEnd ℂ) (χ (Q y)) = χ (Q z) * χ ((a + c a) * ip c y z)`. Introduce `y z`. Establish `h1 : χ (a * ip c z y) = χ (c a * ip c y z)`.

Rewrite using `[← hinv, map_mul, cj_ip c hc]`. Establish `h2 : Q (y + z) + -Q y = Q z + a * ip c y z + a * ip c z y`. Simplify using `only [hQ, ip_add_left, ip_add_right]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, h2, AddChar.map_add_eq_mul, h1, add_mul, AddChar.map_add_eq_mul χ (Q z), AddChar.map_add_eq_mul χ (a * ip c y z), mul_assoc]`.

Establish `hsq : S * (starRingEnd ℂ) S = (((q : ℝ) ^ n) ^ 2 : ℝ)`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[hS, ← Equiv.sum_comp (Equiv.addLeft y), Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun z _ => key y z`.

Use `_ = ∑ z : Fin n → B, χ (Q z) * ∑ y : Fin n → B, χ ((a + c a) * ip c y z) := by`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [Finset.mul_sum]`. Use `_ = (((q : ℝ) ^ n) ^ 2 : ℝ) := by`. Rewrite using `[Finset.sum_eq_single (0 : Fin n → B)]`.

Simplify using `[hQ, ip_zero_left, ip_zero_right, hB, ← pow_mul, mul_comm]`. Introduce `z _ hz`. Rewrite using `[sum_char_unit_mul_ip_eq_zero c hc χ hχ ha hz, mul_zero]`. Simplify using the standard rewrite rules. Rewrite `hsq` using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Establish `h3 : ‖S‖ ^ 2 = ((q : ℝ) ^ n) ^ 2` using `by exact_mod_cast hsq`. Conclude with `((pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3).le`.
-/
theorem norm_gauss_sum_ip_le {B : Type} [CommRing B] [Fintype B] (c : B →+* B)
    (hc : ∀ u, c (c u) = u) (q : ℕ) (_hq : 2 ≤ q) (hB : Fintype.card B = q ^ 2)
    (χ : AddChar B ℂ) (hχ : χ.IsPrimitive) (hinv : ∀ u, χ (c u) = χ u) (n : ℕ) (a : B)
    (ha : IsUnit (a + c a)) (v : Fin n → B) :
    ‖∑ y : Fin n → B, χ (a * ip c y y + ip c y v)‖ ≤ (q : ℝ) ^ n := by
  set Q : (Fin n → B) → B := fun y => a * ip c y y + ip c y v with hQ
  set S : ℂ := ∑ y : Fin n → B, χ (Q y) with hS
  have key : ∀ y z : Fin n → B,
      χ (Q (y + z)) * (starRingEnd ℂ) (χ (Q y)) = χ (Q z) * χ ((a + c a) * ip c y z) := by
    intro y z
    have h1 : χ (a * ip c z y) = χ (c a * ip c y z) := by
      rw [← hinv, map_mul, cj_ip c hc]
    have h2 : Q (y + z) + -Q y = Q z + a * ip c y z + a * ip c z y := by
      simp only [hQ, ip_add_left, ip_add_right]
      ring
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, h2, AddChar.map_add_eq_mul, h1,
      add_mul, AddChar.map_add_eq_mul χ (Q z), AddChar.map_add_eq_mul χ (a * ip c y z), mul_assoc]
  have hsq : S * (starRingEnd ℂ) S = (((q : ℝ) ^ n) ^ 2 : ℝ) := by
    calc S * (starRingEnd ℂ) S
        = ∑ y : Fin n → B, S * (starRingEnd ℂ) (χ (Q y)) := by
          conv_lhs => rw [hS, map_sum, ← hS, Finset.mul_sum]
      _ = ∑ y : Fin n → B, ∑ z : Fin n → B, χ (Q z) * χ ((a + c a) * ip c y z) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hS, ← Equiv.sum_comp (Equiv.addLeft y), Finset.sum_mul]
          exact Finset.sum_congr rfl fun z _ => key y z
      _ = ∑ z : Fin n → B, χ (Q z) * ∑ y : Fin n → B, χ ((a + c a) * ip c y z) := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
      _ = (((q : ℝ) ^ n) ^ 2 : ℝ) := by
          rw [Finset.sum_eq_single (0 : Fin n → B)]
          · simp [hQ, ip_zero_left, ip_zero_right, hB, ← pow_mul, mul_comm]
          · intro z _ hz
            rw [sum_char_unit_mul_ip_eq_zero c hc χ hχ ha hz, mul_zero]
          · simp
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hsq
  have h3 : ‖S‖ ^ 2 = ((q : ℝ) ^ n) ^ 2 := by exact_mod_cast hsq
  exact ((pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3).le

end GlobalTheory.GramCount
