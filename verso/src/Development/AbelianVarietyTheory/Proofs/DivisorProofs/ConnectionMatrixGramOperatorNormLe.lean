import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

noncomputable section

namespace GlobalTheory.ConnPointwise

variable {g : ℕ}

/- English proof (translation)
Rewrite using `[gnorm, form_eq_sum]`. Use `congr 1`. Simplify using `only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, re_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, ofReal_re]`.
-/
theorem gnorm_one_eq (v : Fin g → ℂ) : gnorm 1 v = √(∑ a, ‖v a‖ ^ 2) := by
  rw [gnorm, form_eq_sum]
  congr 1
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ofReal_re]

/- English proof (translation)
Use `opNorm_le_of_bound (by positivity) fun v => ?_` and prove the remaining obligations. Rewrite using `[gnorm_one_eq, gnorm_one_eq]`. Use `set S := ∑ a, ‖v a‖ ^ 2 with hS`. Establish `hS0 : 0 ≤ S` using `Finset.sum_nonneg fun _ _ => sq_nonneg _`. Establish `hrw : (g : ℝ) * E * √S = √(((g : ℝ) * E) ^ 2 * S)`.

Rewrite using `[Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]`. Rewrite using `[hrw]`. Apply `Real.sqrt_le_sqrt` to reduce the goal to its premises. Establish `hrow : ∀ j, ‖(M *ᵥ v) j‖ ^ 2 ≤ E ^ 2 * (g * S)` using `fun j => by`. Establish `h1 : ‖(M *ᵥ v) j‖ ≤ E * ∑ k, ‖v k‖`.

Rewrite using `[Finset.mul_sum]`. Simplify using `only [mulVec, dotProduct]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (h j k) (norm_nonneg _)`.

Establish `h2 : (∑ k, ‖v k‖) ^ 2 ≤ g * S`. Use `sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => ‖v k‖)` as an intermediate fact. Simplify `this` using `[hS]`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem opNorm_one_le_of_entry (M : Matrix (Fin g) (Fin g) ℂ) {E : ℝ} (hE : 0 ≤ E)
    (h : ∀ j k, ‖M j k‖ ≤ E) : opNorm 1 1 M ≤ g * E := by
  refine opNorm_le_of_bound (by positivity) fun v => ?_
  rw [gnorm_one_eq, gnorm_one_eq]
  set S := ∑ a, ‖v a‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hrw : (g : ℝ) * E * √S = √(((g : ℝ) * E) ^ 2 * S) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [hrw]
  apply Real.sqrt_le_sqrt
  have hrow : ∀ j, ‖(M *ᵥ v) j‖ ^ 2 ≤ E ^ 2 * (g * S) := fun j => by
    have h1 : ‖(M *ᵥ v) j‖ ≤ E * ∑ k, ‖v k‖ := by
      rw [Finset.mul_sum]
      simp only [mulVec, dotProduct]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (h j k) (norm_nonneg _)
    have h2 : (∑ k, ‖v k‖) ^ 2 ≤ g * S := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => ‖v k‖)
      simpa [hS] using this
    calc ‖(M *ᵥ v) j‖ ^ 2 ≤ (E * ∑ k, ‖v k‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = E ^ 2 * (∑ k, ‖v k‖) ^ 2 := by ring
      _ ≤ E ^ 2 * (g * S) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  calc ∑ j, ‖(M *ᵥ v) j‖ ^ 2 ≤ ∑ _j : Fin g, E ^ 2 * (g * S) := Finset.sum_le_sum fun j _ => hrow j
    _ = ((g : ℝ) * E) ^ 2 * S := by simp; ring

/- English proof (translation)
Establish `hdet : IsUnit Y.det`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`. Take `⟨x, hx, hx0⟩` from `(Matrix.exists_mulVec_eq_zero_iff).2 h0`. Establish `h1` using `hY x`.

Rewrite `h1` using `[hx0, dotProduct_zero]`. Establish `h2 : x ⬝ᵥ x ≤ 0` using `by nlinarith [show 0 ≤ x ⬝ᵥ x from Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)]`. Apply `hx` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Establish `h3 : ∀ i ∈ Finset.univ, 0 ≤ x i * x i` using `fun i _ => mul_self_nonneg _`.

Use `(Finset.sum_eq_zero_iff_of_nonneg h3).1 (le_antisymm h2 (Finset.sum_nonneg h3)) i (Finset.mem_univ _)` as an intermediate fact. Simplify using `using mul_self_eq_zero.1 this`. Use `⟨hdet, fun j k => ?_⟩` and prove the remaining obligations. Use `set u := Y⁻¹ *ᵥ Pi.single k 1 with hu`. Establish `hYu : Y *ᵥ u = Pi.single k 1`.

Rewrite using `[hu, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]`. Apply the tactic sequence `have hentry : Y⁻¹ j k = u j := by`. Rewrite using `[hu, mulVec_single_one]`. Both sides reduce to the same expression. Use `set N := u ⬝ᵥ u with hN`.

Establish `hN0 : 0 ≤ N` using `Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)`. Establish `hcomp : ∀ i, u i ^ 2 ≤ N` using `fun i => by`. Rewrite using `[hN, dotProduct, sq]`. Conclude with `Finset.single_le_sum (f := fun i => u i * u i) (fun i _ => mul_self_nonneg (u i)) (Finset.mem_univ i)`. Establish `h1 : c * N ≤ u k`.

Use `hY u` as an intermediate fact. Rewrite `this` using `[hYu, dotProduct_single, mul_one]`. Then use the resulting hypothesis. Establish `huk : 0 ≤ u k` using `le_trans (mul_nonneg hc.le hN0) h1`. Establish `h2 : c ^ 2 * N ^ 2 ≤ N`. Combine the equalities or inequalities in the displayed calculation.

Establish `h3 : c ^ 2 * N ≤ 1`. Break down `hN0.eq_or_lt with h | h` into its components or cases. Rewrite using `[← h]`. Simplify using the standard rewrite rules. Use the polynomial consequences of the given equalities and inequalities.

Establish `h4 : (c * u j) ^ 2 ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hentry, le_div_iff₀ hc, mul_comm]`. Use `(sq_le_one_iff_abs_le_one _).1 h4` as an intermediate fact. Rewrite `this` using `[abs_mul, abs_of_pos hc]`. Then use the resulting hypothesis.
-/
theorem inv_entry_le (Y : Matrix (Fin g) (Fin g) ℝ) {c : ℝ} (hc : 0 < c)
    (hY : ∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) : IsUnit Y.det ∧ ∀ j k, |Y⁻¹ j k| ≤ 1 / c := by
  have hdet : IsUnit Y.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨x, hx, hx0⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    have h1 := hY x
    rw [hx0, dotProduct_zero] at h1
    have h2 : x ⬝ᵥ x ≤ 0 := by nlinarith [show 0 ≤ x ⬝ᵥ x from Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)]
    apply hx
    funext i
    have h3 : ∀ i ∈ Finset.univ, 0 ≤ x i * x i := fun i _ => mul_self_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg h3).1 (le_antisymm h2 (Finset.sum_nonneg h3)) i (Finset.mem_univ _)
    simpa using mul_self_eq_zero.1 this
  refine ⟨hdet, fun j k => ?_⟩
  set u := Y⁻¹ *ᵥ Pi.single k 1 with hu
  have hYu : Y *ᵥ u = Pi.single k 1 := by
    rw [hu, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hentry : Y⁻¹ j k = u j := by
    rw [hu, mulVec_single_one]; rfl
  set N := u ⬝ᵥ u with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)
  have hcomp : ∀ i, u i ^ 2 ≤ N := fun i => by
    rw [hN, dotProduct, sq]
    exact Finset.single_le_sum (f := fun i => u i * u i) (fun i _ => mul_self_nonneg (u i)) (Finset.mem_univ i)
  have h1 : c * N ≤ u k := by
    have := hY u
    rwa [hYu, dotProduct_single, mul_one] at this
  have huk : 0 ≤ u k := le_trans (mul_nonneg hc.le hN0) h1
  have h2 : c ^ 2 * N ^ 2 ≤ N := by
    calc c ^ 2 * N ^ 2 = (c * N) ^ 2 := by ring
      _ ≤ u k ^ 2 := pow_le_pow_left₀ (mul_nonneg hc.le hN0) h1 2
      _ ≤ N := hcomp k
  have h3 : c ^ 2 * N ≤ 1 := by
    rcases hN0.eq_or_lt with h | h
    · rw [← h]; simp
    · nlinarith
  have h4 : (c * u j) ^ 2 ≤ 1 := by
    calc (c * u j) ^ 2 = c ^ 2 * u j ^ 2 := by ring
      _ ≤ c ^ 2 * N := mul_le_mul_of_nonneg_left (hcomp j) (sq_nonneg c)
      _ ≤ 1 := h3
  rw [hentry, le_div_iff₀ hc, mul_comm]
  have := (sq_le_one_iff_abs_le_one _).1 h4
  rwa [abs_mul, abs_of_pos hc] at this

end GlobalTheory.ConnPointwise

namespace GlobalTheory.ConnPointwise

variable {g : ℕ}

/- English proof (translation)
Establish `h1` using `h (Pi.single k 1)`. Establish `hs : ‖(Pi.single k (1 : ℝ) : Fin g → ℝ)‖ ≤ 1` using `(pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by`. Distinguish the cases in `hi : i = k`. Substitute `hi` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Pi.single_apply, hi]`. Rewrite `h1` using `[mulVec_single_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem entry_le_of_mulVec (P : Matrix (Fin g) (Fin g) ℝ) {W : ℝ} (hW : 0 ≤ W)
    (h : ∀ x, ‖P *ᵥ x‖ ≤ W * ‖x‖) (j k : Fin g) : |P j k| ≤ W := by
  have h1 := h (Pi.single k 1)
  have hs : ‖(Pi.single k (1 : ℝ) : Fin g → ℝ)‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
      by_cases hi : i = k
      · subst hi; simp
      · simp [Pi.single_apply, hi]
  rw [mulVec_single_one] at h1
  calc |P j k| = ‖Pᵀ k j‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖Pᵀ k‖ := norm_le_pi_norm _ j
    _ ≤ W * ‖(Pi.single k (1 : ℝ) : Fin g → ℝ)‖ := h1
    _ ≤ W := mul_le_of_le_one_right hW hs

end GlobalTheory.ConnPointwise

namespace GlobalTheory

open GlobalTheory.ConnPointwise

/- English proof (translation)
Introduce `g a Y Bs Dm s t c K W hc hK hW hY ht hB hD`. Take `⟨hdet, hinv⟩` from `inv_entry_le Y hc hY`. Establish `hmapinv : (Y.map Complex.ofReal)⁻¹ = (Y⁻¹).map Complex.ofReal`. Apply `inv_eq_left_inv` to reduce the goal to its premises. Use `show (Y⁻¹).map Complex.ofRealHom * Y.map Complex.ofRealHom = 1`.

Rewrite using `[← Matrix.map_mul, nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hBe : ∀ i j k, |(Y⁻¹ * Bs i) j k| ≤ W / t i` using `fun i j k => by`. Use `entry_le_of_mulVec _ hW (hB i) j k` as an intermediate fact. Rewrite `this` using `[Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (ht i)]`. Rewrite using `[le_div_iff₀ (ht i), mul_comm]`.

Conclude with `this`. Establish `hE0 : 0 ≤ (g : ℝ) * K / c + W * ∑ i, ‖s i‖ / t i`. Establish `: 0 ≤ ∑ i, ‖s i‖ / t i` using `Finset.sum_nonneg fun i _ => div_nonneg (norm_nonneg _) (ht i).le`. Check the signs of the components of the expression. Apply the tactic sequence `refine opNorm_one_le_of_entry _ hE0 fun j k => ?_`.

Rewrite using `[hmapinv]`. Establish `hexp : ((Y⁻¹).map Complex.ofReal * ((1 / (2 * Complex.I)) • (Dm + ∑ i, s i • (Bs i).map Complex.ofReal))) j k = (1 / (2 * Complex.I)) * (∑ l, ((Y⁻¹ j l : ℝ) : ℂ) * Dm l k + ∑ i, s i * (((Y⁻¹ * Bs i) j k : ℝ) : ℂ))`. Simplify using `only [mul_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sum_apply, map_apply, smul_eq_mul, ofReal_sum, ofReal_mul, Finset.mul_sum, mul_add, Finset.sum_add_distrib]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun l _ => by ring`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring`. Rewrite using `[hexp, norm_mul]`. Establish `hhalf : ‖(1 / (2 * Complex.I) : ℂ)‖ ≤ 1` using `by simp; norm_num`. Establish `hA : ‖∑ l, ((Y⁻¹ j l : ℝ) : ℂ) * Dm l k‖ ≤ g * K / c`.

Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs]`. Conclude with `mul_le_mul (hinv j l) (hD l k) (norm_nonneg _) (by positivity)`. Use `_ = g * K / c := by simp; ring`.

Establish `hBs : ‖∑ i, s i * (((Y⁻¹ * Bs i) j k : ℝ) : ℂ)‖ ≤ W * ∑ i, ‖s i‖ / t i`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs]`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem connMatrix_opNorm_le : ∀ (g a : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (Bs : Fin a → Matrix (Fin g) (Fin g) ℝ) (Dm : Matrix (Fin g) (Fin g) ℂ) (s : Fin a → ℂ) (t : Fin a → ℝ) (c K W : ℝ), 0 < c → 0 ≤ K → 0 ≤ W → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ i, 0 < t i) → (∀ i x, ‖(t i • (Y⁻¹ * Bs i)) *ᵥ x‖ ≤ W * ‖x‖) → (∀ j k, ‖Dm j k‖ ≤ K) → opNorm 1 1 ((Y.map Complex.ofReal)⁻¹ * ((1 / (2 * Complex.I)) • (Dm + ∑ i, s i • (Bs i).map Complex.ofReal))) ≤ g * (g * K / c + W * ∑ i, ‖s i‖ / t i) := by
  intro g a Y Bs Dm s t c K W hc hK hW hY ht hB hD
  obtain ⟨hdet, hinv⟩ := inv_entry_le Y hc hY
  have hmapinv : (Y.map Complex.ofReal)⁻¹ = (Y⁻¹).map Complex.ofReal := by
    apply inv_eq_left_inv
    show (Y⁻¹).map Complex.ofRealHom * Y.map Complex.ofRealHom = 1
    rw [← Matrix.map_mul, nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBe : ∀ i j k, |(Y⁻¹ * Bs i) j k| ≤ W / t i := fun i j k => by
    have := entry_le_of_mulVec _ hW (hB i) j k
    rw [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (ht i)] at this
    rw [le_div_iff₀ (ht i), mul_comm]; exact this
  have hE0 : 0 ≤ (g : ℝ) * K / c + W * ∑ i, ‖s i‖ / t i := by
    have : 0 ≤ ∑ i, ‖s i‖ / t i := Finset.sum_nonneg fun i _ => div_nonneg (norm_nonneg _) (ht i).le
    positivity
  refine opNorm_one_le_of_entry _ hE0 fun j k => ?_
  rw [hmapinv]
  have hexp : ((Y⁻¹).map Complex.ofReal * ((1 / (2 * Complex.I)) • (Dm + ∑ i, s i • (Bs i).map Complex.ofReal))) j k
      = (1 / (2 * Complex.I)) * (∑ l, ((Y⁻¹ j l : ℝ) : ℂ) * Dm l k + ∑ i, s i * (((Y⁻¹ * Bs i) j k : ℝ) : ℂ)) := by
    simp only [mul_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sum_apply, map_apply, smul_eq_mul, ofReal_sum,
      ofReal_mul, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun l _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  rw [hexp, norm_mul]
  have hhalf : ‖(1 / (2 * Complex.I) : ℂ)‖ ≤ 1 := by simp; norm_num
  have hA : ‖∑ l, ((Y⁻¹ j l : ℝ) : ℂ) * Dm l k‖ ≤ g * K / c := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ l, ‖((Y⁻¹ j l : ℝ) : ℂ) * Dm l k‖ ≤ ∑ _l : Fin g, 1 / c * K :=
          Finset.sum_le_sum fun l _ => by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul (hinv j l) (hD l k) (norm_nonneg _) (by positivity)
      _ = g * K / c := by simp; ring
  have hBs : ‖∑ i, s i * (((Y⁻¹ * Bs i) j k : ℝ) : ℂ)‖ ≤ W * ∑ i, ‖s i‖ / t i := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖s i‖ * |(Y⁻¹ * Bs i) j k| ≤ ‖s i‖ * (W / t i) :=
          mul_le_mul_of_nonneg_left (hBe i j k) (norm_nonneg _)
      _ = W * (‖s i‖ / t i) := by ring
  calc ‖(1 / (2 * Complex.I) : ℂ)‖ * ‖∑ l, ((Y⁻¹ j l : ℝ) : ℂ) * Dm l k + ∑ i, s i * (((Y⁻¹ * Bs i) j k : ℝ) : ℂ)‖
      ≤ 1 * ((g : ℝ) * K / c + W * ∑ i, ‖s i‖ / t i) :=
        mul_le_mul hhalf ((norm_add_le _ _).trans (add_le_add hA hBs)) (norm_nonneg _) zero_le_one
    _ = (g : ℝ) * K / c + W * ∑ i, ‖s i‖ / t i := one_mul _

end GlobalTheory
