import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtConst
open Matrix GlobalTheory.MatDeriv
open scoped Topology

namespace GlobalTheory.HermOpBound

/- English proof (translation)
Establish `h : star (Pi.single a (1:ℂ) : Fin n → ℂ) = Pi.single a 1`. Apply the tactic sequence `ext i; by_cases hi : i = a <;> simp [Pi.single_apply, hi]`. Rewrite using `[h, single_dotProduct]`. Simplify using `[mulVec, dotProduct, Pi.single_apply]`.
-/
lemma entry {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    star (Pi.single a (1:ℂ) : Fin n → ℂ) ⬝ᵥ M *ᵥ (Pi.single b (1:ℂ)) = M a b := by
  have h : star (Pi.single a (1:ℂ) : Fin n → ℂ) = Pi.single a 1 := by
    ext i; by_cases hi : i = a <;> simp [Pi.single_apply, hi]
  rw [h, single_dotProduct]
  simp [mulVec, dotProduct, Pi.single_apply]

/- English proof (translation)
Simplify using `only [star_add, star_smul, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma expand {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (u w : Fin n → ℂ) (s : ℂ) :
    star (u + s • w) ⬝ᵥ M *ᵥ (u + s • w)
      = star u ⬝ᵥ M *ᵥ u + s * (star u ⬝ᵥ M *ᵥ w) + star s * (star w ⬝ᵥ M *ᵥ u)
        + star s * s * (star w ⬝ᵥ M *ᵥ w) := by
  simp only [star_add, star_smul, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

/- English proof (translation)
The claim follows from `(pi_norm_le_iff_of_nonneg zero_le_one).2 (fun i => by by_cases h : i = a <;> simp [Pi.single_apply, h])`.
-/
lemma norm_single_le {n : ℕ} (a : Fin n) : ‖(Pi.single a (1:ℂ) : Fin n → ℂ)‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun i => by
    by_cases h : i = a <;> simp [Pi.single_apply, h])

/- English proof (translation)
Use `norm_le_pi_norm (Pi.single a (1:ℂ) : Fin n → ℂ) a` as an intermediate fact. Simplify using `using this`.
-/
lemma one_le_norm_single {n : ℕ} (a : Fin n) : 1 ≤ ‖(Pi.single a (1:ℂ) : Fin n → ℂ)‖ := by
  have := norm_le_pi_norm (Pi.single a (1:ℂ) : Fin n → ℂ) a
  simpa using this

/- English proof (translation)
Establish `h1 : ‖(Pi.single a (1:ℂ) : Fin n → ℂ) + s • Pi.single b 1‖ ≤ 2`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_smul, hs, one_mul]`. Conclude with `add_le_add (norm_single_le a) (norm_single_le b)`. Use `_ = 2 := by norm_num`.

Establish `h0` using `norm_nonneg ((Pi.single a (1:ℂ) : Fin n → ℂ) + s • Pi.single b 1)`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma norm_comb_sq_le {n : ℕ} (a b : Fin n) (s : ℂ) (hs : ‖s‖ = 1) :
    ‖(Pi.single a (1:ℂ) : Fin n → ℂ) + s • Pi.single b 1‖ ^ 2 ≤ 4 := by
  have h1 : ‖(Pi.single a (1:ℂ) : Fin n → ℂ) + s • Pi.single b 1‖ ≤ 2 := by
    calc _ ≤ ‖(Pi.single a (1:ℂ) : Fin n → ℂ)‖ + ‖s • (Pi.single b (1:ℂ) : Fin n → ℂ)‖ := norm_add_le _ _
      _ ≤ 1 + 1 := by
        rw [norm_smul, hs, one_mul]
        exact add_le_add (norm_single_le a) (norm_single_le b)
      _ = 2 := by norm_num
  have h0 := norm_nonneg ((Pi.single a (1:ℂ) : Fin n → ℂ) + s • Pi.single b 1)
  nlinarith

/- English proof (translation)
Take `⟨h0, h1⟩` from `hQ (Pi.single a 1)`. Use `one_le_norm_single a` as an intermediate fact. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h2 : c * ‖(Pi.single a (1:ℂ) : Fin n → ℂ)‖ ^ 2 ≤ c * 1` using `mul_le_mul_of_nonpos_left (by nlinarith) hc.le`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma c_nonneg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (c : ℝ)
    (hQ : ∀ v : Fin n → ℂ, 0 ≤ (star v ⬝ᵥ M *ᵥ v).re ∧ (star v ⬝ᵥ M *ᵥ v).re ≤ c * ‖v‖ ^ 2)
    (a : Fin n) : 0 ≤ c := by
  obtain ⟨h0, h1⟩ := hQ (Pi.single a 1)
  have := one_le_norm_single a
  by_contra hc
  push_neg at hc
  have h2 : c * ‖(Pi.single a (1:ℂ) : Fin n → ℂ)‖ ^ 2 ≤ c * 1 :=
    mul_le_mul_of_nonpos_left (by nlinarith) hc.le
  linarith

/- English proof (translation)
Establish `hc` using `c_nonneg M c hQ a`. Establish `key : ∀ s : ℂ, ‖s‖ = 1 → 0 ≤ (M a a + s * M a b + star s * star (M a b) + star s * s * M b b).re ∧ (M a a + s * M a b + star s * star (M a b) + star s * s * M b b).re ≤ 4 * c`. Introduce `s hs`. Take `⟨h0, h1⟩` from `hQ (Pi.single a 1 + s • Pi.single b 1)`. Rewrite `h0`, `h1` using `[expand, entry, entry, entry, entry, ← hM.apply b a]`.

Establish `hn` using `norm_comb_sq_le a b s hs`. Conclude with `⟨h0, h1.trans ((mul_le_mul_of_nonneg_left hn hc).trans_eq (by ring))⟩`. Take `⟨p1, p1'⟩` from `key 1 (by simp)`. Take `⟨p2, p2'⟩` from `key (-1) (by simp)`. Take `⟨p3, p3'⟩` from `key Complex.I (by simp)`.

Take `⟨p4, p4'⟩` from `key (-Complex.I) (by simp)`. Simplify using `[Complex.add_re, Complex.mul_re, Complex.mul_im] at p1 p1' p2 p2' p3 p3' p4 p4'`. Establish `hre : |(M a b).re| ≤ c` using `abs_le.2 ⟨by linarith, by linarith⟩`. Establish `him : |(M a b).im| ≤ c` using `abs_le.2 ⟨by linarith, by linarith⟩`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma entry_bound {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (hM : M.IsHermitian)
    (hQ : ∀ v : Fin n → ℂ, 0 ≤ (star v ⬝ᵥ M *ᵥ v).re ∧ (star v ⬝ᵥ M *ᵥ v).re ≤ c * ‖v‖ ^ 2)
    (a b : Fin n) : ‖M a b‖ ≤ 2 * c := by
  have hc := c_nonneg M c hQ a
  have key : ∀ s : ℂ, ‖s‖ = 1 →
      0 ≤ (M a a + s * M a b + star s * star (M a b) + star s * s * M b b).re ∧
      (M a a + s * M a b + star s * star (M a b) + star s * s * M b b).re ≤ 4 * c := by
    intro s hs
    obtain ⟨h0, h1⟩ := hQ (Pi.single a 1 + s • Pi.single b 1)
    rw [expand, entry, entry, entry, entry, ← hM.apply b a] at h0 h1
    have hn := norm_comb_sq_le a b s hs
    exact ⟨h0, h1.trans ((mul_le_mul_of_nonneg_left hn hc).trans_eq (by ring))⟩
  obtain ⟨p1, p1'⟩ := key 1 (by simp)
  obtain ⟨p2, p2'⟩ := key (-1) (by simp)
  obtain ⟨p3, p3'⟩ := key Complex.I (by simp)
  obtain ⟨p4, p4'⟩ := key (-Complex.I) (by simp)
  simp [Complex.add_re, Complex.mul_re, Complex.mul_im] at p1 p1' p2 p2' p3 p3' p4 p4'
  have hre : |(M a b).re| ≤ c := abs_le.2 ⟨by linarith, by linarith⟩
  have him : |(M a b).im| ≤ c := abs_le.2 ⟨by linarith, by linarith⟩
  calc ‖M a b‖ ≤ |(M a b).re| + |(M a b).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * c := by linarith

/- English proof (translation)
Break down `isEmpty_or_nonempty (Fin n) with h | ⟨⟨a⟩⟩` into its components or cases. Establish `hn : n = 0`. Break down `n with _ | n` into its components or cases. Both sides reduce to the same expression. Conclude with `(h.false 0).elim`.

Establish `: M *ᵥ x = 0` using `Subsingleton.elim _ _`. Rewrite using `[this, norm_zero]`. Simplify using `[hn]`. Establish `hc` using `c_nonneg M c hQ a`. Establish `hx` using `norm_nonneg x`.

Use `(pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (entry_bound M c hM hQ i j) (norm_le_pi_norm x j) (norm_nonneg _) (by linarith)`. Use `_ = n * (2 * c * ‖x‖) := by simp`.

Use `_ ≤ 4 * n * c * ‖x‖ := by`. Establish `: (0:ℝ) ≤ n` using `by positivity`. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg this hc) hx]`.
-/
theorem mulVec_norm_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (hM : M.IsHermitian)
    (hQ : ∀ v : Fin n → ℂ, 0 ≤ (star v ⬝ᵥ M *ᵥ v).re ∧ (star v ⬝ᵥ M *ᵥ v).re ≤ c * ‖v‖ ^ 2)
    (x : Fin n → ℂ) : ‖M *ᵥ x‖ ≤ 4 * n * c * ‖x‖ := by
  rcases isEmpty_or_nonempty (Fin n) with h | ⟨⟨a⟩⟩
  · have hn : n = 0 := by
      rcases n with _ | n
      · rfl
      · exact (h.false 0).elim
    have : M *ᵥ x = 0 := Subsingleton.elim _ _
    rw [this, norm_zero]; simp [hn]
  · have hc := c_nonneg M c hQ a
    have hx := norm_nonneg x
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    calc ‖(M *ᵥ x) i‖ = ‖∑ j, M i j * x j‖ := rfl
      _ ≤ ∑ j, ‖M i j * x j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin n, 2 * c * ‖x‖ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul]
          exact mul_le_mul (entry_bound M c hM hQ i j) (norm_le_pi_norm x j) (norm_nonneg _) (by linarith)
      _ = n * (2 * c * ‖x‖) := by simp
      _ ≤ 4 * n * c * ‖x‖ := by
          have : (0:ℝ) ≤ n := by positivity
          nlinarith [mul_nonneg (mul_nonneg this hc) hx]

end GlobalTheory.HermOpBound

/- English proof (translation)
Introduce `M c hM hQ x` and use `GlobalTheory.HermOpBound.mulVec_norm_le M c hM hQ x`.
-/
theorem GlobalTheory.hermitian_mulVec_norm_le_of_quadForm : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (c : ℝ), M.IsHermitian → (∀ v : Fin n → ℂ, 0 ≤ (star v ⬝ᵥ M *ᵥ v).re ∧ (star v ⬝ᵥ M *ᵥ v).re ≤ c * ‖v‖ ^ 2) → ∀ x : Fin n → ℂ, ‖M *ᵥ x‖ ≤ 4 * n * c * ‖x‖ :=
  fun M c hM hQ x => GlobalTheory.HermOpBound.mulVec_norm_le M c hM hQ x
