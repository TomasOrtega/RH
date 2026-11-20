import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedThetaQProductDistributionRelationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdSmoothedThetaQProductDistributionStatement
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

noncomputable section

namespace GlobalTheory.SiegDist

/- English proof (translation)
Unfold `ee`. Rewrite using `[← Complex.exp_add]`. Put the polynomial expressions in normal form.
-/
lemma ee_add (a b : ℂ) : ee (a + b) = ee a * ee b := by
  unfold ee; rw [← Complex.exp_add]; ring_nf

/- English proof (translation)
Unfold `ee`. Rewrite using `[← Complex.exp_int_mul]`. Put the polynomial expressions in normal form.
-/
lemma ee_int_mul (n : ℤ) (z : ℂ) : ee (n * z) = ee z ^ n := by
  unfold ee; rw [← Complex.exp_int_mul]; ring_nf

/- English proof (translation)
Unfold `ee`. Rewrite using `[← Complex.exp_nat_mul]`. Put the polynomial expressions in normal form.
-/
lemma ee_nat_mul (n : ℕ) (z : ℂ) : ee (n * z) = ee z ^ n := by
  unfold ee; rw [← Complex.exp_nat_mul]; ring_nf

/- English proof (translation)
The claim follows from `Complex.exp_ne_zero _`.
-/
lemma ee_ne_zero (z : ℂ) : ee z ≠ 0 := Complex.exp_ne_zero _

/- English proof (translation)
Unfold `ee`. Rewrite using `[Complex.norm_exp]`. Establish `h : (2 * Real.pi * Complex.I * (τ : ℂ)).re = -(2 * Real.pi * τ.im)`. Simplify using `[Complex.mul_re, Complex.mul_im]`. Rewrite using `[h, ← Real.exp_zero, Real.exp_lt_exp]`.

Use `mul_pos Real.pi_pos τ.im_pos` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma norm_ee_lt_one (τ : ℍ) : ‖ee (τ : ℂ)‖ < 1 := by
  unfold ee
  rw [Complex.norm_exp]
  have h : (2 * Real.pi * Complex.I * (τ : ℂ)).re = -(2 * Real.pi * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h, ← Real.exp_zero, Real.exp_lt_exp]
  have := mul_pos Real.pi_pos τ.im_pos
  linarith

/- English proof (translation)
Unfold `ee at h`. Rewrite `h` using `[Complex.exp_eq_one_iff]`. Take `⟨k, hk⟩` from `h`. Establish `hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `by simp [Real.pi_ne_zero, Complex.I_ne_zero]`. Establish `h2 : (u : ℂ) * τ + v = k`.

Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Rewrite using `[hk]`. Expand and normalize the polynomial expressions, which then agree. Establish `him` using `congrArg Complex.im h2`. Establish `hre` using `congrArg Complex.re h2`.

Simplify using `at him hre`. Establish `hu : u = 0`. Break down `him with h | h` into its components or cases. Conclude with `h` after adjusting the coercions. Conclude with `absurd h τ.im_pos.ne'`.

Substitute `hu` using the available equality. Simplify using `at hre`. Conclude with `⟨rfl, k, by exact_mod_cast hre⟩`.
-/
lemma ee_eq_one (u v : ℚ) (τ : ℍ) (h : ee ((u : ℂ) * τ + v) = 1) : u = 0 ∧ ∃ k : ℤ, v = k := by
  unfold ee at h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h2 : (u : ℂ) * τ + v = k := by
    apply mul_left_cancel₀ hne
    rw [hk]; ring
  have him := congrArg Complex.im h2
  have hre := congrArg Complex.re h2
  simp at him hre
  have hu : u = 0 := by
    rcases him with h | h
    · exact_mod_cast h
    · exact absurd h τ.im_pos.ne'
  subst hu
  simp at hre
  exact ⟨rfl, k, by exact_mod_cast hre⟩

/- English proof (translation)
Introduce `c m x τ hA hm hcm`. Take `⟨hc1, hc6, hnot⟩` from `hA`. Establish `hmC : (m : ℂ) ≠ 0` using `by exact_mod_cast hm.ne'`. Establish `hq0 : ee (τ : ℂ) ≠ 0` using `ee_ne_zero _`. Establish `hsplit : ∀ a b : ℕ, sg c ![(x 0 + a) / m, (x 1 + b) / m] τ = cth c (ee (τ : ℂ)) (ee ((((x 0 : ℂ) + a) * τ + x 1) / m) * ee ((b : ℂ) / m))`.

Introduce `a b`. Unfold `sg`. Rewrite using `[← ee_add]`. Use `congr 2`. Simplify using `[pt]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hpow : ∀ a : ℕ, ee ((((x 0 : ℂ) + a) * τ + x 1) / m) ^ m = ee (pt x τ) * ee (τ : ℂ) ^ a`. Introduce `a`. Rewrite using `[← ee_nat_mul, ← ee_nat_mul, ← ee_add]`.

Use `congr 1`. Simplify using `only [pt]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hND : ∀ n : ℤ, ee (τ : ℂ) ^ n * ee (pt x τ) ^ c ≠ 1`.

Introduce `n h`. Establish `h' : ee ((((n : ℚ) + c * x 0 : ℚ) : ℂ) * τ + ((c * x 1 : ℚ) : ℂ)) = 1`. Rewrite using `[← h, ← ee_int_mul, ← ee_nat_mul, ← ee_add]`. Use `congr 1`. Simplify using `only [pt]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨h0, k, hk⟩` from `ee_eq_one _ _ τ h'`. Apply `hnot` to reduce the goal to its premises. Use `⟨⟨-n, ?_⟩, ⟨k, hk.symm⟩⟩` and prove the remaining obligations.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hD1 : ∀ a : ℕ, ∀ n : ℤ, ee (τ : ℂ) ^ n * ee ((((x 0 : ℂ) + a) * τ + x 1) / m) ^ (c * m) ≠ 1`. Introduce `a n h`. Rewrite `h` using `[mul_comm c m, pow_mul, hpow a, mul_pow, ← pow_mul]`.

Apply `hND (n + ((a * c : ℕ) : ℤ))` to reduce the goal to its premises. Rewrite using `[zpow_add₀ hq0, zpow_natCast, ← h]`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.prod_congr rfl` to reduce the goal to its premises.

Introduce `a _`. Repeatedly rewrite using `[hsplit a]`. Rewrite using `[GlobalTheory.T.smoothedThetaQProduct_distribution_relation c m _ _ hc1 hc6 hm hcm (norm_ee_lt_one τ) hq0 (ee_ne_zero _) (hD1 a), hpow a]`. Use `_ = cth c (ee (τ : ℂ)) (ee (pt x τ)) := GlobalTheory.T.prod_smoothedThetaQProduct_distribution c m _ _ hc1 hc6 hm hcm (norm_ee_lt_one τ) hq0 (ee_ne_zero _) hND`. Use `_ = sg c x τ := rfl`.
-/
theorem sg_distribution : ∀ (c m : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), admitted c x → 0 < m → Nat.Coprime c m →
    ∏ a ∈ Finset.range m, ∏ b ∈ Finset.range m, sg c ![(x 0 + a) / m, (x 1 + b) / m] τ = sg c x τ := by
  intro c m x τ hA hm hcm
  obtain ⟨hc1, hc6, hnot⟩ := hA
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hq0 : ee (τ : ℂ) ≠ 0 := ee_ne_zero _
  have hsplit : ∀ a b : ℕ, sg c ![(x 0 + a) / m, (x 1 + b) / m] τ
      = cth c (ee (τ : ℂ)) (ee ((((x 0 : ℂ) + a) * τ + x 1) / m) * ee ((b : ℂ) / m)) := by
    intro a b
    unfold sg
    rw [← ee_add]
    congr 2
    simp [pt]
    field_simp
    ring
  have hpow : ∀ a : ℕ, ee ((((x 0 : ℂ) + a) * τ + x 1) / m) ^ m = ee (pt x τ) * ee (τ : ℂ) ^ a := by
    intro a
    rw [← ee_nat_mul, ← ee_nat_mul, ← ee_add]
    congr 1
    simp only [pt]
    field_simp
    ring
  have hND : ∀ n : ℤ, ee (τ : ℂ) ^ n * ee (pt x τ) ^ c ≠ 1 := by
    intro n h
    have h' : ee ((((n : ℚ) + c * x 0 : ℚ) : ℂ) * τ + ((c * x 1 : ℚ) : ℂ)) = 1 := by
      rw [← h, ← ee_int_mul, ← ee_nat_mul, ← ee_add]
      congr 1; simp only [pt]; push_cast; ring
    obtain ⟨h0, k, hk⟩ := ee_eq_one _ _ τ h'
    apply hnot
    refine ⟨⟨-n, ?_⟩, ⟨k, hk.symm⟩⟩
    push_cast; linarith
  have hD1 : ∀ a : ℕ, ∀ n : ℤ, ee (τ : ℂ) ^ n * ee ((((x 0 : ℂ) + a) * τ + x 1) / m) ^ (c * m) ≠ 1 := by
    intro a n h
    rw [mul_comm c m, pow_mul, hpow a, mul_pow, ← pow_mul] at h
    apply hND (n + ((a * c : ℕ) : ℤ))
    rw [zpow_add₀ hq0, zpow_natCast, ← h]
    ring
  calc ∏ a ∈ Finset.range m, ∏ b ∈ Finset.range m, sg c ![(x 0 + a) / m, (x 1 + b) / m] τ
      = ∏ a ∈ Finset.range m, cth c (ee (τ : ℂ) ^ m) (ee (pt x τ) * ee (τ : ℂ) ^ a) := by
        apply Finset.prod_congr rfl
        intro a _
        simp_rw [hsplit a]
        rw [GlobalTheory.T.smoothedThetaQProduct_distribution_relation c m _ _ hc1 hc6 hm hcm (norm_ee_lt_one τ) hq0 (ee_ne_zero _) (hD1 a), hpow a]
    _ = cth c (ee (τ : ℂ)) (ee (pt x τ)) :=
        GlobalTheory.T.prod_smoothedThetaQProduct_distribution c m _ _ hc1 hc6 hm hcm (norm_ee_lt_one τ) hq0 (ee_ne_zero _) hND
    _ = sg c x τ := rfl

end GlobalTheory.SiegDist
