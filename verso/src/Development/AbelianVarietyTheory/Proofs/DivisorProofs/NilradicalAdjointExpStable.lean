import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin
open scoped ContDiff

noncomputable section
namespace GlobalTheory.TorFin.NilAdj

/- English proof (translation)
Distinguish the cases in `hφ : φ = 0`. Use `⟨0, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `h (Pi.single i 1) (by simp [hφ])` as an intermediate fact. Simplify using `using this`.

Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, φ i ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hφ (funext hc)`. Use `⟨ψ ⬝ᵥ Pi.single i (φ i)⁻¹, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `j`. Establish `hw` using `h (Pi.single j 1 - φ j • Pi.single i (φ i)⁻¹) (by`. Simplify using `[dotProduct_sub, dotProduct_smul, hi])`. Simplify using `[dotProduct_sub, dotProduct_smul] at hw`. Simplify using `only [Pi.smul_apply, smul_eq_mul, dotProduct_single] at hw ⊢`.

Take the linear combination `hw`.
-/
theorem exists_smul_of_ker {n : ℕ} (ψ φ : Fin n → ℂ) (h : ∀ w, φ ⬝ᵥ w = 0 → ψ ⬝ᵥ w = 0) :
    ∃ b : ℂ, ψ = b • φ := by
  classical
  by_cases hφ : φ = 0
  · refine ⟨0, ?_⟩
    funext i
    have := h (Pi.single i 1) (by simp [hφ])
    simpa using this
  · obtain ⟨i, hi⟩ : ∃ i, φ i ≠ 0 := by
      by_contra hc; push_neg at hc; exact hφ (funext hc)
    refine ⟨ψ ⬝ᵥ Pi.single i (φ i)⁻¹, ?_⟩
    funext j
    have hw := h (Pi.single j 1 - φ j • Pi.single i (φ i)⁻¹) (by
      simp [dotProduct_sub, dotProduct_smul, hi])
    simp [dotProduct_sub, dotProduct_smul] at hw
    simp only [Pi.smul_apply, smul_eq_mul, dotProduct_single] at hw ⊢
    linear_combination hw

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hY`. Apply `Matrix.mulVec_injective` to reduce the goal to its premises. Use function extensionality and compare the values at `v`. Establish `hv : (star x ᵥ* J) ⬝ᵥ (Y *ᵥ v) = 0` using `by rw [dotProduct_mulVec, h2, zero_dotProduct]`. Take `⟨a, ha⟩` from `h3 _ hv`.

Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, ha, mulVec_smul, h1, smul_zero, zero_mulVec]`.
-/
theorem cube_eq_zero {n : ℕ} {J Y : Matrix (Fin n) (Fin n) ℂ} {x : Fin n → ℂ} (hY : Y ∈ nilRad J x) :
    Y * Y * Y = 0 := by
  obtain ⟨h1, h2, h3⟩ := hY
  apply Matrix.mulVec_injective
  funext v
  have hv : (star x ᵥ* J) ⬝ᵥ (Y *ᵥ v) = 0 := by rw [dotProduct_mulVec, h2, zero_dotProduct]
  obtain ⟨a, ha⟩ := h3 _ hv
  rw [← mulVec_mulVec, ← mulVec_mulVec, ha, mulVec_smul, h1, smul_zero, zero_mulVec]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hY`. Use `⟨by rw [← mulVec_mulVec, h1, mulVec_zero], by rw [← vecMul_vecMul, h2, zero_vecMul], fun v hv => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `h3 v hv`. Conclude with `⟨0, by rw [← mulVec_mulVec, ha, mulVec_smul, h1, smul_zero, zero_smul]⟩`.
-/
theorem sq_mem {n : ℕ} {J Y : Matrix (Fin n) (Fin n) ℂ} {x : Fin n → ℂ} (hY : Y ∈ nilRad J x) :
    Y * Y ∈ nilRad J x := by
  obtain ⟨h1, h2, h3⟩ := hY
  refine ⟨by rw [← mulVec_mulVec, h1, mulVec_zero], by rw [← vecMul_vecMul, h2, zero_vecMul], fun v hv => ?_⟩
  obtain ⟨a, ha⟩ := h3 v hv
  exact ⟨0, by rw [← mulVec_mulVec, ha, mulVec_smul, h1, smul_zero, zero_smul]⟩

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hY`. Establish `hsφ : star (star x ᵥ* J) = J *ᵥ x` using `by rw [star_vecMul, star_star, hJ]`. Use `⟨?_, ?_, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, ← hsφ, ← star_vecMul, h2, star_zero, mulVec_zero]`. Rewrite using `[← vecMul_vecMul, ← vecMul_vecMul, vecMul_vecMul (star x) J, mul_nonsing_inv J hdet, vecMul_one, ← star_mulVec, h1, star_zero, zero_vecMul]`.

Establish `hker : ∀ w, (star x ᵥ* J) ⬝ᵥ w = 0 → (star (J *ᵥ v) ᵥ* Y) ⬝ᵥ w = 0`. Introduce `w hw`. Take `⟨a, ha⟩` from `h3 w hw`. Rewrite using `[← dotProduct_mulVec, ha, dotProduct_smul]`. Establish `: star (J *ᵥ v) ⬝ᵥ x = 0`.

Establish `e` using `star_dotProduct_star (star x) (J *ᵥ v)`. Rewrite `e` using `[star_star]`. Rewrite using `[dotProduct_comm, e, dotProduct_comm, dotProduct_mulVec, hv, star_zero]`. Rewrite using `[this, smul_zero]`. Take `⟨b, hb⟩` from `exists_smul_of_ker _ _ hker`.

Use `⟨star b, ?_⟩` and prove the remaining obligations. Establish `e : Yᴴ *ᵥ (J *ᵥ v) = star b • (J *ᵥ x)`. Use `congrArg star hb` as an intermediate fact. Rewrite `this` using `[star_vecMul, star_star, star_smul, hsφ]`. Conclude with `this`.

Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, e, mulVec_smul, mulVec_mulVec, nonsing_inv_mul J hdet, one_mulVec]`.
-/
theorem adj_mem {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) (hdet : IsUnit J.det) {x : Fin n → ℂ}
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ nilRad J x) : J⁻¹ * Yᴴ * J ∈ nilRad J x := by
  obtain ⟨h1, h2, h3⟩ := hY
  have hsφ : star (star x ᵥ* J) = J *ᵥ x := by rw [star_vecMul, star_star, hJ]
  refine ⟨?_, ?_, fun v hv => ?_⟩
  · rw [← mulVec_mulVec, ← mulVec_mulVec, ← hsφ, ← star_vecMul, h2, star_zero, mulVec_zero]
  · rw [← vecMul_vecMul, ← vecMul_vecMul, vecMul_vecMul (star x) J, mul_nonsing_inv J hdet, vecMul_one,
      ← star_mulVec, h1, star_zero, zero_vecMul]
  · have hker : ∀ w, (star x ᵥ* J) ⬝ᵥ w = 0 → (star (J *ᵥ v) ᵥ* Y) ⬝ᵥ w = 0 := by
      intro w hw
      obtain ⟨a, ha⟩ := h3 w hw
      rw [← dotProduct_mulVec, ha, dotProduct_smul]
      have : star (J *ᵥ v) ⬝ᵥ x = 0 := by
        have e := star_dotProduct_star (star x) (J *ᵥ v)
        rw [star_star] at e
        rw [dotProduct_comm, e, dotProduct_comm, dotProduct_mulVec, hv, star_zero]
      rw [this, smul_zero]
    obtain ⟨b, hb⟩ := exists_smul_of_ker _ _ hker
    refine ⟨star b, ?_⟩
    have e : Yᴴ *ᵥ (J *ᵥ v) = star b • (J *ᵥ x) := by
      have := congrArg star hb
      rw [star_vecMul, star_star, star_smul, hsφ] at this
      exact this
    rw [← mulVec_mulVec, ← mulVec_mulVec, e, mulVec_smul, mulVec_mulVec, nonsing_inv_mul J hdet, one_mulVec]

/- English proof (translation)
Establish `h3 : ∀ k, 3 ≤ k → Y ^ k = 0`. Introduce `k hk`. Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le hk`. Rewrite using `[pow_add, pow_three, ← mul_assoc, h, zero_mul]`. Rewrite using `[NormedSpace.exp_eq_tsum ℂ]`.

Use `beta_reduce`. Rewrite using `[tsum_eq_sum (s := Finset.range 3)]`. Simplify using `[Finset.sum_range_succ, pow_two]`. Normalize the expressions using the abelian group laws. Introduce `k hk`.

Simplify using `at hk`. Rewrite using `[h3 k hk, smul_zero]`.
-/
theorem exp_sub_one_eq {n : ℕ} {Y : Matrix (Fin n) (Fin n) ℂ} (h : Y * Y * Y = 0) :
    NormedSpace.exp Y - 1 = Y + (1 / 2 : ℂ) • (Y * Y) := by
  have h3 : ∀ k, 3 ≤ k → Y ^ k = 0 := by
    intro k hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add, pow_three, ← mul_assoc, h, zero_mul]
  rw [NormedSpace.exp_eq_tsum ℂ]
  beta_reduce
  rw [tsum_eq_sum (s := Finset.range 3)]
  · simp [Finset.sum_range_succ, pow_two]
    abel
  · intro k hk
    simp at hk
    rw [h3 k hk, smul_zero]

/- English proof (translation)
Introduce `n J hJ hdet x Y hY`. Use `⟨adj_mem hJ hdet hY, ?_⟩` and prove the remaining obligations. Rewrite using `[exp_sub_one_eq (cube_eq_zero hY)]`. Conclude with `(nilRad J x).add_mem hY ((nilRad J x).smul_mem _ (sq_mem hY))`.
-/
theorem nilRad_adj_exp : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), Jᴴ = J → IsUnit J.det → ∀ (x : Fin n → ℂ)
    (Y : Matrix (Fin n) (Fin n) ℂ), Y ∈ nilRad J x → J⁻¹ * Yᴴ * J ∈ nilRad J x ∧ NormedSpace.exp Y - 1 ∈ nilRad J x := by
  intro n J hJ hdet x Y hY
  refine ⟨adj_mem hJ hdet hY, ?_⟩
  rw [exp_sub_one_eq (cube_eq_zero hY)]
  exact (nilRad J x).add_mem hY ((nilRad J x).smul_mem _ (sq_mem hY))

end GlobalTheory.TorFin.NilAdj
