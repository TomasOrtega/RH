import Mathlib
open Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

section LocalHom

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {A : Type*} [CommGroup A]
  {ρ : ℝ} {e₀ : V → A}

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Establish `h0` using `h 0 0 (by simpa using hρ) (by simpa using hρ) (by simpa using hρ)`. Simplify using `only [add_zero] at h0`. Simplify using `using h0`.

Consider the case `succ k ih`. Establish `hz` using `norm_nonneg z`. Establish `hk0 : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`. Move the coercions through the operations in `at hk ⊢`. Establish `h1 : (k : ℝ) * ‖z‖ < ρ` using `by nlinarith`.

Establish `h2 : ‖z‖ < ρ` using `by nlinarith`. Establish `h3 : ‖(k : ℝ) • z‖ < ρ` using `by rwa [norm_smul, Real.norm_of_nonneg hk0]`. Establish `h4 : ‖(k : ℝ) • z + z‖ < ρ`. Establish `: (k : ℝ) • z + z = ((k : ℝ) + 1) • z` using `by rw [add_smul, one_smul]`. Rewrite using `[this, norm_smul, Real.norm_of_nonneg (by positivity)]` and apply the resulting hypothesis.

Rewrite using `[add_smul, one_smul, h _ _ h3 h2 h4, ih h1, pow_succ]`.
-/
theorem localHom_nsmul (hρ : 0 < ρ)
    (h : ∀ z w : V, ‖z‖ < ρ → ‖w‖ < ρ → ‖z + w‖ < ρ → e₀ (z + w) = e₀ z * e₀ w)
    (z : V) (k : ℕ) (hk : (k : ℝ) * ‖z‖ < ρ) : e₀ ((k : ℝ) • z) = e₀ z ^ k := by
  induction k with
  | zero =>
    have h0 := h 0 0 (by simpa using hρ) (by simpa using hρ) (by simpa using hρ)
    simp only [add_zero] at h0
    simpa using h0
  | succ k ih =>
    have hz := norm_nonneg z
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    push_cast at hk ⊢
    have h1 : (k : ℝ) * ‖z‖ < ρ := by nlinarith
    have h2 : ‖z‖ < ρ := by nlinarith
    have h3 : ‖(k : ℝ) • z‖ < ρ := by rwa [norm_smul, Real.norm_of_nonneg hk0]
    have h4 : ‖(k : ℝ) • z + z‖ < ρ := by
      have : (k : ℝ) • z + z = ((k : ℝ) + 1) • z := by rw [add_smul, one_smul]
      rwa [this, norm_smul, Real.norm_of_nonneg (by positivity)]
    rw [add_smul, one_smul, h _ _ h3 h2 h4, ih h1, pow_succ]

/- English proof (translation)
Establish `hN' : (0 : ℝ) < N` using `by exact_mod_cast hN`. Rewrite using `[norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_lt_iff₀ hN']`. Conclude with `hz`.
-/
theorem localHom_norm_inv_smul_lt (z : V) {N : ℕ} (hN : 0 < N) (hz : ‖z‖ < N * ρ) :
    ‖(N : ℝ)⁻¹ • z‖ < ρ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_lt_iff₀ hN']
  exact hz

/- English proof (translation)
Establish `hN' : (0 : ℝ) < N` using `by exact_mod_cast hN`. Establish `hM' : (0 : ℝ) < M` using `by exact_mod_cast hM`. Establish `e1 : (N : ℝ)⁻¹ • z = (M : ℝ) • (((N : ℝ) * M)⁻¹ • z)`. Rewrite using `[smul_smul]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Establish `hb` using `localHom_norm_inv_smul_lt z hN hz`. Establish `hk : (M : ℝ) * ‖((N : ℝ) * M)⁻¹ • z‖ < ρ`. Rewrite `hb` using `[e1, norm_smul, Real.norm_of_nonneg hM'.le]`. Then use the resulting hypothesis. Rewrite using `[e1, localHom_nsmul hρ h _ M hk, ← pow_mul, mul_comm M N]`.
-/
theorem localHom_pow_mul (hρ : 0 < ρ)
    (h : ∀ z w : V, ‖z‖ < ρ → ‖w‖ < ρ → ‖z + w‖ < ρ → e₀ (z + w) = e₀ z * e₀ w)
    (z : V) {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (hz : ‖z‖ < N * ρ) :
    e₀ ((N : ℝ)⁻¹ • z) ^ N = e₀ (((N : ℝ) * M)⁻¹ • z) ^ (N * M) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have e1 : (N : ℝ)⁻¹ • z = (M : ℝ) • (((N : ℝ) * M)⁻¹ • z) := by
    rw [smul_smul]; congr 1; field_simp
  have hb := localHom_norm_inv_smul_lt z hN hz
  have hk : (M : ℝ) * ‖((N : ℝ) * M)⁻¹ • z‖ < ρ := by
    rwa [e1, norm_smul, Real.norm_of_nonneg hM'.le] at hb
  rw [e1, localHom_nsmul hρ h _ M hk, ← pow_mul, mul_comm M N]

/- English proof (translation)
Rewrite using `[localHom_pow_mul hρ h z hN hM hzN, localHom_pow_mul hρ h z hM hN hzM, mul_comm N M, mul_comm (N : ℝ) M]`.
-/
theorem localHom_pow_indep (hρ : 0 < ρ)
    (h : ∀ z w : V, ‖z‖ < ρ → ‖w‖ < ρ → ‖z + w‖ < ρ → e₀ (z + w) = e₀ z * e₀ w)
    (z : V) {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (hzN : ‖z‖ < N * ρ) (hzM : ‖z‖ < M * ρ) :
    e₀ ((N : ℝ)⁻¹ • z) ^ N = e₀ ((M : ℝ)⁻¹ • z) ^ M := by
  rw [localHom_pow_mul hρ h z hN hM hzN, localHom_pow_mul hρ h z hM hN hzM, mul_comm N M,
    mul_comm (N : ℝ) M]

/- English proof (translation)
Take `⟨n, hn⟩` from `exists_nat_gt (r / ρ)`. Use `⟨n + 1, Nat.succ_pos n, ?_⟩` and prove the remaining obligations. Rewrite `hn` using `[div_lt_iff₀ hρ]`. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem localHom_exists_nat (hρ : 0 < ρ) (r : ℝ) : ∃ N : ℕ, 0 < N ∧ r < N * ρ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (r / ρ)
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  rw [div_lt_iff₀ hρ] at hn
  push_cast
  nlinarith

/- English proof (translation)
Use `choose N hN hNz using fun z : V => localHom_exists_nat hρ ‖z‖`. Use `⟨fun z => e₀ ((N z : ℝ)⁻¹ • z) ^ N z, ⟨fun z w => ?_, fun z hz => ?_⟩, ?_⟩` and prove the remaining obligations. Take `⟨M, hM, hMz⟩` from `localHom_exists_nat hρ (‖z‖ + ‖w‖)`. Establish `hz : ‖z‖ < M * ρ` using `by linarith [norm_nonneg w]`. Establish `hw : ‖w‖ < M * ρ` using `by linarith [norm_nonneg z]`.

Establish `hzw : ‖z + w‖ < M * ρ` using `(norm_add_le z w).trans_lt hMz`. Establish `hb` using `localHom_norm_inv_smul_lt _ hM hzw`. Rewrite `hb` using `[smul_add]`. Simplify using `only`. Rewrite using `[localHom_pow_indep hρ h z (hN z) hM (hNz z) hz, localHom_pow_indep hρ h w (hN w) hM (hNz w) hw, localHom_pow_indep hρ h (z + w) (hN _) hM (hNz _) hzw, smul_add, h _ _ (localHom_norm_inv_smul_lt z hM hz) (localHom_norm_inv_smul_lt w hM hw) hb, mul_pow]`.

Simplify using `only`. Rewrite using `[localHom_pow_indep hρ h z (hN z) one_pos (hNz z) (by simpa using hz)]`. Simplify using the standard rewrite rules. Introduce and unpack `e ⟨he, he₀⟩`. Use function extensionality and compare the values at `z`.

Establish `hN' : (0 : ℝ) < N z` using `by exact_mod_cast hN z`. Establish `hb` using `localHom_norm_inv_smul_lt z (hN z) (hNz z)`. Establish `key` using `localHom_nsmul (ρ := ‖z‖ + 1) (e₀ := e) (by positivity) (fun a b _ _ _ => he a b) ((N z : ℝ)⁻¹ • z) (N z) (by`. Rewrite using `[norm_smul, Real.norm_of_nonneg (by positivity), mul_inv_cancel_left₀ hN'.ne']`. Use the proof step `linarith)`.

Rewrite `key` using `[smul_inv_smul₀ hN'.ne', he₀ _ hb]`. Conclude with `key`.
-/
theorem localHom_existsUnique_extension (hρ : 0 < ρ)
    (h : ∀ z w : V, ‖z‖ < ρ → ‖w‖ < ρ → ‖z + w‖ < ρ → e₀ (z + w) = e₀ z * e₀ w) :
    ∃! e : V → A, (∀ z w, e (z + w) = e z * e w) ∧ ∀ z, ‖z‖ < ρ → e z = e₀ z := by
  choose N hN hNz using fun z : V => localHom_exists_nat hρ ‖z‖
  refine ⟨fun z => e₀ ((N z : ℝ)⁻¹ • z) ^ N z, ⟨fun z w => ?_, fun z hz => ?_⟩, ?_⟩
  · obtain ⟨M, hM, hMz⟩ := localHom_exists_nat hρ (‖z‖ + ‖w‖)
    have hz : ‖z‖ < M * ρ := by linarith [norm_nonneg w]
    have hw : ‖w‖ < M * ρ := by linarith [norm_nonneg z]
    have hzw : ‖z + w‖ < M * ρ := (norm_add_le z w).trans_lt hMz
    have hb := localHom_norm_inv_smul_lt _ hM hzw
    rw [smul_add] at hb
    simp only
    rw [localHom_pow_indep hρ h z (hN z) hM (hNz z) hz,
      localHom_pow_indep hρ h w (hN w) hM (hNz w) hw,
      localHom_pow_indep hρ h (z + w) (hN _) hM (hNz _) hzw, smul_add,
      h _ _ (localHom_norm_inv_smul_lt z hM hz) (localHom_norm_inv_smul_lt w hM hw) hb, mul_pow]
  · simp only
    rw [localHom_pow_indep hρ h z (hN z) one_pos (hNz z) (by simpa using hz)]
    simp
  · rintro e ⟨he, he₀⟩
    funext z
    have hN' : (0 : ℝ) < N z := by exact_mod_cast hN z
    have hb := localHom_norm_inv_smul_lt z (hN z) (hNz z)
    have key := localHom_nsmul (ρ := ‖z‖ + 1) (e₀ := e) (by positivity)
      (fun a b _ _ _ => he a b) ((N z : ℝ)⁻¹ • z) (N z) (by
        rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_inv_cancel_left₀ hN'.ne']
        linarith)
    rw [smul_inv_smul₀ hN'.ne', he₀ _ hb] at key
    exact key

end LocalHom

/- English proof (translation)
Introduce `g A _ ρ hρ e₀ h`. Simplify using `only [mem_ball_zero_iff] at h ⊢`. Conclude with `localHom_existsUnique_extension hρ fun z w hz hw hzw => h z hz w hw hzw`.
-/
theorem existsUnique_extension_of_ball :
    ∀ (g : ℕ) (A : Type) [CommGroup A] (ρ : ℝ), 0 < ρ → ∀ e₀ : (Fin g → ℂ) → A,
      (∀ z ∈ ball (0 : Fin g → ℂ) ρ, ∀ w ∈ ball (0 : Fin g → ℂ) ρ,
        z + w ∈ ball (0 : Fin g → ℂ) ρ → e₀ (z + w) = e₀ z * e₀ w) →
      ∃! e : (Fin g → ℂ) → A, (∀ z w, e (z + w) = e z * e w) ∧
        ∀ z ∈ ball (0 : Fin g → ℂ) ρ, e z = e₀ z := by
  intro g A _ ρ hρ e₀ h
  simp only [mem_ball_zero_iff] at h ⊢
  exact localHom_existsUnique_extension hρ fun z w hz hw hzw => h z hz w hw hzw

end GlobalTheory.CompanionTheory.Ar.Flat
