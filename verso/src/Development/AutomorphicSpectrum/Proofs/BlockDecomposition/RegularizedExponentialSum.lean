import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FibreFactorHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VandermondeSeparation

open Filter Topology
open scoped Classical

namespace GlobalTheory.CompanionTheory.ExpSums

/- English proof (translation)
Establish `ht : |t| < 1` using `by rw [abs_of_nonneg h0]; exact h1`. Establish `hlim : Tendsto (fun n : ℕ => (2 : ℝ) ^ N * ((n : ℝ) ^ N * t ^ n)) atTop (𝓝 0)`. Establish `h` using `(tendsto_pow_const_mul_const_pow_of_abs_lt_one N ht).const_mul ((2 : ℝ) ^ N)`. Rewrite `h` using `[mul_zero]`. Then use the resulting hypothesis. Use `squeeze_zero' (Filter.Eventually.of_forall fun n => mul_nonneg (by positivity) (pow_nonneg h0 n)) ?_ hlim` and prove the remaining obligations.

Use `filter_upwards [eventually_ge_atTop 1] with n hn`. Establish `hn' : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hle : (1 + (n : ℝ)) ^ N ≤ (2 * (n : ℝ)) ^ N` using `by gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tendsto_one_add_pow_mul_pow {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) (N : ℕ) :
    Tendsto (fun n : ℕ => (1 + (n : ℝ)) ^ N * t ^ n) atTop (𝓝 0) := by
  have ht : |t| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have hlim : Tendsto (fun n : ℕ => (2 : ℝ) ^ N * ((n : ℝ) ^ N * t ^ n)) atTop (𝓝 0) := by
    have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one N ht).const_mul ((2 : ℝ) ^ N)
    rwa [mul_zero] at h
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => mul_nonneg (by positivity) (pow_nonneg h0 n)) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hle : (1 + (n : ℝ)) ^ N ≤ (2 * (n : ℝ)) ^ N := by
    gcongr
    linarith
  calc (1 + (n : ℝ)) ^ N * t ^ n ≤ (2 * (n : ℝ)) ^ N * t ^ n :=
        mul_le_mul_of_nonneg_right hle (pow_nonneg h0 n)
    _ = (2 : ℝ) ^ N * ((n : ℝ) ^ N * t ^ n) := by ring

/- English proof (translation)
Introduce `ι _ c lam ρ C N hρ hbound μ hμ`. Take `⟨d, hd⟩ : ∃ d : ℂ → ℂ, ∀ ν, d ν = ∑ i with lam i = ν, c i` from `⟨_, fun _ => rfl⟩`. Rewrite using `[← hd]`. Take `⟨S, hS⟩ : ∃ S : Finset ℂ, S = Finset.univ.image lam` from `⟨_, rfl⟩`. Distinguish the cases in `hμS : μ ∉ S`.

Rewrite using `[hd]`. Use `Finset.sum_eq_zero fun i hi => absurd ?_ hμS` and prove the remaining obligations. Rewrite using `[hS, ← (Finset.mem_filter.mp hi).2]`. Conclude with `Finset.mem_image_of_mem lam (Finset.mem_univ i)`. Use `push_neg at hμS`.

Establish `hmaps : ∀ i ∈ (Finset.univ : Finset ι), lam i ∈ S` using `fun i _ => by`. Rewrite using `[hS]`. Conclude with `Finset.mem_image_of_mem lam (Finset.mem_univ i)`. Establish `hsum : ∀ k : ℕ, ∑ i, c i * lam i ^ k = ∑ ν ∈ S, d ν * ν ^ k`. Introduce `k`.

Rewrite using `[← Finset.sum_fiberwise_of_maps_to hmaps]`. Use `Finset.sum_congr rfl fun ν _ => ?_` and prove the remaining obligations. Rewrite using `[hd, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[(Finset.mem_filter.mp hi).2]`.

Take `⟨e, -⟩ : ∃ e : Fin S.card ≃ S, e = S.equivFin.symm` from `⟨_, rfl⟩`. Take `⟨α, hα⟩ : ∃ α : Fin S.card → ℂ, ∀ k, α k = (e k : ℂ)` from `⟨_, fun _ => rfl⟩`. Establish `hinj : Function.Injective α`. Introduce `a b hab`. Rewrite `hab` using `[hα, hα]`.

Conclude with `e.injective (Subtype.val_injective hab)`. Establish `hpow : ∀ n : ℕ, ∑ k, d (α k) * α k ^ n = ∑ i, c i * lam i ^ n`. Introduce `n`. Rewrite using `[hsum n]`. Simplify using `only [hα]`.

Conclude with `(Equiv.sum_comp e (fun x : S => d x * (x : ℂ) ^ n)).trans (Finset.sum_coe_sort S (fun ν => d ν * ν ^ n))`. Take `⟨C', hC'⟩` from `GlobalTheory.CompanionTheory.ExpSums.vandermonde_separation S.card α hinj`. Take `⟨C1, hC1, hC'1⟩ : ∃ C1 : ℝ, 0 ≤ C1 ∧ C' ≤ C1` from `⟨max C' 0, le_max_right _ _, le_max_left _ _⟩`. Take `⟨C2, hC2, hCC2⟩ : ∃ C2 : ℝ, 0 ≤ C2 ∧ C ≤ C2` from `⟨max C 0, le_max_right _ _, le_max_left _ _⟩`. Take `⟨B, hB⟩ : ∃ B : ℝ, B = ∑ s : Fin S.card, (1 + ((s : ℕ) : ℝ)) ^ N * ρ ^ (s : ℕ)` from `⟨_, rfl⟩`.

Take `⟨K0, hK0⟩` from `Filter.eventually_atTop.mp hbound`. Establish `hK0' : ∀ k : ℕ, K0 ≤ k → ‖∑ i, c i * lam i ^ k‖ ≤ C2 * (1 + (k : ℝ)) ^ N * ρ ^ k`. Introduce `k hk`. Use `(hK0 k hk).trans ?_` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC2 (pow_nonneg (by positivity) N)) (pow_nonneg hρ k)`.

Take `⟨j, hj⟩ : ∃ j : Fin S.card, α j = μ` from `⟨e.symm ⟨μ, hμS⟩, by rw [hα, Equiv.apply_symm_apply]⟩`. Establish `key : ∀ m : ℕ, K0 ≤ m → ‖d μ‖ * ‖μ‖ ^ m ≤ C1 * (C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * B)`. Introduce `m hm`. Establish `h1` using `hC' (fun k => d (α k) * α k ^ m) j`. Establish `hinner : ∀ s : Fin S.card, ∑ k, d (α k) * α k ^ m * α k ^ (s : ℕ) = ∑ i, c i * lam i ^ (m + (s : ℕ))`.

Introduce `s`. Rewrite using `[← hpow (m + (s : ℕ))]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[pow_add]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [hinner, hj, norm_mul, norm_pow] at h1`. Establish `hT : 0 ≤ ∑ s : Fin S.card, ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖` using `Finset.sum_nonneg fun _ _ => norm_nonneg _`. Establish `hsb : ∑ s : Fin S.card, ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖ ≤ C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * B`. Rewrite using `[hB, Finset.mul_sum]`. Use `Finset.sum_le_sum fun s _ => ?_` and prove the remaining obligations.

Establish `hk` using `hK0' (m + (s : ℕ)) (le_trans hm (Nat.le_add_right m _))`. Rewrite `hk` using `[Nat.cast_add]`. Establish `hbase : 1 + ((m : ℝ) + ((s : ℕ) : ℝ)) ≤ (1 + (m : ℝ)) * (1 + ((s : ℕ) : ℝ))`. Establish `hms : (0 : ℝ) ≤ (m : ℝ) * ((s : ℕ) : ℝ)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hle : (1 + ((m : ℝ) + ((s : ℕ) : ℝ))) ^ N ≤ (1 + (m : ℝ)) ^ N * (1 + ((s : ℕ) : ℝ)) ^ N`. Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ (by positivity) hbase N`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[pow_add]`.

Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Establish `hμpos : 0 < ‖μ‖` using `lt_of_le_of_lt hρ hμ`. Take `⟨t, ht⟩ : ∃ t : ℝ, t = ρ / ‖μ‖` from `⟨_, rfl⟩`. Establish `ht0 : 0 ≤ t` using `by rw [ht]; exact div_nonneg hρ (norm_nonneg _)`.

Establish `ht1 : t < 1` using `by rw [ht, div_lt_one hμpos]; exact hμ`. Establish `hlim` using `(tendsto_one_add_pow_mul_pow ht0 ht1 N).const_mul (C1 * (C2 * B))`. Rewrite `hlim` using `[mul_zero]`. Establish `hle : ∀ m : ℕ, K0 ≤ m → ‖d μ‖ ≤ C1 * (C2 * B) * ((1 + (m : ℝ)) ^ N * t ^ m)`. Introduce `m hm`.

Establish `h` using `(le_div_iff₀ (pow_pos hμpos m)).mpr (key m hm)`. Rewrite using `[ht, div_pow]`. Combine the equalities or inequalities in the displayed calculation. Establish `h0 : ‖d μ‖ ≤ 0` using `ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨K0, hle⟩)`. Conclude with `norm_le_zero_iff.mp h0`.
-/
theorem expSum_holds : PositivityTheory.Rg.BcB.F.ExpSum := by
  intro ι _ c lam ρ C N hρ hbound μ hμ
  obtain ⟨d, hd⟩ : ∃ d : ℂ → ℂ, ∀ ν, d ν = ∑ i with lam i = ν, c i := ⟨_, fun _ => rfl⟩
  rw [← hd]
  obtain ⟨S, hS⟩ : ∃ S : Finset ℂ, S = Finset.univ.image lam := ⟨_, rfl⟩
  by_cases hμS : μ ∉ S
  · rw [hd]
    refine Finset.sum_eq_zero fun i hi => absurd ?_ hμS
    rw [hS, ← (Finset.mem_filter.mp hi).2]
    exact Finset.mem_image_of_mem lam (Finset.mem_univ i)
  push_neg at hμS
  have hmaps : ∀ i ∈ (Finset.univ : Finset ι), lam i ∈ S := fun i _ => by
    rw [hS]; exact Finset.mem_image_of_mem lam (Finset.mem_univ i)
  have hsum : ∀ k : ℕ, ∑ i, c i * lam i ^ k = ∑ ν ∈ S, d ν * ν ^ k := by
    intro k
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [hd, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.mp hi).2]
  obtain ⟨e, -⟩ : ∃ e : Fin S.card ≃ S, e = S.equivFin.symm := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : Fin S.card → ℂ, ∀ k, α k = (e k : ℂ) := ⟨_, fun _ => rfl⟩
  have hinj : Function.Injective α := by
    intro a b hab
    rw [hα, hα] at hab
    exact e.injective (Subtype.val_injective hab)
  have hpow : ∀ n : ℕ, ∑ k, d (α k) * α k ^ n = ∑ i, c i * lam i ^ n := by
    intro n
    rw [hsum n]
    simp only [hα]
    exact (Equiv.sum_comp e (fun x : S => d x * (x : ℂ) ^ n)).trans
      (Finset.sum_coe_sort S (fun ν => d ν * ν ^ n))
  obtain ⟨C', hC'⟩ := GlobalTheory.CompanionTheory.ExpSums.vandermonde_separation S.card α hinj
  obtain ⟨C1, hC1, hC'1⟩ : ∃ C1 : ℝ, 0 ≤ C1 ∧ C' ≤ C1 := ⟨max C' 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨C2, hC2, hCC2⟩ : ∃ C2 : ℝ, 0 ≤ C2 ∧ C ≤ C2 := ⟨max C 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∑ s : Fin S.card, (1 + ((s : ℕ) : ℝ)) ^ N * ρ ^ (s : ℕ) := ⟨_, rfl⟩
  obtain ⟨K0, hK0⟩ := Filter.eventually_atTop.mp hbound
  have hK0' : ∀ k : ℕ, K0 ≤ k → ‖∑ i, c i * lam i ^ k‖ ≤ C2 * (1 + (k : ℝ)) ^ N * ρ ^ k := by
    intro k hk
    refine (hK0 k hk).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCC2 (pow_nonneg (by positivity) N)) (pow_nonneg hρ k)
  obtain ⟨j, hj⟩ : ∃ j : Fin S.card, α j = μ := ⟨e.symm ⟨μ, hμS⟩, by rw [hα, Equiv.apply_symm_apply]⟩
  have key : ∀ m : ℕ, K0 ≤ m → ‖d μ‖ * ‖μ‖ ^ m ≤ C1 * (C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * B) := by
    intro m hm
    have h1 := hC' (fun k => d (α k) * α k ^ m) j
    have hinner : ∀ s : Fin S.card,
        ∑ k, d (α k) * α k ^ m * α k ^ (s : ℕ) = ∑ i, c i * lam i ^ (m + (s : ℕ)) := by
      intro s
      rw [← hpow (m + (s : ℕ))]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_add]
      ring
    simp only [hinner, hj, norm_mul, norm_pow] at h1
    have hT : 0 ≤ ∑ s : Fin S.card, ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hsb : ∑ s : Fin S.card, ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖ ≤
        C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * B := by
      rw [hB, Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      have hk := hK0' (m + (s : ℕ)) (le_trans hm (Nat.le_add_right m _))
      rw [Nat.cast_add] at hk
      have hbase : 1 + ((m : ℝ) + ((s : ℕ) : ℝ)) ≤ (1 + (m : ℝ)) * (1 + ((s : ℕ) : ℝ)) := by
        have hms : (0 : ℝ) ≤ (m : ℝ) * ((s : ℕ) : ℝ) := by positivity
        nlinarith
      have hle : (1 + ((m : ℝ) + ((s : ℕ) : ℝ))) ^ N ≤ (1 + (m : ℝ)) ^ N * (1 + ((s : ℕ) : ℝ)) ^ N := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) hbase N
      calc ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖
          ≤ C2 * (1 + ((m : ℝ) + ((s : ℕ) : ℝ))) ^ N * ρ ^ (m + (s : ℕ)) := hk
        _ ≤ C2 * ((1 + (m : ℝ)) ^ N * (1 + ((s : ℕ) : ℝ)) ^ N) * ρ ^ (m + (s : ℕ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hC2) (pow_nonneg hρ _)
        _ = C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * ((1 + ((s : ℕ) : ℝ)) ^ N * ρ ^ (s : ℕ)) := by
          rw [pow_add]
          ring
    calc ‖d μ‖ * ‖μ‖ ^ m ≤ C' * ∑ s : Fin S.card, ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖ := h1
      _ ≤ C1 * ∑ s : Fin S.card, ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖ :=
        mul_le_mul_of_nonneg_right hC'1 hT
      _ ≤ C1 * (C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * B) := mul_le_mul_of_nonneg_left hsb hC1
  have hμpos : 0 < ‖μ‖ := lt_of_le_of_lt hρ hμ
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ρ / ‖μ‖ := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg hρ (norm_nonneg _)
  have ht1 : t < 1 := by rw [ht, div_lt_one hμpos]; exact hμ
  have hlim := (tendsto_one_add_pow_mul_pow ht0 ht1 N).const_mul (C1 * (C2 * B))
  rw [mul_zero] at hlim
  have hle : ∀ m : ℕ, K0 ≤ m → ‖d μ‖ ≤ C1 * (C2 * B) * ((1 + (m : ℝ)) ^ N * t ^ m) := by
    intro m hm
    have h := (le_div_iff₀ (pow_pos hμpos m)).mpr (key m hm)
    rw [ht, div_pow]
    calc ‖d μ‖ ≤ C1 * (C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * B) / ‖μ‖ ^ m := h
      _ = C1 * (C2 * B) * ((1 + (m : ℝ)) ^ N * (ρ ^ m / ‖μ‖ ^ m)) := by ring
  have h0 : ‖d μ‖ ≤ 0 := ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨K0, hle⟩)
  exact norm_le_zero_iff.mp h0

end GlobalTheory.CompanionTheory.ExpSums
