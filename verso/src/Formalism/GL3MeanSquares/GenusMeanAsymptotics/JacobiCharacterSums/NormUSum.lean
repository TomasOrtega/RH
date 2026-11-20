import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.UbTerms
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHFinishB

open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds

/- English proof (translation)
Establish `e : ∑ i, ((η : ℂ) / w i) ^ j = (η : ℂ) ^ j * ∑ i, 1 / (w i) ^ j`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[div_pow, mul_one_div]`. Rewrite using `[e, norm_mul, norm_pow]`.

Use `congr 2`. Simplify using `using abs_of_nonneg hη`.
-/
theorem norm_u_sum (η : ℝ) {N : ℕ} (w : Fin N → ℂ) (j : ℕ) (hη : 0 ≤ η) :
    ‖∑ i, ((η : ℂ) / w i) ^ j‖ = η ^ j * ‖∑ i, 1 / (w i) ^ j‖ := by
  have e : ∑ i, ((η : ℂ) / w i) ^ j = (η : ℂ) ^ j * ∑ i, 1 / (w i) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_pow, mul_one_div]
  rw [e, norm_mul, norm_pow]
  congr 2
  simpa using abs_of_nonneg hη

/- English proof (translation)
Use `set D := Real.log (max CT 1) with hD_def`. Establish `hD : 0 ≤ D` using `Real.log_nonneg (le_max_right _ _)`. Establish `hL0 : 0 < L` using `by linarith`. Establish `hη : 0 < η` using `lt_of_lt_of_le (by positivity) hηZ`. Establish `hr` using `rr_gt a`.

Establish `hr0 : 0 < rr a` using `by linarith`. Establish `hε0` using `eps_pos a`. Establish `hε1` using `eps_le a`. Establish `hth` using `th_pos a`. Establish `hκ` using `kap_pos a ha D hD`.

Establish `hκth` using `kap_le a ha D hD`. Establish `hE0 : 0 < E0 a D` using `Real.exp_pos _`. Establish `hG : 0 < GG a CP cZ cS c₁` using `by unfold GG; positivity`. Establish `hK0 : 0 < K0 a D CP cZ cS c₁` using `by unfold K0; positivity`. Establish `hKpos : 0 < K` using `lt_trans hK0 hK`.

Establish `hthK : E0 a D * GG a CP cZ cS c₁ < th a * K`. Establish `h1 : K0 a D CP cZ cS c₁ * th a = E0 a D * GG a CP cZ cS c₁` using `by unfold K0; field_simp`. Establish `h2 : K0 a D CP cZ cS c₁ * th a < K * th a` using `mul_lt_mul_of_pos_right hK hth`. Combine the linear relations using `only [h1, h2]`. Establish `hexpK : Real.exp (-K) ≤ 1` using `Real.exp_le_one_iff.mpr (by linarith)`.

Establish `hXc : lam * L ^ 3 ≤ c₁`. Rewrite using `[hX]`. Use `mul_le_mul_of_nonneg_left hexpK hc₁.le` as an intermediate fact. Combine the linear relations using `only [this]`. Establish `hlη1 : lam / η ≤ 2 * (lam * L) / cZ`.

Rewrite using `[div_le_div_iff₀ hη hcZ]`. Establish `h1 : cZ ≤ 2 * L * η` using `by rw [div_le_iff₀ (by positivity)] at hηZ; linarith only [hηZ]`. Use `mul_le_mul_of_nonneg_left h1 hlam.le` as an intermediate fact. Combine the linear relations using `only [this]`. Establish `hlamL : lam * L ≤ lam * L ^ 3`.

Establish `h2 : 1 ≤ L ^ 2` using `one_le_pow₀ hL`. Establish `h3 : L ≤ L ^ 3`. Establish `: L ^ 3 = L * L ^ 2` using `by ring`. Rewrite using `[this]`. Use `mul_le_mul_of_nonneg_left h2 hL0.le` as an intermediate fact.

Combine the linear relations using `only [this]`. Conclude with `mul_le_mul_of_nonneg_left h3 hlam.le`. Establish `hlη2 : lam / η ≤ 1 / 2`. Establish `h1 : 2 * (lam * L) / cZ ≤ 1 / 2`. Rewrite using `[div_le_iff₀ hcZ]`.

Combine the linear relations using `only [hlamL, hXc, hc₁Z]`. Combine the linear relations using `only [h1, hlη1]`. Use `set u : Fin N → ℂ := fun i => (η : ℂ) / w i with hu_def`. Establish `hu : ∀ i, ‖u i‖ ^ 2 ≤ (u i).re` using `fun i => Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.u_disc η hη (w i) (hw i)`. Establish `hi : ∃ i, 1 / 2 ≤ ‖u i‖`.

Take `⟨i, hi⟩` from `hi0`. Use `⟨i, ?_⟩` and prove the remaining obligations. Simplify using `only [hu_def, hi, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη, abs_of_pos (by linarith : (0 : ℝ) < η + η)]`. Rewrite using `[le_div_iff₀ (by linarith)]; linarith`. Use `set S : ℝ := ∑ i, (u i).re with hS_def`.

Establish `hS0 : 0 ≤ S` using `Finset.sum_nonneg (fun i _ => le_trans (by positivity) (hu i))`. Establish `hS_eq : S = η * (∑ i, 1 / w i).re`. Use `Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.u_sum_re η w 1` as an intermediate fact. Simplify using `only [pow_one] at this`. Rewrite using `[hS_def, ← this, Complex.re_sum]`.

Establish `hSle : S ≤ 2 * (lam / η) + 25 * CF * (η * L)`. Rewrite using `[hS_eq]`. Establish `h2` using `mul_le_mul_of_nonneg_left hS hη.le`. Establish `h3 : η * (2 * lam / η ^ 2 + CF * L * 25) = 2 * (lam / η) + 25 * CF * (η * L)`. Clear the denominators using the available nonvanishing facts.

Combine the linear relations using `only [h2, h3]`. Establish `h25c : 25 * CF * c₂ ≤ kap a D`. Rewrite using `[le_div_iff₀ (by positivity)] at hc₂κ; linarith only [hc₂κ]`. Establish `hCFηL : 25 * CF * (η * L) ≤ kap a D * K`. Establish `h1 : 25 * CF * (η * L) ≤ 25 * CF * (c₂ * K)` using `mul_le_mul_of_nonneg_left hηL.le (by positivity)`.

Establish `h2` using `mul_le_mul_of_nonneg_right h25c hKpos.le`. Combine the linear relations using `only [h1, h2]`. Establish `hSK : S ≤ 1 + kap a D * K` using `by linarith only [hSle, hCFηL, hlη2]`. Use `set m := ⌈th a * K⌉₊ with hm_def`. Establish `hm1 : 1 ≤ m` using `Nat.one_le_iff_ne_zero.mpr (by`.

Rewrite using `[hm_def]; exact (Nat.ceil_pos.mpr (by positivity)).ne')`. Establish `hmle : (m : ℝ) < th a * K + 1` using `Nat.ceil_lt_add_one (by positivity)`. Establish `hmge : th a * K ≤ m` using `Nat.le_ceil _`. Take `⟨j, n, hmj, hjan, hn1, hnS, hLB⟩` from `exists_power_sum_lower_bound CT a hCT hT (eps a) hε0 (by linarith) N u hu hi m hm1`. Establish `hjr1 : (m : ℝ) + 1 ≤ j` using `by exact_mod_cast hmj`.

Establish `hjr : th a * K < j` using `by linarith only [hjr1, hmge]`. Establish `hj1 : 1 ≤ j` using `by omega`. Establish `hj2 : 2 ≤ j` using `by omega`. Establish `hnε : (n : ℝ) * eps a ^ 2 ≤ 1 + kap a D * K` using `le_trans hnS hSK`. Establish `hjan' : (j : ℝ) ≤ m + a * n` using `by exact_mod_cast hjan`.

Establish `hjup : (j : ℝ) ≤ 2 * th a * K + j0 a`. Establish `h1 : (a : ℝ) * n ≤ a / eps a ^ 2 + a * kap a D / eps a ^ 2 * K`. Establish `: (n : ℝ) ≤ (1 + kap a D * K) / eps a ^ 2` using `by rw [le_div_iff₀ (by positivity)]; exact hnε`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : a * kap a D / eps a ^ 2 * K ≤ th a * K` using `mul_le_mul_of_nonneg_right (akap_le' a ha D hD) hKpos.le`.

Unfold `j0`. Combine the linear relations using `only [h1, h2, hjan', hmle]`. Establish `hanD : (a : ℝ) * n * D ≤ a * D / eps a ^ 2 + j`. Establish `h1 : (a : ℝ) * n * D = (a * D / eps a ^ 2) * (n * eps a ^ 2)` using `by field_simp`. Establish `h2` using `akapD_le a ha D hD`.

Establish `h3 : (a * D / eps a ^ 2) * (n * eps a ^ 2) ≤ (a * D / eps a ^ 2) * (1 + kap a D * K)` using `mul_le_mul_of_nonneg_left hnε (by positivity)`. Establish `h4 : (a * D / eps a ^ 2) * (1 + kap a D * K) = a * D / eps a ^ 2 + (a * D * kap a D / eps a ^ 2) * K` using `by ring`. Establish `h5` using `mul_le_mul_of_nonneg_right h2 hKpos.le`. Combine the linear relations using `only [h1, h3, h4, h5, hjr]`. Establish `hLB2 : 1 / (E0 a D * (rr a / 8) ^ j) ≤ ‖∑ i, u i ^ j‖ + eps a ^ (j - 2) * S` using `le_trans (lb_part a D m n j _ (by omega) hanD (turan_lb CT hCT a n m hn1)) hLB`.

Establish `hU : ‖∑ i, u i ^ j‖ ≤ (8 * CP / cZ + 4 / cZ + 32 * CP / cS) * ((j : ℝ) + 1) ^ 2 * (lam * L ^ 3) + (1 + rr a) * ((j : ℝ) + 1) ^ 2 / rr a ^ j`. Establish `h1 : ‖∑ i, u i ^ j‖ = η ^ j * ‖∑ i, 1 / (w i) ^ j‖` using `norm_u_sum η w j hη.le`. Establish `h2` using `mul_le_mul_of_nonneg_left (hpow j hj1) (pow_pos hη j).le`. Establish `hc₂P' : 2 * Real.exp 1 * CP * c₂ * rr a ≤ th a`. Rewrite using `[le_div_iff₀ (by positivity)] at hc₂P; linarith only [hc₂P]`.

Establish `h3` using `ub_terms a CP CF cZ cS c₂ (kap a D) L ℓ lam η Mr K j hj1 hCP hCF hcZ hcS hc₂ hL hℓ0 hℓ hlam hη hMr hKpos hlη1 hM hηc hηL h25c hκth hc₂P' hjr`. Rewrite using `[h1]`. Conclude with `le_trans h2 h3`. Establish `hF : eps a ^ (j - 2) * S ≤ rr a ^ 2 * ((j : ℝ) + 1) ^ 2 / rr a ^ j` using `far_part a S j hj2 (by linarith only [hSK, hjr, mul_le_mul_of_nonneg_right hκth hKpos.le])`. Establish `hXj` using `x_part a c₁ K hc₁ j hjup`.

Rewrite `hXj` using `[← hX]`. Use `set cA := 8 * CP / cZ + 4 / cZ + 32 * CP / cS with hcA`. Establish `hcA0 : 0 ≤ cA` using `by positivity`. Establish `hJ0 : 0 ≤ ((j : ℝ) + 1) ^ 2` using `by positivity`. Establish `hU2 : cA * ((j : ℝ) + 1) ^ 2 * (lam * L ^ 3) ≤ cA * ((j : ℝ) + 1) ^ 2 * (c₁ * Real.exp (j0 a * Real.log (rr a)) / rr a ^ j)` using `mul_le_mul_of_nonneg_left hXj (by positivity)`.

Establish `htot : 1 / (E0 a D * (rr a / 8) ^ j) ≤ GG a CP cZ cS c₁ * ((j : ℝ) + 1) ^ 2 / rr a ^ j`. Establish `: GG a CP cZ cS c₁ * ((j : ℝ) + 1) ^ 2 / rr a ^ j = cA * ((j : ℝ) + 1) ^ 2 * (c₁ * Real.exp (j0 a * Real.log (rr a)) / rr a ^ j) + (1 + rr a) * ((j : ℝ) + 1) ^ 2 / rr a ^ j + rr a ^ 2 * ((j : ℝ) + 1) ^ 2 / rr a ^ j`. Unfold `GG`. Rewrite using `[hcA]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Combine the linear relations using `only [hLB2, hU, hF, hU2]`. Conclude with `final_step a (E0 a D) (GG a CP cZ cS c₁) hE0 hG j (by linarith only [hthK, hjr]) htot`.
-/
theorem core2 (CT : ℝ) (a : ℕ) (hCT : 0 < CT) (ha : 1 ≤ a)
    (hT : ∀ (n m : ℕ) (z : Fin n → ℂ), 1 ≤ n → (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) →
      ∃ k : ℕ, m + 1 ≤ k ∧ k ≤ m + a * n ∧ ((n : ℝ) / (CT * ((m : ℝ) + n))) ^ (a * n) ≤ ‖∑ i, z i ^ k‖)
    (CF CP cZ cS c₁ c₂ : ℝ) (hCF : 0 < CF) (hCP : 0 < CP) (hcZ : 0 < cZ) (hcS : 0 < cS) (hc₁ : 0 < c₁)
    (hc₁Z : c₁ ≤ cZ / 4) (hc₂ : 0 < c₂)
    (hc₂κ : c₂ ≤ kap a (Real.log (max CT 1)) / (25 * CF))
    (hc₂P : c₂ ≤ th a / (2 * Real.exp 1 * CP * rr a))
    (L ℓ lam η Mr K : ℝ) (hL : 1 ≤ L) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ 2 * L) (hlam : 0 < lam)
    (hηZ : cZ / (2 * L) ≤ η) (hηc : η ≤ c0 a) (hηL : η * L < c₂ * K) (hMr : 0 < Mr)
    (hM : ℓ ^ 2 / Mr ≤ 32 * lam / cS) (hX : lam * L ^ 3 = c₁ * Real.exp (-K))
    (hK : K0 a (Real.log (max CT 1)) CP cZ cS c₁ < K)
    (N : ℕ) (w : Fin N → ℂ) (hw : ∀ i, η ≤ (w i).re) (hi0 : ∃ i, w i = ((η + η : ℝ) : ℂ))
    (hS : (∑ i, 1 / w i).re ≤ 2 * lam / η ^ 2 + CF * L * 25)
    (hpow : ∀ j : ℕ, 1 ≤ j → ‖∑ i, 1 / (w i) ^ j‖ ≤
        CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η ^ (j + 1) + (CP * ℓ) ^ j / ((j - 1).factorial : ℝ)
        + CP * ((j : ℝ) + 1) * ℓ ^ 2 / (Mr * η ^ j) + 2 * j * lam / η ^ (j + 1) + CF * L * 25 ^ j) :
    False := by
  set D := Real.log (max CT 1) with hD_def
  have hD : 0 ≤ D := Real.log_nonneg (le_max_right _ _)
  have hL0 : 0 < L := by linarith
  have hη : 0 < η := lt_of_lt_of_le (by positivity) hηZ
  have hr := rr_gt a
  have hr0 : 0 < rr a := by linarith
  have hε0 := eps_pos a
  have hε1 := eps_le a
  have hth := th_pos a
  have hκ := kap_pos a ha D hD
  have hκth := kap_le a ha D hD
  have hE0 : 0 < E0 a D := Real.exp_pos _
  have hG : 0 < GG a CP cZ cS c₁ := by unfold GG; positivity
  have hK0 : 0 < K0 a D CP cZ cS c₁ := by unfold K0; positivity
  have hKpos : 0 < K := lt_trans hK0 hK
  have hthK : E0 a D * GG a CP cZ cS c₁ < th a * K := by
    have h1 : K0 a D CP cZ cS c₁ * th a = E0 a D * GG a CP cZ cS c₁ := by unfold K0; field_simp
    have h2 : K0 a D CP cZ cS c₁ * th a < K * th a := mul_lt_mul_of_pos_right hK hth
    linarith only [h1, h2]
  have hexpK : Real.exp (-K) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hXc : lam * L ^ 3 ≤ c₁ := by
    rw [hX]; have := mul_le_mul_of_nonneg_left hexpK hc₁.le; linarith only [this]
  have hlη1 : lam / η ≤ 2 * (lam * L) / cZ := by
    rw [div_le_div_iff₀ hη hcZ]
    have h1 : cZ ≤ 2 * L * η := by rw [div_le_iff₀ (by positivity)] at hηZ; linarith only [hηZ]
    have := mul_le_mul_of_nonneg_left h1 hlam.le
    linarith only [this]
  have hlamL : lam * L ≤ lam * L ^ 3 := by
    have h2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
    have h3 : L ≤ L ^ 3 := by
      have : L ^ 3 = L * L ^ 2 := by ring
      rw [this]; have := mul_le_mul_of_nonneg_left h2 hL0.le; linarith only [this]
    exact mul_le_mul_of_nonneg_left h3 hlam.le
  have hlη2 : lam / η ≤ 1 / 2 := by
    have h1 : 2 * (lam * L) / cZ ≤ 1 / 2 := by
      rw [div_le_iff₀ hcZ]; linarith only [hlamL, hXc, hc₁Z]
    linarith only [h1, hlη1]

  set u : Fin N → ℂ := fun i => (η : ℂ) / w i with hu_def
  have hu : ∀ i, ‖u i‖ ^ 2 ≤ (u i).re := fun i => Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.u_disc η hη (w i) (hw i)
  have hi : ∃ i, 1 / 2 ≤ ‖u i‖ := by
    obtain ⟨i, hi⟩ := hi0
    refine ⟨i, ?_⟩
    simp only [hu_def, hi, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη,
      abs_of_pos (by linarith : (0 : ℝ) < η + η)]
    rw [le_div_iff₀ (by linarith)]; linarith
  set S : ℝ := ∑ i, (u i).re with hS_def
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => le_trans (by positivity) (hu i))
  have hS_eq : S = η * (∑ i, 1 / w i).re := by
    have := Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.u_sum_re η w 1
    simp only [pow_one] at this
    rw [hS_def, ← this, Complex.re_sum]
  have hSle : S ≤ 2 * (lam / η) + 25 * CF * (η * L) := by
    rw [hS_eq]
    have h2 := mul_le_mul_of_nonneg_left hS hη.le
    have h3 : η * (2 * lam / η ^ 2 + CF * L * 25) = 2 * (lam / η) + 25 * CF * (η * L) := by
      field_simp
    linarith only [h2, h3]
  have h25c : 25 * CF * c₂ ≤ kap a D := by
    rw [le_div_iff₀ (by positivity)] at hc₂κ; linarith only [hc₂κ]
  have hCFηL : 25 * CF * (η * L) ≤ kap a D * K := by
    have h1 : 25 * CF * (η * L) ≤ 25 * CF * (c₂ * K) := mul_le_mul_of_nonneg_left hηL.le (by positivity)
    have h2 := mul_le_mul_of_nonneg_right h25c hKpos.le
    linarith only [h1, h2]
  have hSK : S ≤ 1 + kap a D * K := by linarith only [hSle, hCFηL, hlη2]

  set m := ⌈th a * K⌉₊ with hm_def
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by
    rw [hm_def]; exact (Nat.ceil_pos.mpr (by positivity)).ne')
  have hmle : (m : ℝ) < th a * K + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmge : th a * K ≤ m := Nat.le_ceil _
  obtain ⟨j, n, hmj, hjan, hn1, hnS, hLB⟩ :=
    exists_power_sum_lower_bound CT a hCT hT (eps a) hε0 (by linarith) N u hu hi m hm1
  have hjr1 : (m : ℝ) + 1 ≤ j := by exact_mod_cast hmj
  have hjr : th a * K < j := by linarith only [hjr1, hmge]
  have hj1 : 1 ≤ j := by omega
  have hj2 : 2 ≤ j := by omega
  have hnε : (n : ℝ) * eps a ^ 2 ≤ 1 + kap a D * K := le_trans hnS hSK
  have hjan' : (j : ℝ) ≤ m + a * n := by exact_mod_cast hjan
  have hjup : (j : ℝ) ≤ 2 * th a * K + j0 a := by
    have h1 : (a : ℝ) * n ≤ a / eps a ^ 2 + a * kap a D / eps a ^ 2 * K := by
      have : (n : ℝ) ≤ (1 + kap a D * K) / eps a ^ 2 := by rw [le_div_iff₀ (by positivity)]; exact hnε
      calc (a : ℝ) * n ≤ a * ((1 + kap a D * K) / eps a ^ 2) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have h2 : a * kap a D / eps a ^ 2 * K ≤ th a * K :=
      mul_le_mul_of_nonneg_right (akap_le' a ha D hD) hKpos.le
    unfold j0; linarith only [h1, h2, hjan', hmle]
  have hanD : (a : ℝ) * n * D ≤ a * D / eps a ^ 2 + j := by
    have h1 : (a : ℝ) * n * D = (a * D / eps a ^ 2) * (n * eps a ^ 2) := by field_simp
    have h2 := akapD_le a ha D hD
    have h3 : (a * D / eps a ^ 2) * (n * eps a ^ 2) ≤ (a * D / eps a ^ 2) * (1 + kap a D * K) :=
      mul_le_mul_of_nonneg_left hnε (by positivity)
    have h4 : (a * D / eps a ^ 2) * (1 + kap a D * K) = a * D / eps a ^ 2 + (a * D * kap a D / eps a ^ 2) * K := by ring
    have h5 := mul_le_mul_of_nonneg_right h2 hKpos.le
    linarith only [h1, h3, h4, h5, hjr]
  have hLB2 : 1 / (E0 a D * (rr a / 8) ^ j) ≤ ‖∑ i, u i ^ j‖ + eps a ^ (j - 2) * S :=
    le_trans (lb_part a D m n j _ (by omega) hanD (turan_lb CT hCT a n m hn1)) hLB

  have hU : ‖∑ i, u i ^ j‖ ≤ (8 * CP / cZ + 4 / cZ + 32 * CP / cS) * ((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)
        + (1 + rr a) * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
    have h1 : ‖∑ i, u i ^ j‖ = η ^ j * ‖∑ i, 1 / (w i) ^ j‖ := norm_u_sum η w j hη.le
    have h2 := mul_le_mul_of_nonneg_left (hpow j hj1) (pow_pos hη j).le
    have hc₂P' : 2 * Real.exp 1 * CP * c₂ * rr a ≤ th a := by
      rw [le_div_iff₀ (by positivity)] at hc₂P; linarith only [hc₂P]
    have h3 := ub_terms a CP CF cZ cS c₂ (kap a D) L ℓ lam η Mr K j hj1 hCP hCF hcZ hcS hc₂ hL hℓ0 hℓ hlam hη
      hMr hKpos hlη1 hM hηc hηL h25c hκth hc₂P' hjr
    rw [h1]; exact le_trans h2 h3
  have hF : eps a ^ (j - 2) * S ≤ rr a ^ 2 * ((j : ℝ) + 1) ^ 2 / rr a ^ j :=
    far_part a S j hj2 (by linarith only [hSK, hjr, mul_le_mul_of_nonneg_right hκth hKpos.le])
  have hXj := x_part a c₁ K hc₁ j hjup
  rw [← hX] at hXj
  set cA := 8 * CP / cZ + 4 / cZ + 32 * CP / cS with hcA
  have hcA0 : 0 ≤ cA := by positivity
  have hJ0 : 0 ≤ ((j : ℝ) + 1) ^ 2 := by positivity
  have hU2 : cA * ((j : ℝ) + 1) ^ 2 * (lam * L ^ 3) ≤
      cA * ((j : ℝ) + 1) ^ 2 * (c₁ * Real.exp (j0 a * Real.log (rr a)) / rr a ^ j) :=
    mul_le_mul_of_nonneg_left hXj (by positivity)
  have htot : 1 / (E0 a D * (rr a / 8) ^ j) ≤ GG a CP cZ cS c₁ * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
    have : GG a CP cZ cS c₁ * ((j : ℝ) + 1) ^ 2 / rr a ^ j =
        cA * ((j : ℝ) + 1) ^ 2 * (c₁ * Real.exp (j0 a * Real.log (rr a)) / rr a ^ j)
        + (1 + rr a) * ((j : ℝ) + 1) ^ 2 / rr a ^ j + rr a ^ 2 * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
      unfold GG; rw [hcA]; ring
    rw [this]; linarith only [hLB2, hU, hF, hU2]
  exact final_step a (E0 a D) (GG a CP cZ cS c₁) hE0 hG j (by linarith only [hthK, hjr]) htot

end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
