import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.KurDefs

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

omit [CompleteSpace K] [CharZero K] in
/- English proof (translation)
Rewrite using `[IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]`.
-/
theorem semilin_norm_add_of_lt {a b : K} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

omit [CompleteSpace K] [CharZero K] in
/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rwa [norm_neg]))`.
-/
theorem semilin_norm_sub_le {a b : K} {t : ℝ} (ha : ‖a‖ ≤ t) (hb : ‖b‖ ≤ t) : ‖a - b‖ ≤ t := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rwa [norm_neg]))

omit [CompleteSpace K] [CharZero K] in

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `e : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n` using `by ring`. Rewrite using `[e]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, norm_pow]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem semilin_norm_pow_sub_pow {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ ‖a - b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖a‖ * ‖a ^ n - b ^ n‖ ≤ 1 * ‖a - b‖ := mul_le_mul ha ih (norm_nonneg _) zero_le_one
        _ = ‖a - b‖ := one_mul _
    · rw [norm_mul, norm_pow]
      calc ‖a - b‖ * ‖b‖ ^ n ≤ ‖a - b‖ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hb) (norm_nonneg _)
        _ = ‖a - b‖ := mul_one _

omit [CompleteSpace K] [CharZero K] in

/- English proof (translation)
Establish `hp : x ^ (l ^ 2) = (x ^ l) ^ l` using `by rw [← pow_mul, sq]`. Establish `e : σ (σ x) - x ^ (l ^ 2) = σ (σ x - x ^ l) + ((σ x) ^ l - (x ^ l) ^ l)`. Rewrite using `[hp, map_sub, map_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : ‖σ x - x ^ l‖ ≤ ‖(l : K)‖` using `h.frob x hx`.

Rewrite using `[e]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[h.isom]`. Conclude with `h1`. Use `(semilin_norm_pow_sub_pow (by rw [h.isom]; exact hx) ?_ l).trans h1` and prove the remaining obligations.

Rewrite using `[norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) hx`.
-/
theorem FrobField.norm_sq_sub_pow_le {l : ℕ} {σ : K →+* K} (h : FrobField K l σ) (x : K) (hx : ‖x‖ ≤ 1) :
    ‖σ (σ x) - x ^ (l ^ 2)‖ ≤ ‖(l : K)‖ := by
  have hp : x ^ (l ^ 2) = (x ^ l) ^ l := by rw [← pow_mul, sq]
  have e : σ (σ x) - x ^ (l ^ 2) = σ (σ x - x ^ l) + ((σ x) ^ l - (x ^ l) ^ l) := by
    rw [hp, map_sub, map_pow]
    ring
  have h1 : ‖σ x - x ^ l‖ ≤ ‖(l : K)‖ := h.frob x hx
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [h.isom]; exact h1
  · refine (semilin_norm_pow_sub_pow (by rw [h.isom]; exact hx) ?_ l).trans h1
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx

omit [CompleteSpace K] [CharZero K] in
open Polynomial in

/- English proof (translation)
Establish `hdeg : (C a * X + C b : K[X]).degree < (X ^ m : K[X]).degree`. Rewrite using `[degree_X_pow]`. Conclude with `lt_of_le_of_lt degree_linear_le (by exact_mod_cast hm)`. Establish `hmon : (X ^ m + (C a * X + C b) : K[X]).Monic` using `monic_X_pow_add (by rwa [degree_X_pow] at hdeg)`. Establish `hnat : (X ^ m + (C a * X + C b) : K[X]).natDegree = m`.

Rewrite using `[natDegree_add_eq_left_of_degree_lt hdeg, natDegree_X_pow]`. Establish `hco : ∀ i, ‖(X ^ m + (C a * X + C b) : K[X]).coeff i‖ ≤ 1`. Introduce `i`. Simplify using `only [coeff_add, coeff_X_pow, coeff_C_mul_X, coeff_C]`. Apply the tactic sequence `refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_))) <;> split_ifs <;> simp [ha, hb]`.

Take `⟨x, hx, hev⟩` from `hR _ hmon (by omega) hco`. Use `⟨x, hx, ?_⟩` and prove the remaining obligations. Simplify `hev` using `[add_assoc]`.
-/
theorem semilin_root {l : ℕ} (hR : ResClosed K l) {m : ℕ} (hm : 2 ≤ m) (a b : K) (ha : ‖a‖ ≤ 1)
    (hb : ‖b‖ ≤ 1) : ∃ x : K, ‖x‖ ≤ 1 ∧ ‖x ^ m + a * x + b‖ ≤ ‖(l : K)‖ := by
  have hdeg : (C a * X + C b : K[X]).degree < (X ^ m : K[X]).degree := by
    rw [degree_X_pow]
    exact lt_of_le_of_lt degree_linear_le (by exact_mod_cast hm)
  have hmon : (X ^ m + (C a * X + C b) : K[X]).Monic := monic_X_pow_add (by rwa [degree_X_pow] at hdeg)
  have hnat : (X ^ m + (C a * X + C b) : K[X]).natDegree = m := by
    rw [natDegree_add_eq_left_of_degree_lt hdeg, natDegree_X_pow]
  have hco : ∀ i, ‖(X ^ m + (C a * X + C b) : K[X]).coeff i‖ ≤ 1 := by
    intro i
    simp only [coeff_add, coeff_X_pow, coeff_C_mul_X, coeff_C]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_))) <;> split_ifs <;> simp [ha, hb]
  obtain ⟨x, hx, hev⟩ := hR _ hmon (by omega) hco
  refine ⟨x, hx, ?_⟩
  simpa [add_assoc] using hev

open Filter Topology in

/- English proof (translation)
Establish `hl2 : 2 ≤ l` using `h.prime.two_le`. Establish `hc0 : c ≠ 0` using `norm_ne_zero_iff.mp (by rw [hc]; norm_num)`. Establish `hcc : c * c⁻¹ = 1` using `mul_inv_cancel₀ hc0`. Establish `hci : ‖c⁻¹‖ = 1` using `by rw [norm_inv, hc, inv_one]`. Establish `hl0 : (l : K) ≠ 0` using `Nat.cast_ne_zero.mpr h.prime.ne_zero`.

Establish `hl1` using `h.norm_l`. Establish `hq4 : 4 ≤ l ^ 2` using `by nlinarith`. Set `P : ℕ → K → Prop` to `fun n ε => ‖ε‖ = 1 ∧ ‖ε - c * σ (σ ε)‖ ≤ ‖(l : K)‖ ^ (n + 1)`. Establish `h0 : ∃ ε, P 0 ε`. Take `⟨x, hx, hev⟩` from `semilin_root hR (m := l ^ 2 - 1) (by omega) 0 (-c⁻¹) (by simp) (by rw [norm_neg, hci])`.

Rewrite `hev` using `[zero_mul, add_zero, ← sub_eq_add_neg]`. Establish `hx1 : ‖x‖ = 1`. Establish `h1 : ‖x ^ (l ^ 2 - 1)‖ = 1`. Establish `e : x ^ (l ^ 2 - 1) = c⁻¹ + (x ^ (l ^ 2 - 1) - c⁻¹)` using `by ring`. Rewrite using `[e, semilin_norm_add_of_lt (by rw [hci]; exact hev.trans_lt hl1), hci]`.

Rewrite `h1` using `[norm_pow]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp h1`. Use `⟨x, hx1, ?_⟩` and prove the remaining obligations. Establish `hxq : x ^ (l ^ 2) = x * x ^ (l ^ 2 - 1)`. Rewrite using `[← pow_succ']`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `e : x - c * σ (σ x) = -(c * x) * (x ^ (l ^ 2 - 1) - c⁻¹) - c * (σ (σ x) - x ^ (l ^ 2))`. Rewrite using `[hxq]`. Take the linear combination `(-x) * hcc`.

Rewrite using `[e, zero_add, pow_one]`. Use `semilin_norm_sub_le ?_ ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_neg, norm_mul, hc, hx1, one_mul, one_mul]`. Conclude with `hev`. Rewrite using `[norm_mul, hc, one_mul]`.

Conclude with `h.norm_sq_sub_pow_le x hx`. Establish `hstep : ∀ n ε, P n ε → ∃ ε', P (n + 1) ε' ∧ ‖ε' - ε‖ ≤ ‖(l : K)‖ ^ (n + 1)`. Introduce and unpack `n ε ⟨hε1, hε2⟩`. Establish `hlam0 : (l : K) ^ (n + 1) ≠ 0` using `pow_ne_zero _ hl0`. Establish `hnl : ‖(l : K) ^ (n + 1)‖ = ‖(l : K)‖ ^ (n + 1)` using `norm_pow _ _`.

Establish `hsm : ‖(l : K)‖ ^ (n + 1) < 1` using `pow_lt_one₀ (norm_nonneg _) hl1 (Nat.succ_ne_zero n)`. Take `⟨ρ, hρ⟩ : ∃ ρ, ε - c * σ (σ ε) = (l : K) ^ (n + 1) * ρ` from `⟨(ε - c * σ (σ ε)) / (l : K) ^ (n + 1), by field_simp⟩`. Establish `hρ1 : ‖ρ‖ ≤ 1`. Establish `hpos : 0 < ‖(l : K)‖ ^ (n + 1)` using `by rw [← hnl]; exact norm_pos_iff.mpr hlam0`. Rewrite `hε2` using `[hρ, norm_mul, hnl]`.

Conclude with `le_of_mul_le_mul_left (by rwa [mul_one]) hpos`. Take `⟨δ, hδ, hev⟩` from `semilin_root hR (m := l ^ 2) (by omega) (-c⁻¹) (-(c⁻¹ * ρ)) (by rw [norm_neg, hci]) (by rw [norm_neg, norm_mul, hci, one_mul]; exact hρ1)`. Establish `hσl : σ (σ ((l : K) ^ (n + 1))) = (l : K) ^ (n + 1)` using `by simp [map_pow, map_natCast]`. Establish `hlδ : ‖(l : K) ^ (n + 1) * δ‖ ≤ ‖(l : K)‖ ^ (n + 1)`. Rewrite using `[norm_mul, hnl]`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨ε + (l : K) ^ (n + 1) * δ, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[semilin_norm_add_of_lt (by rw [hε1]; exact hlδ.trans_lt hsm), hε1]`. Establish `e : ε + (l : K) ^ (n + 1) * δ - c * σ (σ (ε + (l : K) ^ (n + 1) * δ)) = (l : K) ^ (n + 1) * (-c * (δ ^ (l ^ 2) + -c⁻¹ * δ + -(c⁻¹ * ρ)) - c * (σ (σ δ) - δ ^ (l ^ 2)))`. Rewrite using `[map_add, map_add, map_mul, map_mul, hσl]`.

Take the linear combination `hρ - ((l : K) ^ (n + 1) * ρ + (l : K) ^ (n + 1) * δ) * hcc`. Rewrite using `[e, norm_mul, hnl, pow_succ ‖(l : K)‖ (n + 1)]`. Use `mul_le_mul_of_nonneg_left (semilin_norm_sub_le ?_ ?_) (by positivity)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_neg, hc, one_mul]`. Conclude with `hev`.

Rewrite using `[norm_mul, hc, one_mul]`. Conclude with `h.norm_sq_sub_pow_le δ hδ`. Rewrite using `[add_sub_cancel_left]`. Conclude with `hlδ`. Take `⟨ε0, hε0⟩` from `h0`.

Use `choose g hg using hstep`. Set `v : (n : ℕ) → {x : K // P n x}` to `fun n => Nat.rec (motive := fun n => {x : K // P n x}) ⟨ε0, hε0⟩ (fun n ih => ⟨g n ih.1 ih.2, (hg n ih.1 ih.2).1⟩) n`. Set `u : ℕ → K` to `fun n => (v n).1`. Establish `hu : ∀ n, P n (u n)` using `fun n => (v n).2`. Establish `hud : ∀ n, ‖u (n + 1) - u n‖ ≤ ‖(l : K)‖ ^ (n + 1)` using `fun n => (hg n (u n) (hu n)).2`.

Establish `hcau : CauchySeq u`. Use `cauchySeq_of_le_geometric ‖(l : K)‖ ‖(l : K)‖ hl1 fun n => ?_` and prove the remaining obligations. Rewrite using `[dist_eq_norm, norm_sub_rev, ← pow_succ']`. Conclude with `hud n`. Take `⟨ε, hlim⟩` from `cauchySeq_tendsto_of_complete hcau`.

Establish `hσc : Continuous σ` using `((AddMonoidHomClass.isometry_iff_norm σ).mpr h.isom).continuous`. Establish `hres : Tendsto (fun n => u n - c * σ (σ (u n))) atTop (𝓝 (ε - c * σ (σ ε)))` using `hlim.sub ((((hσc.comp hσc).tendsto ε).comp hlim).const_mul c)`. Establish `hres0 : Tendsto (fun n => u n - c * σ (σ (u n))) atTop (𝓝 0)` using `squeeze_zero_norm (fun n => (hu n).2.trans (pow_le_pow_of_le_one (norm_nonneg _) hl1.le (Nat.le_succ n))) (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl1)`. Establish `hn : Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖ε‖)` using `hlim.norm`. Establish `hconst : (fun n => ‖u n‖) = fun _ => (1 : ℝ)` using `funext fun n => (hu n).1`.

Rewrite `hn` using `[hconst]`. Conclude with `⟨ε, tendsto_nhds_unique hn tendsto_const_nhds, sub_eq_zero.mp (tendsto_nhds_unique hres hres0)⟩`.
-/
theorem lang_semilinear {l : ℕ} {σ : K →+* K} (h : FrobField K l σ) (hR : ResClosed K l)
    (c : K) (hc : ‖c‖ = 1) : ∃ ε : K, ‖ε‖ = 1 ∧ ε = c * σ (σ ε) := by
  have hl2 : 2 ≤ l := h.prime.two_le
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; norm_num)
  have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc0
  have hci : ‖c⁻¹‖ = 1 := by rw [norm_inv, hc, inv_one]
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr h.prime.ne_zero
  have hl1 := h.norm_l
  have hq4 : 4 ≤ l ^ 2 := by nlinarith

  let P : ℕ → K → Prop := fun n ε => ‖ε‖ = 1 ∧ ‖ε - c * σ (σ ε)‖ ≤ ‖(l : K)‖ ^ (n + 1)
  have h0 : ∃ ε, P 0 ε := by
    obtain ⟨x, hx, hev⟩ := semilin_root hR (m := l ^ 2 - 1) (by omega) 0 (-c⁻¹) (by simp)
      (by rw [norm_neg, hci])
    rw [zero_mul, add_zero, ← sub_eq_add_neg] at hev
    have hx1 : ‖x‖ = 1 := by
      have h1 : ‖x ^ (l ^ 2 - 1)‖ = 1 := by
        have e : x ^ (l ^ 2 - 1) = c⁻¹ + (x ^ (l ^ 2 - 1) - c⁻¹) := by ring
        rw [e, semilin_norm_add_of_lt (by rw [hci]; exact hev.trans_lt hl1), hci]
      rw [norm_pow] at h1
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp h1
    refine ⟨x, hx1, ?_⟩
    have hxq : x ^ (l ^ 2) = x * x ^ (l ^ 2 - 1) := by
      rw [← pow_succ']; congr 1; omega
    have e : x - c * σ (σ x) = -(c * x) * (x ^ (l ^ 2 - 1) - c⁻¹) - c * (σ (σ x) - x ^ (l ^ 2)) := by
      rw [hxq]
      linear_combination (-x) * hcc
    rw [e, zero_add, pow_one]
    refine semilin_norm_sub_le ?_ ?_
    · rw [norm_mul, norm_neg, norm_mul, hc, hx1, one_mul, one_mul]; exact hev
    · rw [norm_mul, hc, one_mul]; exact h.norm_sq_sub_pow_le x hx
  have hstep : ∀ n ε, P n ε → ∃ ε', P (n + 1) ε' ∧ ‖ε' - ε‖ ≤ ‖(l : K)‖ ^ (n + 1) := by
    rintro n ε ⟨hε1, hε2⟩
    have hlam0 : (l : K) ^ (n + 1) ≠ 0 := pow_ne_zero _ hl0
    have hnl : ‖(l : K) ^ (n + 1)‖ = ‖(l : K)‖ ^ (n + 1) := norm_pow _ _
    have hsm : ‖(l : K)‖ ^ (n + 1) < 1 := pow_lt_one₀ (norm_nonneg _) hl1 (Nat.succ_ne_zero n)
    obtain ⟨ρ, hρ⟩ : ∃ ρ, ε - c * σ (σ ε) = (l : K) ^ (n + 1) * ρ :=
      ⟨(ε - c * σ (σ ε)) / (l : K) ^ (n + 1), by field_simp⟩
    have hρ1 : ‖ρ‖ ≤ 1 := by
      have hpos : 0 < ‖(l : K)‖ ^ (n + 1) := by rw [← hnl]; exact norm_pos_iff.mpr hlam0
      rw [hρ, norm_mul, hnl] at hε2
      exact le_of_mul_le_mul_left (by rwa [mul_one]) hpos
    obtain ⟨δ, hδ, hev⟩ := semilin_root hR (m := l ^ 2) (by omega) (-c⁻¹) (-(c⁻¹ * ρ))
      (by rw [norm_neg, hci]) (by rw [norm_neg, norm_mul, hci, one_mul]; exact hρ1)
    have hσl : σ (σ ((l : K) ^ (n + 1))) = (l : K) ^ (n + 1) := by simp [map_pow, map_natCast]
    have hlδ : ‖(l : K) ^ (n + 1) * δ‖ ≤ ‖(l : K)‖ ^ (n + 1) := by
      rw [norm_mul, hnl]
      calc ‖(l : K)‖ ^ (n + 1) * ‖δ‖ ≤ ‖(l : K)‖ ^ (n + 1) * 1 :=
            mul_le_mul_of_nonneg_left hδ (by positivity)
        _ = _ := mul_one _
    refine ⟨ε + (l : K) ^ (n + 1) * δ, ⟨?_, ?_⟩, ?_⟩
    · rw [semilin_norm_add_of_lt (by rw [hε1]; exact hlδ.trans_lt hsm), hε1]
    · have e : ε + (l : K) ^ (n + 1) * δ - c * σ (σ (ε + (l : K) ^ (n + 1) * δ)) =
          (l : K) ^ (n + 1) * (-c * (δ ^ (l ^ 2) + -c⁻¹ * δ + -(c⁻¹ * ρ)) - c * (σ (σ δ) - δ ^ (l ^ 2))) := by
        rw [map_add, map_add, map_mul, map_mul, hσl]
        linear_combination hρ - ((l : K) ^ (n + 1) * ρ + (l : K) ^ (n + 1) * δ) * hcc
      rw [e, norm_mul, hnl, pow_succ ‖(l : K)‖ (n + 1)]
      refine mul_le_mul_of_nonneg_left (semilin_norm_sub_le ?_ ?_) (by positivity)
      · rw [norm_mul, norm_neg, hc, one_mul]; exact hev
      · rw [norm_mul, hc, one_mul]; exact h.norm_sq_sub_pow_le δ hδ
    · rw [add_sub_cancel_left]; exact hlδ

  obtain ⟨ε0, hε0⟩ := h0
  choose g hg using hstep
  let v : (n : ℕ) → {x : K // P n x} := fun n =>
    Nat.rec (motive := fun n => {x : K // P n x}) ⟨ε0, hε0⟩
      (fun n ih => ⟨g n ih.1 ih.2, (hg n ih.1 ih.2).1⟩) n
  let u : ℕ → K := fun n => (v n).1
  have hu : ∀ n, P n (u n) := fun n => (v n).2
  have hud : ∀ n, ‖u (n + 1) - u n‖ ≤ ‖(l : K)‖ ^ (n + 1) := fun n => (hg n (u n) (hu n)).2
  have hcau : CauchySeq u := by
    refine cauchySeq_of_le_geometric ‖(l : K)‖ ‖(l : K)‖ hl1 fun n => ?_
    rw [dist_eq_norm, norm_sub_rev, ← pow_succ']
    exact hud n
  obtain ⟨ε, hlim⟩ := cauchySeq_tendsto_of_complete hcau
  have hσc : Continuous σ := ((AddMonoidHomClass.isometry_iff_norm σ).mpr h.isom).continuous
  have hres : Tendsto (fun n => u n - c * σ (σ (u n))) atTop (𝓝 (ε - c * σ (σ ε))) :=
    hlim.sub ((((hσc.comp hσc).tendsto ε).comp hlim).const_mul c)
  have hres0 : Tendsto (fun n => u n - c * σ (σ (u n))) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (hu n).2.trans (pow_le_pow_of_le_one (norm_nonneg _) hl1.le (Nat.le_succ n)))
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl1)
  have hn : Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖ε‖) := hlim.norm
  have hconst : (fun n => ‖u n‖) = fun _ => (1 : ℝ) := funext fun n => (hu n).1
  rw [hconst] at hn
  exact ⟨ε, tendsto_nhds_unique hn tendsto_const_nhds, sub_eq_zero.mp (tendsto_nhds_unique hres hres0)⟩

end ReciprocityTheory.ChartRestriction.L1
