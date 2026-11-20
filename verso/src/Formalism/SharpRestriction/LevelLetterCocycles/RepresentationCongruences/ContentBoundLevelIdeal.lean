import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ConstantCoeffResidueUXPow
import Mathlib.Analysis.SpecialFunctions.Log.Base

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open PowerSeries

section Core

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
variable {l : ℕ} [Fact l.Prime] (P : PhiData O l)

include P in
/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible P.hl0 hϖ`. Establish `hv : IsDiscreteValuationRing.addVal O (l : O) = n`. Rewrite using `[hu, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ, IsDiscreteValuationRing.addVal_eq_zero_of_unit]`. Simplify using the standard rewrite rules.

Establish `hn : n ≠ 0`. Introduce and unpack `rfl`. Establish `h` using `P.hl`. Rewrite `h` using `[hu, pow_zero, mul_one, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `h u.isUnit`.

Unfold `eO`. Rewrite using `[hv]`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
theorem eO_pos : 1 ≤ eO (O := O) l := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible P.hl0 hϖ
  have hv : IsDiscreteValuationRing.addVal O (l : O) = n := by
    rw [hu, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, IsDiscreteValuationRing.addVal_eq_zero_of_unit]
    simp
  have hn : n ≠ 0 := by
    rintro rfl
    have h := P.hl
    rw [hu, pow_zero, mul_one, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h
    exact h u.isUnit
  unfold eO
  rw [hv]
  simp
  omega

/- English proof (translation)
Establish `h1` using `Nat.div_add_mod (b₀ + l - 1) l`. Establish `h2` using `Nat.mod_lt (b₀ + l - 1) (show 0 < l by omega)`. Use linear arithmetic over natural numbers and integers.
-/
theorem ceil_le (b₀ : ℕ) (hl : 1 ≤ l) : b₀ ≤ l * ((b₀ + l - 1) / l) := by
  have h1 := Nat.div_add_mod (b₀ + l - 1) l
  have h2 := Nat.mod_lt (b₀ + l - 1) (show 0 < l by omega)
  omega

/- English proof (translation)
Establish `hl1 : 1 ≤ l` using `(Fact.out : l.Prime).one_lt.le`. Establish `hb₀ : b₀ ≤ l * ((b₀ + l - 1) / l)` using `ceil_le b₀ hl1`. Generalize the expression as in `ha' : (b₀ + l - 1) / l = a' at hB hb₀ ⊢`. Use `set k := eO (O := O) l * s₁ with hk`. Take `⟨vl, hvl⟩` from `l_eq_unit_mul_pow hϖ P.hl0`.

Take `⟨g₁, g₂, hg⟩` from `Ideal.mem_span_pair.1 (P.p_one_pow_mem_span_X_pow_mul_l_pow hϖ a' s₁ hs₁)`. Take `⟨α, β, hαβ⟩` from `Ideal.mem_span_pair.1 h`. Establish `hXa : (X : O⟦X⟧) ^ (l * a') = X ^ (l * a' - b₀) * X ^ b₀`. Rewrite using `[← pow_add, Nat.sub_add_cancel hb₀]`. Establish `hCl : (C (l : O) : O⟦X⟧) ^ s₁ = C ((vl : O) ^ s₁) * C ϖ ^ k`.

Rewrite using `[hvl, map_mul, mul_pow, map_pow, map_pow, ← pow_mul, hk, mul_comm (eO (O := O) l) s₁, pow_mul]`. Establish `hm1 : P.p 1 ^ (a' + s₁ - 1) * P.p 2 ^ w ∈ Ideal.span {C ϖ ^ k, P.p 1 ^ B}`. Use `Ideal.mem_span_pair.2 ⟨g₁ * X ^ (l * a' - b₀) * α + C ((vl : O) ^ s₁) * g₂ * P.p 2 ^ w, g₁ * X ^ (l * a' - b₀) * β, ?_⟩` and prove the remaining obligations. Rewrite using `[← hg, hXa, hCl]`. Take the linear combination `(g₁ * X ^ (l * a' - b₀)) * hαβ`.

Establish `hm2` using `V2 hϖ (P.isDist_p 1) (a' + s₁ - 1) B k (by omega) (P.p 2 ^ w) hm1`. Establish `hp2 : P.p 2 = P.φ (P.p 1)` using `P.p_succ 1`. Establish `hp1 : P.p 1 = P.φ X` using `P.p_succ 0`. Establish `hm3 : P.p 1 ^ w ∈ Ideal.span {C ϖ ^ k, X ^ (B - (a' + s₁ - 1))}`. Apply `P.DESC hϖ` to reduce the goal to its premises.

Rewrite using `[map_pow, map_pow, ← hp2, ← hp1]`. Conclude with `hm2`. Establish `hB1 : 1 ≤ B - (a' + s₁ - 1)` using `by omega`. Take `⟨hne, hle⟩` from `P.constant_le_rpow_of_three_le hϖ (B - (a' + s₁ - 1)) w hB1 hw`. Establish `hk' : (k : ℕ∞) ≤ cont ϖ (X ^ (B - (a' + s₁ - 1))) (P.p 1 ^ w)` using `(mem_iff_le_cont hϖ (ContPA.dist_X_pow (B - (a' + s₁ - 1))).1 _ k).1 hm3`.

Take `⟨c', hc'⟩` from `ENat.ne_top_iff_exists.1 hne`. Rewrite `hk'`, `hle` using `[← hc']`. Establish `hkc : (k : ℝ) ≤ c'` using `by exact_mod_cast hk'`. Rewrite `hle` using `[ENat.toNat_natCast]`. Establish `he : (1 : ℝ) ≤ eO (O` using `O) l := by exact_mod_cast eO_pos (O := O) P`.

Establish `: (eO (O` using `O) l : ℝ) * s₁ ≤ eO (O := O) l * max 0 ((w : ℝ) - ((B - (a' + s₁ - 1) : ℕ) : ℝ) / l + 2 + Real.logb l w) := by`. Establish `: (k : ℝ) = (eO (O` using `O) l : ℝ) * s₁ := by rw [hk]; push_cast; ring`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `le_of_mul_le_mul_left this (by linarith)`.
-/
theorem content_bound_level_ideal {ϖ : O} (hϖ : Irreducible ϖ) (w b₀ B s₁ : ℕ) (hw : 1 ≤ w) (hs₁ : 1 ≤ s₁)
    (hB : (b₀ + l - 1) / l + s₁ ≤ B)
    (h : P.p 2 ^ w * X ^ b₀ ∈ Ideal.span {C ϖ ^ (eO (O := O) l * s₁), P.p 1 ^ B}) :
    (s₁ : ℝ) ≤ max 0 ((w : ℝ) - ((B - ((b₀ + l - 1) / l + s₁ - 1) : ℕ) : ℝ) / l + 2 +
      Real.logb l w) := by
  have hl1 : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  have hb₀ : b₀ ≤ l * ((b₀ + l - 1) / l) := ceil_le b₀ hl1
  generalize ha' : (b₀ + l - 1) / l = a' at hB hb₀ ⊢
  set k := eO (O := O) l * s₁ with hk
  obtain ⟨vl, hvl⟩ := l_eq_unit_mul_pow hϖ P.hl0

  obtain ⟨g₁, g₂, hg⟩ := Ideal.mem_span_pair.1 (P.p_one_pow_mem_span_X_pow_mul_l_pow hϖ a' s₁ hs₁)
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1 h
  have hXa : (X : O⟦X⟧) ^ (l * a') = X ^ (l * a' - b₀) * X ^ b₀ := by
    rw [← pow_add, Nat.sub_add_cancel hb₀]
  have hCl : (C (l : O) : O⟦X⟧) ^ s₁ = C ((vl : O) ^ s₁) * C ϖ ^ k := by
    rw [hvl, map_mul, mul_pow, map_pow, map_pow, ← pow_mul, hk, mul_comm (eO (O := O) l) s₁, pow_mul]
  have hm1 : P.p 1 ^ (a' + s₁ - 1) * P.p 2 ^ w ∈ Ideal.span {C ϖ ^ k, P.p 1 ^ B} := by
    refine Ideal.mem_span_pair.2 ⟨g₁ * X ^ (l * a' - b₀) * α + C ((vl : O) ^ s₁) * g₂ * P.p 2 ^ w,
      g₁ * X ^ (l * a' - b₀) * β, ?_⟩
    rw [← hg, hXa, hCl]
    linear_combination (g₁ * X ^ (l * a' - b₀)) * hαβ

  have hm2 := V2 hϖ (P.isDist_p 1) (a' + s₁ - 1) B k (by omega) (P.p 2 ^ w) hm1

  have hp2 : P.p 2 = P.φ (P.p 1) := P.p_succ 1
  have hp1 : P.p 1 = P.φ X := P.p_succ 0
  have hm3 : P.p 1 ^ w ∈ Ideal.span {C ϖ ^ k, X ^ (B - (a' + s₁ - 1))} := by
    apply P.DESC hϖ
    rw [map_pow, map_pow, ← hp2, ← hp1]
    exact hm2

  have hB1 : 1 ≤ B - (a' + s₁ - 1) := by omega
  obtain ⟨hne, hle⟩ := P.constant_le_rpow_of_three_le hϖ (B - (a' + s₁ - 1)) w hB1 hw
  have hk' : (k : ℕ∞) ≤ cont ϖ (X ^ (B - (a' + s₁ - 1))) (P.p 1 ^ w) :=
    (mem_iff_le_cont hϖ (ContPA.dist_X_pow (B - (a' + s₁ - 1))).1 _ k).1 hm3
  obtain ⟨c', hc'⟩ := ENat.ne_top_iff_exists.1 hne
  rw [← hc'] at hk' hle
  have hkc : (k : ℝ) ≤ c' := by exact_mod_cast hk'
  rw [ENat.toNat_natCast] at hle
  have he : (1 : ℝ) ≤ eO (O := O) l := by exact_mod_cast eO_pos (O := O) P
  have : (eO (O := O) l : ℝ) * s₁ ≤ eO (O := O) l *
      max 0 ((w : ℝ) - ((B - (a' + s₁ - 1) : ℕ) : ℝ) / l + 2 + Real.logb l w) := by
    have : (k : ℝ) = (eO (O := O) l : ℝ) * s₁ := by rw [hk]; push_cast; ring
    linarith
  exact le_of_mul_le_mul_left this (by linarith)

end Core

section Real

/- English proof (translation)
Establish `hL0 : (0 : ℝ) < L` using `by linarith`. Establish `hL1 : (0 : ℝ) < L - 1` using `by linarith`. Establish `hw : w' ≤ wS * L` using `by rwa [div_le_iff₀ hL0] at hwS`. Establish `hS : 0 ≤ wS` using `le_trans (div_nonneg hw' hL0.le) hwS`. Break down `le_total (w' - Bq + hh + 2 + lg) 0 with hx | hx` into its components or cases.

Rewrite using `[max_eq_left hx, mul_zero]`. Conclude with `le_max_left _ _`. Rewrite using `[max_eq_right hx]`. Apply `le_max_of_le_right` to reduce the goal to its premises. Rewrite using `[div_mul_eq_mul_div, div_le_iff₀ hL1]`.

Use polynomial arithmetic with `[mul_nonneg (show (0 : ℝ) ≤ L - 11 by linarith) hS, mul_nonneg (show (0 : ℝ) ≤ L - 11 by linarith) hhh, mul_nonneg (show (0 : ℝ) ≤ L - 11 by linarith) hlg, mul_nonneg (show (0 : ℝ) ≤ L - 11 by linarith) hBq]`.
-/
theorem realA (L w' Bq hh lg wS : ℝ) (hL : 11 ≤ L) (hw' : 0 ≤ w') (hBq : 0 ≤ Bq) (hhh : 0 ≤ hh)
    (hlg : 0 ≤ lg) (hwS : w' / L ≤ wS) :
    (L / (L - 1)) * max 0 (w' - Bq + hh + 2 + lg) ≤ max 0 (w' - Bq + 16 / 5 * (hh + wS + lg + 1)) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hL1 : (0 : ℝ) < L - 1 := by linarith
  have hw : w' ≤ wS * L := by rwa [div_le_iff₀ hL0] at hwS
  have hS : 0 ≤ wS := le_trans (div_nonneg hw' hL0.le) hwS
  rcases le_total (w' - Bq + hh + 2 + lg) 0 with hx | hx
  · rw [max_eq_left hx, mul_zero]
    exact le_max_left _ _
  · rw [max_eq_right hx]
    apply le_max_of_le_right
    rw [div_mul_eq_mul_div, div_le_iff₀ hL1]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ L - 11 by linarith) hS, mul_nonneg (show (0 : ℝ) ≤ L - 11 by linarith) hhh,
      mul_nonneg (show (0 : ℝ) ≤ L - 11 by linarith) hlg, mul_nonneg (show (0 : ℝ) ≤ L - 11 by linarith) hBq]

set_option maxHeartbeats 800000 in

/- English proof (translation)
Establish `hL : (11 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hL0 : (0 : ℝ) < l` using `by linarith`. Establish `hL1 : (0 : ℝ) < (l : ℝ) - 1` using `by linarith`. Establish `hl1 : (1 : ℝ) < l` using `by linarith`. Establish `hw'1r : (1 : ℝ) ≤ w'` using `by exact_mod_cast hw'1`.

Establish `hw'wr : (w' : ℝ) ≤ w` using `by exact_mod_cast hw'w`. Establish `h20wr : 20 * (w : ℝ) ≤ b` using `by exact_mod_cast h20w`. Establish `h20ηr : 20 * (η : ℝ) ≤ b` using `by exact_mod_cast h20η`. Establish `hbb₁r : (b : ℝ) ≤ b₁` using `by exact_mod_cast hbb₁`. Establish `hb₀r : (b₀ : ℝ) ≤ b + η` using `by exact_mod_cast hb₀`.

Establish `hS0 : (0 : ℝ) ≤ S` using `Nat.cast_nonneg S`. Establish `hη0 : (0 : ℝ) ≤ η` using `Nat.cast_nonneg η`. Establish `hb20 : (20 : ℝ) ≤ b` using `by linarith`. Establish `hN : ((b + η + S : ℕ) : ℝ) = b + η + S` using `by push_cast; ring`. Take `⟨c, hc⟩ : ∃ c, c = (b₀ + l - 1) / l` from `⟨_, rfl⟩`.

Rewrite using `[← hc]`. Establish `hcl' : c * l + 1 ≤ b₀ + l`. Establish `h` using `Nat.div_mul_le_self (b₀ + l - 1) l`. Rewrite `h` using `[← hc]`. Use linear arithmetic over natural numbers and integers.

Establish `hclr : (c : ℝ) * l + 1 ≤ b₀ + l` using `by exact_mod_cast hcl'`. Take `⟨lg, hlg⟩ : ∃ lg, lg = Real.logb l w'` from `⟨_, rfl⟩`. Rewrite using `[← hlg]`. Establish `hlg0 : 0 ≤ lg` using `hlg ▸ Real.logb_nonneg hl1 hw'1r`. Establish `hlog40 : 1 < Real.log 40`.

Establish `h3 : 1 - (3 : ℝ)⁻¹ ≤ Real.log 3` using `Real.one_sub_inv_le_log_of_pos (by norm_num)`. Establish `h27 : Real.log ((3 : ℝ) ^ 3) ≤ Real.log 40` using `Real.log_le_log (by norm_num) (by norm_num)`. Rewrite `h27` using `[Real.log_pow]`. Move the coercions through the operations in `at h27`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hlogl : 0 < Real.log l` using `Real.log_pos hl1`. Establish `hloglt : Real.log l < l`. Use `Real.log_le_sub_one_of_pos hL0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hslack : lg + 1 / l ≤ Real.logb l (2 * ((b + η + S : ℕ) : ℝ))`.

Rewrite using `[hN, hlg]`. Establish `h40 : 40 * (w' : ℝ) ≤ 2 * ((b : ℝ) + η + S)` using `by linarith`. Establish `hmono : Real.logb l (40 * w') ≤ Real.logb l (2 * ((b : ℝ) + η + S))` using `Real.logb_le_logb_of_le hl1 (by positivity) h40`. Rewrite `hmono` using `[Real.logb_mul (by norm_num) (by positivity)]`. Establish `h1 : 1 / (l : ℝ) ≤ Real.logb l 40`.

Rewrite using `[Real.logb, div_le_div_iff₀ hL0 hlogl]`. Use polynomial arithmetic with `[mul_pos (sub_pos.mpr hlog40) hL0]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨Q, hQ⟩ : ∃ Q, Q = (w' : ℝ) - ((b₁ : ℝ) + S - c + 1) / l + 2 + lg` from `⟨_, rfl⟩`. Take `⟨s₁, hs₁⟩ : ∃ s, s = ⌊max 0 (Q * l / (l - 1))⌋₊ + 1` from `⟨_, rfl⟩`.

Establish `hs1 : 1 ≤ s₁` using `by rw [hs₁]; exact Nat.le_add_left 1 _`. Establish `hsgt : Q * l / (l - 1) < s₁`. Use `Nat.lt_floor_add_one (max 0 (Q * l / (l - 1)))` as an intermediate fact. Rewrite using `[hs₁]`. Use `push_cast`.

Conclude with `lt_of_le_of_lt (le_max_right _ _) this`. Establish `hsle : (s₁ : ℝ) ≤ max 0 (Q * l / (l - 1)) + 1`. Rewrite using `[hs₁]`. Use `push_cast`. Combine the linear relations using `[Nat.floor_le (le_max_left 0 (Q * l / (l - 1)))]`.

Establish `hA` using `realA (l : ℝ) w' (((b₁ : ℝ) + S) / l) ((c : ℝ) / l) lg (((w : ℝ) + S + η) / l) hL (by linarith) (by positivity) (by positivity) hlg0 (div_le_div_of_nonneg_right (by linarith) hL0.le)`. Establish `hQle : Q ≤ (w' : ℝ) - ((b₁ : ℝ) + S) / l + (c : ℝ) / l + 2 + lg`. Establish `e : ((b₁ : ℝ) + S - c + 1) / l = ((b₁ : ℝ) + S) / l - c / l + 1 / l` using `by ring`. Establish `: 0 < 1 / (l : ℝ)` using `by positivity`. Rewrite using `[hQ, e]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfrac : 0 < (l : ℝ) / (l - 1)` using `div_pos hL0 hL1`. Establish `hX : max 0 (Q * l / (l - 1)) ≤ ((l : ℝ) / (l - 1)) * max 0 ((w' : ℝ) - ((b₁ : ℝ) + S) / l + (c : ℝ) / l + 2 + lg)`. Apply `max_le (mul_nonneg hfrac.le (le_max_left _ _))` to reduce the goal to its premises. Establish `e : Q * l / (l - 1) = ((l : ℝ) / (l - 1)) * Q` using `by ring`.

Rewrite using `[e]`. Conclude with `mul_le_mul_of_nonneg_left (le_trans hQle (le_max_right _ _)) hfrac.le`. Establish `hc1 : (c : ℝ) * l ≤ ((b : ℝ) + η + S) + l` using `by linarith`. Establish `hcL : (c : ℝ) / l ≤ ((b + η + S : ℕ) : ℝ) / (l : ℝ) ^ 2 + 1 / l`. Rewrite using `[hN, div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ hL0 (by positivity)]`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hc1 (sq_nonneg (l : ℝ))]`. Establish `hR : (w' : ℝ) - ((b₁ : ℝ) + S) / l + 16 / 5 * ((c : ℝ) / l + ((w : ℝ) + S + η) / l + lg + 1) ≤ (w' : ℝ) - ((b₁ : ℝ) + S) / l + 16 / 5 * Sg`. Rewrite using `[hSg]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hupper : (s₁ : ℝ) ≤ max 1 ((w' : ℝ) - ((b₁ : ℝ) + S) / l + 16 / 5 * Sg) + 1`.

Establish `h2` using `max_le_max (show (0 : ℝ) ≤ 1 by norm_num) hR`. Combine the linear relations using `[le_trans hX hA]`. Establish `hSgb : Sg ≤ (b : ℝ) / 160` using `by linarith`. Establish `hBq : 0 ≤ ((b₁ : ℝ) + S) / l` using `by positivity`. Establish `hupper' : (s₁ : ℝ) ≤ 2 + (b : ℝ) / 20 + (b : ℝ) / 50`.

Establish `: max 1 ((w' : ℝ) - ((b₁ : ℝ) + S) / l + 16 / 5 * Sg) ≤ 1 + (b : ℝ) / 20 + (b : ℝ) / 50` using `max_le (by linarith) (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcb : (c : ℝ) ≤ ((b : ℝ) + η) / 11 + 1`. Establish `h' : ((c : ℝ) - 1) * l ≤ (b : ℝ) + η` using `by linarith`. Break down `le_or_gt (c : ℝ) 1 with h | h` into its components or cases.

Establish `: 0 ≤ ((b : ℝ) + η) / 11` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: ((c : ℝ) - 1) * 11 ≤ ((c : ℝ) - 1) * l` using `mul_le_mul_of_nonneg_left hL (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum : (c : ℝ) + s₁ ≤ b₁ + S` using `by linarith`.

Establish `hnat : c + s₁ ≤ b₁ + S` using `by exact_mod_cast hsum`. Use `⟨s₁, hs1, hupper, hnat, ?_⟩` and prove the remaining obligations. Introduce `hle`. Establish `hcast : ((b₁ + S - (c + s₁ - 1) : ℕ) : ℝ) = (b₁ : ℝ) + S - c - s₁ + 1`. Rewrite using `[Nat.cast_sub (le_trans (Nat.sub_le _ _) hnat), Nat.cast_sub (le_add_left hs1)]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hle` using `[hcast]`. Establish `hpos : (0 : ℝ) < s₁` using `by exact_mod_cast hs1`. Break down `le_max_iff.mp hle with h | h` into its components or cases.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `e : (w' : ℝ) - ((b₁ : ℝ) + S - c - s₁ + 1) / l + 2 + lg = Q + s₁ / l`. Rewrite using `[hQ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e]`.

Establish `h'` using `mul_le_mul_of_nonneg_right h hL0.le`. Establish `e2 : (s₁ : ℝ) / l * l = s₁` using `by field_simp`. Rewrite `h'` using `[add_mul, e2]`. Establish `h3 : (s₁ : ℝ) ≤ Q * l / (l - 1)`. Rewrite using `[le_div_iff₀ hL1]`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_s1_bound_choice (l b w S η b₀ b₁ w' : ℕ) (hl : 11 ≤ l) (Sg : ℝ)
    (hSg : Sg = ((b + η + S : ℕ) : ℝ) / (l : ℝ) ^ 2 + ((w : ℝ) + S + η) / l +
      Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) + 1)
    (hsm : 40 * Sg ≤ (b : ℝ) / 4) (h20w : 20 * w ≤ b) (h20η : 20 * η ≤ b) (hw'1 : 1 ≤ w')
    (hw'w : w' ≤ w) (hbb₁ : b ≤ b₁) (hb₀ : b₀ ≤ b + η) :
    ∃ s₁ : ℕ, 1 ≤ s₁ ∧ (s₁ : ℝ) ≤ max 1 ((w' : ℝ) - ((b₁ : ℝ) + S) / l + 16 / 5 * Sg) + 1 ∧
      (b₀ + l - 1) / l + s₁ ≤ b₁ + S ∧
      ¬ ((s₁ : ℝ) ≤ max 0 ((w' : ℝ) - ((b₁ + S - ((b₀ + l - 1) / l + s₁ - 1) : ℕ) : ℝ) / l + 2 +
        Real.logb l w')) := by
  have hL : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hL0 : (0 : ℝ) < l := by linarith
  have hL1 : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have hl1 : (1 : ℝ) < l := by linarith
  have hw'1r : (1 : ℝ) ≤ w' := by exact_mod_cast hw'1
  have hw'wr : (w' : ℝ) ≤ w := by exact_mod_cast hw'w
  have h20wr : 20 * (w : ℝ) ≤ b := by exact_mod_cast h20w
  have h20ηr : 20 * (η : ℝ) ≤ b := by exact_mod_cast h20η
  have hbb₁r : (b : ℝ) ≤ b₁ := by exact_mod_cast hbb₁
  have hb₀r : (b₀ : ℝ) ≤ b + η := by exact_mod_cast hb₀
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  have hη0 : (0 : ℝ) ≤ η := Nat.cast_nonneg η
  have hb20 : (20 : ℝ) ≤ b := by linarith
  have hN : ((b + η + S : ℕ) : ℝ) = b + η + S := by push_cast; ring
  obtain ⟨c, hc⟩ : ∃ c, c = (b₀ + l - 1) / l := ⟨_, rfl⟩
  rw [← hc]
  have hcl' : c * l + 1 ≤ b₀ + l := by
    have h := Nat.div_mul_le_self (b₀ + l - 1) l
    rw [← hc] at h
    omega
  have hclr : (c : ℝ) * l + 1 ≤ b₀ + l := by exact_mod_cast hcl'
  obtain ⟨lg, hlg⟩ : ∃ lg, lg = Real.logb l w' := ⟨_, rfl⟩
  rw [← hlg]
  have hlg0 : 0 ≤ lg := hlg ▸ Real.logb_nonneg hl1 hw'1r

  have hlog40 : 1 < Real.log 40 := by
    have h3 : 1 - (3 : ℝ)⁻¹ ≤ Real.log 3 := Real.one_sub_inv_le_log_of_pos (by norm_num)
    have h27 : Real.log ((3 : ℝ) ^ 3) ≤ Real.log 40 := Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h27
    push_cast at h27
    linarith
  have hlogl : 0 < Real.log l := Real.log_pos hl1
  have hloglt : Real.log l < l := by
    have := Real.log_le_sub_one_of_pos hL0
    linarith
  have hslack : lg + 1 / l ≤ Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) := by
    rw [hN, hlg]
    have h40 : 40 * (w' : ℝ) ≤ 2 * ((b : ℝ) + η + S) := by linarith
    have hmono : Real.logb l (40 * w') ≤ Real.logb l (2 * ((b : ℝ) + η + S)) :=
      Real.logb_le_logb_of_le hl1 (by positivity) h40
    rw [Real.logb_mul (by norm_num) (by positivity)] at hmono
    have h1 : 1 / (l : ℝ) ≤ Real.logb l 40 := by
      rw [Real.logb, div_le_div_iff₀ hL0 hlogl]
      nlinarith [mul_pos (sub_pos.mpr hlog40) hL0]
    linarith
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (w' : ℝ) - ((b₁ : ℝ) + S - c + 1) / l + 2 + lg := ⟨_, rfl⟩
  obtain ⟨s₁, hs₁⟩ : ∃ s, s = ⌊max 0 (Q * l / (l - 1))⌋₊ + 1 := ⟨_, rfl⟩
  have hs1 : 1 ≤ s₁ := by rw [hs₁]; exact Nat.le_add_left 1 _
  have hsgt : Q * l / (l - 1) < s₁ := by
    have := Nat.lt_floor_add_one (max 0 (Q * l / (l - 1)))
    rw [hs₁]
    push_cast
    exact lt_of_le_of_lt (le_max_right _ _) this
  have hsle : (s₁ : ℝ) ≤ max 0 (Q * l / (l - 1)) + 1 := by
    rw [hs₁]
    push_cast
    linarith [Nat.floor_le (le_max_left 0 (Q * l / (l - 1)))]
  have hA := realA (l : ℝ) w' (((b₁ : ℝ) + S) / l) ((c : ℝ) / l) lg (((w : ℝ) + S + η) / l) hL
    (by linarith) (by positivity) (by positivity) hlg0
    (div_le_div_of_nonneg_right (by linarith) hL0.le)
  have hQle : Q ≤ (w' : ℝ) - ((b₁ : ℝ) + S) / l + (c : ℝ) / l + 2 + lg := by
    have e : ((b₁ : ℝ) + S - c + 1) / l = ((b₁ : ℝ) + S) / l - c / l + 1 / l := by ring
    have : 0 < 1 / (l : ℝ) := by positivity
    rw [hQ, e]
    linarith
  have hfrac : 0 < (l : ℝ) / (l - 1) := div_pos hL0 hL1
  have hX : max 0 (Q * l / (l - 1)) ≤
      ((l : ℝ) / (l - 1)) * max 0 ((w' : ℝ) - ((b₁ : ℝ) + S) / l + (c : ℝ) / l + 2 + lg) := by
    apply max_le (mul_nonneg hfrac.le (le_max_left _ _))
    have e : Q * l / (l - 1) = ((l : ℝ) / (l - 1)) * Q := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (le_trans hQle (le_max_right _ _)) hfrac.le
  have hc1 : (c : ℝ) * l ≤ ((b : ℝ) + η + S) + l := by linarith
  have hcL : (c : ℝ) / l ≤ ((b + η + S : ℕ) : ℝ) / (l : ℝ) ^ 2 + 1 / l := by
    rw [hN, div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ hL0 (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hc1 (sq_nonneg (l : ℝ))]
  have hR : (w' : ℝ) - ((b₁ : ℝ) + S) / l + 16 / 5 * ((c : ℝ) / l + ((w : ℝ) + S + η) / l + lg + 1) ≤
      (w' : ℝ) - ((b₁ : ℝ) + S) / l + 16 / 5 * Sg := by
    rw [hSg]
    linarith
  have hupper : (s₁ : ℝ) ≤ max 1 ((w' : ℝ) - ((b₁ : ℝ) + S) / l + 16 / 5 * Sg) + 1 := by
    have h2 := max_le_max (show (0 : ℝ) ≤ 1 by norm_num) hR
    linarith [le_trans hX hA]
  have hSgb : Sg ≤ (b : ℝ) / 160 := by linarith
  have hBq : 0 ≤ ((b₁ : ℝ) + S) / l := by positivity
  have hupper' : (s₁ : ℝ) ≤ 2 + (b : ℝ) / 20 + (b : ℝ) / 50 := by
    have : max 1 ((w' : ℝ) - ((b₁ : ℝ) + S) / l + 16 / 5 * Sg) ≤ 1 + (b : ℝ) / 20 + (b : ℝ) / 50 :=
      max_le (by linarith) (by linarith)
    linarith
  have hcb : (c : ℝ) ≤ ((b : ℝ) + η) / 11 + 1 := by
    have h' : ((c : ℝ) - 1) * l ≤ (b : ℝ) + η := by linarith
    rcases le_or_gt (c : ℝ) 1 with h | h
    · have : 0 ≤ ((b : ℝ) + η) / 11 := by positivity
      linarith
    · have : ((c : ℝ) - 1) * 11 ≤ ((c : ℝ) - 1) * l := mul_le_mul_of_nonneg_left hL (by linarith)
      linarith
  have hsum : (c : ℝ) + s₁ ≤ b₁ + S := by linarith
  have hnat : c + s₁ ≤ b₁ + S := by exact_mod_cast hsum
  refine ⟨s₁, hs1, hupper, hnat, ?_⟩
  intro hle
  have hcast : ((b₁ + S - (c + s₁ - 1) : ℕ) : ℝ) = (b₁ : ℝ) + S - c - s₁ + 1 := by
    rw [Nat.cast_sub (le_trans (Nat.sub_le _ _) hnat), Nat.cast_sub (le_add_left hs1)]
    push_cast
    ring
  rw [hcast] at hle
  have hpos : (0 : ℝ) < s₁ := by exact_mod_cast hs1
  rcases le_max_iff.mp hle with h | h
  · linarith
  · have e : (w' : ℝ) - ((b₁ : ℝ) + S - c - s₁ + 1) / l + 2 + lg = Q + s₁ / l := by
      rw [hQ]
      ring
    rw [e] at h
    have h' := mul_le_mul_of_nonneg_right h hL0.le
    have e2 : (s₁ : ℝ) / l * l = s₁ := by field_simp
    rw [add_mul, e2] at h'
    have h3 : (s₁ : ℝ) ≤ Q * l / (l - 1) := by
      rw [le_div_iff₀ hL1]
      linarith
    linarith

end Real

section End

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Distinguish the cases in `hx0 : x = 0`. Simplify using `[hx0]`. Assume the negation of the conclusion as `hnd`. Apply `hC` to reduce the goal to its premises. Take `⟨m, v, hx⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ`.

Take `⟨e, u, hl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible P.hl0 hϖ`. Establish `he : eO (O` using `O) l = e := by`. Unfold `eO`. Rewrite using `[hl, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ, IsDiscreteValuationRing.addVal_eq_zero_of_unit]`. Simplify using the standard rewrite rules.

Rewrite using `[he]`. Establish `hlt : e * s₁ + m < e * κ`. Assume the negation of the conclusion as `hle`. Use `push_neg at hle`. Apply `hnd` to reduce the goal to its premises.

Use `⟨(u : O) ^ s₁ * v * ((u⁻¹ : Oˣ) : O) ^ κ * ϖ ^ (e * s₁ + m - e * κ), ?_⟩` and prove the remaining obligations. Establish `h1 : ((u : O) * ((u⁻¹ : Oˣ) : O)) ^ κ = 1` using `by rw [Units.mul_inv, one_pow]`. Establish `hpow : ϖ ^ (e * s₁ + m) = ϖ ^ (e * κ) * ϖ ^ (e * s₁ + m - e * κ)`. Rewrite using `[← pow_add]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hx, hl]`. Take the linear combination `(-((u : O) ^ s₁ * v * ϖ ^ (e * κ) * ϖ ^ (e * s₁ + m - e * κ))) * h1 + ((u : O) ^ s₁ * v) * hpow`. Establish `hd : IsDist (P.p 1 ^ B)`. Unfold `IsDist`.

Rewrite using `[map_pow]`. Conclude with `pow_ne_zero _ (P.isDist_p 1)`. Rewrite using `[← C2' hϖ hd D (e * s₁)]`. Use `⟨C (ϖ ^ (e * κ - m - e * s₁) * ((v⁻¹ : Oˣ) : O) * (u : O) ^ κ) * U₁, m, ?_⟩` and prove the remaining obligations. Establish `hvv : C (v : O) * C ((v⁻¹ : Oˣ) : O) = 1` using `by rw [← map_mul, Units.mul_inv, map_one]`.

Establish `hpow2 : C ϖ ^ (e * κ) = C ϖ ^ m * C ϖ ^ (e * s₁) * C ϖ ^ (e * κ - m - e * s₁)`. Rewrite using `[← pow_add, ← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite `hU` using `[hx, hl]`.

Simplify using `only [map_mul, map_pow] at hU ⊢`. Establish `key : C ϖ ^ m * (D - C ϖ ^ (e * s₁) * (C ϖ ^ (e * κ - m - e * s₁) * C ((v⁻¹ : Oˣ) : O) * C (u : O) ^ κ * U₁)) = P.p 1 ^ B * (-(C ((v⁻¹ : Oˣ) : O)) * U₂)`. Take the linear combination `C ((v⁻¹ : Oˣ) : O) * hU - C ϖ ^ m * D * hvv + C ((v⁻¹ : Oˣ) : O) * C (u : O) ^ κ * U₁ * hpow2`. Rewrite using `[key]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))`.
-/
theorem den_of_rel (P : PhiData O l) {ϖ : O} (hϖ : Irreducible ϖ) {D U₁ U₂ : O⟦X⟧} {x : O} {κ B s₁ : ℕ}
    (hU : D * C x = C (l : O) ^ κ * 1 * U₁ - P.p 1 ^ B * U₂)
    (hC : D ∉ Ideal.span {C ϖ ^ (eO (O := O) l * s₁), P.p 1 ^ B}) :
    (l : O) ^ κ ∣ (l : O) ^ s₁ * x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_contra hnd
  apply hC
  obtain ⟨m, v, hx⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  obtain ⟨e, u, hl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible P.hl0 hϖ
  have he : eO (O := O) l = e := by
    unfold eO
    rw [hl, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, IsDiscreteValuationRing.addVal_eq_zero_of_unit]
    simp
  rw [he]

  have hlt : e * s₁ + m < e * κ := by
    by_contra hle
    push_neg at hle
    apply hnd
    refine ⟨(u : O) ^ s₁ * v * ((u⁻¹ : Oˣ) : O) ^ κ * ϖ ^ (e * s₁ + m - e * κ), ?_⟩
    have h1 : ((u : O) * ((u⁻¹ : Oˣ) : O)) ^ κ = 1 := by rw [Units.mul_inv, one_pow]
    have hpow : ϖ ^ (e * s₁ + m) = ϖ ^ (e * κ) * ϖ ^ (e * s₁ + m - e * κ) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hx, hl]
    linear_combination (-((u : O) ^ s₁ * v * ϖ ^ (e * κ) * ϖ ^ (e * s₁ + m - e * κ))) * h1 +
      ((u : O) ^ s₁ * v) * hpow
  have hd : IsDist (P.p 1 ^ B) := by
    unfold IsDist
    rw [map_pow]
    exact pow_ne_zero _ (P.isDist_p 1)
  rw [← C2' hϖ hd D (e * s₁)]
  refine ⟨C (ϖ ^ (e * κ - m - e * s₁) * ((v⁻¹ : Oˣ) : O) * (u : O) ^ κ) * U₁, m, ?_⟩
  have hvv : C (v : O) * C ((v⁻¹ : Oˣ) : O) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hpow2 : C ϖ ^ (e * κ) = C ϖ ^ m * C ϖ ^ (e * s₁) * C ϖ ^ (e * κ - m - e * s₁) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [hx, hl] at hU
  simp only [map_mul, map_pow] at hU ⊢
  have key : C ϖ ^ m * (D - C ϖ ^ (e * s₁) *
      (C ϖ ^ (e * κ - m - e * s₁) * C ((v⁻¹ : Oˣ) : O) * C (u : O) ^ κ * U₁)) =
      P.p 1 ^ B * (-(C ((v⁻¹ : Oˣ) : O)) * U₂) := by
    linear_combination C ((v⁻¹ : Oˣ) : O) * hU - C ϖ ^ m * D * hvv +
      C ((v⁻¹ : Oˣ) : O) * C (u : O) ^ κ * U₁ * hpow2
  rw [key]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))

end End

end Formalism.MainNotions.N.FrobeniusPowerSeries
