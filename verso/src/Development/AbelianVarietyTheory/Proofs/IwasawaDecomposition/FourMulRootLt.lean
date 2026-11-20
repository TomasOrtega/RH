import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PowEqOfPartEq

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.TamePow

/- English proof (translation)
Establish `hk5 : (5 : ℝ) ≤ k` using `by linarith`. Establish `hg0 : 0 ≤ g` using `le_trans (by positivity) hg`. Use `set t := g ^ ((1 : ℝ) / 4) with ht`. Establish `ht4 : t ^ 4 = g`. Rewrite using `[ht, ← Real.rpow_natCast, ← Real.rpow_mul hg0]`.

Evaluate the numerical expressions. Establish `hkt : k ^ 2 ≤ t`. Establish `h8 : (k ^ 8) ^ ((1 : ℝ) / 4) ≤ t` using `Real.rpow_le_rpow (by positivity) hg (by norm_num)`. Establish `e : (k ^ 8) ^ ((1 : ℝ) / 4) = k ^ 2`. Rewrite using `[show (k ^ 8 : ℝ) = (k ^ 2) ^ (4 : ℕ) by ring, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]`.

Evaluate the numerical expressions. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ht25 : 25 ≤ t` using `by nlinarith`. Establish `h1 : 4 * m * t < k ^ 2 * t`. Establish `: 4 * m < k ^ 2` using `by nlinarith`.

Conclude with `mul_lt_mul_of_pos_right this (by linarith)`. Establish `h2 : k ^ 2 * t ≤ t * t` using `mul_le_mul_of_nonneg_right hkt (by linarith)`. Establish `hs : 625 ≤ t * t` using `by nlinarith`. Establish `h3 : t * t + 1 < t ^ 4`. Establish `e4 : t ^ 4 = t * t * (t * t)` using `by ring`.

Use `mul_le_mul_of_nonneg_right hs (by positivity : (0 : ℝ) ≤ t * t)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem four_mul_root_lt {m k g : ℝ} (hm : 2 ≤ m) (hk : m + 3 ≤ k) (hg : k ^ 8 ≤ g) :
    4 * m * g ^ ((1 : ℝ) / 4) < g - 1 := by
  have hk5 : (5 : ℝ) ≤ k := by linarith
  have hg0 : 0 ≤ g := le_trans (by positivity) hg
  set t := g ^ ((1 : ℝ) / 4) with ht
  have ht4 : t ^ 4 = g := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hg0]
    norm_num
  have hkt : k ^ 2 ≤ t := by
    have h8 : (k ^ 8) ^ ((1 : ℝ) / 4) ≤ t := Real.rpow_le_rpow (by positivity) hg (by norm_num)
    have e : (k ^ 8) ^ ((1 : ℝ) / 4) = k ^ 2 := by
      rw [show (k ^ 8 : ℝ) = (k ^ 2) ^ (4 : ℕ) by ring, ← Real.rpow_natCast,
        ← Real.rpow_mul (by positivity)]
      norm_num
    linarith
  have ht25 : 25 ≤ t := by nlinarith
  have h1 : 4 * m * t < k ^ 2 * t := by
    have : 4 * m < k ^ 2 := by nlinarith
    exact mul_lt_mul_of_pos_right this (by linarith)
  have h2 : k ^ 2 * t ≤ t * t := mul_le_mul_of_nonneg_right hkt (by linarith)
  have hs : 625 ≤ t * t := by nlinarith
  have h3 : t * t + 1 < t ^ 4 := by
    have e4 : t ^ 4 = t * t * (t * t) := by ring
    have := mul_le_mul_of_nonneg_right hs (by positivity : (0 : ℝ) ≤ t * t)
    nlinarith
  linarith

/- English proof (translation)
Take `⟨sp, hT, hY, hA, hV, hz, rfl, -⟩` from `h`. Use `show 4 * (K.P.R.m : ℝ) * (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4) < (K.P.H.g i : ℝ) - 1`. Establish `hr : RankVal K.s K.P.R` using `K.ok.rank`. Unfold `RankVal at hr`. Take `⟨-, ⟨-, hm⟩, ⟨hk, -⟩, -⟩` from `hr`.

Establish `hv : HostVal K.s K.C.P.Cpde K.P.H` using `K.ok.val`. Unfold `HostVal at hv`. Take `⟨-, -, -, -, hg, -⟩` from `hv`. Establish `hx1 : 1 < K.s.x` using `K.s.one_lt_alt`. Establish `he0 : 0 < K.s.eps` using `K.s.eps_pos`.

Establish `hx0 : (0 : ℝ) ≤ K.s.x` using `by linarith`. Establish `hd1 : K.s.delta1 ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by linarith)`. Establish `hd0 : 0 ≤ K.s.delta1` using `Real.rpow_nonneg hx0 _`. Use `set y := Real.sqrt K.s.x with hy`. Establish `hy2 : y ^ 2 = K.s.x` using `Real.sq_sqrt hx0`.

Establish `hy1 : 1 ≤ y`. Rewrite using `[show (1 : ℝ) = Real.sqrt 1 by simp]`. Conclude with `Real.sqrt_le_sqrt hx1.le`. Establish `hmy : (K.P.R.m : ℝ) ≤ 2 * y`. Establish `: Real.sqrt (K.s.x * K.s.delta1) ≤ y` using `Real.sqrt_le_sqrt (by nlinarith)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk4 : K.s.x ^ (4 : ℕ) ≤ (K.P.R.k : ℝ)`. Establish `h1 : K.s.x ^ (4 : ℝ) ≤ K.s.x ^ ((9 : ℝ) / 2 + 10 * K.s.eps)` using `Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)`. Establish `h2 : K.s.x ^ (4 : ℝ) = K.s.x ^ (4 : ℕ)` using `by exact_mod_cast Real.rpow_natCast K.s.x 4`. Conclude with `le_trans (le_trans h2.symm.le h1) hk`.

Establish `hk8 : y ^ 8 ≤ (K.P.R.k : ℝ)`. Establish `: y ^ 8 = K.s.x ^ (4 : ℕ)` using `by rw [← hy2]; ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk2 : (2 : ℝ) ≤ K.P.R.k`. Establish `h1 : (1 : ℝ) < K.P.R.k` using `lt_of_lt_of_le (one_lt_pow₀ hx1 (by norm_num)) hk4`.

Establish `h2 : 1 < K.P.R.k` using `by exact_mod_cast h1`. Conclude with `h2` after adjusting the coercions. Establish `hb : (2.718 : ℝ) ≤ K.s.b`. Establish `hL : 1 ≤ K.s.L` using `Real.one_le_rpow hx1.le he0.le`. Establish `h1 : Real.exp 1 ≤ K.s.b` using `Real.exp_le_exp.2 hL`.

Establish `h2` using `Real.exp_one_gt_d9`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hkb1 : (5 : ℝ) ≤ (K.P.R.k : ℝ) * K.s.b` using `by nlinarith`. Establish `hkb2 : 2 * y + 3 ≤ (K.P.R.k : ℝ) * K.s.b`. Establish `hkb : 2.718 * (K.P.R.k : ℝ) ≤ (K.P.R.k : ℝ) * K.s.b` using `by nlinarith`.

Distinguish the cases in `h5 : (5 : ℝ) ≤ (K.P.R.k : ℝ)`. Establish `: y ≤ y ^ 8` using `le_self_pow₀ hy1 (by norm_num)`. Combine the linear equalities and inequalities to obtain the conclusion. Use `push_neg at h5`. Establish `hk4' : (K.P.R.k : ℝ) ≤ 4`.

Establish `: K.P.R.k < 5` using `by exact_mod_cast h5`. Establish `: K.P.R.k ≤ 4` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hy12 : y ≤ 1.2`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Establish `: (1.2 : ℝ) ^ 8 < y ^ 8` using `pow_lt_pow_left₀ hc (by norm_num) (by norm_num)`. Evaluate the numerical expressions using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hM : max 2 (K.P.R.m : ℝ) + 3 ≤ (K.P.R.k : ℝ) * K.s.b`. Establish `: max 2 (K.P.R.m : ℝ) ≤ (K.P.R.k : ℝ) * K.s.b - 3` using `max_le (by linarith) (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmain` using `four_mul_root_lt (le_max_left 2 (K.P.R.m : ℝ)) hM (hg i).1`. Establish `ht : (0 : ℝ) ≤ (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4)` using `Real.rpow_nonneg (by positivity) _`.

Establish `hle : 4 * (K.P.R.m : ℝ) * (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4) ≤ 4 * max 2 (K.P.R.m : ℝ) * (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4)`. Establish `: (K.P.R.m : ℝ) ≤ max 2 (K.P.R.m : ℝ)` using `le_max_right _ _`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bound_of_over (K : Ctx) (B : Pre) (h : K.Over B) (i : Fin 2) :
    4 * (B.R.m : ℝ) * (B.host.g i : ℝ) ^ ((1 : ℝ) / 4) < (B.host.g i : ℝ) - 1 := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  show 4 * (K.P.R.m : ℝ) * (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4) < (K.P.H.g i : ℝ) - 1
  have hr : RankVal K.s K.P.R := K.ok.rank
  unfold RankVal at hr
  obtain ⟨-, ⟨-, hm⟩, ⟨hk, -⟩, -⟩ := hr
  have hv : HostVal K.s K.C.P.Cpde K.P.H := K.ok.val
  unfold HostVal at hv
  obtain ⟨-, -, -, -, hg, -⟩ := hv
  have hx1 : 1 < K.s.x := K.s.one_lt_alt
  have he0 : 0 < K.s.eps := K.s.eps_pos
  have hx0 : (0 : ℝ) ≤ K.s.x := by linarith
  have hd1 : K.s.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by linarith)
  have hd0 : 0 ≤ K.s.delta1 := Real.rpow_nonneg hx0 _
  set y := Real.sqrt K.s.x with hy
  have hy2 : y ^ 2 = K.s.x := Real.sq_sqrt hx0
  have hy1 : 1 ≤ y := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx1.le
  have hmy : (K.P.R.m : ℝ) ≤ 2 * y := by
    have : Real.sqrt (K.s.x * K.s.delta1) ≤ y := Real.sqrt_le_sqrt (by nlinarith)
    linarith
  have hk4 : K.s.x ^ (4 : ℕ) ≤ (K.P.R.k : ℝ) := by
    have h1 : K.s.x ^ (4 : ℝ) ≤ K.s.x ^ ((9 : ℝ) / 2 + 10 * K.s.eps) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    have h2 : K.s.x ^ (4 : ℝ) = K.s.x ^ (4 : ℕ) := by exact_mod_cast Real.rpow_natCast K.s.x 4
    exact le_trans (le_trans h2.symm.le h1) hk
  have hk8 : y ^ 8 ≤ (K.P.R.k : ℝ) := by
    have : y ^ 8 = K.s.x ^ (4 : ℕ) := by rw [← hy2]; ring
    linarith
  have hk2 : (2 : ℝ) ≤ K.P.R.k := by
    have h1 : (1 : ℝ) < K.P.R.k := lt_of_lt_of_le (one_lt_pow₀ hx1 (by norm_num)) hk4
    have h2 : 1 < K.P.R.k := by exact_mod_cast h1
    exact_mod_cast h2
  have hb : (2.718 : ℝ) ≤ K.s.b := by
    have hL : 1 ≤ K.s.L := Real.one_le_rpow hx1.le he0.le
    have h1 : Real.exp 1 ≤ K.s.b := Real.exp_le_exp.2 hL
    have h2 := Real.exp_one_gt_d9
    linarith
  have hkb1 : (5 : ℝ) ≤ (K.P.R.k : ℝ) * K.s.b := by nlinarith
  have hkb2 : 2 * y + 3 ≤ (K.P.R.k : ℝ) * K.s.b := by
    have hkb : 2.718 * (K.P.R.k : ℝ) ≤ (K.P.R.k : ℝ) * K.s.b := by nlinarith
    by_cases h5 : (5 : ℝ) ≤ (K.P.R.k : ℝ)
    · have : y ≤ y ^ 8 := le_self_pow₀ hy1 (by norm_num)
      linarith
    · push_neg at h5
      have hk4' : (K.P.R.k : ℝ) ≤ 4 := by
        have : K.P.R.k < 5 := by exact_mod_cast h5
        have : K.P.R.k ≤ 4 := by omega
        exact_mod_cast this
      have hy12 : y ≤ 1.2 := by
        by_contra hc
        push_neg at hc
        have : (1.2 : ℝ) ^ 8 < y ^ 8 := pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
        norm_num at this
        linarith
      linarith
  have hM : max 2 (K.P.R.m : ℝ) + 3 ≤ (K.P.R.k : ℝ) * K.s.b := by
    have : max 2 (K.P.R.m : ℝ) ≤ (K.P.R.k : ℝ) * K.s.b - 3 := max_le (by linarith) (by linarith)
    linarith
  have hmain := four_mul_root_lt (le_max_left 2 (K.P.R.m : ℝ)) hM (hg i).1
  have ht : (0 : ℝ) ≤ (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
  have hle : 4 * (K.P.R.m : ℝ) * (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4) ≤
      4 * max 2 (K.P.R.m : ℝ) * (K.P.H.g i : ℝ) ^ ((1 : ℝ) / 4) := by
    have : (K.P.R.m : ℝ) ≤ max 2 (K.P.R.m : ℝ) := le_max_right _ _
    nlinarith
  linarith

/- English proof (translation)
Assemble the required witnesses or components as `⟨X.toD7.host.g_prime k⟩; DC.TameDistinct X.toD7.R.r (X.toD7.host.g k) (X.toD7.nd.chiT k v) := by have key : ∀ K : Ctx, ∀ X : Stages, K.Over X.B.toPre → (∀ (k : Fin 2) (v : X.N.nd.PlG k), ∃ w : (ZMod (X.B.host.g k))ˣ, orderOf w = X.B.host.g k - 1 ∧ ∀ j : Fin X.B.R.m, X.N.nd.chiT k …`.
-/
theorem tame_of_pow : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → (∀ (k : Fin 2) (v : X.N.nd.PlG k), ∃ w : (ZMod (X.B.host.g k))ˣ, orderOf w = X.B.host.g k - 1 ∧ ∀ j : Fin X.B.R.m, X.N.nd.chiT k v j = w ^ (2 * (j.1 + 1))) → ∀ (k : Fin 2) (v : X.toD7.nd.PlG k), haveI : Fact (X.toD7.host.g k).Prime := ⟨X.toD7.host.g_prime k⟩; DC.TameDistinct X.toD7.R.r (X.toD7.host.g k) (X.toD7.nd.chiT k v) := by
  have key : ∀ K : Ctx, ∀ X : Stages, K.Over X.B.toPre → (∀ (k : Fin 2) (v : X.N.nd.PlG k),
      ∃ w : (ZMod (X.B.host.g k))ˣ, orderOf w = X.B.host.g k - 1 ∧
        ∀ j : Fin X.B.R.m, X.N.nd.chiT k v j = w ^ (2 * (j.1 + 1))) →
      ∀ (k : Fin 2) (v : X.toD7.nd.PlG k), haveI : Fact (X.toD7.host.g k).Prime := ⟨X.toD7.host.g_prime k⟩;
        DC.TameDistinct X.toD7.R.r (X.toD7.host.g k) (X.toD7.nd.chiT k v) := by
    intro K X hO hpow k v
    obtain ⟨w, hw, hchi⟩ := hpow k v
    have hb := bound_of_over K X.B.toPre hO k
    have hr : 1 ≤ X.toD7.R.r := by
      have h2 := X.toD7.R.two_le_m
      first
      | (show 1 ≤ X.toD7.R.k + X.toD7.R.m - 1; omega)
      | omega
      | (simp only [Formalism.MainNotions.Ranks.r]; omega)
      | (unfold Formalism.MainNotions.Ranks.r; omega)
    have e : X.toD7.nd.chiT k v = fun j : Fin X.B.R.m => w ^ (2 * (j.1 + 1)) := funext hchi
    haveI : Fact (X.toD7.host.g k).Prime := ⟨X.toD7.host.g_prime k⟩
    have h := GlobalTheory.EX.DC.TameGen.tameDistinct_gen X.toD7.R.r (X.toD7.host.g k) X.B.R.m w hw hb hr
    rw [e]
    exact h
  unfold Ev
  refine ⟨1, one_pos, ?_⟩
  intro eps C8 _ _ _ _
  refine ⟨?k0, fun C _ _ _ => ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun K => ?_⟩⟩⟩⟩
  case k0 => first | exact ⟨0, 0, 0, 0⟩ | exact default | exact Classical.arbitrary _
  first
  | exact key K
  | exact fun _ => key K
  | exact fun _ _ => key K
  | exact fun _ _ _ => key K
  | exact fun _ _ _ _ => key K
  | exact fun _ _ _ _ _ => key K
  | exact fun _ _ _ _ _ _ => key K
  | exact fun _ _ _ _ _ _ _ => key K
  | exact fun _ _ _ _ _ _ _ _ => key K

end GlobalTheory.Mem.Top.TamePow
