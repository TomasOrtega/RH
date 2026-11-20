import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HostBoundsTwoMulRpowLogSqLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodTopCountLeConstMulLog
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmData
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DimVRowPos
import Development.AutomorphicArithmetic.WeightCongruences.TorsionOrderLeTwoMulFinrankSq

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

noncomputable section

namespace GlobalTheory.EX.WinLow

open Formalism.MainNotions.StandardLattice Finset

/- English proof (translation)
Establish `h` using `UpperTheory.torsionOrder_le_two_mul_finrank_sq H.E`. Rewrite `h` using `[finrank_E H]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem roots_le {R : Ranks} (H : Host R) : NumberField.Units.torsionOrder H.E ≤ 8 * R.f ^ 2 := by
  have h := UpperTheory.torsionOrder_le_two_mul_finrank_sq H.E
  rw [finrank_E H] at h
  linarith

/- English proof (translation)
Take `⟨x1, hx1⟩` from `rank_basic_bounds eps h0 h1`. Take `⟨x2, hx2⟩` from `scale_sizes eps cD (ch + 7) h0 h1 hcD (by linarith)`. Use `⟨max 8 (max x1 x2), fun s R he hx hR => ?_⟩` and prove the remaining obligations. Simplify using `only [max_le_iff] at hx`. Take `⟨h8, hxa, hxb⟩` from `hx`.

Take `⟨hf, -⟩` from `hx1 s R he hxa hR`. Take `⟨-, -, -, -, s5, -⟩` from `hx2 s R he hxb hR`. Establish `hxp : 0 < s.x` using `by linarith`. Establish `hf' : (R.f : ℝ) ≤ s.x ^ (3 : ℕ)` using `by exact_mod_cast hf`. Establish `o3 : 1 ≤ s.x ^ ch` using `Real.one_le_rpow (by linarith) hch`.

Establish `hH : (h0v s ch : ℝ) ≤ 4 * s.x ^ ch`. Use `(Nat.ceil_lt_add_one (show 0 ≤ s.x ^ ch by positivity)).le` as an intermediate fact. Unfold `h0v`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hH' : 2 * (s.x ^ ch * s.x ^ (7 : ℕ)) ≤ (h0v s (ch + 7) : ℝ)`. Use `Nat.le_ceil (s.x ^ (ch + 7))` as an intermediate fact. Establish `e : s.x ^ (ch + 7) = s.x ^ ch * s.x ^ (7 : ℕ)`. Rewrite using `[Real.rpow_add hxp]`. Use `norm_cast`.

Unfold `h0v`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hm : (1 : ℝ) ≤ R.m` using `by exact_mod_cast (by have := R.two_le_m; omega : 1 ≤ R.m)`. Establish `hf2 : (R.f : ℝ) ^ 2 ≤ s.x ^ (6 : ℕ)`.

Combine the equalities or inequalities in the displayed calculation. Establish `p6 : 1 ≤ s.x ^ (6 : ℕ)` using `one_le_pow₀ (by linarith)`. Establish `p7 : 8 * s.x ^ (6 : ℕ) ≤ s.x ^ (7 : ℕ)`. Rewrite using `[pow_succ' s.x 6]; exact mul_le_mul_of_nonneg_right h8 (by positivity)`. Establish `hz : 1 ≤ (R.m : ℝ) * s.x ^ ch` using `one_le_mul_of_one_le_of_one_le hm o3`.

Establish `a1` using `mul_le_mul_of_nonneg_left hH (by linarith : (0 : ℝ) ≤ R.m)`. Establish `a2` using `mul_le_mul_of_nonneg_left hH' (by linarith : (0 : ℝ) ≤ R.m)`. Establish `a3 : (R.m : ℝ) * s.x ^ ch * 4 ≤ (R.m : ℝ) * s.x ^ ch * s.x ^ (7 : ℕ)` using `mul_le_mul_of_nonneg_left (by linarith) (by linarith)`. Establish `a4 : s.x ^ (7 : ℕ) ≤ (R.m : ℝ) * s.x ^ ch * s.x ^ (7 : ℕ)` using `le_mul_of_one_le_left (by linarith) hz`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem span_roots (eps cD ch : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hcD : 0 ≤ cD) (hch : 0 ≤ ch) :
    ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R →
      R.m * (h0v s ch : ℝ) + 8 * (R.f : ℝ) ^ 2 + 2 ≤ s.b := by
  obtain ⟨x1, hx1⟩ := rank_basic_bounds eps h0 h1
  obtain ⟨x2, hx2⟩ := scale_sizes eps cD (ch + 7) h0 h1 hcD (by linarith)
  refine ⟨max 8 (max x1 x2), fun s R he hx hR => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨h8, hxa, hxb⟩ := hx
  obtain ⟨hf, -⟩ := hx1 s R he hxa hR
  obtain ⟨-, -, -, -, s5, -⟩ := hx2 s R he hxb hR
  have hxp : 0 < s.x := by linarith
  have hf' : (R.f : ℝ) ≤ s.x ^ (3 : ℕ) := by exact_mod_cast hf
  have o3 : 1 ≤ s.x ^ ch := Real.one_le_rpow (by linarith) hch
  have hH : (h0v s ch : ℝ) ≤ 4 * s.x ^ ch := by
    have := (Nat.ceil_lt_add_one (show 0 ≤ s.x ^ ch by positivity)).le
    unfold h0v; push_cast; linarith
  have hH' : 2 * (s.x ^ ch * s.x ^ (7 : ℕ)) ≤ (h0v s (ch + 7) : ℝ) := by
    have := Nat.le_ceil (s.x ^ (ch + 7))
    have e : s.x ^ (ch + 7) = s.x ^ ch * s.x ^ (7 : ℕ) := by
      rw [Real.rpow_add hxp]; norm_cast
    unfold h0v; push_cast; linarith
  have hm : (1 : ℝ) ≤ R.m := by exact_mod_cast (by have := R.two_le_m; omega : 1 ≤ R.m)
  have hf2 : (R.f : ℝ) ^ 2 ≤ s.x ^ (6 : ℕ) := by
    calc (R.f : ℝ) ^ 2 ≤ (s.x ^ (3 : ℕ)) ^ 2 := pow_le_pow_left₀ (by positivity) hf' 2
      _ = _ := by ring
  have p6 : 1 ≤ s.x ^ (6 : ℕ) := one_le_pow₀ (by linarith)
  have p7 : 8 * s.x ^ (6 : ℕ) ≤ s.x ^ (7 : ℕ) := by
    rw [pow_succ' s.x 6]; exact mul_le_mul_of_nonneg_right h8 (by positivity)
  have hz : 1 ≤ (R.m : ℝ) * s.x ^ ch := one_le_mul_of_one_le_of_one_le hm o3
  have a1 := mul_le_mul_of_nonneg_left hH (by linarith : (0 : ℝ) ≤ R.m)
  have a2 := mul_le_mul_of_nonneg_left hH' (by linarith : (0 : ℝ) ≤ R.m)
  have a3 : (R.m : ℝ) * s.x ^ ch * 4 ≤ (R.m : ℝ) * s.x ^ ch * s.x ^ (7 : ℕ) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have a4 : s.x ^ (7 : ℕ) ≤ (R.m : ℝ) * s.x ^ ch * s.x ^ (7 : ℕ) := le_mul_of_one_le_left (by linarith) hz
  linarith

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hmid, -⟩` from `hC`. Establish `hLa : 1 ≤ C.GK.La` using `hmid _ (by simp [FC.cMid])`. Take `⟨x1, hx1⟩` from `bottom_len eps C.GK h0 h1 hLa`. Take `⟨x2, hx2⟩` from `scale_sizes eps cD ch h0 h1 hcD hch`. Take `⟨x3, hx3⟩` from `span_roots eps cD ch h0 h1 hcD hch`.

Use `⟨max (max x1 x2) x3, fun s P q1 a b c he hx h u τ => ?_⟩` and prove the remaining obligations. Simplify using `only [max_le_iff] at hx`. Establish `hbl` using `hx1 s P.R he hx.1.1 h.rank`. Take `⟨s1, s2, s3, s4, s5, s6, s7, -⟩` from `hx2 s P.R he hx.1.2 h.rank`. Establish `s8` using `hx3 s P.R he hx.2 h.rank`.

Establish `hf0 : (0 : ℝ) ≤ (P.R.f : ℝ) ^ 2` using `by positivity`. Take `⟨v1, v2, ⟨b1, v3, v4, v5, v6⟩, -⟩` from `h.hc u`. Establish `hx1'` using `s.one_lt_alt`. Establish `hxp : 0 < s.x` using `by linarith`. Establish `hk` using `P.R.m_add_three_le_k`.

Establish `hk2 : (2 : ℝ) ≤ P.R.k` using `by exact_mod_cast (by omega : 2 ≤ P.R.k)`. Establish `hD : (1 : ℝ) ≤ (Delv s cD : ℝ)`. Establish `: 0 < ⌈s.x ^ cD⌉₊` using `Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hxp _)`. Conclude with `this` after adjusting the coercions. Establish `htop : (τ : P.R.GG) ∈ P.H.topPlaces → ∃ t : P.H.TT, (τ : P.R.GG) = P.R.tau1 t`.

Introduce `h1`. Unfold `Host.topPlaces at h1`. Take `⟨t, ht, e⟩` from `Finset.mem_image.1 h1`. Conclude with `⟨⟨t, ht⟩, e.symm⟩`. Establish `hb1 : s.w'' P.R.n ≤ (b1 τ : ℝ) ∧ (b1 τ : ℝ) ≤ s.b + 8 * (P.R.f : ℝ) ^ 2 + 2`.

Distinguish the cases in `c1 : (τ : P.R.GG) ∈ P.H.topPlaces`. Take `⟨t, ht⟩` from `htop c1`. Take `⟨-, w1, w2⟩` from `h.win t t.2`. Establish `f1 : (0 : ℝ) ≤ (⌊s.b' / s.x⌋ : ℤ)` using `by exact_mod_cast Int.floor_nonneg.2 (by positivity)`. Establish `f2 : ((⌊s.b' / s.x⌋ : ℤ) : ℝ) ≤ s.b'` using `(Int.floor_le _).trans (div_le_self s3 hx1'.le)`.

Rewrite using `[v4 τ t ht]`. Use `push_cast`. Apply the tactic sequence `constructor <;> linarith`. Distinguish the cases in `c2 : (τ : P.R.GG) ∈ P.H.thickPlaces`. Establish `f1` using `Int.le_ceil s.b`.

Establish `f2` using `Int.ceil_lt_add_one s.b`. Take `⟨e1, e2⟩` from `v5 τ c2`. Establish `e3 : ((⌈s.b⌉ : ℤ) : ℝ) ≤ (b1 τ : ℝ)` using `by exact_mod_cast e1`. Establish `e4 : (b1 τ : ℝ) < ((⌈s.b⌉ : ℤ) : ℝ) + (NumberField.Units.torsionOrder P.H.E : ℝ)` using `by exact_mod_cast e2`. Establish `e5 : (NumberField.Units.torsionOrder P.H.E : ℝ) ≤ 8 * (P.R.f : ℝ) ^ 2` using `by exact_mod_cast roots_le P.H`.

Apply the tactic sequence `constructor <;> linarith`. Establish `f1` using `Int.le_ceil (s.w'' P.R.n)`. Establish `f2` using `Int.ceil_lt_add_one (s.w'' P.R.n)`. Rewrite using `[v6 τ ⟨τ.2, c1, c2⟩]`. Apply the tactic sequence `constructor <;> linarith`.

Use `place_data (P.hcW u τ) s.x (Delv s cD) s.a s.b (h0v s ch) (b1 τ) hx1'.le hD (by positivity) (fun i => ?_) (fun hp hp' => ?_) (fun j => ?_) (s1.trans hb1.1) (by linarith [hb1.2])` and prove the remaining obligations. Rewrite using `[v1 τ i]`. Use `push_cast`. Both sides reduce to the same expression. Distinguish the cases in `c1 : (τ : P.R.GG) ∈ P.H.topPlaces`.

Use `left`. Take `⟨t, ht⟩` from `htop c1`. Take `⟨⟨-, w0⟩, w1, w2⟩` from `h.win t t.2`. Take `⟨e1, e2⟩` from `h.top u τ t hp ht`. Establish `ha : 0 ≤ s.a` using `by linarith`.

Establish `o1 : 1 ≤ s.x ^ (Scale.A / 2)` using `Real.one_le_rpow hx1'.le (by norm_num [Scale.A])`. Establish `o2 : s.a / ((P.R.k : ℝ) * s.x ^ (Scale.A / 2)) ≤ s.a / 2` using `div_le_div_of_nonneg_left ha (by norm_num) (by nlinarith)`. Rewrite using `[e1, e2]`. Use `push_cast`. Apply the tactic sequence `constructor <;> linarith`.

Use `right`. Take `⟨e1, e2⟩` from `v2 τ hp c1`. Rewrite using `[e1, e2]`. Use `push_cast`. Conclude with `⟨rfl, rfl⟩`.

Take `⟨e1, e2⟩` from `v3 τ j`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e1]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[e2]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem places_ok (eps : ℝ) (C : FC) (cD ch : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hC : Std C) (hcD : 0 ≤ cD)
    (hch : 0 ≤ ch) : ∃ x0 : ℝ, ∀ (s : Scale) (P : PreCh) (q1 : ℕ) (a b : P.R.A → ℤ)
      (c : P.Word → Fin (P.R.k - 2) → Bool), s.eps = eps → x0 ≤ s.x → ChOK s C cD ch P q1 a b c →
      ∀ u τ, Formalism.LogVandermondeBounds.StandardLattice.PlaceData s.x (Delv s cD) s.a s.b P.R.k P.R.m (seqOf (P.hcW u τ).u) (seqOf (P.hcW u τ).v)
        (seqOf (P.hcW u τ).b) (seqOf (P.hcW u τ).e) ∧ ∀ j < P.R.m, 1 ≤ seqOf (P.hcW u τ).e j := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hmid, -⟩ := hC
  have hLa : 1 ≤ C.GK.La := hmid _ (by simp [FC.cMid])
  obtain ⟨x1, hx1⟩ := bottom_len eps C.GK h0 h1 hLa
  obtain ⟨x2, hx2⟩ := scale_sizes eps cD ch h0 h1 hcD hch
  obtain ⟨x3, hx3⟩ := span_roots eps cD ch h0 h1 hcD hch
  refine ⟨max (max x1 x2) x3, fun s P q1 a b c he hx h u τ => ?_⟩
  simp only [max_le_iff] at hx
  have hbl := hx1 s P.R he hx.1.1 h.rank
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, -⟩ := hx2 s P.R he hx.1.2 h.rank
  have s8 := hx3 s P.R he hx.2 h.rank
  have hf0 : (0 : ℝ) ≤ (P.R.f : ℝ) ^ 2 := by positivity
  obtain ⟨v1, v2, ⟨b1, v3, v4, v5, v6⟩, -⟩ := h.hc u
  have hx1' := s.one_lt_alt
  have hxp : 0 < s.x := by linarith
  have hk := P.R.m_add_three_le_k
  have hk2 : (2 : ℝ) ≤ P.R.k := by exact_mod_cast (by omega : 2 ≤ P.R.k)
  have hD : (1 : ℝ) ≤ (Delv s cD : ℝ) := by
    have : 0 < ⌈s.x ^ cD⌉₊ := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hxp _)
    exact_mod_cast this
  have htop : (τ : P.R.GG) ∈ P.H.topPlaces → ∃ t : P.H.TT, (τ : P.R.GG) = P.R.tau1 t := by
    intro h1
    unfold Host.topPlaces at h1
    obtain ⟨t, ht, e⟩ := Finset.mem_image.1 h1
    exact ⟨⟨t, ht⟩, e.symm⟩
  have hb1 : s.w'' P.R.n ≤ (b1 τ : ℝ) ∧ (b1 τ : ℝ) ≤ s.b + 8 * (P.R.f : ℝ) ^ 2 + 2 := by
    by_cases c1 : (τ : P.R.GG) ∈ P.H.topPlaces
    · obtain ⟨t, ht⟩ := htop c1
      obtain ⟨-, w1, w2⟩ := h.win t t.2
      have f1 : (0 : ℝ) ≤ (⌊s.b' / s.x⌋ : ℤ) := by exact_mod_cast Int.floor_nonneg.2 (by positivity)
      have f2 : ((⌊s.b' / s.x⌋ : ℤ) : ℝ) ≤ s.b' := (Int.floor_le _).trans (div_le_self s3 hx1'.le)
      rw [v4 τ t ht]
      push_cast
      constructor <;> linarith
    · by_cases c2 : (τ : P.R.GG) ∈ P.H.thickPlaces
      · have f1 := Int.le_ceil s.b
        have f2 := Int.ceil_lt_add_one s.b
        obtain ⟨e1, e2⟩ := v5 τ c2
        have e3 : ((⌈s.b⌉ : ℤ) : ℝ) ≤ (b1 τ : ℝ) := by exact_mod_cast e1
        have e4 : (b1 τ : ℝ) < ((⌈s.b⌉ : ℤ) : ℝ) + (NumberField.Units.torsionOrder P.H.E : ℝ) := by exact_mod_cast e2
        have e5 : (NumberField.Units.torsionOrder P.H.E : ℝ) ≤ 8 * (P.R.f : ℝ) ^ 2 := by exact_mod_cast roots_le P.H
        constructor <;> linarith
      · have f1 := Int.le_ceil (s.w'' P.R.n)
        have f2 := Int.ceil_lt_add_one (s.w'' P.R.n)
        rw [v6 τ ⟨τ.2, c1, c2⟩]
        constructor <;> linarith
  refine place_data (P.hcW u τ) s.x (Delv s cD) s.a s.b (h0v s ch) (b1 τ) hx1'.le hD (by positivity)
    (fun i => ?_) (fun hp hp' => ?_) (fun j => ?_) (s1.trans hb1.1) (by linarith [hb1.2])
  · rw [v1 τ i]; push_cast; rfl
  · by_cases c1 : (τ : P.R.GG) ∈ P.H.topPlaces
    · left
      obtain ⟨t, ht⟩ := htop c1
      obtain ⟨⟨-, w0⟩, w1, w2⟩ := h.win t t.2
      obtain ⟨e1, e2⟩ := h.top u τ t hp ht
      have ha : 0 ≤ s.a := by linarith
      have o1 : 1 ≤ s.x ^ (Scale.A / 2) := Real.one_le_rpow hx1'.le (by norm_num [Scale.A])
      have o2 : s.a / ((P.R.k : ℝ) * s.x ^ (Scale.A / 2)) ≤ s.a / 2 :=
        div_le_div_of_nonneg_left ha (by norm_num) (by nlinarith)
      rw [e1, e2]
      push_cast
      constructor <;> linarith
    · right
      obtain ⟨e1, e2⟩ := v2 τ hp c1
      rw [e1, e2]
      push_cast
      exact ⟨rfl, rfl⟩
  · obtain ⟨e1, e2⟩ := v3 τ j
    refine ⟨?_, ?_⟩
    · rw [e1]; push_cast; rfl
    · rw [e2]; push_cast; rfl

/- English proof (translation)
Take `⟨x1, hx1⟩` from `rank_basic_bounds eps h0 h1`. Use `⟨max x1 (max ((2 * |c|) ^ 4) ((2 * |g|) ^ 4)), fun s R he hx hR => ?_⟩` and prove the remaining obligations. Simplify using `only [max_le_iff] at hx`. Take `⟨hxa, hxc, hxg⟩` from `hx`. Take `⟨-, hm, -, -, -, -, hL, -, -, -, -, -, -, -, -, hm1, -⟩` from `hx1 s R he hxa hR`.

Take `⟨-, -, ⟨hk, -⟩, -⟩` from `hR`. Establish `hx1'` using `s.one_lt_alt`. Establish `hxp : 0 < s.x` using `by linarith`. Establish `e0` using `s.eps_pos`. Establish `e1` using `s.eps_lt`.

Establish `root : ∀ y : ℝ, 0 ≤ y → y ^ 4 ≤ s.x → y ≤ s.x ^ ((1 : ℝ) / 4)` using `fun y hy h => by`. Use `Real.rpow_le_rpow (by positivity) h (show (0 : ℝ) ≤ 1 / 4 by norm_num)` as an intermediate fact. Rewrite `this` using `[← Real.rpow_natCast, ← Real.rpow_mul hy, show ((4 : ℕ) : ℝ) * (1 / 4) = 1 by norm_num, Real.rpow_one]`. Then use the resulting hypothesis. Establish `m0 : (0 : ℝ) ≤ R.m` using `by positivity`. Establish `m4 : (R.m : ℝ) ^ 4 ≤ s.x ^ 4` using `pow_le_pow_left₀ m0 hm 4`.

Establish `m2 : (R.m : ℝ) ^ 2 ≤ s.x ^ 2` using `pow_le_pow_left₀ m0 hm 2`. Use `⟨(root _ (by positivity) hxc).trans ((Real.rpow_le_rpow_of_exponent_le hx1'.le (by linarith)).trans hm1), ?_, ?_, hL⟩` and prove the remaining obligations. Use `m2.trans (le_trans ?_ hk)` and prove the remaining obligations. Rewrite using `[← Real.rpow_two]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hx1'.le (by linarith)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.rpow_add hxp, ← Real.rpow_natCast]`. Evaluate the numerical expressions. Use `_ ≤ s.x ^ (9 / 2 + 10 * s.eps) := Real.rpow_le_rpow_of_exponent_le hx1'.le (by linarith)`. Use `_ ≤ R.k := hk`.
-/
theorem rank_consts (eps c g : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) :
    ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R →
      2 * |c| ≤ R.m ∧ (R.m : ℝ) ^ 2 ≤ R.k ∧ 2 * g * (R.m : ℝ) ^ 4 ≤ R.k ∧ 1 ≤ s.L := by
  obtain ⟨x1, hx1⟩ := rank_basic_bounds eps h0 h1
  refine ⟨max x1 (max ((2 * |c|) ^ 4) ((2 * |g|) ^ 4)), fun s R he hx hR => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨hxa, hxc, hxg⟩ := hx
  obtain ⟨-, hm, -, -, -, -, hL, -, -, -, -, -, -, -, -, hm1, -⟩ := hx1 s R he hxa hR
  obtain ⟨-, -, ⟨hk, -⟩, -⟩ := hR
  have hx1' := s.one_lt_alt
  have hxp : 0 < s.x := by linarith
  have e0 := s.eps_pos
  have e1 := s.eps_lt
  have root : ∀ y : ℝ, 0 ≤ y → y ^ 4 ≤ s.x → y ≤ s.x ^ ((1 : ℝ) / 4) := fun y hy h => by
    have := Real.rpow_le_rpow (by positivity) h (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hy, show ((4 : ℕ) : ℝ) * (1 / 4) = 1 by norm_num,
      Real.rpow_one] at this
  have m0 : (0 : ℝ) ≤ R.m := by positivity
  have m4 : (R.m : ℝ) ^ 4 ≤ s.x ^ 4 := pow_le_pow_left₀ m0 hm 4
  have m2 : (R.m : ℝ) ^ 2 ≤ s.x ^ 2 := pow_le_pow_left₀ m0 hm 2
  refine ⟨(root _ (by positivity) hxc).trans
    ((Real.rpow_le_rpow_of_exponent_le hx1'.le (by linarith)).trans hm1), ?_, ?_, hL⟩
  · refine m2.trans (le_trans ?_ hk)
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hx1'.le (by linarith)
  · calc 2 * g * (R.m : ℝ) ^ 4 ≤ 2 * |g| * (R.m : ℝ) ^ 4 := by gcongr; exact le_abs_self g
      _ ≤ s.x ^ ((1 : ℝ) / 4) * s.x ^ 4 :=
          mul_le_mul (root _ (by positivity) hxg) m4 (by positivity) (by positivity)
      _ = s.x ^ ((1 : ℝ) / 4 + 4) := by
          rw [Real.rpow_add hxp, ← Real.rpow_natCast]; norm_num
      _ ≤ s.x ^ (9 / 2 + 10 * s.eps) := Real.rpow_le_rpow_of_exponent_le hx1'.le (by linarith)
      _ ≤ R.k := hk

/- English proof (translation)
Introduce `h2b eps C h0 h1 hC cD hcD`. Use `⟨0, fun ch hch => ?_⟩` and prove the remaining obligations. Take `⟨C1, hC1⟩` from `Formalism.LogVandermondeBounds.vandermonde_place_lower_bound eps 5 h0 h1 (by norm_num)`. Take `⟨x1, hx1⟩` from `places_ok eps C cD ch h0 h1 hC hcD hch`. Take `⟨x2, hx2⟩` from `scale_sizes eps cD ch h0 h1 hcD hch`.

Take `⟨x3, hx3⟩` from `rank_consts eps C1 C.CGam h0 h1`. Take `⟨x4, hx4⟩` from `hostBounds eps C.P.Cpde h0 h1 hC.2.2.2.2.2.2.2.2.2.2.2.2.1`. Use `⟨max (max x1 x2) (max x3 x4), fun s P q1 a b c du Ds he hx h hdu hDs u => ?_⟩` and prove the remaining obligations. Simplify using `only [max_le_iff] at hx`. Take `⟨⟨a1, a2⟩, a3, a4⟩` from `hx`.

Establish `hpl` using `hx1 s P q1 a b c he a1 h u`. Take `⟨-, -, -, -, -, -, -, hk5⟩` from `hx2 s P.R he a2 h.rank`. Take `⟨r1, r2, r3, hL⟩` from `hx3 s P.R he a3 h.rank`. Take `⟨-, -, -, -, -, rd1, -, rd2, -⟩` from `hx4 s P.R P.H he a4 h.rank h.val`. Substitute `he` using the available equality.

Set `_` to `P.H.cmStar`. Establish `hcm` using `host_cm P.H`. Establish `hk` using `P.R.m_add_three_le_k`. Establish `hm` using `P.R.two_le_m`. Establish `hxp : 0 < s.x` using `by linarith [s.one_lt_alt]`.

Establish `hk1 : (1 : ℝ) ≤ P.R.k` using `by exact_mod_cast (by omega : 1 ≤ P.R.k)`. Establish `hf1 : (1 : ℝ) ≤ P.R.f` using `by exact_mod_cast f_pos P.R`. Establish `hm0 : (0 : ℝ) ≤ P.R.m` using `by positivity`. Establish `hv` using `pi_le_v P.H`. Establish `hv0 : 0 < P.H.v` using `lt_of_lt_of_le Real.pi_pos hv`.

Establish `hlv : Real.log P.H.v ≤ s.L` using `(Real.log_le_log hv0 (by unfold Host.v; linarith)).trans rd2`. Establish `hD : (1 : ℝ) ≤ (Delv s cD : ℝ)`. Establish `: 0 < ⌈s.x ^ cD⌉₊` using `Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hxp _)`. Conclude with `this` after adjusting the coercions. Establish `hbp : 0 < s.b` using `Real.exp_pos _`.

Establish `hgb : ∀ i, s.b ^ 8 ≤ (P.H.g i : ℝ)` using `fun i => (pow_le_pow_left₀ hbp.le (le_mul_of_one_le_left hbp.le hk1) 8).trans (h.val.2.2.2.2.1 i).1`. Establish `hlg : ∀ i, 8 * s.L ≤ Real.log (P.H.g i)` using `fun i => by`. Use `Real.log_le_log (by positivity) (hgb i)` as an intermediate fact. Rewrite `this` using `[Real.log_pow]`. Unfold `Scale.b at this`.

Rewrite `this` using `[Real.log_exp]`. Conclude with `this` after adjusting the coercions. Establish `hg3 : ∀ i, 3 ≤ P.H.g i` using `fun i => by`. Establish `h2 : 2 ≤ s.b` using `by have := Real.add_one_le_exp s.L; unfold Scale.b; linarith`. Establish `h3 : (2 : ℝ) ^ 8 ≤ s.b ^ 8` using `pow_le_pow_left₀ (by norm_num) h2 8`.

Establish `: (3 : ℝ) ≤ P.H.g i` using `by linarith [hgb i]`. Conclude with `this` after adjusting the coercions. Establish `hg1 : ∀ i, (1 : ℝ) ≤ (P.H.g i : ℝ)` using `fun i => by exact_mod_cast (P.H.g_prime i).one_lt.le`. Take `⟨i1, i2, i3⟩` from `idx_ratio P.R P.H.g P.H.g_prime hg3`. Establish `hDpos : 0 < Ds`.

Use `lt_of_lt_of_le ?_ hDs` and prove the remaining obligations. Use `mass_pos P.H.E hcm P.R.r` as an intermediate fact. Conclude with `mul_pos (by positivity) (Finset.prod_pos fun τ _ => dimV_row_pos _)`. Establish `hmass` using `mass_tel h2b P.H.E hcm P.R.k (by omega) (P.R.m - 1)`. Establish `e1 : P.R.k + (P.R.m - 1) = P.R.r` using `by unfold Ranks.r; omega`.

Establish `e2 : P.R.r + 1 = P.R.k - 1 + P.R.m + 1` using `by unfold Ranks.r; omega`. Rewrite `hmass` using `[e1, e2]`. Unfold `Formalism.HermitianLatticesTheory.massRatioRightSide at hmass`. Rewrite `hmass` using `[vInv_E, fDeg_E]`. Establish `key` using `hC1 s.x s.one_lt_alt.le P.R.f P.R.m P.R.k P.H.v (Delv s cD) (P.H.g 0 : ℝ) (P.H.g 1 : ℝ) (fun n => seqOf (P.hcW u (placeNo P.H n)).u) (fun n => seqOf (P.hcW u (placeNo P.H n)).v) (fun n => seqOf (P.hcW u (placeNo P.H n)).b) (fun n => seqOf (P.hcW u (placeNo P.H n)).e) Ds (du u) _ …`.

Establish `hM2 : 2 ≤ M` using `by have := (Finset.mem_Ico.1 hM).1; omega`. Use `⟨(Formalism.HermitianLattices.GlobalBoundRefinements.log_l_value_field_bound P.H.E hcm M hM2).2.1, ?_⟩` and prove the remaining obligations. Use `cmField_unramified_massIdentity P.H.E hcm M hM2` as an intermediate fact. Rewrite using `[fDeg_E] at this)` and apply the resulting hypothesis. Use `hmass i3`.

Use the proof step `(by`. Rewrite `hDs` using `[prod_places P.H]`. Simplify using `only [dimV_row] at hDs`. Simplify using `only [P.hcW_v u, P.hcW_b u]`. Conclude with `hDs)`.

Use the proof step `(by`. Use `hdu u` as an intermediate fact. Rewrite `this` using `[prod_places P.H]`. Simplify using `only [dimV_col] at this`. Conclude with `this)`.

Establish `hsum : 0 ≤ ∑ j ∈ range P.R.m, (1 / (P.R.f : ℝ)) * ∑ ρ ∈ range P.R.f, Real.log (seqOf (P.hcW u (placeNo P.H ρ)).e j * P.H.v / Real.pi)`. Use `Finset.sum_nonneg fun j hj => mul_nonneg (by positivity) (Finset.sum_nonneg fun ρ _ => Real.log_nonneg ?_)` and prove the remaining obligations. Rewrite using `[one_le_div Real.pi_pos]`. Conclude with `hv.trans (le_mul_of_one_le_left hv0.le ((hpl _).2 j (Finset.mem_range.1 hj)))`. Establish `hq : (P.R.m : ℝ) ^ 2 * s.L / P.R.k ≤ s.L`.

Rewrite using `[div_le_iff₀ (by linarith)]; nlinarith`. Establish `hq0 : 0 ≤ (P.R.m : ℝ) ^ 2 * s.L / P.R.k` using `by positivity`. Establish `hC2 : C1 * (s.L + (P.R.m : ℝ) ^ 2 * s.L / P.R.k) ≤ P.R.m * s.L`. Combine the equalities or inequalities in the displayed calculation. Establish `hg : (P.R.m : ℝ) * (16 * s.L) ≤ P.R.m * (Real.log (P.H.g 0) + Real.log (P.H.g 1))` using `mul_le_mul_of_nonneg_left (by linarith [hlg 0, hlg 1]) hm0`.

Establish `hmain : 15 * (P.R.m * s.L) ≤ 1 / ((P.R.f : ℝ) * P.R.k) * Real.log (Ds / du u)`. Establish `key' : _ + _ - C1 * (s.L + (P.R.m : ℝ) ^ 2 * s.L / P.R.k) ≤ _` using `key`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmL : 0 < (P.R.m : ℝ) * s.L`. Establish `: (2 : ℝ) ≤ P.R.m` using `by exact_mod_cast hm`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hdu0 : (0 : ℝ) < du u`. Break down `(Nat.cast_nonneg (α := ℝ) (du u)).lt_or_eq with h' | h'` into its components or cases. Conclude with `h'`. Rewrite `hmain` using `[← h']`.

Simplify using `only [div_zero, Real.log_zero, mul_zero] at hmain`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hG : 0 < GamS C s P.R` using `Real.exp_pos _`. Rewrite using `[Real.log_mul (Real.rpow_pos_of_pos (div_pos hDpos hdu0) _).ne' (Real.rpow_pos_of_pos hG _).ne', Real.log_rpow (div_pos hDpos hdu0), Real.log_rpow hG]`. Unfold `GamS`.

Rewrite using `[Real.log_exp]`. Establish `e3 : -(2 : ℝ) / (P.R.f * P.R.k) * (C.CGam * (P.R.m : ℝ) ^ 5 * P.R.f * s.L) = -((2 * C.CGam * (P.R.m : ℝ) ^ 4 / P.R.k) * (P.R.m * s.L))`. Clear the denominators using the available nonvanishing facts. Establish `e4 : 2 * C.CGam * (P.R.m : ℝ) ^ 4 / P.R.k ≤ 1` using `(div_le_one (by linarith)).2 r3`. Establish `e5` using `mul_le_mul_of_nonneg_right e4 hmL.le`.

Rewrite using `[e3]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem window_lower : Formalism.MainNotions.StandardLattice.SiegelMassRatioCM → ∀ (eps : ℝ) (C : FC), 0 < eps → eps < 1 / 52 → Std C → ∀ cD : ℝ, 0 ≤ cD → ∃ c2 : ℝ, ∀ ch ≥ c2, ∃ x0 : ℝ, ∀ (s : Scale) (P : PreCh) (q1 : ℕ) (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool) (du : P.Word → ℕ) (Ds : ℝ), s.eps = eps → x0 ≤ s.x → ChOK s C cD ch P q1 a b c → (∀ u, (du u : ℝ) = (letI := P.H.cmStar; Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm P.H.E P.R.k) (Formalism.MainNotions.StandardLattice.stdLat P.H.E P.R.k)) * (Formalism.MainNotions.StandardLattice.idxColLoc (P.H.g 0) P.R.k ^ P.R.f * Formalism.MainNotions.StandardLattice.idxColLoc (P.H.g 1) P.R.k ^ P.R.f) * ∏ τ : Tau P.R, Formalism.MainNotions.StandardLattice.dimV (fun i : Fin P.R.k => (((P.hcW u τ).u i : ℚ) : ℝ))) → (2 / 3 : ℝ) ^ P.R.f * (letI := P.H.cmStar; Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm P.H.E P.R.r) (Formalism.MainNotions.StandardLattice.stdLat P.H.E P.R.r)) * (Formalism.MainNotions.StandardLattice.idxRowLoc (P.H.g 0) P.R.k P.R.m ^ P.R.f * Formalism.MainNotions.StandardLattice.idxRowLoc (P.H.g 1) P.R.k P.R.m ^ P.R.f) * ∏ τ : Tau P.R, Formalism.MainNotions.StandardLattice.dimV (Fin.append (fun i => (((P.hcW P.u₀ τ).v i : ℚ) : ℝ)) (fun j => -(((P.hcW P.u₀ τ).b j : ℚ) : ℝ))) ≤ Ds → ∀ u, (P.R.m : ℝ) * s.L ≤ Real.log ((Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * GamS C s P.R ^ (-(2 : ℝ) / (P.R.f * P.R.k))) := by
  intro h2b eps C h0 h1 hC cD hcD
  refine ⟨0, fun ch hch => ?_⟩
  obtain ⟨C1, hC1⟩ := Formalism.LogVandermondeBounds.vandermonde_place_lower_bound eps 5 h0 h1 (by norm_num)
  obtain ⟨x1, hx1⟩ := places_ok eps C cD ch h0 h1 hC hcD hch
  obtain ⟨x2, hx2⟩ := scale_sizes eps cD ch h0 h1 hcD hch
  obtain ⟨x3, hx3⟩ := rank_consts eps C1 C.CGam h0 h1
  obtain ⟨x4, hx4⟩ := hostBounds eps C.P.Cpde h0 h1 hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨max (max x1 x2) (max x3 x4), fun s P q1 a b c du Ds he hx h hdu hDs u => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hx
  have hpl := hx1 s P q1 a b c he a1 h u
  obtain ⟨-, -, -, -, -, -, -, hk5⟩ := hx2 s P.R he a2 h.rank
  obtain ⟨r1, r2, r3, hL⟩ := hx3 s P.R he a3 h.rank
  obtain ⟨-, -, -, -, -, rd1, -, rd2, -⟩ := hx4 s P.R P.H he a4 h.rank h.val
  subst he
  let _ := P.H.cmStar
  have hcm := host_cm P.H
  have hk := P.R.m_add_three_le_k
  have hm := P.R.two_le_m
  have hxp : 0 < s.x := by linarith [s.one_lt_alt]
  have hk1 : (1 : ℝ) ≤ P.R.k := by exact_mod_cast (by omega : 1 ≤ P.R.k)
  have hf1 : (1 : ℝ) ≤ P.R.f := by exact_mod_cast f_pos P.R
  have hm0 : (0 : ℝ) ≤ P.R.m := by positivity
  have hv := pi_le_v P.H
  have hv0 : 0 < P.H.v := lt_of_lt_of_le Real.pi_pos hv
  have hlv : Real.log P.H.v ≤ s.L :=
    (Real.log_le_log hv0 (by unfold Host.v; linarith)).trans rd2
  have hD : (1 : ℝ) ≤ (Delv s cD : ℝ) := by
    have : 0 < ⌈s.x ^ cD⌉₊ := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hxp _)
    exact_mod_cast this
  have hbp : 0 < s.b := Real.exp_pos _
  have hgb : ∀ i, s.b ^ 8 ≤ (P.H.g i : ℝ) := fun i =>
    (pow_le_pow_left₀ hbp.le (le_mul_of_one_le_left hbp.le hk1) 8).trans (h.val.2.2.2.2.1 i).1
  have hlg : ∀ i, 8 * s.L ≤ Real.log (P.H.g i) := fun i => by
    have := Real.log_le_log (by positivity) (hgb i)
    rw [Real.log_pow] at this
    unfold Scale.b at this
    rw [Real.log_exp] at this
    exact_mod_cast this
  have hg3 : ∀ i, 3 ≤ P.H.g i := fun i => by
    have h2 : 2 ≤ s.b := by have := Real.add_one_le_exp s.L; unfold Scale.b; linarith
    have h3 : (2 : ℝ) ^ 8 ≤ s.b ^ 8 := pow_le_pow_left₀ (by norm_num) h2 8
    have : (3 : ℝ) ≤ P.H.g i := by linarith [hgb i]
    exact_mod_cast this
  have hg1 : ∀ i, (1 : ℝ) ≤ (P.H.g i : ℝ) := fun i => by exact_mod_cast (P.H.g_prime i).one_lt.le
  obtain ⟨i1, i2, i3⟩ := idx_ratio P.R P.H.g P.H.g_prime hg3
  have hDpos : 0 < Ds := by
    refine lt_of_lt_of_le ?_ hDs
    have := mass_pos P.H.E hcm P.R.r
    exact mul_pos (by positivity) (Finset.prod_pos fun τ _ => dimV_row_pos _)
  have hmass := mass_tel h2b P.H.E hcm P.R.k (by omega) (P.R.m - 1)
  have e1 : P.R.k + (P.R.m - 1) = P.R.r := by unfold Ranks.r; omega
  have e2 : P.R.r + 1 = P.R.k - 1 + P.R.m + 1 := by unfold Ranks.r; omega
  rw [e1, e2] at hmass
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide at hmass
  rw [vInv_E, fDeg_E] at hmass
  have key := hC1 s.x s.one_lt_alt.le P.R.f P.R.m P.R.k P.H.v (Delv s cD) (P.H.g 0 : ℝ) (P.H.g 1 : ℝ)
    (fun n => seqOf (P.hcW u (placeNo P.H n)).u) (fun n => seqOf (P.hcW u (placeNo P.H n)).v)
    (fun n => seqOf (P.hcW u (placeNo P.H n)).b) (fun n => seqOf (P.hcW u (placeNo P.H n)).e)
    Ds (du u) _ _ _ _ (fun M => Formalism.HermitianLatticesTheory.lValEta P.H.E M)
    (f_pos P.R) (by omega) (by omega) hk5 hv hlv hD (hg1 0) (hg1 1) (fun n _ => (hpl _).1)
    (mass_pos P.H.E hcm P.R.k) (mass_pos P.H.E hcm P.R.r) i2 i1
    (fun M hM => by
      have hM2 : 2 ≤ M := by have := (Finset.mem_Ico.1 hM).1; omega
      refine ⟨(Formalism.HermitianLattices.GlobalBoundRefinements.log_l_value_field_bound P.H.E hcm M hM2).2.1, ?_⟩
      have := cmField_unramified_massIdentity P.H.E hcm M hM2
      rwa [fDeg_E] at this)
    hmass i3
    (by
      rw [prod_places P.H] at hDs
      simp only [dimV_row] at hDs
      simp only [P.hcW_v u, P.hcW_b u]
      exact hDs)
    (by
      have := hdu u
      rw [prod_places P.H] at this
      simp only [dimV_col] at this
      exact this)
  have hsum : 0 ≤ ∑ j ∈ range P.R.m, (1 / (P.R.f : ℝ)) *
      ∑ ρ ∈ range P.R.f, Real.log (seqOf (P.hcW u (placeNo P.H ρ)).e j * P.H.v / Real.pi) := by
    refine Finset.sum_nonneg fun j hj => mul_nonneg (by positivity) (Finset.sum_nonneg fun ρ _ => Real.log_nonneg ?_)
    rw [one_le_div Real.pi_pos]
    exact hv.trans (le_mul_of_one_le_left hv0.le ((hpl _).2 j (Finset.mem_range.1 hj)))
  have hq : (P.R.m : ℝ) ^ 2 * s.L / P.R.k ≤ s.L := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hq0 : 0 ≤ (P.R.m : ℝ) ^ 2 * s.L / P.R.k := by positivity
  have hC2 : C1 * (s.L + (P.R.m : ℝ) ^ 2 * s.L / P.R.k) ≤ P.R.m * s.L :=
    calc _ ≤ |C1| * (s.L + (P.R.m : ℝ) ^ 2 * s.L / P.R.k) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ |C1| * (2 * s.L) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = 2 * |C1| * s.L := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right r1 (by linarith)
  have hg : (P.R.m : ℝ) * (16 * s.L) ≤ P.R.m * (Real.log (P.H.g 0) + Real.log (P.H.g 1)) :=
    mul_le_mul_of_nonneg_left (by linarith [hlg 0, hlg 1]) hm0
  have hmain : 15 * (P.R.m * s.L) ≤ 1 / ((P.R.f : ℝ) * P.R.k) * Real.log (Ds / du u) := by
    have key' : _ + _ - C1 * (s.L + (P.R.m : ℝ) ^ 2 * s.L / P.R.k) ≤ _ := key
    linarith
  have hmL : 0 < (P.R.m : ℝ) * s.L := by
    have : (2 : ℝ) ≤ P.R.m := by exact_mod_cast hm
    nlinarith
  have hdu0 : (0 : ℝ) < du u := by
    rcases (Nat.cast_nonneg (α := ℝ) (du u)).lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at hmain
      simp only [div_zero, Real.log_zero, mul_zero] at hmain
      linarith
  have hG : 0 < GamS C s P.R := Real.exp_pos _
  rw [Real.log_mul (Real.rpow_pos_of_pos (div_pos hDpos hdu0) _).ne' (Real.rpow_pos_of_pos hG _).ne',
    Real.log_rpow (div_pos hDpos hdu0), Real.log_rpow hG]
  unfold GamS
  rw [Real.log_exp]
  have e3 : -(2 : ℝ) / (P.R.f * P.R.k) * (C.CGam * (P.R.m : ℝ) ^ 5 * P.R.f * s.L) =
      -((2 * C.CGam * (P.R.m : ℝ) ^ 4 / P.R.k) * (P.R.m * s.L)) := by
    field_simp
  have e4 : 2 * C.CGam * (P.R.m : ℝ) ^ 4 / P.R.k ≤ 1 := (div_le_one (by linarith)).2 r3
  have e5 := mul_le_mul_of_nonneg_right e4 hmL.le
  rw [e3]
  linarith

end GlobalTheory.EX.WinLow

end
