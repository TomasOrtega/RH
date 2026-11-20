import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumFrameIdem

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

variable {r : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨ht.1, fun i j h => (mul_le_mul_of_nonneg_right hcc (ht.1 j).le).trans (ht.2.1 i j h), fun i h => hcc.trans (ht.2.2 i h)⟩`.
-/
theorem cone_anti {c c' : ℝ} (hcc : c' ≤ c) {t : Fin r → ℝ} (ht : t ∈ cone r c) : t ∈ cone r c' :=
  ⟨ht.1, fun i j h => (mul_le_mul_of_nonneg_right hcc (ht.1 j).le).trans (ht.2.1 i j h),
    fun i h => hcc.trans (ht.2.2 i h)⟩

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero`. Introduce `a b h`. Establish `e : b = a` using `Fin.ext (by simpa using h)`. Substitute `e` using the available equality.

Simplify using the standard rewrite rules. Consider the case `succ d ih`. Introduce `a b h`. Establish `hm : a.val + d < r`. Use `b.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `h1` using `ih a ⟨a.val + d, hm⟩ rfl`. Establish `h2` using `ht.2.1 ⟨a.val + d, hm⟩ b (by simp only []; omega)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cone_step {c : ℝ} (hc0 : 0 < c) {t : Fin r → ℝ} (ht : t ∈ cone r c) (d : ℕ) :
    ∀ a b : Fin r, b.val = a.val + d → c ^ d * t b ≤ t a := by
  induction d with
  | zero =>
    intro a b h
    have e : b = a := Fin.ext (by simpa using h)
    subst e
    simp
  | succ d ih =>
    intro a b h
    have hm : a.val + d < r := by
      have := b.2
      omega
    have h1 := ih a ⟨a.val + d, hm⟩ rfl
    have h2 := ht.2.1 ⟨a.val + d, hm⟩ b (by simp only []; omega)
    calc c ^ (d + 1) * t b = c ^ d * (c * t b) := by ring
      _ ≤ c ^ d * t ⟨a.val + d, hm⟩ := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ t a := h1

/- English proof (translation)
Establish `hab' : a.val ≤ b.val` using `hab`. Establish `h1` using `cone_step hc0 ht (b.val - a.val) a b (by omega)`. Establish `hle : c ^ r ≤ c ^ (b.val - a.val)` using `pow_le_pow_of_le_one hc0.le hc1 (by have := b.2; omega)`. Conclude with `(mul_le_mul_of_nonneg_right hle (ht.1 b).le).trans h1`.
-/
theorem cone_pow_mul_le {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {t : Fin r → ℝ} (ht : t ∈ cone r c)
    {a b : Fin r} (hab : a ≤ b) : c ^ r * t b ≤ t a := by
  have hab' : a.val ≤ b.val := hab
  have h1 := cone_step hc0 ht (b.val - a.val) a b (by omega)
  have hle : c ^ r ≤ c ^ (b.val - a.val) :=
    pow_le_pow_of_le_one hc0.le hc1 (by have := b.2; omega)
  exact (mul_le_mul_of_nonneg_right hle (ht.1 b).le).trans h1

/- English proof (translation)
Establish `hi` using `i.2`. Establish `hl : r - 1 < r` using `by omega`. Establish `h1` using `cone_step hc0 ht (r - 1 - i.val) i ⟨r - 1, hl⟩ (by simp only []; omega)`. Establish `h2` using `ht.2.2 ⟨r - 1, hl⟩ (by simp only []; omega)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cone_pow_le {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {t : Fin r → ℝ} (ht : t ∈ cone r c)
    (i : Fin r) : c ^ r ≤ t i := by
  have hi := i.2
  have hl : r - 1 < r := by omega
  have h1 := cone_step hc0 ht (r - 1 - i.val) i ⟨r - 1, hl⟩ (by simp only []; omega)
  have h2 := ht.2.2 ⟨r - 1, hl⟩ (by simp only []; omega)
  calc c ^ r ≤ c ^ (r - 1 - i.val + 1) := pow_le_pow_of_le_one hc0.le hc1 (by omega)
    _ = c ^ (r - 1 - i.val) * c := pow_succ _ _
    _ ≤ c ^ (r - 1 - i.val) * t ⟨r - 1, hl⟩ := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ t i := h1

/- English proof (translation)
Establish `hA0 : 0 < A` using `he0.trans_le heA`. Establish `hT0 : 0 < T` using `he0.trans_le heT`. Establish `hee : e * e ^ 2 ≤ e ^ 2`. Establish `: 0 ≤ e ^ 2` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Break down `h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩` into its components or cases. Establish `h3 : e * (e * A) ≤ wa`. Establish `: 0 ≤ e * A` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Establish `h3 : e * e ^ 2 ≤ T * wa`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem weights_across_levels {e A T wa wb : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) (heA : e ≤ A) (heT : e ≤ T)
    (h : (e * A ≤ wa ∧ wb * e ^ 2 ≤ T) ∨ (e ^ 2 ≤ wa * T ∧ e * A * wb ≤ 1) ∨ (e * A ≤ wa ∧ e * A * wb ≤ 1)) :
    wb * (e ^ 4 * A) ≤ T * wa := by
  have hA0 : 0 < A := he0.trans_le heA
  have hT0 : 0 < T := he0.trans_le heT
  have hee : e * e ^ 2 ≤ e ^ 2 := by
    have : 0 ≤ e ^ 2 := by positivity
    nlinarith
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h3 : e * (e * A) ≤ wa := by
      have : 0 ≤ e * A := by positivity
      nlinarith
    calc wb * (e ^ 4 * A) = (wb * e ^ 2) * (e * (e * A)) := by ring
      _ ≤ T * wa := mul_le_mul h2 h3 (by positivity) hT0.le
  · calc wb * (e ^ 4 * A) = (e * A * wb) * (e * e ^ 2) := by ring
      _ ≤ 1 * e ^ 2 := mul_le_mul h2 hee (by positivity) zero_le_one
      _ = e ^ 2 := one_mul _
      _ ≤ wa * T := h1
      _ = T * wa := mul_comm _ _
  · have h3 : e * e ^ 2 ≤ T * wa := by
      calc e * e ^ 2 = e * (e * e) := by ring
        _ ≤ T * (e * A) := mul_le_mul heT (mul_le_mul_of_nonneg_left heA he0.le) (by positivity) hT0.le
        _ ≤ T * wa := mul_le_mul_of_nonneg_left h1 hT0.le
    calc wb * (e ^ 4 * A) = (e * A * wb) * (e * e ^ 2) := by ring
      _ ≤ 1 * (e * e ^ 2) := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = e * e ^ 2 := one_mul _
      _ ≤ T * wa := h3

/- English proof (translation)
Introduce `r c hc`. Establish `hc0 : 0 < min c 1` using `lt_min hc one_pos`. Establish `hc1 : min c 1 ≤ 1` using `min_le_right _ _`. Use `set c' := min c 1 with hc'`. Use `set e := c' ^ r with he`.

Establish `he0 : 0 < e` using `by positivity`. Establish `he1 : e ≤ 1` using `pow_le_one₀ hc0.le hc1`. Use `⟨(e ^ 4)⁻¹, by positivity, fun s t ht0 α β hlev => ?_⟩` and prove the remaining obligations. Establish `ht : t ∈ cone r c'` using `cone_anti (min_le_left _ _) ht0`. Establish `hpos` using `ht.1`.

Establish `hge : ∀ i, e ≤ t i` using `cone_pow_le hc0 hc1 ht`. Establish `hle : ∀ {a b : Fin r}, a ≤ b → e * t b ≤ t a` using `fun h => cone_pow_mul_le hc0 hc1 ht h`. Establish `hsq : e ^ 2 ≤ e` using `by nlinarith`. Choose the witnesses or unpack the hypotheses as in `⟨T, heT, hrat, hTb⟩ : ∃ T, e ≤ T ∧ ratio t s = t s / T ∧ ∀ b : Fin r, s < b → e * t b ≤ T := by`. Distinguish the cases in `h : s.val + 1 < r`.

Use `⟨t ⟨s.val + 1, h⟩, hge _, by simp [ratio, h], fun b hb => hle ?_⟩` and prove the remaining obligations. Establish `hb' : s.val < b.val` using `hb`. Conclude with `Fin.le_def.2 (by simp only []; omega)`. Use `⟨1, he1, by simp [ratio, h], fun b hb => ?_⟩` and prove the remaining obligations. Establish `hb' : s.val < b.val` using `hb`.

Use `b.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hT0 : 0 < T` using `he0.trans_le heT`. Establish `lev2 : ∀ γ, frameLev s γ = 2 → e * t s ≤ frameWt t γ`. Introduce `γ h`.

Break down `γ with _ | a | a` into its components or cases. Simplify using `[frameLev] at h`. Establish `ha : a ≤ s`. Assume the negation of the conclusion as `hn`. Simplify using `[frameLev, hn] at h`.

Simplify `hle ha` using `[frameWt]`. It suffices to derive a contradiction. Simplify using `only [frameLev] at h`. Apply the tactic sequence `split_ifs at h <;> omega`. Establish `lev0 : ∀ γ, frameLev s γ = 0 → e * t s * frameWt t γ ≤ 1`.

Introduce `γ h`. Break down `γ with _ | a | a` into its components or cases. Simplify using `[frameLev] at h`. It suffices to derive a contradiction. Simplify using `only [frameLev] at h`.

Apply the tactic sequence `split_ifs at h <;> omega`. Establish `ha : a ≤ s`. Assume the negation of the conclusion as `hn`. Simplify using `[frameLev, hn] at h`. Simplify using `only [frameWt]`.

Rewrite using `[← div_eq_mul_inv]`. Conclude with `(div_le_one (hpos a)).2 (hle ha)`. Establish `lev1 : ∀ γ, frameLev s γ = 1 → e ^ 2 ≤ frameWt t γ * T ∧ frameWt t γ * e ^ 2 ≤ T`. Introduce `γ h`. Establish `key : ∀ b : Fin r, s < b → e ^ 2 ≤ t b * T ∧ t b * e ^ 2 ≤ T` using `fun b hb => by`.

Establish `h1` using `hTb b hb`. Establish `h2` using `hge b`. Prove the components needed by the constructor for the conclusion. Rewrite using `[sq]`. Conclude with `mul_le_mul h2 heT he0.le (hpos b).le`.

Establish `: 0 ≤ e * t b` using `(mul_pos he0 (hpos b)).le`. Use the polynomial consequences of the given equalities and inequalities. Break down `γ with _ | a | a` into its components or cases. Simplify using `only [frameWt, one_mul]`. Conclude with `⟨hsq.trans heT, hsq.trans heT⟩`.

Establish `ha : s < a`. Assume the negation of the conclusion as `hn`. Simplify using `[frameLev, not_lt.1 hn] at h`. Simplify `key a ha` using `[frameWt]`. Establish `ha : s < a`.

Assume the negation of the conclusion as `hn`. Simplify using `[frameLev, not_lt.1 hn] at h`. Establish `h1` using `hTb a ha`. Establish `h2` using `hge a`. Simplify using `only [frameWt]`.

Rewrite using `[inv_mul_eq_div, inv_mul_eq_div, le_div_iff₀ (hpos a), div_le_iff₀ (hpos a)]`. Prove the components needed by the constructor for the conclusion. Establish `: 0 ≤ e * t a` using `(mul_pos he0 (hpos a)).le`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[sq]`.

Conclude with `mul_le_mul heT h2 he0.le hT0.le |>.trans_eq' (by ring) |>.trans_eq (by ring)`. Establish `lvl : ∀ γ, frameLev s γ = 0 ∨ frameLev s γ = 1 ∨ frameLev s γ = 2`. Introduce `γ`. Apply the tactic sequence `rcases γ with _ | a | a <;> simp only [frameLev] <;> (try split_ifs) <;> simp`. Establish `hcases : (e * t s ≤ frameWt t α ∧ frameWt t β * e ^ 2 ≤ T) ∨ (e ^ 2 ≤ frameWt t α * T ∧ e * t s * frameWt t β ≤ 1) ∨ (e * t s ≤ frameWt t α ∧ e * t s * frameWt t β ≤ 1)`.

Apply the tactic sequence `rcases lvl α with a | a | a <;> rcases lvl β with b | b | b <;> rw [a, b] at hlev <;> first`. Consider the case `exact Or.inl ⟨lev2 α a, (lev1 β b).2⟩`. Consider the case `exact Or.inr (Or.inl ⟨(lev1 α a).1, lev0 β b⟩)`. Consider the case `exact Or.inr (Or.inr ⟨lev2 α a, lev0 β b⟩)`. Consider the case `(exfalso; omega)`.

Establish `key` using `weights_across_levels he0 he1 (hge s) heT hcases`. Establish `hwa : 0 < frameWt t α` using `frameWt_pos hpos α`. Establish `hA0 : 0 < t s` using `hpos s`. Establish `hK : (e ^ 4)⁻¹ / ratio t s = T / (e ^ 4 * t s)`. Rewrite using `[hrat]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hK, div_le_div_iff₀ hwa (by positivity)]`. Conclude with `key`.
-/
theorem frameWt_div_le_div_ratio : ∀ (r : ℕ) (c : ℝ), 0 < c → ∃ K : ℝ, 0 ≤ K ∧ ∀ (s : Fin r), ∀ t ∈ cone r c,
    ∀ α β : FrameIx r, frameLev s β < frameLev s α → frameWt t β / frameWt t α ≤ K / ratio t s := by
  intro r c hc
  have hc0 : 0 < min c 1 := lt_min hc one_pos
  have hc1 : min c 1 ≤ 1 := min_le_right _ _
  set c' := min c 1 with hc'
  set e := c' ^ r with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 := pow_le_one₀ hc0.le hc1
  refine ⟨(e ^ 4)⁻¹, by positivity, fun s t ht0 α β hlev => ?_⟩
  have ht : t ∈ cone r c' := cone_anti (min_le_left _ _) ht0
  have hpos := ht.1
  have hge : ∀ i, e ≤ t i := cone_pow_le hc0 hc1 ht
  have hle : ∀ {a b : Fin r}, a ≤ b → e * t b ≤ t a := fun h => cone_pow_mul_le hc0 hc1 ht h
  have hsq : e ^ 2 ≤ e := by nlinarith
  obtain ⟨T, heT, hrat, hTb⟩ : ∃ T, e ≤ T ∧ ratio t s = t s / T ∧ ∀ b : Fin r, s < b → e * t b ≤ T := by
    by_cases h : s.val + 1 < r
    · refine ⟨t ⟨s.val + 1, h⟩, hge _, by simp [ratio, h], fun b hb => hle ?_⟩
      have hb' : s.val < b.val := hb
      exact Fin.le_def.2 (by simp only []; omega)
    · refine ⟨1, he1, by simp [ratio, h], fun b hb => ?_⟩
      have hb' : s.val < b.val := hb
      have := b.2
      omega
  have hT0 : 0 < T := he0.trans_le heT
  have lev2 : ∀ γ, frameLev s γ = 2 → e * t s ≤ frameWt t γ := by
    intro γ h
    rcases γ with _ | a | a
    · simp [frameLev] at h
    · have ha : a ≤ s := by
        by_contra hn
        simp [frameLev, hn] at h
      simpa [frameWt] using hle ha
    · exfalso
      simp only [frameLev] at h
      split_ifs at h <;> omega
  have lev0 : ∀ γ, frameLev s γ = 0 → e * t s * frameWt t γ ≤ 1 := by
    intro γ h
    rcases γ with _ | a | a
    · simp [frameLev] at h
    · exfalso
      simp only [frameLev] at h
      split_ifs at h <;> omega
    · have ha : a ≤ s := by
        by_contra hn
        simp [frameLev, hn] at h
      simp only [frameWt]
      rw [← div_eq_mul_inv]
      exact (div_le_one (hpos a)).2 (hle ha)
  have lev1 : ∀ γ, frameLev s γ = 1 → e ^ 2 ≤ frameWt t γ * T ∧ frameWt t γ * e ^ 2 ≤ T := by
    intro γ h
    have key : ∀ b : Fin r, s < b → e ^ 2 ≤ t b * T ∧ t b * e ^ 2 ≤ T := fun b hb => by
      have h1 := hTb b hb
      have h2 := hge b
      constructor
      · rw [sq]
        exact mul_le_mul h2 heT he0.le (hpos b).le
      · have : 0 ≤ e * t b := (mul_pos he0 (hpos b)).le
        nlinarith
    rcases γ with _ | a | a
    · simp only [frameWt, one_mul]
      exact ⟨hsq.trans heT, hsq.trans heT⟩
    · have ha : s < a := by
        by_contra hn
        simp [frameLev, not_lt.1 hn] at h
      simpa [frameWt] using key a ha
    · have ha : s < a := by
        by_contra hn
        simp [frameLev, not_lt.1 hn] at h
      have h1 := hTb a ha
      have h2 := hge a
      simp only [frameWt]
      rw [inv_mul_eq_div, inv_mul_eq_div, le_div_iff₀ (hpos a), div_le_iff₀ (hpos a)]
      constructor
      · have : 0 ≤ e * t a := (mul_pos he0 (hpos a)).le
        nlinarith
      · rw [sq]
        exact mul_le_mul heT h2 he0.le hT0.le |>.trans_eq' (by ring) |>.trans_eq (by ring)
  have lvl : ∀ γ, frameLev s γ = 0 ∨ frameLev s γ = 1 ∨ frameLev s γ = 2 := by
    intro γ
    rcases γ with _ | a | a <;> simp only [frameLev] <;> (try split_ifs) <;> simp
  have hcases : (e * t s ≤ frameWt t α ∧ frameWt t β * e ^ 2 ≤ T) ∨
      (e ^ 2 ≤ frameWt t α * T ∧ e * t s * frameWt t β ≤ 1) ∨
      (e * t s ≤ frameWt t α ∧ e * t s * frameWt t β ≤ 1) := by
    rcases lvl α with a | a | a <;> rcases lvl β with b | b | b <;> rw [a, b] at hlev <;>
      first
        | exact Or.inl ⟨lev2 α a, (lev1 β b).2⟩
        | exact Or.inr (Or.inl ⟨(lev1 α a).1, lev0 β b⟩)
        | exact Or.inr (Or.inr ⟨lev2 α a, lev0 β b⟩)
        | (exfalso; omega)
  have key := weights_across_levels he0 he1 (hge s) heT hcases
  have hwa : 0 < frameWt t α := frameWt_pos hpos α
  have hA0 : 0 < t s := hpos s
  have hK : (e ^ 4)⁻¹ / ratio t s = T / (e ^ 4 * t s) := by
    rw [hrat]
    field_simp
  rw [hK, div_le_div_iff₀ hwa (by positivity)]
  exact key

end GlobalTheory.CompanionTheory.RapidDecay

end
