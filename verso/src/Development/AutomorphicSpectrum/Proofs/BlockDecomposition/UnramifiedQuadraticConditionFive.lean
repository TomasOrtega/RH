import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.QuadAtOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.HenselRoot
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUTr
import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe

noncomputable section

namespace GlobalTheory.CompanionTheory.GunrInert

open PositivityTheory.PfSWUS.Loc

section Core

variable {K A : Type} [NormedField K] [IsUltrametricDist K] [CommRing A] [Algebra K A]

/- English proof (translation)
Use `hind (X - X') (Y - Y') (by rw [map_sub, map_sub]; linear_combination h)` as an intermediate fact. Conclude with `⟨sub_eq_zero.1 this.1, sub_eq_zero.1 this.2⟩`.
-/
theorem coord_unique {Δ : A}
    (hind : ∀ X Y : K, algebraMap K A X + algebraMap K A Y * Δ = 0 → X = 0 ∧ Y = 0) {X Y X' Y' : K}
    (h : algebraMap K A X + algebraMap K A Y * Δ = algebraMap K A X' + algebraMap K A Y' * Δ) :
    X = X' ∧ Y = Y' := by
  have := hind (X - X') (Y - Y') (by rw [map_sub, map_sub]; linear_combination h)
  exact ⟨sub_eq_zero.1 this.1, sub_eq_zero.1 this.2⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `hF ⟨c, hc⟩`. Use `hF.isDomain` as an intermediate fact. Establish `e : algebraMap K A c * algebraMap K A c = algebraMap K A D` using `by rw [← map_mul, hc]`. Establish `h0 : (Δ - algebraMap K A c) * (Δ + algebraMap K A c) = 0`.

Take the linear combination `hsq - e`. Break down `mul_eq_zero.1 h0 with h | h` into its components or cases. Conclude with `one_ne_zero (hind (-c) 1 (by rw [map_neg, map_one]; linear_combination h)).2`. Conclude with `one_ne_zero (hind c 1 (by rw [map_one]; linear_combination h)).2`. Introduce `hns`.

Use `⟨⟨0, 1, fun h => ?_⟩, mul_comm, fun {a} ha => ?_⟩` and prove the remaining obligations. Conclude with `one_ne_zero (hind 1 0 (by rw [map_one, map_zero, zero_mul, add_zero]; exact h.symm)).1`. Take `⟨X, Y, rfl⟩` from `hsp a`. Establish `hn : X * X - Y * Y * D ≠ 0`. Introduce `hn`.

Distinguish the cases in `hY : Y = 0`. Substitute `hY` using the available equality. Establish `hX : X = 0` using `by simpa using hn`. Substitute `hX` using the available equality. Conclude with `ha (by simp)`.

Conclude with `hns ⟨X / Y, by field_simp; linear_combination hn⟩`. Establish `e : algebraMap K A (X * X - Y * Y * D)⁻¹ * algebraMap K A (X * X - Y * Y * D) = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ hn, map_one]`. Establish `en : algebraMap K A (X * X - Y * Y * D) = algebraMap K A X * algebraMap K A X - algebraMap K A Y * algebraMap K A Y * algebraMap K A D`. Simplify using `only [map_sub, map_mul]`.

Use `⟨algebraMap K A (X * X - Y * Y * D)⁻¹ * (algebraMap K A X - algebraMap K A Y * Δ), ?_⟩` and prove the remaining obligations. Take the linear combination `e - algebraMap K A (X * X - Y * Y * D)⁻¹ * en - algebraMap K A (X * X - Y * Y * D)⁻¹ * algebraMap K A Y * algebraMap K A Y * hsq`.
-/
theorem isField_iff_not_sq {Δ : A} {D : K} (hsq : Δ * Δ = algebraMap K A D)
    (hind : ∀ X Y : K, algebraMap K A X + algebraMap K A Y * Δ = 0 → X = 0 ∧ Y = 0)
    (hsp : ∀ a : A, ∃ X Y : K, a = algebraMap K A X + algebraMap K A Y * Δ) :
    IsField A ↔ ¬ ∃ c : K, c * c = D := by
  constructor
  · rintro hF ⟨c, hc⟩
    have := hF.isDomain
    have e : algebraMap K A c * algebraMap K A c = algebraMap K A D := by rw [← map_mul, hc]
    have h0 : (Δ - algebraMap K A c) * (Δ + algebraMap K A c) = 0 := by
      linear_combination hsq - e
    rcases mul_eq_zero.1 h0 with h | h
    · exact one_ne_zero (hind (-c) 1 (by rw [map_neg, map_one]; linear_combination h)).2
    · exact one_ne_zero (hind c 1 (by rw [map_one]; linear_combination h)).2
  · intro hns
    refine ⟨⟨0, 1, fun h => ?_⟩, mul_comm, fun {a} ha => ?_⟩
    · exact one_ne_zero (hind 1 0 (by rw [map_one, map_zero, zero_mul, add_zero]; exact h.symm)).1
    · obtain ⟨X, Y, rfl⟩ := hsp a
      have hn : X * X - Y * Y * D ≠ 0 := by
        intro hn
        by_cases hY : Y = 0
        · subst hY
          have hX : X = 0 := by simpa using hn
          subst hX
          exact ha (by simp)
        · exact hns ⟨X / Y, by field_simp; linear_combination hn⟩
      have e : algebraMap K A (X * X - Y * Y * D)⁻¹ * algebraMap K A (X * X - Y * Y * D) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hn, map_one]
      have en : algebraMap K A (X * X - Y * Y * D) = algebraMap K A X * algebraMap K A X -
          algebraMap K A Y * algebraMap K A Y * algebraMap K A D := by
        simp only [map_sub, map_mul]
      refine ⟨algebraMap K A (X * X - Y * Y * D)⁻¹ * (algebraMap K A X - algebraMap K A Y * Δ), ?_⟩
      linear_combination e - algebraMap K A (X * X - Y * Y * D)⁻¹ * en -
        algebraMap K A (X * X - Y * Y * D)⁻¹ * algebraMap K A Y * algebraMap K A Y * hsq

/- English proof (translation)
Establish `hYD : ‖Y * Y * D‖ = ‖Y‖ * ‖Y‖` using `by rw [norm_mul, norm_mul, hD, mul_one]`. Establish `hle : ‖X * X - Y * Y * D‖ ≤ 1`. Rewrite using `[sub_eq_add_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Conclude with `mul_le_one₀ hX (norm_nonneg _) hX`. Rewrite using `[norm_neg, hYD]`. Conclude with `mul_le_one₀ hY (norm_nonneg _) hY`. Use `le_antisymm hle (not_lt.1 fun hlt => ?_)` and prove the remaining obligations. Distinguish the cases in `hY1 : ‖Y‖ < 1`.

Use `hp ⟨?_, hY1⟩` and prove the remaining obligations. Establish `h1 : ‖X * X‖ < 1`. Establish `e : X * X = (X * X - Y * Y * D) + Y * Y * D` using `by ring`. Rewrite using `[e]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hlt ?_)` and prove the remaining obligations.

Rewrite using `[hYD]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hY1 hY1.le`. Rewrite `h1` using `[norm_mul]`. Assume the negation of the conclusion as `hc`. Establish `: 1 ≤ ‖X‖` using `not_lt.1 hc`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hYe : ‖Y‖ = 1` using `le_antisymm hY (not_lt.1 hY1)`. Establish `hY0 : Y ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hYe`.

Use `set w := X / Y with hw`. Establish `hww : ‖w * w - D‖ < 1`. Establish `e : w * w - D = (X * X - Y * Y * D) / (Y * Y)`. Rewrite using `[hw]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e, norm_div, norm_mul, hYe, mul_one, div_one]`. Conclude with `hlt`. Establish `hw1 : ‖w * w‖ = 1`. Establish `e : w * w = (w * w - D) + D` using `by ring`. Rewrite using `[e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hD]; exact hww.ne), hD]`.

Conclude with `max_eq_right hww.le`. Establish `hw0 : w ≠ 0`. Introduce and unpack `h`. Rewrite `hw1` using `[h]`. Simplify using `at hw1`.

Take `⟨z, hz⟩` from `hroot (D / (w * w)) (by`. Establish `e : D / (w * w) - 1 = -(w * w - D) / (w * w)` using `by field_simp; ring`. Rewrite using `[e, norm_div, hw1, div_one, norm_neg]`. Conclude with `hww)`. Use `hns ⟨z * w, ?_⟩` and prove the remaining obligations.

Establish `: z * z = D / (w * w)` using `by rw [← hz]; ring`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_form_eq_one {D : K} (hD : ‖D‖ = 1) (hroot : ∀ u : K, ‖u - 1‖ < 1 → ∃ z : K, z ^ 2 = u)
    (hns : ¬ ∃ c : K, c * c = D) {X Y : K} (hX : ‖X‖ ≤ 1) (hY : ‖Y‖ ≤ 1) (hp : ¬ (‖X‖ < 1 ∧ ‖Y‖ < 1)) :
    ‖X * X - Y * Y * D‖ = 1 := by
  have hYD : ‖Y * Y * D‖ = ‖Y‖ * ‖Y‖ := by rw [norm_mul, norm_mul, hD, mul_one]
  have hle : ‖X * X - Y * Y * D‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]; exact mul_le_one₀ hX (norm_nonneg _) hX
    · rw [norm_neg, hYD]; exact mul_le_one₀ hY (norm_nonneg _) hY
  refine le_antisymm hle (not_lt.1 fun hlt => ?_)
  by_cases hY1 : ‖Y‖ < 1
  · refine hp ⟨?_, hY1⟩
    have h1 : ‖X * X‖ < 1 := by
      have e : X * X = (X * X - Y * Y * D) + Y * Y * D := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hlt ?_)
      rw [hYD]
      exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hY1 hY1.le
    rw [norm_mul] at h1
    by_contra hc
    have : 1 ≤ ‖X‖ := not_lt.1 hc
    nlinarith
  · have hYe : ‖Y‖ = 1 := le_antisymm hY (not_lt.1 hY1)
    have hY0 : Y ≠ 0 := by
      rintro rfl
      simp at hYe
    set w := X / Y with hw
    have hww : ‖w * w - D‖ < 1 := by
      have e : w * w - D = (X * X - Y * Y * D) / (Y * Y) := by
        rw [hw]; field_simp
      rw [e, norm_div, norm_mul, hYe, mul_one, div_one]
      exact hlt
    have hw1 : ‖w * w‖ = 1 := by
      have e : w * w = (w * w - D) + D := by ring
      rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hD]; exact hww.ne), hD]
      exact max_eq_right hww.le
    have hw0 : w ≠ 0 := by
      rintro h
      rw [h] at hw1
      simp at hw1
    obtain ⟨z, hz⟩ := hroot (D / (w * w)) (by
      have e : D / (w * w) - 1 = -(w * w - D) / (w * w) := by field_simp; ring
      rw [e, norm_div, hw1, div_one, norm_neg]
      exact hww)
    refine hns ⟨z * w, ?_⟩
    have : z * z = D / (w * w) := by rw [← hz]; ring
    calc z * w * (z * w) = z * z * (w * w) := by ring
      _ = D := by rw [this]; field_simp

/- English proof (translation)
Establish `hlev : ∀ (X Y : K) (h : algebraMap K A X + algebraMap K A Y * Δ ∈ S), (⟨_, h⟩ : S) ∈ lev (⟨_, hϖ⟩ : S) 1 ↔ ‖X‖ < 1 ∧ ‖Y‖ < 1`. Introduce `X Y h`. Rewrite using `[lev, pow_one, Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs⟩`.

Take `⟨X', Y', e⟩` from `hsp s`. Establish `hs'` using `(hS X' Y').1 (e ▸ s.2)`. Establish `e2 : (s : A) * algebraMap K A ϖ = algebraMap K A X + algebraMap K A Y * Δ` using `congrArg Subtype.val hs`. Rewrite `e2` using `[e]`. Take `⟨a1, a2⟩` from `coord_unique hind (X := X' * ϖ) (Y := Y' * ϖ) (X' := X) (Y' := Y) (by`.

Rewrite using `[← e2, map_mul, map_mul]`. Use the proof step `ring)`. Rewrite using `[← a1, ← a2, norm_mul, norm_mul]`. Conclude with `⟨mul_lt_one_of_nonneg_of_lt_one_right hs'.1 (norm_nonneg _) hϖ1, mul_lt_one_of_nonneg_of_lt_one_right hs'.2 (norm_nonneg _) hϖ1⟩`. Introduce and unpack `⟨h1, h2⟩`.

Take `⟨x, hx, rfl⟩` from `hdv X h1`. Take `⟨y, hy, rfl⟩` from `hdv Y h2`. Use `⟨⟨_, (hS x y).2 ⟨hx, hy⟩⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show (algebraMap K A x + algebraMap K A y * Δ) * algebraMap K A ϖ = algebraMap K A (x * ϖ) + algebraMap K A (y * ϖ) * Δ`. Rewrite using `[map_mul, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hc1 : ∀ c : K, c * c = D → ‖c‖ = 1`. Introduce `c hc`. Establish `h` using `congrArg norm hc`. Rewrite `h` using `[norm_mul, hD]`.

Use polynomial arithmetic with `[norm_nonneg c, sq_nonneg (‖c‖ - 1), sq_nonneg (‖c‖ + 1)]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `hF ⟨c, hc⟩`. Use `hF.isDomain` as an intermediate fact. Establish `hcn` using `hc1 c hc`.

Establish `m1 : algebraMap K A (-c) + algebraMap K A 1 * Δ ∈ S` using `(hS _ _).2 ⟨by rw [norm_neg, hcn], by simp⟩`. Establish `m2 : algebraMap K A c + algebraMap K A 1 * Δ ∈ S` using `(hS _ _).2 ⟨hcn.le, by simp⟩`. Establish `e : algebraMap K A c * algebraMap K A c = algebraMap K A D` using `by rw [← map_mul, hc]`. Establish `h0 : (⟨_, m1⟩ : S) * ⟨_, m2⟩ = 0` using `Subtype.ext (by show (algebraMap K A (-c) + algebraMap K A 1 * Δ) * (algebraMap K A c + algebraMap K A 1 * Δ) = 0`. Rewrite using `[map_neg, map_one]`.

Take the linear combination `hsq - e)`. Establish `h1` using `congrArg (Ideal.Quotient.mk (lev (⟨_, hϖ⟩ : S) 1)) h0`. Rewrite `h1` using `[map_mul, map_zero]`. Break down `mul_eq_zero.1 h1 with h | h` into its components or cases. Use `((hlev _ _ m1).1 (Ideal.Quotient.eq_zero_iff_mem.1 h)).2` as an intermediate fact.

Simplify using `at this`. Use `((hlev _ _ m2).1 (Ideal.Quotient.eq_zero_iff_mem.1 h)).2` as an intermediate fact. Simplify using `at this`. Introduce `hns`. Use `⟨⟨0, 1, fun h => ?_⟩, mul_comm, fun {a} ha => ?_⟩` and prove the remaining obligations.

Establish `m : algebraMap K A 1 + algebraMap K A 0 * Δ ∈ S` using `(hS _ _).2 ⟨by simp, by simp⟩`. Establish `e : (⟨_, m⟩ : S) = 1` using `Subtype.ext (by show algebraMap K A 1 + algebraMap K A 0 * Δ = 1 simp)`. Establish `h1 : (⟨_, m⟩ : S) ∈ lev (⟨_, hϖ⟩ : S) 1`. Rewrite using `[e]`. Apply `Ideal.Quotient.eq_zero_iff_mem.1` to reduce the goal to its premises.

Rewrite using `[map_one]`. Conclude with `h.symm`. Use `((hlev _ _ m).1 h1).1` as an intermediate fact. Simplify using `at this`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`.

Take `⟨X, Y, e⟩` from `hsp a`. Establish `ma : algebraMap K A X + algebraMap K A Y * Δ ∈ S` using `e ▸ a.2`. Establish `ea : a = ⟨_, ma⟩` using `Subtype.ext e`. Substitute `ea` using the available equality. Establish `hXY` using `(hS X Y).1 ma`.

Establish `hp : ¬ (‖X‖ < 1 ∧ ‖Y‖ < 1)` using `fun h => ha (Ideal.Quotient.eq_zero_iff_mem.2 ((hlev X Y ma).2 h))`. Establish `hn` using `norm_form_eq_one hD hroot hns hXY.1 hXY.2 hp`. Establish `hn0 : X * X - Y * Y * D ≠ 0`. Introduce `h`. Rewrite `hn` using `[h]`.

Simplify using `at hn`. Establish `mb : algebraMap K A (X / (X * X - Y * Y * D)) + algebraMap K A (-Y / (X * X - Y * Y * D)) * Δ ∈ S` using `(hS _ _).2 ⟨by rw [norm_div, hn, div_one]; exact hXY.1, by rw [norm_div, hn, div_one, norm_neg]; exact hXY.2⟩`. Use `⟨Ideal.Quotient.mk _ ⟨_, mb⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, ← map_one (Ideal.Quotient.mk _)]`. Use `congr 1`.

Use `Subtype.ext ?_` and prove the remaining obligations. Use `show (algebraMap K A X + algebraMap K A Y * Δ) * (algebraMap K A (X / (X * X - Y * Y * D)) + algebraMap K A (-Y / (X * X - Y * Y * D)) * Δ) = 1`. Establish `e1 : algebraMap K A X * algebraMap K A (X / (X * X - Y * Y * D)) + algebraMap K A Y * algebraMap K A (-Y / (X * X - Y * Y * D)) * algebraMap K A D = 1`. Rewrite using `[← map_mul, ← map_mul, ← map_mul, ← map_add, ← map_one (algebraMap K A)]`. Use `congr 1`.

Rewrite using `[show X * (X / (X * X - Y * Y * D)) + Y * (-Y / (X * X - Y * Y * D)) * D = (X * X - Y * Y * D) / (X * X - Y * Y * D) by ring, div_self hn0]`. Establish `e2 : algebraMap K A X * algebraMap K A (-Y / (X * X - Y * Y * D)) + algebraMap K A Y * algebraMap K A (X / (X * X - Y * Y * D)) = 0`. Rewrite using `[← map_mul, ← map_mul, ← map_add, ← map_zero (algebraMap K A)]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Take the linear combination `e1 + Δ * e2 + algebraMap K A Y * algebraMap K A (-Y / (X * X - Y * Y * D)) * hsq`.
-/
theorem isField_quot_iff_not_sq (S : Subring A) {Δ : A} {D ϖ : K} (hsq : Δ * Δ = algebraMap K A D)
    (hind : ∀ X Y : K, algebraMap K A X + algebraMap K A Y * Δ = 0 → X = 0 ∧ Y = 0)
    (hsp : ∀ a : A, ∃ X Y : K, a = algebraMap K A X + algebraMap K A Y * Δ)
    (hS : ∀ X Y : K, algebraMap K A X + algebraMap K A Y * Δ ∈ S ↔ ‖X‖ ≤ 1 ∧ ‖Y‖ ≤ 1)
    (hD : ‖D‖ = 1) (hϖ1 : ‖ϖ‖ < 1) (hdv : ∀ x : K, ‖x‖ < 1 → ∃ y : K, ‖y‖ ≤ 1 ∧ x = y * ϖ)
    (hroot : ∀ u : K, ‖u - 1‖ < 1 → ∃ z : K, z ^ 2 = u) (hϖ : algebraMap K A ϖ ∈ S) :
    IsField (S ⧸ lev (⟨_, hϖ⟩ : S) 1) ↔ ¬ ∃ c : K, c * c = D := by

  have hlev : ∀ (X Y : K) (h : algebraMap K A X + algebraMap K A Y * Δ ∈ S),
      (⟨_, h⟩ : S) ∈ lev (⟨_, hϖ⟩ : S) 1 ↔ ‖X‖ < 1 ∧ ‖Y‖ < 1 := by
    intro X Y h
    rw [lev, pow_one, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨s, hs⟩
      obtain ⟨X', Y', e⟩ := hsp s
      have hs' := (hS X' Y').1 (e ▸ s.2)
      have e2 : (s : A) * algebraMap K A ϖ = algebraMap K A X + algebraMap K A Y * Δ :=
        congrArg Subtype.val hs
      rw [e] at e2
      obtain ⟨a1, a2⟩ := coord_unique hind (X := X' * ϖ) (Y := Y' * ϖ) (X' := X) (Y' := Y) (by
        rw [← e2, map_mul, map_mul]; ring)
      rw [← a1, ← a2, norm_mul, norm_mul]
      exact ⟨mul_lt_one_of_nonneg_of_lt_one_right hs'.1 (norm_nonneg _) hϖ1,
        mul_lt_one_of_nonneg_of_lt_one_right hs'.2 (norm_nonneg _) hϖ1⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨x, hx, rfl⟩ := hdv X h1
      obtain ⟨y, hy, rfl⟩ := hdv Y h2
      refine ⟨⟨_, (hS x y).2 ⟨hx, hy⟩⟩, Subtype.ext ?_⟩
      show (algebraMap K A x + algebraMap K A y * Δ) * algebraMap K A ϖ =
        algebraMap K A (x * ϖ) + algebraMap K A (y * ϖ) * Δ
      rw [map_mul, map_mul]
      ring
  have hc1 : ∀ c : K, c * c = D → ‖c‖ = 1 := by
    intro c hc
    have h := congrArg norm hc
    rw [norm_mul, hD] at h
    nlinarith [norm_nonneg c, sq_nonneg (‖c‖ - 1), sq_nonneg (‖c‖ + 1)]
  constructor
  · rintro hF ⟨c, hc⟩
    have := hF.isDomain
    have hcn := hc1 c hc
    have m1 : algebraMap K A (-c) + algebraMap K A 1 * Δ ∈ S :=
      (hS _ _).2 ⟨by rw [norm_neg, hcn], by simp⟩
    have m2 : algebraMap K A c + algebraMap K A 1 * Δ ∈ S := (hS _ _).2 ⟨hcn.le, by simp⟩
    have e : algebraMap K A c * algebraMap K A c = algebraMap K A D := by rw [← map_mul, hc]
    have h0 : (⟨_, m1⟩ : S) * ⟨_, m2⟩ = 0 := Subtype.ext (by
      show (algebraMap K A (-c) + algebraMap K A 1 * Δ) * (algebraMap K A c + algebraMap K A 1 * Δ) = 0
      rw [map_neg, map_one]
      linear_combination hsq - e)
    have h1 := congrArg (Ideal.Quotient.mk (lev (⟨_, hϖ⟩ : S) 1)) h0
    rw [map_mul, map_zero] at h1
    rcases mul_eq_zero.1 h1 with h | h
    · have := ((hlev _ _ m1).1 (Ideal.Quotient.eq_zero_iff_mem.1 h)).2
      simp at this
    · have := ((hlev _ _ m2).1 (Ideal.Quotient.eq_zero_iff_mem.1 h)).2
      simp at this
  · intro hns
    refine ⟨⟨0, 1, fun h => ?_⟩, mul_comm, fun {a} ha => ?_⟩
    · have m : algebraMap K A 1 + algebraMap K A 0 * Δ ∈ S := (hS _ _).2 ⟨by simp, by simp⟩
      have e : (⟨_, m⟩ : S) = 1 := Subtype.ext (by
        show algebraMap K A 1 + algebraMap K A 0 * Δ = 1
        simp)
      have h1 : (⟨_, m⟩ : S) ∈ lev (⟨_, hϖ⟩ : S) 1 := by
        rw [e]
        apply Ideal.Quotient.eq_zero_iff_mem.1
        rw [map_one]
        exact h.symm
      have := ((hlev _ _ m).1 h1).1
      simp at this
    · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨X, Y, e⟩ := hsp a
      have ma : algebraMap K A X + algebraMap K A Y * Δ ∈ S := e ▸ a.2
      have ea : a = ⟨_, ma⟩ := Subtype.ext e
      subst ea
      have hXY := (hS X Y).1 ma
      have hp : ¬ (‖X‖ < 1 ∧ ‖Y‖ < 1) := fun h =>
        ha (Ideal.Quotient.eq_zero_iff_mem.2 ((hlev X Y ma).2 h))
      have hn := norm_form_eq_one hD hroot hns hXY.1 hXY.2 hp
      have hn0 : X * X - Y * Y * D ≠ 0 := by
        intro h
        rw [h] at hn
        simp at hn
      have mb : algebraMap K A (X / (X * X - Y * Y * D)) +
          algebraMap K A (-Y / (X * X - Y * Y * D)) * Δ ∈ S :=
        (hS _ _).2 ⟨by rw [norm_div, hn, div_one]; exact hXY.1,
          by rw [norm_div, hn, div_one, norm_neg]; exact hXY.2⟩
      refine ⟨Ideal.Quotient.mk _ ⟨_, mb⟩, ?_⟩
      rw [← map_mul, ← map_one (Ideal.Quotient.mk _)]
      congr 1
      refine Subtype.ext ?_
      show (algebraMap K A X + algebraMap K A Y * Δ) * (algebraMap K A (X / (X * X - Y * Y * D)) +
          algebraMap K A (-Y / (X * X - Y * Y * D)) * Δ) = 1
      have e1 : algebraMap K A X * algebraMap K A (X / (X * X - Y * Y * D)) +
          algebraMap K A Y * algebraMap K A (-Y / (X * X - Y * Y * D)) * algebraMap K A D = 1 := by
        rw [← map_mul, ← map_mul, ← map_mul, ← map_add, ← map_one (algebraMap K A)]
        congr 1
        rw [show X * (X / (X * X - Y * Y * D)) + Y * (-Y / (X * X - Y * Y * D)) * D =
          (X * X - Y * Y * D) / (X * X - Y * Y * D) by ring, div_self hn0]
      have e2 : algebraMap K A X * algebraMap K A (-Y / (X * X - Y * Y * D)) +
          algebraMap K A Y * algebraMap K A (X / (X * X - Y * Y * D)) = 0 := by
        rw [← map_mul, ← map_mul, ← map_add, ← map_zero (algebraMap K A)]
        congr 1
        ring
      linear_combination e1 + Δ * e2 +
        algebraMap K A Y * algebraMap K A (-Y / (X * X - Y * Y * D)) * hsq

end Core

section Concrete

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.SiegelWeilFormula.Gen PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `⟨(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom⟩`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2, h.2.2.2, star_star]`.
-/
theorem sig_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := ⟨(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom⟩
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `⟨(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom⟩`. Establish `hr : NumberField.ComplexEmbedding.IsReal τ`. Use extensionality with `x`.

Simplify using `only [NumberField.ComplexEmbedding.conjugate_coe_eq]`. Establish `e` using `h.2.2.2 τ x`. Rewrite `e` using `[hc]`. Conclude with `e.symm`. Establish `hc2` using `h.2.1.isComplex (NumberField.InfinitePlace.mk τ)`.

Conclude with `(NumberField.InfinitePlace.isComplex_mk_iff.1 hc2) hr`.
-/
theorem sig_moves {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ x, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := ⟨(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom⟩
  have hr : NumberField.ComplexEmbedding.IsReal τ := by
    ext x
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq]
    have e := h.2.2.2 τ x
    rw [hc] at e
    exact e.symm
  have hc2 := h.2.1.isComplex (NumberField.InfinitePlace.mk τ)
  exact (NumberField.InfinitePlace.isComplex_mk_iff.1 hc2) hr

/- English proof (translation)
Establish `hinv` using `sig_invol hσ`. Establish `tr` using `Formalism.L2.SG.Pf.NcVal.VolUTr.TrW.trace_eq_add σ hinv (sig_moves hσ) hσ.2.2.1`. Use `⟨by simp only [map_sub, map_mul, hinv]; ring, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.discr_def, Matrix.det_fin_two]`. Simplify using `only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, map_sub, map_mul, tr]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem delta_props {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (bs : Module.Basis (Fin 2) F E) :
    σ (bs 0 * σ (bs 1) - bs 1 * σ (bs 0)) = -(bs 0 * σ (bs 1) - bs 1 * σ (bs 0)) ∧
    (bs 0 * σ (bs 1) - bs 1 * σ (bs 0)) * (bs 0 * σ (bs 1) - bs 1 * σ (bs 0)) =
      algebraMap F E (Algebra.discr F (⇑bs)) := by
  have hinv := sig_invol hσ
  have tr := Formalism.L2.SG.Pf.NcVal.VolUTr.TrW.trace_eq_add σ hinv (sig_moves hσ) hσ.2.2.1
  refine ⟨by simp only [map_sub, map_mul, hinv]; ring, ?_⟩
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, map_sub, map_mul, tr]
  ring

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff]`.
-/
theorem mem_integers_iff {v : HeightOneSpectrum (𝓞 F)} (x : Fv F v) :
    x ∈ v.adicCompletionIntegers F ↔ ‖x‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff]

/- English proof (translation)
Rewrite `h1`, `h2` using `[mem_integers_iff]`. Establish `e : ‖y‖ * ‖y⁻¹‖ = 1` using `by rw [← norm_mul, mul_inv_cancel₀ hy, norm_one]`. Use polynomial arithmetic with `[norm_nonneg y, norm_nonneg y⁻¹]`.
-/
theorem norm_eq_one_of_inv {v : HeightOneSpectrum (𝓞 F)} {y : Fv F v} (hy : y ≠ 0)
    (h1 : y ∈ v.adicCompletionIntegers F) (h2 : y⁻¹ ∈ v.adicCompletionIntegers F) : ‖y‖ = 1 := by
  rw [mem_integers_iff] at h1 h2
  have e : ‖y‖ * ‖y⁻¹‖ = 1 := by rw [← norm_mul, mul_inv_cancel₀ hy, norm_one]
  nlinarith [norm_nonneg y, norm_nonneg y⁻¹]

/- English proof (translation)
Establish `h1 : algebraMap F (Fv F v) (2 : F)⁻¹ ∈ v.adicCompletionIntegers F` using `hB _ (by simp [basisSet])`. Rewrite `h1` using `[map_inv₀, map_ofNat]`. Establish `h20 : (2 : Fv F v) ≠ 0`. Use `(map_ne_zero (algebraMap F (Fv F v))).2 (two_ne_zero : (2 : F) ≠ 0)` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis.

Use `norm_eq_one_of_inv h20 ?_ h1` and prove the remaining obligations. Rewrite using `[mem_integers_iff, ← one_add_one_eq_two]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (by simp)`.
-/
theorem norm_two_eq {σ : E →ₐ[F] E} {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    (hB : IntAt v (basisSet σ bs)) : ‖(2 : Fv F v)‖ = 1 := by
  have h1 : algebraMap F (Fv F v) (2 : F)⁻¹ ∈ v.adicCompletionIntegers F := hB _ (by simp [basisSet])
  rw [map_inv₀, map_ofNat] at h1
  have h20 : (2 : Fv F v) ≠ 0 := by
    have := (map_ne_zero (algebraMap F (Fv F v))).2 (two_ne_zero : (2 : F) ≠ 0)
    rwa [map_ofNat] at this
  refine norm_eq_one_of_inv h20 ?_ h1
  rw [mem_integers_iff, ← one_add_one_eq_two]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (by simp)

/- English proof (translation)
Establish `hfin : FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; omega)`. Establish `h0 : Algebra.discr F (⇑bs) ≠ 0` using `Algebra.discr_not_zero_of_basis F bs`. Establish `h1 : algebraMap F (Fv F v) (Algebra.discr F (⇑bs)) ∈ v.adicCompletionIntegers F` using `hB _ (by simp [basisSet])`. Establish `h2 : algebraMap F (Fv F v) (Algebra.discr F (⇑bs))⁻¹ ∈ v.adicCompletionIntegers F` using `hB _ (by simp [basisSet])`. Rewrite `h2` using `[map_inv₀]`.

Conclude with `norm_eq_one_of_inv ((map_ne_zero _).2 h0) h1 h2`.
-/
theorem norm_discr_eq {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {d : ℕ} {bs : Module.Basis (Fin d) F E}
    {v : HeightOneSpectrum (𝓞 F)} (hB : IntAt v (basisSet σ bs)) :
    ‖algebraMap F (Fv F v) (Algebra.discr F (⇑bs))‖ = 1 := by
  have hfin : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; omega)
  have h0 : Algebra.discr F (⇑bs) ≠ 0 := Algebra.discr_not_zero_of_basis F bs
  have h1 : algebraMap F (Fv F v) (Algebra.discr F (⇑bs)) ∈ v.adicCompletionIntegers F :=
    hB _ (by simp [basisSet])
  have h2 : algebraMap F (Fv F v) (Algebra.discr F (⇑bs))⁻¹ ∈ v.adicCompletionIntegers F :=
    hB _ (by simp [basisSet])
  rw [map_inv₀] at h2
  exact norm_eq_one_of_inv ((map_ne_zero _).2 h0) h1 h2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sigR_tmul' (σ : E →ₐ[F] E) {v : HeightOneSpectrum (𝓞 F)} (s : Fv F v) (x : E) :
    sigR (Fv F v) σ (s ⊗ₜ[F] x) = s ⊗ₜ[F] σ x := rfl

/- English proof (translation)
Use `show sigR (Fv F v) σ (c ⊗ₜ[F] (1 : E)) = c ⊗ₜ[F] (1 : E)`. Rewrite using `[sigR_tmul', map_one]`.
-/
theorem sigR_scalar (σ : E →ₐ[F] E) {v : HeightOneSpectrum (𝓞 F)} (c : Fv F v) :
    sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) c) = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := by
  show sigR (Fv F v) σ (c ⊗ₜ[F] (1 : E)) = c ⊗ₜ[F] (1 : E)
  rw [sigR_tmul', map_one]

end Concrete

section Main

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.SiegelWeilFormula.Gen PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `h1 : x ∈ Rv bs v`. Rewrite using `[← hcar]`. Conclude with `hx`. Establish `h2 : β • x ∈ Rv bs v` using `fun k => by`. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul]`.

Conclude with `mul_mem ((mem_integers_iff _).2 hβ) (h1 k)`. Rewrite `h2` using `[← hcar]`. Conclude with `h2`.
-/
theorem smul_mem_of {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    {S : Subring (Fv F v ⊗[F] E)} (hcar : (S : Set (Fv F v ⊗[F] E)) = Rv bs v) {β : Fv F v} (hβ : ‖β‖ ≤ 1)
    {x : Fv F v ⊗[F] E} (hx : x ∈ S) : β • x ∈ S := by
  have h1 : x ∈ Rv bs v := by
    rw [← hcar]
    exact hx
  have h2 : β • x ∈ Rv bs v := fun k => by
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem ((mem_integers_iff _).2 hβ) (h1 k)
  rw [← hcar] at h2
  exact h2

/- English proof (translation)
Establish `h : Algebra.TensorProduct.basis (Fv F v) bs i ∈ Rv bs v` using `fun k => by`. Rewrite using `[Module.Basis.repr_self, Finsupp.single_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`.

Rewrite `h` using `[← hcar, Algebra.TensorProduct.basis_apply]`. Conclude with `h`.
-/
theorem basis_mem_of {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    {S : Subring (Fv F v ⊗[F] E)} (hcar : (S : Set (Fv F v ⊗[F] E)) = Rv bs v) (i : Fin d) :
    (1 : Fv F v) ⊗ₜ[F] bs i ∈ S := by
  have h : Algebra.TensorProduct.basis (Fv F v) bs i ∈ Rv bs v := fun k => by
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  rw [← hcar, Algebra.TensorProduct.basis_apply] at h
  exact h

/- English proof (translation)
Establish `hc : ∀ (x : Fv F v ⊗[F] E), x ∈ S → ∀ k, ‖(Algebra.TensorProduct.basis (Fv F v) bs).repr x k‖ ≤ 1`. Introduce `x hx k`. Establish `h1 : x ∈ Rv bs v`. Rewrite using `[← hcar]`. Conclude with `hx`.

Conclude with `(mem_integers_iff _).1 (h1 k)`. Establish `hm : ∀ i, a * Algebra.TensorProduct.basis (Fv F v) bs i ∈ S` using `fun i => by`. Rewrite using `[Algebra.TensorProduct.basis_apply]`. Conclude with `mul_mem ha (basis_mem_of hcar i)`. Rewrite using `[Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis (Fv F v) bs), Matrix.trace, Fin.sum_univ_two]`.

Simplify using `only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hc _ (hm 0) 0) (hc _ (hm 1) 1))`.
-/
theorem norm_trace_le {bs : Module.Basis (Fin 2) F E} {v : HeightOneSpectrum (𝓞 F)}
    {S : Subring (Fv F v ⊗[F] E)} (hcar : (S : Set (Fv F v ⊗[F] E)) = Rv bs v)
    {a : Fv F v ⊗[F] E} (ha : a ∈ S) : ‖Algebra.trace (Fv F v) (Fv F v ⊗[F] E) a‖ ≤ 1 := by
  have hc : ∀ (x : Fv F v ⊗[F] E), x ∈ S → ∀ k, ‖(Algebra.TensorProduct.basis (Fv F v) bs).repr x k‖ ≤ 1 := by
    intro x hx k
    have h1 : x ∈ Rv bs v := by
      rw [← hcar]
      exact hx
    exact (mem_integers_iff _).1 (h1 k)
  have hm : ∀ i, a * Algebra.TensorProduct.basis (Fv F v) bs i ∈ S := fun i => by
    rw [Algebra.TensorProduct.basis_apply]
    exact mul_mem ha (basis_mem_of hcar i)
  rw [Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis (Fv F v) bs), Matrix.trace, Fin.sum_univ_two]
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hc _ (hm 0) 0) (hc _ (hm 1) 1))

/- English proof (translation)
Establish `h` using `norm_trace_le hcar hc`. Rewrite `h` using `[Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis (Fv F v) bs), Fintype.card_fin, two_nsmul, ← two_mul, norm_mul, norm_two_eq hB, one_mul]`. Conclude with `h`.
-/
theorem norm_scalar_le {σ : E →ₐ[F] E} {bs : Module.Basis (Fin 2) F E} {v : HeightOneSpectrum (𝓞 F)}
    (hB : IntAt v (basisSet σ bs)) {S : Subring (Fv F v ⊗[F] E)}
    (hcar : (S : Set (Fv F v ⊗[F] E)) = Rv bs v) {c : Fv F v}
    (hc : algebraMap (Fv F v) (Fv F v ⊗[F] E) c ∈ S) : ‖c‖ ≤ 1 := by
  have h := norm_trace_le hcar hc
  rw [Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis (Fv F v) bs), Fintype.card_fin, two_nsmul,
    ← two_mul, norm_mul, norm_two_eq hB, one_mul] at h
  exact h

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d bs v S σS ϖ h hϖ`. Take `⟨hσ, hB, hcar, hsig, h0, h1, hdv, -⟩` from `h`. Choose the witnesses or unpack the hypotheses as in `rfl : d = 2 := by`. Use `Module.finrank_eq_card_basis bs` as an intermediate fact. Rewrite `this` using `[hσ.2.2.1, Fintype.card_fin]`.

Conclude with `this.symm`. Take `⟨hδσ, hδ2⟩` from `delta_props hσ bs`. Use `set δ := bs 0 * σ (bs 1) - bs 1 * σ (bs 0) with hδ`. Use `set D := algebraMap F (Fv F v) (Algebra.discr F (⇑bs)) with hDdef`. Establish `hD : ‖D‖ = 1` using `norm_discr_eq hσ hB`.

Establish `h2` using `norm_two_eq hB`. Establish `hD0 : D ≠ 0` using `fun e => by`. Rewrite `hD` using `[e, norm_zero]`. Conclude with `zero_ne_one hD`. Establish `h20 : (2 : Fv F v) ≠ 0` using `fun e => by`.

Rewrite `h2` using `[e, norm_zero]`. Conclude with `zero_ne_one h2`. Set `bK` to `Algebra.TensorProduct.basis (Fv F v) bs`. Establish `: Nontrivial (Fv F v ⊗[F] E)` using `⟨⟨bK 0, 0, bK.ne_zero 0⟩⟩`. Establish `: FiniteDimensional (Fv F v) (Fv F v ⊗[F] E)` using `Module.Finite.of_basis bK`.

Establish `hinj` using `(algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective`. Use `set Δ : Fv F v ⊗[F] E := (1 : Fv F v) ⊗ₜ[F] δ with hΔ`. Establish `hsq : Δ * Δ = algebraMap (Fv F v) (Fv F v ⊗[F] E) D`. Rewrite using `[hΔ, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hδ2, hDdef, ← Algebra.TensorProduct.tmul_one_eq_one_tmul]`. Both sides reduce to the same expression.

Establish `hsΔ : sigR (Fv F v) σ Δ = -Δ`. Rewrite using `[hΔ, sigR_tmul', hδσ, TensorProduct.tmul_neg]`. Establish `hind : ∀ X Y : Fv F v, algebraMap (Fv F v) (Fv F v ⊗[F] E) X + algebraMap (Fv F v) (Fv F v ⊗[F] E) Y * Δ = 0 → X = 0 ∧ Y = 0`. Introduce `X Y h`. Establish `h'` using `congrArg (sigR (Fv F v) σ) h`.

Rewrite `h'` using `[map_add, map_mul, sigR_scalar, sigR_scalar, hsΔ, map_zero]`. Establish `hX : algebraMap (Fv F v) (Fv F v ⊗[F] E) (2 * X) = 0`. Rewrite using `[map_mul, map_ofNat]`. Take the linear combination `h + h'`. Establish `hX0 : X = 0`.

Use `hinj (hX.trans (map_zero _).symm)` as an intermediate fact. Conclude with `(mul_eq_zero.1 this).resolve_left h20`. Substitute `hX0` using the available equality. Use `⟨rfl, ?_⟩` and prove the remaining obligations. Establish `hY : algebraMap (Fv F v) (Fv F v ⊗[F] E) (Y * D) = 0`.

Rewrite using `[map_mul, ← hsq]`. Rewrite `h` using `[map_zero, zero_add]`. Take the linear combination `Δ * h`. Conclude with `(mul_eq_zero.1 (hinj (hY.trans (map_zero _).symm))).resolve_right hD0`. Establish `hsp : ∀ a : Fv F v ⊗[F] E, ∃ X Y : Fv F v, a = algebraMap (Fv F v) (Fv F v ⊗[F] E) X + algebraMap (Fv F v) (Fv F v ⊗[F] E) Y * Δ`.

Introduce `a`. Establish `hli : LinearIndependent (Fv F v) ![(1 : Fv F v ⊗[F] E), Δ]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Conclude with `hind s t (by rw [← hst, Algebra.smul_def, Algebra.smul_def, mul_one])`.

Establish `hspan` using `hli.span_eq_top_of_card_eq_finrank' (by`. Rewrite using `[Module.finrank_eq_card_basis bK])`. Establish `ha : a ∈ Submodule.span (Fv F v) (Set.range ![(1 : Fv F v ⊗[F] E), Δ])`. Rewrite using `[hspan]`. Conclude with `Submodule.mem_top`.

Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun (Fv F v)).1 ha`. Rewrite `hc` using `[Fin.sum_univ_two]`. Use `⟨c 0, c 1, ?_⟩` and prove the remaining obligations. Rewrite using `[← hc]`. Simplify using `[Algebra.smul_def]`.

Establish `hσmem : ∀ x, x ∈ S → sigR (Fv F v) σ x ∈ S` using `fun x hx => by`. Rewrite using `[← hsig ⟨x, hx⟩]`. Conclude with `(σS ⟨x, hx⟩).2`. Establish `hΔS : Δ ∈ S`. Establish `e : Δ = (1 : Fv F v) ⊗ₜ[F] bs 0 * sigR (Fv F v) σ ((1 : Fv F v) ⊗ₜ[F] bs 1) - (1 : Fv F v) ⊗ₜ[F] bs 1 * sigR (Fv F v) σ ((1 : Fv F v) ⊗ₜ[F] bs 0)`.

Rewrite using `[sigR_tmul', sigR_tmul', Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_sub]`. Rewrite using `[e]`. Conclude with `sub_mem (mul_mem (basis_mem_of hcar 0) (hσmem _ (basis_mem_of hcar 1))) (mul_mem (basis_mem_of hcar 1) (hσmem _ (basis_mem_of hcar 0)))`. Establish `hS : ∀ X Y : Fv F v, algebraMap (Fv F v) (Fv F v ⊗[F] E) X + algebraMap (Fv F v) (Fv F v ⊗[F] E) Y * Δ ∈ S ↔ ‖X‖ ≤ 1 ∧ ‖Y‖ ≤ 1`. Introduce `X Y`.

Prove the components needed by the constructor for the conclusion. Introduce `ha`. Establish `hb` using `hσmem _ ha`. Rewrite `hb` using `[map_add, map_mul, sigR_scalar, sigR_scalar, hsΔ]`. Establish `hX : algebraMap (Fv F v) (Fv F v ⊗[F] E) (2 * X) ∈ S`.

Use `add_mem ha hb` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_mul, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Establish `hY : algebraMap (Fv F v) (Fv F v ⊗[F] E) (2 * Y * D) ∈ S`.

Use `mul_mem (sub_mem ha hb) hΔS` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_mul, map_mul, map_ofNat, ← hsq]`. Expand and normalize the polynomial expressions, which then agree. Establish `n1` using `norm_scalar_le hB hcar hX`.

Establish `n2` using `norm_scalar_le hB hcar hY`. Rewrite `n1` using `[norm_mul, h2, one_mul]`. Rewrite `n2` using `[norm_mul, norm_mul, h2, hD, one_mul, mul_one]`. Conclude with `⟨n1, n2⟩`. Introduce and unpack `⟨hX, hY⟩`.

Use `add_mem ?_ ?_` and prove the remaining obligations. Use `smul_mem_of hcar hX (one_mem S)` as an intermediate fact. Rewrite `this` using `[← Algebra.algebraMap_eq_smul_one]`. Then use the resulting hypothesis. Use `smul_mem_of hcar hY hΔS` as an intermediate fact. Rewrite `this` using `[Algebra.smul_def]`. Then use the resulting hypothesis.

Establish `hdv' : ∀ x : Fv F v, ‖x‖ < 1 → ∃ y : Fv F v, ‖y‖ ≤ 1 ∧ x = y * (ϖ : Fv F v)`. Introduce `x hx`. Take `⟨c, hc⟩` from `hdv ⟨x, (mem_integers_iff _).2 hx.le⟩ hx`. Use `⟨c, (mem_integers_iff _).1 c.2, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hc` as an intermediate fact.

Rewrite using `[mul_comm]`. Conclude with `this`. Establish `hroot : ∀ u : Fv F v, ‖u - 1‖ < 1 → ∃ z : Fv F v, z ^ 2 = u`. Introduce `u hu`. Use `PI.LocalEndW.henselRoot F v 2 u ?_ (Valued.toNormedField.norm_lt_one_iff.1 hu)` and prove the remaining obligations.

Establish `e : ((2 : ℕ) : Fv F v) = 2` using `by norm_num`. Rewrite using `[e]`. Use `le_antisymm (Valued.toNormedField.norm_le_one_iff.1 h2.le) (not_lt.1 fun hlt => ?_)` and prove the remaining obligations. Conclude with `(Valued.toNormedField.norm_lt_one_iff.2 hlt).ne h2`. Conclude with `(isField_iff_not_sq hsq hind hsp).trans (isField_quot_iff_not_sq S hsq hind hsp hS hD h1 hdv' hroot hϖ).symm`.
-/
theorem isField_tensor_iff_isField_quot : PositivityTheory.SiegelWeilFormula.Gunr.Q5 := by
  intro F E _ _ _ _ _ σ d bs v S σS ϖ h hϖ
  obtain ⟨hσ, hB, hcar, hsig, h0, h1, hdv, -⟩ := h
  obtain rfl : d = 2 := by
    have := Module.finrank_eq_card_basis bs
    rw [hσ.2.2.1, Fintype.card_fin] at this
    exact this.symm
  obtain ⟨hδσ, hδ2⟩ := delta_props hσ bs
  set δ := bs 0 * σ (bs 1) - bs 1 * σ (bs 0) with hδ
  set D := algebraMap F (Fv F v) (Algebra.discr F (⇑bs)) with hDdef
  have hD : ‖D‖ = 1 := norm_discr_eq hσ hB
  have h2 := norm_two_eq hB
  have hD0 : D ≠ 0 := fun e => by
    rw [e, norm_zero] at hD
    exact zero_ne_one hD
  have h20 : (2 : Fv F v) ≠ 0 := fun e => by
    rw [e, norm_zero] at h2
    exact zero_ne_one h2
  let bK := Algebra.TensorProduct.basis (Fv F v) bs
  have : Nontrivial (Fv F v ⊗[F] E) := ⟨⟨bK 0, 0, bK.ne_zero 0⟩⟩
  have : FiniteDimensional (Fv F v) (Fv F v ⊗[F] E) := Module.Finite.of_basis bK
  have hinj := (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective
  set Δ : Fv F v ⊗[F] E := (1 : Fv F v) ⊗ₜ[F] δ with hΔ
  have hsq : Δ * Δ = algebraMap (Fv F v) (Fv F v ⊗[F] E) D := by
    rw [hΔ, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hδ2, hDdef,
      ← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    rfl
  have hsΔ : sigR (Fv F v) σ Δ = -Δ := by
    rw [hΔ, sigR_tmul', hδσ, TensorProduct.tmul_neg]
  have hind : ∀ X Y : Fv F v, algebraMap (Fv F v) (Fv F v ⊗[F] E) X +
      algebraMap (Fv F v) (Fv F v ⊗[F] E) Y * Δ = 0 → X = 0 ∧ Y = 0 := by
    intro X Y h
    have h' := congrArg (sigR (Fv F v) σ) h
    rw [map_add, map_mul, sigR_scalar, sigR_scalar, hsΔ, map_zero] at h'
    have hX : algebraMap (Fv F v) (Fv F v ⊗[F] E) (2 * X) = 0 := by
      rw [map_mul, map_ofNat]
      linear_combination h + h'
    have hX0 : X = 0 := by
      have := hinj (hX.trans (map_zero _).symm)
      exact (mul_eq_zero.1 this).resolve_left h20
    subst hX0
    refine ⟨rfl, ?_⟩
    have hY : algebraMap (Fv F v) (Fv F v ⊗[F] E) (Y * D) = 0 := by
      rw [map_mul, ← hsq]
      rw [map_zero, zero_add] at h
      linear_combination Δ * h
    exact (mul_eq_zero.1 (hinj (hY.trans (map_zero _).symm))).resolve_right hD0
  have hsp : ∀ a : Fv F v ⊗[F] E, ∃ X Y : Fv F v, a = algebraMap (Fv F v) (Fv F v ⊗[F] E) X +
      algebraMap (Fv F v) (Fv F v ⊗[F] E) Y * Δ := by
    intro a
    have hli : LinearIndependent (Fv F v) ![(1 : Fv F v ⊗[F] E), Δ] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      exact hind s t (by rw [← hst, Algebra.smul_def, Algebra.smul_def, mul_one])
    have hspan := hli.span_eq_top_of_card_eq_finrank' (by
      rw [Module.finrank_eq_card_basis bK])
    have ha : a ∈ Submodule.span (Fv F v) (Set.range ![(1 : Fv F v ⊗[F] E), Δ]) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (Fv F v)).1 ha
    rw [Fin.sum_univ_two] at hc
    refine ⟨c 0, c 1, ?_⟩
    rw [← hc]
    simp [Algebra.smul_def]
  have hσmem : ∀ x, x ∈ S → sigR (Fv F v) σ x ∈ S := fun x hx => by
    rw [← hsig ⟨x, hx⟩]
    exact (σS ⟨x, hx⟩).2
  have hΔS : Δ ∈ S := by
    have e : Δ = (1 : Fv F v) ⊗ₜ[F] bs 0 * sigR (Fv F v) σ ((1 : Fv F v) ⊗ₜ[F] bs 1) -
        (1 : Fv F v) ⊗ₜ[F] bs 1 * sigR (Fv F v) σ ((1 : Fv F v) ⊗ₜ[F] bs 0) := by
      rw [sigR_tmul', sigR_tmul', Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, ← TensorProduct.tmul_sub]
    rw [e]
    exact sub_mem (mul_mem (basis_mem_of hcar 0) (hσmem _ (basis_mem_of hcar 1)))
      (mul_mem (basis_mem_of hcar 1) (hσmem _ (basis_mem_of hcar 0)))
  have hS : ∀ X Y : Fv F v, algebraMap (Fv F v) (Fv F v ⊗[F] E) X +
      algebraMap (Fv F v) (Fv F v ⊗[F] E) Y * Δ ∈ S ↔ ‖X‖ ≤ 1 ∧ ‖Y‖ ≤ 1 := by
    intro X Y
    constructor
    · intro ha
      have hb := hσmem _ ha
      rw [map_add, map_mul, sigR_scalar, sigR_scalar, hsΔ] at hb
      have hX : algebraMap (Fv F v) (Fv F v ⊗[F] E) (2 * X) ∈ S := by
        have := add_mem ha hb
        convert this using 1
        rw [map_mul, map_ofNat]
        ring
      have hY : algebraMap (Fv F v) (Fv F v ⊗[F] E) (2 * Y * D) ∈ S := by
        have := mul_mem (sub_mem ha hb) hΔS
        convert this using 1
        rw [map_mul, map_mul, map_ofNat, ← hsq]
        ring
      have n1 := norm_scalar_le hB hcar hX
      have n2 := norm_scalar_le hB hcar hY
      rw [norm_mul, h2, one_mul] at n1
      rw [norm_mul, norm_mul, h2, hD, one_mul, mul_one] at n2
      exact ⟨n1, n2⟩
    · rintro ⟨hX, hY⟩
      refine add_mem ?_ ?_
      · have := smul_mem_of hcar hX (one_mem S)
        rwa [← Algebra.algebraMap_eq_smul_one] at this
      · have := smul_mem_of hcar hY hΔS
        rwa [Algebra.smul_def] at this
  have hdv' : ∀ x : Fv F v, ‖x‖ < 1 → ∃ y : Fv F v, ‖y‖ ≤ 1 ∧ x = y * (ϖ : Fv F v) := by
    intro x hx
    obtain ⟨c, hc⟩ := hdv ⟨x, (mem_integers_iff _).2 hx.le⟩ hx
    refine ⟨c, (mem_integers_iff _).1 c.2, ?_⟩
    have := congrArg Subtype.val hc
    rw [mul_comm]
    exact this
  have hroot : ∀ u : Fv F v, ‖u - 1‖ < 1 → ∃ z : Fv F v, z ^ 2 = u := by
    intro u hu
    refine PI.LocalEndW.henselRoot F v 2 u ?_ (Valued.toNormedField.norm_lt_one_iff.1 hu)
    have e : ((2 : ℕ) : Fv F v) = 2 := by norm_num
    rw [e]
    refine le_antisymm (Valued.toNormedField.norm_le_one_iff.1 h2.le) (not_lt.1 fun hlt => ?_)
    exact (Valued.toNormedField.norm_lt_one_iff.2 hlt).ne h2
  exact (isField_iff_not_sq hsq hind hsp).trans
    (isField_quot_iff_not_sq S hsq hind hsp hS hD h1 hdv' hroot hϖ).symm

end Main

end GlobalTheory.CompanionTheory.GunrInert

end
