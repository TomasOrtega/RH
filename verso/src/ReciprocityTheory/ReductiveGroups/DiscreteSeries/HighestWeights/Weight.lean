import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.SingleMulJmComm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HasDerivAtRealOfComplex
import Formalism.RealPlaceAnalysis.QuotientSettingHolds

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a => T.w_wt a, fun a b hab he => T.w_hw a b hab he⟩`.
-/
theorem KType.kHighest_w {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Formalism.REAL.KHighest ε (kunits T) Λ T.w := ⟨fun a => T.w_wt a, fun a b hab he => T.w_hw a b hab he⟩

/- English proof (translation)
Introduce `h`. Establish `h1` using `T.w_norm`. Rewrite `h1` using `[h, norm_zero]`. Conclude with `zero_ne_one h1`.
-/
theorem KType.w_ne_zero {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : T.w ≠ 0 := by
  intro h
  have h1 := T.w_norm
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

/- English proof (translation)
Break down `KType.dτ_irred T (Formalism.REAL.kSpan ε (kunits T) T.w) (fun a b hab v hv => Formalism.REAL.compact_span_stable T.w a b hab v hv) with h | h` into its components or cases. It suffices to derive a contradiction. Establish `hw` using `Formalism.REAL.mem_compact_span_self (ε := ε) (F := kunits T) T.w`. Rewrite `hw` using `[h, Submodule.mem_bot]`. Conclude with `(KType.w_ne_zero T) hw`.

Conclude with `h`.
-/
theorem KType.kSpan_eq_top {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Formalism.REAL.kSpan ε (kunits T) T.w = ⊤ := by
  rcases KType.dτ_irred T (Formalism.REAL.kSpan ε (kunits T) T.w)
    (fun a b hab v hv => Formalism.REAL.compact_span_stable T.w a b hab v hv) with h | h
  · exfalso
    have hw := Formalism.REAL.mem_compact_span_self (ε := ε) (F := kunits T) T.w
    rw [h, Submodule.mem_bot] at hw
    exact (KType.w_ne_zero T) hw
  · exact h

/- English proof (translation)
Establish `hmem : v ∈ Formalism.REAL.kSpan ε (kunits T) T.w` using `by rw [KType.kSpan_eq_top T]; trivial`. Break down `Formalism.REAL.kHiUniq T.V n ε (kunits T) Λ ν T.w v (KType.kRel T) (KType.kUnit T) (KType.kHighest_w T) hmem h with h0 | h1` into its components or cases. Conclude with `absurd h0 hv`. Conclude with `h1`.
-/
theorem KType.hw_unique {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {ν : Fin n → ℝ} {v : T.V}
    (hv : v ≠ 0) (h : IsKHWVec ε (kunits T) ν v) : ν = Λ ∧ ∃ c : ℂ, v = c • T.w := by
  have hmem : v ∈ Formalism.REAL.kSpan ε (kunits T) T.w := by rw [KType.kSpan_eq_top T]; trivial
  rcases Formalism.REAL.kHiUniq T.V n ε (kunits T) Λ ν T.w v (KType.kRel T) (KType.kUnit T) (KType.kHighest_w T) hmem h with h0 | h1
  · exact absurd h0 hv
  · exact h1

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact ⟨fun _ _ => 0, fun a b h => absurd rfl h, by simp [Formalism.REAL.wordWeightShift]⟩`. Consider the case `cons p w ih`. Take `⟨c, hc, heq⟩` from `ih`. Use `⟨fun a b => c a b + if a = p.2 ∧ b = p.1 then 1 else 0, ?_, ?_⟩` and prove the remaining obligations.

Introduce `a b hab`. Express the relevant statement in the definitionally equal form `c a b + (if a = p.2 ∧ b = p.1 then 1 else 0) ≠ 0 at hab`. Distinguish the cases in `h : c a b = 0`. Rewrite `hab`, `with`, `h2` using `[h, zero_add] at hab split_ifs`. Take `⟨rfl, rfl⟩` from `h2`.

Simplify using the standard rewrite rules. Conclude with `absurd rfl hab`. Conclude with `List.mem_cons_of_mem _ (hc a b h)`. Establish `hs : ∑ a, ∑ b, (((if a = p.2 ∧ b = p.1 then 1 else 0 : ℕ)) : ℝ) • root a b = root p.2 p.1`. Rewrite using `[Finset.sum_eq_single p.2, Finset.sum_eq_single p.1]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[hb]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Introduce `a _ ha`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Simplify using `[ha]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Establish `e : ∀ a b, (((c a b + if a = p.2 ∧ b = p.1 then 1 else 0 : ℕ)) : ℝ) • root a b = (c a b : ℝ) • root a b + (((if a = p.2 ∧ b = p.1 then 1 else 0 : ℕ)) : ℝ) • root a b` using `fun a b => by rw [Nat.cast_add, add_smul]`. Simplify using `only [e, Finset.sum_add_distrib, hs, ← heq]`. Simplify using `only [Formalism.REAL.wordWeightShift, root]`. Normalize the expressions using the abelian group laws.
-/
theorem wtw_eq_sum (w : List (Fin n × Fin n)) :
    ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → (b, a) ∈ w) ∧
      -Formalism.REAL.wordWeightShift w = ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  induction w with
  | nil => exact ⟨fun _ _ => 0, fun a b h => absurd rfl h, by simp [Formalism.REAL.wordWeightShift]⟩
  | cons p w ih =>
    obtain ⟨c, hc, heq⟩ := ih
    refine ⟨fun a b => c a b + if a = p.2 ∧ b = p.1 then 1 else 0, ?_, ?_⟩
    · intro a b hab
      change c a b + (if a = p.2 ∧ b = p.1 then 1 else 0) ≠ 0 at hab
      by_cases h : c a b = 0
      · rw [h, zero_add] at hab
        split_ifs at hab with h2
        · obtain ⟨rfl, rfl⟩ := h2
          simp
        · exact absurd rfl hab
      · exact List.mem_cons_of_mem _ (hc a b h)
    · have hs : ∑ a, ∑ b, (((if a = p.2 ∧ b = p.1 then 1 else 0 : ℕ)) : ℝ) • root a b = root p.2 p.1 := by
        rw [Finset.sum_eq_single p.2, Finset.sum_eq_single p.1]
        · simp
        · intro b _ hb
          simp [hb]
        · intro h
          exact absurd (Finset.mem_univ _) h
        · intro a _ ha
          apply Finset.sum_eq_zero
          intro b _
          simp [ha]
        · intro h
          exact absurd (Finset.mem_univ _) h
      have e : ∀ a b, (((c a b + if a = p.2 ∧ b = p.1 then 1 else 0 : ℕ)) : ℝ) • root a b =
          (c a b : ℝ) • root a b + (((if a = p.2 ∧ b = p.1 then 1 else 0 : ℕ)) : ℝ) • root a b :=
        fun a b => by rw [Nat.cast_add, add_smul]
      simp only [e, Finset.sum_add_distrib, hs, ← heq]
      simp only [Formalism.REAL.wordWeightShift, root]
      abel

/- English proof (translation)
Establish `hmem : v ∈ Formalism.REAL.lowSpan ε (kunits T) T.w`. Rewrite using `[← Formalism.REAL.compact_span_eq_lowering (KType.kRel T) (KType.kHighest_w T), KType.kSpan_eq_top T]`. Discharge the goal by the elementary cases of `trivial`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw, hwμ⟩ : ∃ w : List (Fin n × Fin n), (∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) ∧ Λ + Formalism.REAL.wordWeightShift w = μ := by`. Assume the negation of the conclusion as `hne`.

Use `push Not at hne`. Apply `hv` to reduce the goal to its premises. Establish `horth : ∀ y ∈ Formalism.REAL.lowSpan ε (kunits T) T.w, inner ℂ v y = 0`. Introduce `y hy`. Use `Submodule.span_induction ?_ ?_ ?_ ?_ hy` and prove the remaining obligations.

Introduce and unpack `z ⟨w, hw, rfl⟩`. Establish `hwt` using `Formalism.REAL.word_action_weight (KType.kRel T) (KType.kHighest_w T).1 w (fun q hq => (hw q hq).1)`. Conclude with `Formalism.REAL.kWtOrth T.V n ε (kunits T) μ _ v _ (KType.kUnit T) (fun a => hμ a) hwt (fun h => hne w hw h.symm)`. Simplify using the standard rewrite rules. Introduce `x y _ _ hx hy`.

Rewrite using `[inner_add_right, hx, hy, add_zero]`. Introduce `a x _ hx`. Rewrite using `[inner_smul_right, hx, mul_zero]`. Conclude with `inner_self_eq_zero.mp (horth v hmem)`. Take `⟨c, hc, he⟩` from `wtw_eq_sum (n := n) w`.

Use `⟨c, fun a b hab => ?_, ?_⟩` and prove the remaining obligations. Use `hw _ (hc a b hab)` as an intermediate fact. Conclude with `⟨this.2, this.1.symm⟩`. Rewrite using `[← he, ← hwμ]`. Normalize the expressions using the abelian group laws.
-/
theorem KType.weight_le {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {μ : Fin n → ℝ} {v : T.V}
    (hv : v ≠ 0) (hμ : ∀ a, T.dτ (Matrix.single a a 1) v = ((μ a : ℝ) : ℂ) • v) :
    ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → a < b ∧ ε a = ε b) ∧
      Λ - μ = ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  have hmem : v ∈ Formalism.REAL.lowSpan ε (kunits T) T.w := by
    rw [← Formalism.REAL.compact_span_eq_lowering (KType.kRel T) (KType.kHighest_w T), KType.kSpan_eq_top T]; trivial
  obtain ⟨w, hw, hwμ⟩ : ∃ w : List (Fin n × Fin n), (∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) ∧
      Λ + Formalism.REAL.wordWeightShift w = μ := by
    by_contra hne
    push Not at hne
    apply hv
    have horth : ∀ y ∈ Formalism.REAL.lowSpan ε (kunits T) T.w, inner ℂ v y = 0 := by
      intro y hy
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro z ⟨w, hw, rfl⟩
        have hwt := Formalism.REAL.word_action_weight (KType.kRel T) (KType.kHighest_w T).1 w (fun q hq => (hw q hq).1)
        exact Formalism.REAL.kWtOrth T.V n ε (kunits T) μ _ v _ (KType.kUnit T) (fun a => hμ a) hwt
          (fun h => hne w hw h.symm)
      · simp
      · intro x y _ _ hx hy; rw [inner_add_right, hx, hy, add_zero]
      · intro a x _ hx; rw [inner_smul_right, hx, mul_zero]
    exact inner_self_eq_zero.mp (horth v hmem)
  obtain ⟨c, hc, he⟩ := wtw_eq_sum (n := n) w
  refine ⟨c, fun a b hab => ?_, ?_⟩
  · have := hw _ (hc a b hab)
    exact ⟨this.2, this.1.symm⟩
  · rw [← he, ← hwμ]; abel

end ReciprocityTheory.ChartRestriction.DS.HW
