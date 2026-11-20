import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.TmETmapSmooth

noncomputable section

open Matrix MeasureTheory
open scoped ContDiff InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

/- English proof (translation)
Distinguish the cases in `hpq : pOf ε ≤ qOf ε`. Use `⟨true, ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.card_subtype]`. Use `show _ = min (pOf ε) (qOf ε)`. Rewrite using `[min_eq_left hpq]`.

Both sides reduce to the same expression. Use `⟨false, ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.card_subtype]`. Use `show _ = min (pOf ε) (qOf ε)`. Rewrite using `[min_eq_right (le_of_not_ge hpq)]`.

Both sides reduce to the same expression.
-/
theorem tmG_card (n : ℕ) (ε : Fin n → Bool) : ∃ s : Bool, Fintype.card (S7.SgIxV ε s) = S7.q0 ε := by
  by_cases hpq : pOf ε ≤ qOf ε
  · refine ⟨true, ?_⟩
    rw [Fintype.card_subtype]
    show _ = min (pOf ε) (qOf ε)
    rw [min_eq_left hpq]
    rfl
  · refine ⟨false, ?_⟩
    rw [Fintype.card_subtype]
    show _ = min (pOf ε) (qOf ε)
    rw [min_eq_right (le_of_not_ge hpq)]
    rfl

/- English proof (translation)
Introduce `k r ε lam h H _ _ _ σ D E V T μ ι hσ hD _ _ _ hμ hcoef hp hq hgap hHC hGap x₁ x₀ w hx₀ f hf`. Take `⟨hq0, hneed⟩` from `gapNeed k r ε h hp hq hgap`. Establish `hdd` using `ReciprocityTheory.ChartRestriction.DS.Lap.S0.DecDeriv.decDeriv _ ε lam h T μ hHC hGap hneed hq0 hμ`. Establish `hmq : (min (pOf ε : ℝ) (qOf ε : ℝ)) = (S7.q0 ε : ℝ)`. Rewrite using `[S7.q0, Nat.cast_min]`.

Establish `hg1` using `hgap.1`. Establish `hg2` using `hgap.2`. Rewrite `hg2` using `[hmq]`. Establish `hh0 : 0 ≤ h`. Establish `: 0 ≤ 3 * ((2 * r + k + 1 : ℕ) : ℝ) / 2` using `by positivity`.

Use `le_max_left (3 * ((2 * r + k + 1 : ℕ) : ℝ) / 2) (1 + ((2 * r + k + 1 : ℕ) : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ha0 : 0 ≤ aExp ε h` using `div_nonneg hh0 (by positivity)`. Establish `hA : aExp ε h = h / (8 * Real.sqrt (2 * (S7.q0 ε : ℝ)))` using `rfl`. Establish `hgood : ∀ m : D, m ∈ genSub E V → TmGood ε σ x₀ ((w : D) : H) (aExp ε h) (m : H)` using `fun m hm => tmC_good_genSub hσ hD hμ hcoef ha0 (fun wd v₁ v₂ => hdd wd v₁ v₂) hx₀ w hm`.

Establish `hword` using `tmE_eword_tmap hσ hD hx₀ x₁ ((w : D) : H) hgood f hf`. Establish `hbd : ∀ wd : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)), ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ UJset ε, ‖Formalism.REAL.Eword ε wd (tMap ε σ x₁ x₀ ((w : D) : H) (fun c => ((f c : D) : H))) g‖ ≤ C * frob g ^ (1 - aExp ε h)`. Introduce `wd`. Take `⟨C, hC0, hC⟩` from `tmE_tmap_bound x₁ ((w : D) : H) hgood (tmTw E wd f) (tmE_tmTw_mem f hf wd)`. Conclude with `⟨C, hC0, fun g hg => by rw [hword wd g hg]; exact hC g hg⟩`.

Establish `hsm : Formalism.REAL.SmoothOnG ε (tMap ε σ x₁ x₀ ((w : D) : H) (fun c => ((f c : D) : H)))` using `tmE_tmap_smooth x₁ x₀ _ _ fun c => (hgood _ (hf c)).1`. Use `⟨⟨hsm, fun wd => ?_⟩, fun a b g hg => tmE_eab_tmap hσ hD hx₀ x₁ _ f (fun c => (hgood _ (hf c)).1) a b hg, fun wd => ?_⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `tmG_card _ ε`. Take `⟨C, _, hC⟩` from `hbd wd`. Use `tmF_memLp (Formalism.REAL.smooth_iterated_lie_derivative hsm wd) s ?_ 0 (fun g hg => hC g hg)` and prove the remaining obligations.

Rewrite using `[hs]`. Establish `: 0 ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ)` using `by positivity`. Use `le_max_left (2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ)) (2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2)` as an intermediate fact. Rewrite `hg2` using `[← hA]`. Move the coercions through the operations in `at *`.

Use the polynomial consequences of the given equalities and inequalities. Take `⟨C, _, hC⟩` from `hbd wd`. Conclude with `⟨C, hC⟩`.
-/
theorem tMap_spec : TMapStatement := by
  intro k r ε lam h H _ _ _ σ D E V T μ ι hσ hD _ _ _ hμ hcoef hp hq hgap hHC hGap x₁ x₀ w hx₀ f hf
  obtain ⟨hq0, hneed⟩ := gapNeed k r ε h hp hq hgap
  have hdd := ReciprocityTheory.ChartRestriction.DS.Lap.S0.DecDeriv.decDeriv _ ε lam h T μ hHC hGap hneed hq0 hμ
  have hmq : (min (pOf ε : ℝ) (qOf ε : ℝ)) = (S7.q0 ε : ℝ) := by
    rw [S7.q0, Nat.cast_min]
  have hg1 := hgap.1
  have hg2 := hgap.2
  rw [hmq] at hg2
  have hh0 : 0 ≤ h := by
    have : 0 ≤ 3 * ((2 * r + k + 1 : ℕ) : ℝ) / 2 := by positivity
    have := le_max_left (3 * ((2 * r + k + 1 : ℕ) : ℝ) / 2)
      (1 + ((2 * r + k + 1 : ℕ) : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))
    linarith
  have ha0 : 0 ≤ aExp ε h := div_nonneg hh0 (by positivity)
  have hA : aExp ε h = h / (8 * Real.sqrt (2 * (S7.q0 ε : ℝ))) := rfl
  have hgood : ∀ m : D, m ∈ genSub E V → TmGood ε σ x₀ ((w : D) : H) (aExp ε h) (m : H) :=
    fun m hm => tmC_good_genSub hσ hD hμ hcoef ha0 (fun wd v₁ v₂ => hdd wd v₁ v₂) hx₀ w hm
  have hword := tmE_eword_tmap hσ hD hx₀ x₁ ((w : D) : H) hgood f hf
  have hbd : ∀ wd : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)), ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ UJset ε,
      ‖Formalism.REAL.Eword ε wd (tMap ε σ x₁ x₀ ((w : D) : H) (fun c => ((f c : D) : H))) g‖ ≤
        C * frob g ^ (1 - aExp ε h) := by
    intro wd
    obtain ⟨C, hC0, hC⟩ := tmE_tmap_bound x₁ ((w : D) : H) hgood (tmTw E wd f) (tmE_tmTw_mem f hf wd)
    exact ⟨C, hC0, fun g hg => by rw [hword wd g hg]; exact hC g hg⟩
  have hsm : Formalism.REAL.SmoothOnG ε (tMap ε σ x₁ x₀ ((w : D) : H) (fun c => ((f c : D) : H))) :=
    tmE_tmap_smooth x₁ x₀ _ _ fun c => (hgood _ (hf c)).1
  refine ⟨⟨hsm, fun wd => ?_⟩, fun a b g hg => tmE_eab_tmap hσ hD hx₀ x₁ _ f
    (fun c => (hgood _ (hf c)).1) a b hg, fun wd => ?_⟩
  · obtain ⟨s, hs⟩ := tmG_card _ ε
    obtain ⟨C, _, hC⟩ := hbd wd
    refine tmF_memLp (Formalism.REAL.smooth_iterated_lie_derivative hsm wd) s ?_ 0 (fun g hg => hC g hg)
    rw [hs]
    have : 0 ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) := by positivity
    have := le_max_left (2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ)) (2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2)
    rw [← hA] at hg2
    push_cast at *
    nlinarith
  · obtain ⟨C, _, hC⟩ := hbd wd
    exact ⟨C, hC⟩

end ReciprocityTheory.ChartRestriction.DS.Lap
