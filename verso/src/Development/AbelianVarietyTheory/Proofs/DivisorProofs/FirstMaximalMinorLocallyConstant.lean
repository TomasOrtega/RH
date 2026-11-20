import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply

open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

/- English proof (translation)
Introduce and unpack `⟨h0, hle⟩`. Establish `hm : valuation k (minor Y J) ≠ 0` using `(Valuation.ne_zero_iff _).2 h0`. Establish `hc : ∀ J' : Fin a ↪ Fin d, Continuous fun Y' : Matrix (Fin a) (Fin d) k => minor Y' J'` using `fun J' => (continuous_id.matrix_submatrix id J').matrix_det`. Establish `key : ∀ J' : Fin a ↪ Fin d, ∀ᶠ Y' in nhds Y, valuation k (minor Y' J') = valuation k (minor Y J') ∨ (minor Y J' = 0 ∧ valuation k (minor Y' J') < valuation k (minor Y J))`. Introduce `J'`.

Distinguish the cases in `hz : minor Y J' = 0`. Establish `hn : {x : k | valuation k x < ((Units.mk0 _ hm : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)} ∈ nhds (0 : k)` using `(IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨Units.mk0 _ hm, subset_rfl⟩`. Establish `hca` using `(hc J').continuousAt (x := Y)`. Rewrite `hca` using `[ContinuousAt, hz]`. Use `filter_upwards [hca hn] with Y' hY'`.

Conclude with `Or.inr ⟨hz, hY'⟩`. Establish `hne : valuation k (minor Y J') ≠ 0` using `(Valuation.ne_zero_iff _).2 hz filter_upwards [(hc J').continuousAt (x := Y) ((valuation k).locally_const hne)] with Y' hY'`. Conclude with `Or.inl hY'`. Establish `hall` using `Filter.eventually_all.2 key`. Use `filter_upwards [hall] with Y' hY'`.

Establish `hJ : valuation k (minor Y' J) = valuation k (minor Y J)`. Break down `hY' J with h | ⟨h, -⟩` into its components or cases. Conclude with `h`. Conclude with `absurd h h0`. Use `⟨(Valuation.ne_zero_iff _).1 (hJ ▸ hm), fun J' => ?_⟩` and prove the remaining obligations.

Rewrite using `[hJ]`. Break down `hY' J' with h | ⟨-, h⟩` into its components or cases. Rewrite using `[h]`. Conclude with `hle J'`. Conclude with `⟨h.le, fun _ => h⟩`.
-/
theorem isFirstMax_eventually (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d) :
    IsFirstMax Y J → ∀ᶠ Y' in nhds Y, IsFirstMax Y' J := by
  rintro ⟨h0, hle⟩
  have hm : valuation k (minor Y J) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have hc : ∀ J' : Fin a ↪ Fin d, Continuous fun Y' : Matrix (Fin a) (Fin d) k => minor Y' J' := fun J' =>
    (continuous_id.matrix_submatrix id J').matrix_det
  have key : ∀ J' : Fin a ↪ Fin d, ∀ᶠ Y' in nhds Y,
      valuation k (minor Y' J') = valuation k (minor Y J') ∨
        (minor Y J' = 0 ∧ valuation k (minor Y' J') < valuation k (minor Y J)) := by
    intro J'
    by_cases hz : minor Y J' = 0
    · have hn : {x : k | valuation k x < ((Units.mk0 _ hm : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)}
          ∈ nhds (0 : k) := (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨Units.mk0 _ hm, subset_rfl⟩
      have hca := (hc J').continuousAt (x := Y)
      rw [ContinuousAt, hz] at hca
      filter_upwards [hca hn] with Y' hY'
      exact Or.inr ⟨hz, hY'⟩
    · have hne : valuation k (minor Y J') ≠ 0 := (Valuation.ne_zero_iff _).2 hz
      filter_upwards [(hc J').continuousAt (x := Y) ((valuation k).locally_const hne)] with Y' hY'
      exact Or.inl hY'
  have hall := Filter.eventually_all.2 key
  filter_upwards [hall] with Y' hY'
  have hJ : valuation k (minor Y' J) = valuation k (minor Y J) := by
    rcases hY' J with h | ⟨h, -⟩
    · exact h
    · exact absurd h h0
  refine ⟨(Valuation.ne_zero_iff _).1 (hJ ▸ hm), fun J' => ?_⟩
  rw [hJ]
  rcases hY' J' with h | ⟨-, h⟩
  · rw [h]; exact hle J'
  · exact ⟨h.le, fun _ => h⟩

end GlobalTheory.RankFibreKer
