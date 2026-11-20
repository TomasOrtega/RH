import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartLatRank
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDenominator
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

/- English proof (translation)
Introduce `c hc`. Establish `hle : chartRingZ y c ≤ (chartRingQ y c).restrictScalars ℤ` using `Algebra.adjoin_le (Algebra.subset_adjoin (R := ℚ))`. Conclude with `hle (hs c hc)`.
-/
theorem chartLat_subset_chartLatQ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) {s : Ω} (hs : s ∈ chartLat y a n) :
    s ∈ chartLatQ y a n := by
  intro c hc
  have hle : chartRingZ y c ≤ (chartRingQ y c).restrictScalars ℤ :=
    Algebra.adjoin_le (Algebra.subset_adjoin (R := ℚ))
  exact hle (hs c hc)

/- English proof (translation)
Introduce `K _ ι _ Ω _ _ y a n hy`. Use `set M := AddSubgroup.toIntSubmodule (chartLat y a n) with hM`. Establish `hfg : M.FG` using `(Submodule.fg_iff_addSubgroup_fg M).mpr (hfin K ι Ω y a n hy)`. Establish `: Module.Finite ℤ M` using `Module.Finite.iff_fg.mpr hfg`. Take `⟨r, b⟩` from `Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := M)`.

Use `set v : Fin r → Ω := fun i => ((b i : M) : Ω) with hv`. Establish `hvZ : LinearIndependent ℤ v` using `b.linearIndependent.map' M.subtype M.ker_subtype`. Establish `hvQ : LinearIndependent ℚ v` using `(LinearIndependent.iff_fractionRing ℤ ℚ).mp hvZ`. Establish `hspan : Submodule.span ℚ (Set.range v) = chartLatQ y a n`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `chartLat_subset_chartLatQ y a n (b i).2`. Introduce `s hs`. Take `⟨N, hN, hNs⟩` from `ChartDenominator.proof K ι Ω y a n s hs`.

Establish `hmemM : (⟨(N : Ω) * s, hNs⟩ : M) ∈ Submodule.span ℤ (Set.range b)` using `b.mem_span _`. Establish `hmemZ : (N : Ω) * s ∈ Submodule.span ℤ (Set.range v)`. Establish `h` using `Submodule.mem_map_of_mem (f := M.subtype) hmemM`. Rewrite `h` using `[Submodule.map_span, ← Set.range_comp]`. Conclude with `h`.

Establish `hmemQ : (N : Ω) * s ∈ Submodule.span ℚ (Set.range v)` using `Submodule.span_le_restrictScalars ℤ ℚ _ hmemZ`. Establish `hN0 : (N : Ω) ≠ 0` using `by exact_mod_cast (show N ≠ 0 by omega)`. Establish `hs' : s = ((N : ℚ)⁻¹) • ((N : Ω) * s)`. Rewrite using `[Rat.smul_def]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hs']`. Conclude with `Submodule.smul_mem _ _ hmemQ`. Rewrite using `[Module.finrank_eq_card_basis b, ← hspan, finrank_span_eq_card hvQ]`.
-/
theorem ChartLatRank.proof (hfin : SectionLatticeFinite.Statement) : ChartLatRank.Statement := by
  intro K _ ι _ Ω _ _ y a n hy
  classical
  set M := AddSubgroup.toIntSubmodule (chartLat y a n) with hM
  have hfg : M.FG := (Submodule.fg_iff_addSubgroup_fg M).mpr (hfin K ι Ω y a n hy)
  have : Module.Finite ℤ M := Module.Finite.iff_fg.mpr hfg
  obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := M)
  set v : Fin r → Ω := fun i => ((b i : M) : Ω) with hv
  have hvZ : LinearIndependent ℤ v := b.linearIndependent.map' M.subtype M.ker_subtype
  have hvQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hvZ
  have hspan : Submodule.span ℚ (Set.range v) = chartLatQ y a n := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact chartLat_subset_chartLatQ y a n (b i).2
    · intro s hs
      obtain ⟨N, hN, hNs⟩ := ChartDenominator.proof K ι Ω y a n s hs
      have hmemM : (⟨(N : Ω) * s, hNs⟩ : M) ∈ Submodule.span ℤ (Set.range b) := b.mem_span _
      have hmemZ : (N : Ω) * s ∈ Submodule.span ℤ (Set.range v) := by
        have h := Submodule.mem_map_of_mem (f := M.subtype) hmemM
        rw [Submodule.map_span, ← Set.range_comp] at h
        exact h
      have hmemQ : (N : Ω) * s ∈ Submodule.span ℚ (Set.range v) :=
        Submodule.span_le_restrictScalars ℤ ℚ _ hmemZ
      have hN0 : (N : Ω) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      have hs' : s = ((N : ℚ)⁻¹) • ((N : Ω) * s) := by
        rw [Rat.smul_def]
        push_cast
        field_simp
      rw [hs']
      exact Submodule.smul_mem _ _ hmemQ
  rw [Module.finrank_eq_card_basis b, ← hspan, finrank_span_eq_card hvQ]

end GroundTheory.Heights₂.Heights.HilbertSamuel
