import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatConvolutionLocalFieldPower
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

namespace GlobalTheory

/- English proof (translation)
Introduce `x hx i _` and use `show valuation k (x i) ≤ _ from le_trans (hx i trivial) h`.
-/
theorem box_subset_box_of_valuation_le {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) {s t : kˣ}
    (h : valuation k (s : k) ≤ valuation k (t : k)) : box n s ⊆ box n t :=
  fun x hx i _ => show valuation k (x i) ≤ _ from le_trans (hx i trivial) h

/- English proof (translation)
Introduce `hK r`. Set `ι` to `{s : kˣ // valuation k (r : k) ≤ valuation k (s : k)}`. Use `haveI : Nonempty ι := ⟨⟨r, le_rfl⟩⟩`. Establish `hcov : K ⊆ ⋃ s : ι, box n (s : kˣ)`. Introduce `x _`.

Rewrite using `[Set.mem_iUnion]`. Distinguish the cases in `hn : Nonempty n`. Take `⟨i0, -, hi0⟩` from `Finset.exists_max_image Finset.univ (fun i => valuation k (x i)) Finset.univ_nonempty`. Distinguish the cases in `hle : valuation k (x i0) ≤ valuation k (r : k)`. Use `⟨⟨r, le_rfl⟩, fun i _ => ?_⟩` and prove the remaining obligations.

Conclude with `le_trans (hi0 i (Finset.mem_univ i)) hle`. Use `push_neg at hle`. Establish `hx0 : x i0 ≠ 0`. Introduce `h0`. Rewrite `hle` using `[h0, map_zero]`.

Conclude with `not_lt_zero' hle`. Use `⟨⟨Units.mk0 (x i0) hx0, by simpa using hle.le⟩, fun i _ => ?_⟩` and prove the remaining obligations. Simplify `hi0 i (Finset.mem_univ i)` using `[cball]`. Use `⟨⟨r, le_rfl⟩, fun i _ => (hn ⟨i⟩).elim⟩` and prove the remaining obligations. Establish `hdir : Directed (· ⊆ ·) (fun s : ι => box n (s : kˣ))`.

Introduce `s t`. Break down `le_total (valuation k ((s : kˣ) : k)) (valuation k ((t : kˣ) : k)) with h | h` into its components or cases. Conclude with `⟨t, box_subset_box_of_valuation_le n h, le_rfl⟩`. Conclude with `⟨s, le_rfl, box_subset_box_of_valuation_le n h⟩`. Take `⟨s, hs⟩` from `hK.elim_directed_cover (fun s : ι => box n (s : kˣ)) (fun s => isOpen_box _) hcov hdir`.

Conclude with `⟨s, s.2, hs⟩`.
-/
theorem exists_box_superset_of_isCompact (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (K : Set (n → k)) :
    IsCompact K → ∀ r : kˣ, ∃ R : kˣ, valuation k (r : k) ≤ valuation k (R : k) ∧ K ⊆ box n R := by
  intro hK r
  let ι := {s : kˣ // valuation k (r : k) ≤ valuation k (s : k)}
  haveI : Nonempty ι := ⟨⟨r, le_rfl⟩⟩
  have hcov : K ⊆ ⋃ s : ι, box n (s : kˣ) := by
    intro x _
    rw [Set.mem_iUnion]
    by_cases hn : Nonempty n
    · obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun i => valuation k (x i))
        Finset.univ_nonempty
      by_cases hle : valuation k (x i0) ≤ valuation k (r : k)
      · refine ⟨⟨r, le_rfl⟩, fun i _ => ?_⟩
        exact le_trans (hi0 i (Finset.mem_univ i)) hle
      · push_neg at hle
        have hx0 : x i0 ≠ 0 := by
          intro h0
          rw [h0, map_zero] at hle
          exact not_lt_zero' hle
        refine ⟨⟨Units.mk0 (x i0) hx0, by simpa using hle.le⟩, fun i _ => ?_⟩
        simpa [cball] using hi0 i (Finset.mem_univ i)
    · refine ⟨⟨r, le_rfl⟩, fun i _ => (hn ⟨i⟩).elim⟩
  have hdir : Directed (· ⊆ ·) (fun s : ι => box n (s : kˣ)) := by
    intro s t
    rcases le_total (valuation k ((s : kˣ) : k)) (valuation k ((t : kˣ) : k)) with h | h
    · exact ⟨t, box_subset_box_of_valuation_le n h, le_rfl⟩
    · exact ⟨s, le_rfl, box_subset_box_of_valuation_le n h⟩
  obtain ⟨s, hs⟩ := hK.elim_directed_cover (fun s : ι => box n (s : kˣ))
    (fun s => isOpen_box _) hcov hdir
  exact ⟨s, s.2, hs⟩

end GlobalTheory
