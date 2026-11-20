import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

open KaehlerDifferential in

/- English proof (translation)
Introduce `k _ F _ _ d x hx I hI`. Use `set S : Set F := {y | ∃ i ∈ I, ∃ j, y = x j / x i} with hS`. Establish `hA : _root_.GlobalTheory.PD.rA k x I = Algebra.adjoin k S` using `rfl`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `IsFractionRing.of_field _ F fun z => ?_` and prove the remaining obligations.

Take `⟨i, hi⟩` from `hI`. Establish `hle : IntermediateField.adjoin k (Set.range fun j : Fin d => x j.succ / x 0) ≤ IntermediateField.adjoin k S`. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨j, rfl⟩`. Rewrite using `[SetLike.mem_coe, IntermediateField.mem_adjoin_iff_div]`.

Use `⟨x j.succ / x i, Algebra.subset_adjoin ⟨i, hi, j.succ, rfl⟩, x 0 / x i, Algebra.subset_adjoin ⟨i, hi, 0, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `h0` using `hx.ne 0`. Establish `hi0` using `hx.ne i`. Clear the denominators using the available nonvanishing facts. Establish `hz : z ∈ IntermediateField.adjoin k S`.

Apply `hle` to reduce the goal to its premises. Rewrite using `[hx.gen]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨r, hr, s, hs, rfl⟩` from `IntermediateField.mem_adjoin_iff_div.mp hz`. Conclude with `⟨⟨r, hr⟩, ⟨s, hs⟩, rfl⟩`.

Establish `hfin : S.Finite` using `(Set.finite_range fun q : Fin (d + 1) × Fin (d + 1) => x q.2 / x q.1).subset (by rintro _ ⟨i, -, j, rfl⟩; exact ⟨(i, j), rfl⟩)`. Establish `hfg : (_root_.GlobalTheory.PD.rA k x I).FG`. Rewrite using `[hA, ← hfin.coe_toFinset]`. Conclude with `Subalgebra.fg_adjoin_finset _`. Use `haveI := (Subalgebra.fg_iff_finiteType _).mp hfg`.

Conclude with `Algebra.FiniteType.isNoetherianRing k _`.
-/
theorem _root_.GlobalTheory.PD.rA_isFractionRing_isNoetherianRing : ∀ (k : Type) [Field k]
    (F : Type) [Field F] [Algebra k F] (d : ℕ)
    (x : Fin (d + 1) → F), _root_.GlobalTheory.PD.IsPd k x → ∀ I : Finset (Fin (d + 1)),
      I.Nonempty →
      IsFractionRing (_root_.GlobalTheory.PD.rA k x I) F ∧
        IsNoetherianRing (_root_.GlobalTheory.PD.rA k x I) := by
  intro k _ F _ _ d x hx I hI
  set S : Set F := {y | ∃ i ∈ I, ∃ j, y = x j / x i} with hS
  have hA : _root_.GlobalTheory.PD.rA k x I = Algebra.adjoin k S := rfl
  refine ⟨?_, ?_⟩
  · refine IsFractionRing.of_field _ F fun z => ?_
    obtain ⟨i, hi⟩ := hI
    have hle : IntermediateField.adjoin k (Set.range fun j : Fin d => x j.succ / x 0) ≤
        IntermediateField.adjoin k S := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, IntermediateField.mem_adjoin_iff_div]
      refine ⟨x j.succ / x i, Algebra.subset_adjoin ⟨i, hi, j.succ, rfl⟩,
        x 0 / x i, Algebra.subset_adjoin ⟨i, hi, 0, rfl⟩, ?_⟩
      have h0 := hx.ne 0
      have hi0 := hx.ne i
      field_simp
    have hz : z ∈ IntermediateField.adjoin k S := by
      apply hle
      rw [hx.gen]
      trivial
    obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
    exact ⟨⟨r, hr⟩, ⟨s, hs⟩, rfl⟩
  · have hfin : S.Finite :=
      (Set.finite_range fun q : Fin (d + 1) × Fin (d + 1) => x q.2 / x q.1).subset
        (by rintro _ ⟨i, -, j, rfl⟩; exact ⟨(i, j), rfl⟩)
    have hfg : (_root_.GlobalTheory.PD.rA k x I).FG := by
      rw [hA, ← hfin.coe_toFinset]
      exact Subalgebra.fg_adjoin_finset _
    haveI := (Subalgebra.fg_iff_finiteType _).mp hfg
    exact Algebra.FiniteType.isNoetherianRing k _

end GlobalTheory.PD
