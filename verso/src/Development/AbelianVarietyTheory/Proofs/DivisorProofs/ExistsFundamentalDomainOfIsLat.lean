import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff

namespace GlobalTheory.TorsionForm.FlatAcyc

/- English proof (translation)
Introduce `g M hM`. Take `⟨hd, hz⟩` from `hM`. Set `b` to `Module.Free.chooseBasis ℤ M`. Set `b'` to `Module.Basis.ofZLatticeBasis ℝ M b`. Establish `hspan : Submodule.span ℤ (Set.range b') = M` using `Module.Basis.ofZLatticeBasis_span ℝ M b`.

Use `⟨ZSpan.fundamentalDomain b', ZSpan.fundamentalDomain_measurableSet b', ZSpan.fundamentalDomain_isBounded b', ?_⟩` and prove the remaining obligations. Establish `h` using `ZSpan.isAddFundamentalDomain b' (volume : Measure (Fl g))`. Rewrite `h` using `[hspan]`. Conclude with `h`.
-/
theorem exists_fundamentalDomain_of_isLat : ∀ {g : ℕ} (M : Submodule ℤ (Fl g)), IsLat M →
    ∃ D : Set (Fl g), MeasurableSet D ∧ Bornology.IsBounded D ∧
      IsAddFundamentalDomain M.toAddSubgroup D volume := by
  intro g M hM
  obtain ⟨hd, hz⟩ := hM
  let b := Module.Free.chooseBasis ℤ M
  let b' := Module.Basis.ofZLatticeBasis ℝ M b
  have hspan : Submodule.span ℤ (Set.range b') = M := Module.Basis.ofZLatticeBasis_span ℝ M b
  refine ⟨ZSpan.fundamentalDomain b', ZSpan.fundamentalDomain_measurableSet b',
    ZSpan.fundamentalDomain_isBounded b', ?_⟩
  have h := ZSpan.isAddFundamentalDomain b' (volume : Measure (Fl g))
  rw [hspan] at h
  exact h

end GlobalTheory.TorsionForm.FlatAcyc
