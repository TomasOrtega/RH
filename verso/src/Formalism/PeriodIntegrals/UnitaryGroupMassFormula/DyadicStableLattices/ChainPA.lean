import Mathlib

noncomputable section

namespace PI.GoodTwo.ChainBetweenPairs

open Module

/- English proof (translation)
Establish `hd : DiscreteTopology S` using `DiscreteTopology.of_subset (inferInstance : DiscreteTopology L'.lattice) h2`. Establish `hs : IsZLattice ℝ S`. Use `⟨top_le_iff.mp ?_⟩` and prove the remaining obligations. Rewrite using `[← (inferInstance : IsZLattice ℝ L.lattice).span_top]`. Conclude with `Submodule.span_mono h1`.

Establish `: Module.Finite ℤ S` using `ZLattice.module_finite ℝ S`. Establish `hrank : finrank ℤ S = 2`. Rewrite using `[ZLattice.rank ℝ S, Complex.finrank_real_complex]`. Set `b : Module.Basis (Fin 2) ℤ S` to `Module.finBasisOfFinrankEq ℤ S hrank`. Use `⟨⟨b 0, b 1, ?_⟩, fun z => ?_⟩` and prove the remaining obligations.

Establish `hl` using `(b.ofZLatticeBasis ℝ S).linearIndependent`. Establish `heq : (![((b 0 : S) : ℂ), ((b 1 : S) : ℂ)] : Fin 2 → ℂ) = ⇑(b.ofZLatticeBasis ℝ S)`. Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> simp [Module.Basis.ofZLatticeBasis_apply]`. Rewrite using `[heq]`.

Conclude with `hl`. Establish `hset : ({((b 0 : S) : ℂ), ((b 1 : S) : ℂ)} : Set ℂ) = Set.range (b.ofZLatticeBasis ℝ S)`. Use extensionality with `x`. Simplify using `[Module.Basis.ofZLatticeBasis_apply, Fin.exists_fin_two, eq_comm]`. Use `show z ∈ Submodule.span ℤ {((b 0 : S) : ℂ), ((b 1 : S) : ℂ)} ↔ z ∈ S`.

Rewrite using `[hset, Module.Basis.ofZLatticeBasis_span]`.
-/
theorem exists_pair_of_between (L L' : PeriodPair) (S : Submodule ℤ ℂ)
    (h1 : L.lattice ≤ S) (h2 : S ≤ L'.lattice) :
    ∃ P : PeriodPair, ∀ z, z ∈ P.lattice ↔ z ∈ S := by
  classical
  have hd : DiscreteTopology S :=
    DiscreteTopology.of_subset (inferInstance : DiscreteTopology L'.lattice) h2
  have hs : IsZLattice ℝ S := by
    refine ⟨top_le_iff.mp ?_⟩
    rw [← (inferInstance : IsZLattice ℝ L.lattice).span_top]
    exact Submodule.span_mono h1
  have : Module.Finite ℤ S := ZLattice.module_finite ℝ S
  have hrank : finrank ℤ S = 2 := by
    rw [ZLattice.rank ℝ S, Complex.finrank_real_complex]
  let b : Module.Basis (Fin 2) ℤ S := Module.finBasisOfFinrankEq ℤ S hrank
  refine ⟨⟨b 0, b 1, ?_⟩, fun z => ?_⟩
  · have hl := (b.ofZLatticeBasis ℝ S).linearIndependent
    have heq : (![((b 0 : S) : ℂ), ((b 1 : S) : ℂ)] : Fin 2 → ℂ) = ⇑(b.ofZLatticeBasis ℝ S) := by
      ext i
      fin_cases i <;> simp [Module.Basis.ofZLatticeBasis_apply]
    rw [heq]
    exact hl
  · have hset : ({((b 0 : S) : ℂ), ((b 1 : S) : ℂ)} : Set ℂ) =
        Set.range (b.ofZLatticeBasis ℝ S) := by
      ext x
      simp [Module.Basis.ofZLatticeBasis_apply, Fin.exists_fin_two, eq_comm]
    show z ∈ Submodule.span ℤ {((b 0 : S) : ℂ), ((b 1 : S) : ℂ)} ↔ z ∈ S
    rw [hset, Module.Basis.ofZLatticeBasis_span]

end PI.GoodTwo.ChainBetweenPairs
