import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

/- English proof (translation)
Introduce `K W _ _ _ S n b`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hli, hspan⟩`. Use `⟨fun i => hspan ▸ Submodule.subset_span ⟨i, rfl⟩, fun e he => ?_⟩` and prove the remaining obligations. Rewrite `he` using `[← hspan, Submodule.mem_span_range_iff_exists_fun]`.

Take `⟨x, hx⟩` from `he`. Use `⟨x, hx.symm, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h0 : ∑ i, (y - x) i • b i = 0`. Simplify using `only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, ← hy, hx, sub_self]`. Use function extensionality and compare the values at `i`.

Conclude with `sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 i)`. Introduce and unpack `⟨hb, huniq⟩`. Use `⟨Fintype.linearIndependent_iff.mpr fun g hg i => ?_, le_antisymm ?_ fun e he => ?_⟩` and prove the remaining obligations. Take `⟨x, _, hx⟩` from `huniq 0 S.zero_mem`. Establish `hg0 : g = x` using `hx g hg.symm`.

Establish `h00 : (0 : Fin n → K) = x` using `hx 0 (by simp)`. Rewrite using `[hg0, ← h00]`. Both sides reduce to the same expression. Conclude with `Submodule.span_le.mpr (Set.range_subset_iff.mpr hb)`. Take `⟨x, hx, _⟩` from `huniq e he`.

Rewrite using `[hx]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem basis_iff_unique_combinations : ∀ (K W : Type) [Field K] [AddCommGroup W] [Module K W] (S : Submodule K W) (n : ℕ) (b : Fin n → W),
    (LinearIndependent K b ∧ Submodule.span K (Set.range b) = S) ↔
      (∀ i, b i ∈ S) ∧ ∀ e ∈ S, ∃! x : Fin n → K, e = ∑ i, x i • b i := by
  intro K W _ _ _ S n b
  constructor
  · rintro ⟨hli, hspan⟩
    refine ⟨fun i => hspan ▸ Submodule.subset_span ⟨i, rfl⟩, fun e he => ?_⟩
    rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at he
    obtain ⟨x, hx⟩ := he
    refine ⟨x, hx.symm, fun y hy => ?_⟩
    have h0 : ∑ i, (y - x) i • b i = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, ← hy, hx, sub_self]
    funext i
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 i)
  · rintro ⟨hb, huniq⟩
    refine ⟨Fintype.linearIndependent_iff.mpr fun g hg i => ?_, le_antisymm ?_ fun e he => ?_⟩
    · obtain ⟨x, _, hx⟩ := huniq 0 S.zero_mem
      have hg0 : g = x := hx g hg.symm
      have h00 : (0 : Fin n → K) = x := hx 0 (by simp)
      rw [hg0, ← h00]
      rfl
    · exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hb)
    · obtain ⟨x, hx, _⟩ := huniq e he
      rw [hx]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
