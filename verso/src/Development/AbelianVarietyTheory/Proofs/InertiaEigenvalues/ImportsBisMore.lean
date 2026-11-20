import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK

namespace GlobalTheory.NonzeroScalarLattice

/- English proof (translation)
Establish `hw : w ∈ Submodule.span LL (L.T : Set V)`. Rewrite using `[L.span]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`.

Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, hax⟩` from `hx`. Take `⟨b, hb, hby⟩` from `hy`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_add]`. Use `L.T.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `L.T.smul_mem _ hax`. Rewrite using `[mul_smul]`.

Conclude with `L.T.smul_mem _ hby`. Consider the case `smul c x _ hx`. Take `⟨a, ha, hax⟩` from `hx`. Take `⟨p, q, hq, rfl⟩` from `IsFractionRing.div_surjective (A := O) c`. Establish `hq0 : q ≠ 0` using `nonZeroDivisors.ne_zero hq`.

Establish `hq1 : algebraMap O LL q ≠ 0`. Introduce `h`. Conclude with `hq0 (IsFractionRing.injective O LL (by rw [h, map_zero]))`. Use `⟨a * q, mul_ne_zero ha hq0, ?_⟩` and prove the remaining obligations. Establish `h1 : q • ((algebraMap O LL p / algebraMap O LL q) • x) = p • x`.

Rewrite using `[← algebraMap_smul LL q, smul_smul, mul_div_cancel₀ _ hq1, algebraMap_smul]`. Rewrite using `[mul_smul, h1, smul_comm]`. Conclude with `L.T.smul_mem _ hax`.
-/
theorem exists_ne_zero_smul_mem {G : Type} [Group G] {LL : Type} [Field LL] {O : Type}
    [CommRing O] [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] {ρ : Representation LL G V} [IsDomain O] [IsFractionRing O LL]
    (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (w : V) :
    ∃ (b : O), b ≠ (0 : O) ∧ b • w ∈ Formalism.WeaklyAdmissibleFiltrations.Lattice.T L := by
  have hw : w ∈ Submodule.span LL (L.T : Set V) := by
    rw [L.span]; exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.T.smul_mem _ hax
    · rw [mul_smul]; exact L.T.smul_mem _ hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := O) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap O LL q ≠ 0 := by
      intro h
      exact hq0 (IsFractionRing.injective O LL (by rw [h, map_zero]))
    refine ⟨a * q, mul_ne_zero ha hq0, ?_⟩
    have h1 : q • ((algebraMap O LL p / algebraMap O LL q) • x) = p • x := by
      rw [← algebraMap_smul LL q, smul_smul, mul_div_cancel₀ _ hq1, algebraMap_smul]
    rw [mul_smul, h1, smul_comm]
    exact L.T.smul_mem _ hax

end GlobalTheory.NonzeroScalarLattice
