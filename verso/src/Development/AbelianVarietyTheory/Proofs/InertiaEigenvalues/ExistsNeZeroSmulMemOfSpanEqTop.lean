import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

namespace GlobalTheory.QuotientLatticeTorsion

/- English proof (translation)
Establish `hv : v ∈ Submodule.span K (N : Set V)` using `hN ▸ Submodule.mem_top`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨a, ha, hax⟩` from `hx`. Take `⟨b, hb, hby⟩` from `hy`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `N.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `N.smul_mem b hax`. Rewrite using `[mul_smul]`. Conclude with `N.smul_mem a hby`. Consider the case `smul c x _ hx`.

Take `⟨a, ha, hax⟩` from `hx`. Take `⟨⟨r, s⟩, hrs⟩` from `IsLocalization.surj (nonZeroDivisors O) c`. Use `⟨s.1 * a, mul_ne_zero (nonZeroDivisors.ne_zero s.2) ha, ?_⟩` and prove the remaining obligations. Establish `key : (s.1 * a) • c • x = r • a • x`. Rewrite using `[← algebraMap_smul K (s.1 * a), ← algebraMap_smul K r, ← algebraMap_smul K a x, smul_smul, smul_smul, ← hrs, map_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Conclude with `N.smul_mem r hax`.
-/
theorem exists_ne_zero_smul_mem_of_span_eq_top
    {O K V : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (N : Submodule O V) (hN : Submodule.span K (N : Set V) = ⊤) (v : V) :
    ∃ b : O, b ≠ 0 ∧ b • v ∈ N := by
  have hv : v ∈ Submodule.span K (N : Set V) := hN ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact N.smul_mem b hax
    · rw [mul_smul]
      exact N.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors O) c
    refine ⟨s.1 * a, mul_ne_zero (nonZeroDivisors.ne_zero s.2) ha, ?_⟩
    have key : (s.1 * a) • c • x = r • a • x := by
      rw [← algebraMap_smul K (s.1 * a), ← algebraMap_smul K r, ← algebraMap_smul K a x,
        smul_smul, smul_smul, ← hrs, map_mul]
      congr 1
      ring
    rw [key]
    exact N.smul_mem r hax

/- English proof (translation)
Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ w`. Take `⟨b, hb, hbv⟩` from `exists_ne_zero_smul_mem_of_span_eq_top (K := LL) T.L.T T.L.span v`. Use `⟨b, hb, ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `hbv`.
-/
theorem quotient_lattice_torsion
    {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] {LL : Type} [Field LL]
    [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL] [IsDomain O]
    [IsFractionRing O LL] (T : Formalism.BasicNotions.LocLat G Qp LL O)
    (w : Formalism.BasicNotions.LocLat.V T ⧸ Formalism.WeaklyAdmissibleFiltrations.Lattice.T (Formalism.BasicNotions.LocLat.L T)) :
    ∃ (b : O), b ≠ (0 : O) ∧
      b • w = (0 : Formalism.BasicNotions.LocLat.V T ⧸ Formalism.WeaklyAdmissibleFiltrations.Lattice.T (Formalism.BasicNotions.LocLat.L T)) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨b, hb, hbv⟩ :=
    exists_ne_zero_smul_mem_of_span_eq_top (K := LL) T.L.T T.L.span v
  refine ⟨b, hb, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact hbv

end GlobalTheory.QuotientLatticeTorsion
