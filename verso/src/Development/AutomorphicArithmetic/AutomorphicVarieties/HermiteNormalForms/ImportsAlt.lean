import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Mink3
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Stabfin

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

/- English proof (translation)
Introduce `L _ _ _ N p t`. Establish `hle : MulAction.stabilizer (Gm L N) t ≤ MulAction.stabilizer (Gm L N) (t.1 0)`. Introduce `g hg`. Rewrite `hg`, the goal using `[MulAction.mem_stabilizer_iff]`. Rewrite using `[← Sx.smul_val, hg]`.

Establish `hfin : Finite (MulAction.stabilizer (Gm L N) t)` using `by haveI := UpperTheory.V.KT.stabfin L N (t.1 0)`. Conclude with `Finite.of_injective _ (Subgroup.inclusion_injective hle)`. Establish `hrk : Module.finrank ℤ (Matrix (Fin N) (Fin N) (𝓞 L)) = dd L N * N`. Rewrite using `[Module.finrank_matrix, RingOfIntegers.rank]`. Simplify using `only [Fintype.card_fin, dd]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h` using `UpperTheory.V.KT.mink3 (Matrix (Fin N) (Fin N) (𝓞 L)) (MulAction.stabilizer (Gm L N) t) hfin`. Rewrite `h` using `[hrk]`. Conclude with `⟨hfin, h⟩`.
-/
theorem UpperTheory.V.KT.stab :
    ∀ (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N : ℕ) (p : ℕ),
    KH.StabLe (Gm L N) (Sx L N p) (3 ^ (dd L N * N)) := by
  intro L _ _ _ N p t
  have hle : MulAction.stabilizer (Gm L N) t ≤ MulAction.stabilizer (Gm L N) (t.1 0) := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    rw [← Sx.smul_val, hg]
  have hfin : Finite (MulAction.stabilizer (Gm L N) t) := by
    haveI := UpperTheory.V.KT.stabfin L N (t.1 0)
    exact Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have hrk : Module.finrank ℤ (Matrix (Fin N) (Fin N) (𝓞 L)) = dd L N * N := by
    rw [Module.finrank_matrix, RingOfIntegers.rank]
    simp only [Fintype.card_fin, dd]
    ring
  have h := UpperTheory.V.KT.mink3 (Matrix (Fin N) (Fin N) (𝓞 L))
    (MulAction.stabilizer (Gm L N) t) hfin
  rw [hrk] at h
  exact ⟨hfin, h⟩
