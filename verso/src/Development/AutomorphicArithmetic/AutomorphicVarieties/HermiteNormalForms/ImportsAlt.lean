import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Mink3
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Stabfin

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
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
