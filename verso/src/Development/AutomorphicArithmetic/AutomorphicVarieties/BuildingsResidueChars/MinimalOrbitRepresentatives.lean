import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Exbasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.DetPull
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Hnf
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Nearvec

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped Pointwise

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.minimal_orbit_representatives :
    UpperTheory.V.Af.BA.MinOrb := by
  intro L _ _ _ N p
  classical
  obtain ⟨S, -, hS⟩ := hnf L N (I0 L N)
  refine ⟨⋃ B ∈ {B | B ∈ S ∧ B.det ≠ 0}, Set.pi Set.univ (fun _ => (nearVec B).powerset), ?_, ?_⟩
  · refine Set.Finite.biUnion ?_ ?_
    · exact S.finite_toSet.subset (fun B hB => hB.1)
    · intro B hB
      exact Set.Finite.pi (fun _ => (nearvec L N B hB.2).1.powerset)
  · intro h hR hsp
    obtain ⟨A, hA, hcol⟩ := exbasis L N _ hsp
    have hcm : ∀ j, ColsMin A (h j) := fun j a => hcol a j
    obtain ⟨g, hg⟩ := hS A hA (nrmle L N (h 0) A (hR 0) (hcm 0) hA).1
    have hdet : ((g : Matrix (Fin N) (Fin N) (𝓞 L)) * A).det ≠ 0 := by
      rw [Matrix.det_mul]
      exact mul_ne_zero (Matrix.isUnits_det_units g).ne_zero hA
    refine ⟨g, ?_⟩
    rw [Set.mem_iUnion₂]
    refine ⟨(g : Matrix (Fin N) (Fin N) (𝓞 L)) * A, ⟨hg, hdet⟩, ?_⟩
    intro j _
    rintro y ⟨x, hx, rfl⟩
    refine ⟨g • h j, smul_mem_Ry g (hR j), fun a => ?_, ?_⟩
    · have hc : (fun i => ((g : Matrix (Fin N) (Fin N) (𝓞 L)) * A) i a) = g • (fun i => A i a) := by
        funext i
        rfl
      rw [hc, q_smul, inv_smul_smul]
      exact hcm j a
    · rw [q_smul]
      change q (h j) (g⁻¹ • g • x) = 1
      rw [inv_smul_smul]
      exact hx
