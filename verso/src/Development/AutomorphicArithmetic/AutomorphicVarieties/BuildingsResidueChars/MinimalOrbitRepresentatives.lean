import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Exbasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.DetPull
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Hnf
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Nearvec

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped Pointwise

/- English proof (translation)
Introduce `L _ _ _ N p`. Take `⟨S, -, hS⟩` from `hnf L N (I0 L N)`. Use `⟨⋃ B ∈ {B | B ∈ S ∧ B.det ≠ 0}, Set.pi Set.univ (fun _ => (nearVec B).powerset), ?_, ?_⟩` and prove the remaining obligations. Use `Set.Finite.biUnion ?_ ?_` and prove the remaining obligations. Conclude with `S.finite_toSet.subset (fun B hB => hB.1)`.

Introduce `B hB`. Conclude with `Set.Finite.pi (fun _ => (nearvec L N B hB.2).1.powerset)`. Introduce `h hR hsp`. Take `⟨A, hA, hcol⟩` from `exbasis L N _ hsp`. Establish `hcm : ∀ j, ColsMin A (h j)` using `fun j a => hcol a j`.

Take `⟨g, hg⟩` from `hS A hA (nrmle L N (h 0) A (hR 0) (hcm 0) hA).1`. Establish `hdet : ((g : Matrix (Fin N) (Fin N) (𝓞 L)) * A).det ≠ 0`. Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero (Matrix.isUnits_det_units g).ne_zero hA`. Use `⟨g, ?_⟩` and prove the remaining obligations.

Rewrite using `[Set.mem_iUnion₂]`. Use `⟨(g : Matrix (Fin N) (Fin N) (𝓞 L)) * A, ⟨hg, hdet⟩, ?_⟩` and prove the remaining obligations. Introduce `j _`. Introduce and unpack `y ⟨x, hx, rfl⟩`. Use `⟨g • h j, smul_mem_Ry g (hR j), fun a => ?_, ?_⟩` and prove the remaining obligations.

Establish `hc : (fun i => ((g : Matrix (Fin N) (Fin N) (𝓞 L)) * A) i a) = g • (fun i => A i a)`. Use function extensionality and compare the values at `i`. Both sides reduce to the same expression. Rewrite using `[hc, q_smul, inv_smul_smul]`. Conclude with `hcm j a`.

Rewrite using `[q_smul]`. Express the relevant statement in the definitionally equal form `q (h j) (g⁻¹ • g • x) = 1`. Rewrite using `[inv_smul_smul]`. Conclude with `hx`.
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
