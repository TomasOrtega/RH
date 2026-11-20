import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdealLatticeBasis.IdealBasisAlt

open NumberField

namespace PI.IdealLatticeWork

/- English proof (translation)
Introduce `K _ _ b cc hcc`. Set `bI` to `Ideal.selfBasis b cc hcc`. Use `⟨(bI 0 : 𝓞 K), (bI 0).2, (bI 1 : 𝓞 K), (bI 1).2, ?_, ?_⟩` and prove the remaining obligations. Introduce `c hc`. Use `⟨bI.repr ⟨c, hc⟩ 0, bI.repr ⟨c, hc⟩ 1, ?_⟩` and prove the remaining obligations.

Establish `h` using `congrArg Subtype.val (bI.sum_repr ⟨c, hc⟩)`. Rewrite `h` using `[Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower]`. Conclude with `h.symm`. Use `⟨b.repr (bI 0) 0, b.repr (bI 0) 1, b.repr (bI 1) 0, b.repr (bI 1) 1, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `b.sum_repr (bI 0 : 𝓞 K)`.

Rewrite `h` using `[Fin.sum_univ_two]`. Conclude with `h.symm`. Establish `h` using `b.sum_repr (bI 1 : 𝓞 K)`. Rewrite `h` using `[Fin.sum_univ_two]`. Conclude with `h.symm`.

Establish `h` using `Ideal.natAbs_det_basis_change b cc bI`. Rewrite `h` using `[Module.Basis.det_apply, Matrix.det_fin_two]`. Simplify using `only [Module.Basis.toMatrix_apply, Function.comp_apply] at h`. Rewrite using `[← h]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem idealBasis : IdealBasis := by
  intro K _ _ b cc hcc
  classical
  let bI := Ideal.selfBasis b cc hcc
  refine ⟨(bI 0 : 𝓞 K), (bI 0).2, (bI 1 : 𝓞 K), (bI 1).2, ?_, ?_⟩
  · intro c hc
    refine ⟨bI.repr ⟨c, hc⟩ 0, bI.repr ⟨c, hc⟩ 1, ?_⟩
    have h := congrArg Subtype.val (bI.sum_repr ⟨c, hc⟩)
    rw [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul_of_tower,
      Submodule.coe_smul_of_tower] at h
    exact h.symm
  · refine ⟨b.repr (bI 0) 0, b.repr (bI 0) 1, b.repr (bI 1) 0, b.repr (bI 1) 1, ?_, ?_, ?_⟩
    · have h := b.sum_repr (bI 0 : 𝓞 K)
      rw [Fin.sum_univ_two] at h
      exact h.symm
    · have h := b.sum_repr (bI 1 : 𝓞 K)
      rw [Fin.sum_univ_two] at h
      exact h.symm
    · have h := Ideal.natAbs_det_basis_change b cc bI
      rw [Module.Basis.det_apply, Matrix.det_fin_two] at h
      simp only [Module.Basis.toMatrix_apply, Function.comp_apply] at h
      rw [← h]
      congr 1
      ring

end PI.IdealLatticeWork
