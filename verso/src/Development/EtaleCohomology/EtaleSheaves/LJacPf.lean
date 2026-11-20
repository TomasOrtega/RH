import Development.EtaleCohomology.EtaleSheaves.HensIdemCut

namespace LateralTheory.E.LJacPf

/- English proof (translation)
Introduce `A _ I hH B _ φ hφ`. Use `letI := φ.toAlgebra`. Establish `: Algebra.IsIntegral A B` using `⟨hφ⟩`. Establish `hI : I ≤ Ideal.jacobson ⊥` using `hH.jac`. Rewrite using `[Ideal.jacobson]`.

Use `le_sInf ?_` and prove the remaining obligations. Introduce and unpack `m ⟨-, hm⟩`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Establish `: (m.comap (algebraMap A B)).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m`. Use `hI.trans ?_` and prove the remaining obligations.

Rewrite using `[Ideal.jacobson]`. Conclude with `sInf_le ⟨bot_le, this⟩`.
-/
theorem LJac_of : LateralTheory.E.HensIdemCut.LJac := by
  intro A _ I hH B _ φ hφ
  letI := φ.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hφ⟩
  have hI : I ≤ Ideal.jacobson ⊥ := hH.jac
  rw [Ideal.jacobson]
  refine le_sInf ?_
  rintro m ⟨-, hm⟩
  rw [Ideal.map_le_iff_le_comap]
  have : (m.comap (algebraMap A B)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
  refine hI.trans ?_
  rw [Ideal.jacobson]
  exact sInf_le ⟨bot_le, this⟩

end LateralTheory.E.LJacPf
