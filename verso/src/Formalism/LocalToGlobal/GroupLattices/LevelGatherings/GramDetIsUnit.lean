import Formalism.LocalRingCardinality.DataLevel

noncomputable section

open Formalism.BasicNotions NumberField Formalism.UG

namespace Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

/- English proof (translation)
Rewrite using `[isUnit_iff_ne_zero]`. Introduce `hdet`. Rewrite `hdet` using `[Spaces.gram0, Matrix.det_reindex_self]`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`. Establish `hi : ∀ i, (sp.X 0).hT ((sp.X 0).frame i) (∑ j, v j • (sp.X 0).frame j) = 0`.

Introduce `i`. Establish `h` using `congrFun hv i`. Simplify using `only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at h`. Simplify using `only [map_sum, map_smul, smul_eq_mul]`. Rewrite using `[← h]`.

Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Establish `hy : ∀ x, (sp.X 0).hT x (∑ j, v j • (sp.X 0).frame j) = 0`. Introduce `x`. Rewrite using `[← (sp.X 0).frame.sum_repr x, map_sum (sp.X 0).hT, LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.smul_apply, hi, smul_zero]`. Establish `h0` using `(sp.X 0).nondeg.2 _ hy`. Establish `hv'` using `Fintype.linearIndependent_iff.mp (sp.X 0).frame.linearIndependent v h0`. Conclude with `hv0 (funext hv')`.
-/
theorem isUnit_det_gram0 (sp : Spaces R F E) : IsUnit sp.gram0.det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  rw [Spaces.gram0, Matrix.det_reindex_self] at hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hi : ∀ i, (sp.X 0).hT ((sp.X 0).frame i) (∑ j, v j • (sp.X 0).frame j) = 0 := by
    intro i
    have h := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at h
    simp only [map_sum, map_smul, smul_eq_mul]
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hy : ∀ x, (sp.X 0).hT x (∑ j, v j • (sp.X 0).frame j) = 0 := by
    intro x
    rw [← (sp.X 0).frame.sum_repr x, map_sum (sp.X 0).hT, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hi, smul_zero]
  have h0 := (sp.X 0).nondeg.2 _ hy
  have hv' := Fintype.linearIndependent_iff.mp (sp.X 0).frame.linearIndependent v h0
  exact hv0 (funext hv')

end Formalism.L2.G
