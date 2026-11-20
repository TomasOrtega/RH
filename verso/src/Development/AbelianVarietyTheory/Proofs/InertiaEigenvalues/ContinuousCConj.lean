import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Small2
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet

namespace GlobalTheory.NewPrime

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

/- English proof (translation)
Establish `hu : ∀ g, IsUnit (Tmat i s g).det` using `fun g => by`. Rewrite using `[← Tgl_coe]`. Conclude with `Matrix.isUnits_det_units _`. Set `τ : GE N →* Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)` to `{ toFun := Tdual i s map_one' := by`. Rewrite using `[Tdual, ← Tgl_coe, map_one, map_one]`.

Simplify using the standard rewrite rules. Use the proof step `map_mul' := fun g h => by`. Simplify using `only [Tdual, ← Tgl_coe, map_mul, Units.val_mul, Matrix.mul_inv_rev, Matrix.transpose_mul, smul_mul_smul_comm] }`. Conclude with `⟨τ.toHomUnits, fun g => rfl⟩`.
-/
theorem exists_isDual (i : X.Tw) (s : X.Sig i) : ∃ ρ, IsDual i s ρ := by
  have hu : ∀ g, IsUnit (Tmat i s g).det := fun g => by
    rw [← Tgl_coe]; exact Matrix.isUnits_det_units _
  let τ : GE N →* Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) :=
    { toFun := Tdual i s
      map_one' := by
        rw [Tdual, ← Tgl_coe, map_one, map_one]; simp
      map_mul' := fun g h => by
        simp only [Tdual, ← Tgl_coe, map_mul, Units.val_mul, Matrix.mul_inv_rev, Matrix.transpose_mul, smul_mul_smul_comm] }
  exact ⟨τ.toHomUnits, fun g => rfl⟩

variable (X) in

/- English proof (translation)
Use `continuous_of_continuousAt_one _ ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_one]`. Introduce `U hU`. Take `⟨L, hL, hLU⟩` from `(krullTopology_mem_nhds_one_iff D.host.E N.Om U).1 hU`. Conclude with `Filter.mem_of_superset ((isOpen_comap_cConj X (IntermediateField.fixingSubgroup_isOpen L)).mem_nhds (Subgroup.one_mem _)) fun g hg => hLU hg`.
-/
theorem continuous_cConj : Continuous (cConj X) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff D.host.E N.Om U).1 hU
  exact Filter.mem_of_superset ((isOpen_comap_cConj X (IntermediateField.fixingSubgroup_isOpen L)).mem_nhds
    (Subgroup.one_mem _)) fun g hg => hLU hg

end GlobalTheory.NewPrime
