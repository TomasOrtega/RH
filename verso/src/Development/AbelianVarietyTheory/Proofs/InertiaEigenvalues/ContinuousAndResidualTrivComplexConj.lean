import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ResConjTriv

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem continuous_cConj : Continuous (GlobalTheory.TwistDet.cConj X) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨L, hL, hLs⟩ := (krullTopology_mem_nhds_one_iff D.host.E N.Om s).1 hs
  have h := GlobalTheory.TwistDet.isOpen_comap_cConj X (H := L.fixingSubgroup) (IntermediateField.fixingSubgroup_isOpen L)
  rw [Filter.mem_map]
  exact Filter.mem_of_superset (h.mem_nhds (Subgroup.one_mem _)) fun g hg => hLs hg

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Both sides reduce to the same expression. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem cycZ_cConj (l : ℕ) [Fact l.Prime] (g : GE N) :
    cycZ (F := D.host.E) (Ω := N.Om) l (GlobalTheory.TwistDet.cConj X g) = cycZ (F := D.host.E) (Ω := N.Om) l g := by
  have e : (GlobalTheory.TwistDet.cConj X g).toRingEquiv = X.cc * g.toRingEquiv * X.cc⁻¹ := by
    ext x; rfl
  change cyclotomicCharacter N.Om l (GlobalTheory.TwistDet.cConj X g).toRingEquiv = cyclotomicCharacter N.Om l g.toRingEquiv
  rw [e, map_mul, map_mul, map_inv, mul_inv_cancel_comm]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem auxiliaryCharacter_complexConj_invariant (i : X.Tw) (g : GE N) : eps0 X i (GlobalTheory.TwistDet.cConj X g) = eps0 X i g := by
  simp only [eps0, MonoidHom.comp_apply, cycZ_cConj]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

A detailed English derivation is pending.
-/
theorem resTriv_cConj (i : X.Tw) (s : X.Sig i) (hS : SelfDual i s) (g : GE N) (hg : ResTriv i s g) :
    ResTriv i s (GlobalTheory.TwistDet.cConj X g) := by
  obtain ⟨A, hA⟩ := hS
  obtain ⟨h1, h2⟩ := hg
  have h3 := hA g _ (GlobalTheory.TwistDet.cConj_apply X g)
  refine ⟨?_, by rw [auxiliaryCharacter_complexConj_invariant, h2]⟩
  set φ := IsLocalRing.residue (X.O0 i) with hφ
  have hsm : ∀ (c : X.O0 i) (M : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)), φ c = 1 → (c • M).map φ = M.map φ := by
    intro c M hc
    ext a b
    simp [hc]
  have h4 := congrArg (fun M => M.map φ) h3
  simp only [Tdual] at h4
  rw [hsm _ _ (by rw [auxiliaryCharacter_complexConj_invariant, h2]), Matrix.map_mul, Matrix.map_mul, hsm _ _ (by rw [map_pow, h2, one_pow]), h1,
    mul_one, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.transpose_map,
    Matrix.transpose_eq_one] at h4
  have hu : IsUnit (Tmat i s (GlobalTheory.TwistDet.cConj X g)).det := by
    rw [← Tgl_coe]
    exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  have h5 := congrArg (fun M => M.map φ) (Matrix.mul_nonsing_inv _ hu)
  rwa [Matrix.map_mul, h4, mul_one, Matrix.map_one _ (map_zero φ) (map_one φ)] at h5

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem continuous_cConj_and_resTriv : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N), Continuous (GlobalTheory.TwistDet.cConj X) ∧ ∀ (i : X.Tw) (s : X.Sig i), SelfDual i s → ∀ g : GE N, ResTriv i s g → ResTriv i s (GlobalTheory.TwistDet.cConj X g) :=
  fun _ _ X => ⟨continuous_cConj X, resTriv_cConj X⟩

end GlobalTheory.ResConjTriv
