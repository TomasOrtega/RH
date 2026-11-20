import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ResConjTriv

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

/- English proof (translation)
Use `continuous_of_continuousAt_one _ ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_one]`. Introduce `s hs`. Take `⟨L, hL, hLs⟩` from `(krullTopology_mem_nhds_one_iff D.host.E N.Om s).1 hs`. Establish `h` using `GlobalTheory.TwistDet.isOpen_comap_cConj X (H := L.fixingSubgroup) (IntermediateField.fixingSubgroup_isOpen L)`.

Rewrite using `[Filter.mem_map]`. Conclude with `Filter.mem_of_superset (h.mem_nhds (Subgroup.one_mem _)) fun g hg => hLs hg`.
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
Establish `e : (GlobalTheory.TwistDet.cConj X g).toRingEquiv = X.cc * g.toRingEquiv * X.cc⁻¹`. Use extensionality with `x`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `cyclotomicCharacter N.Om l (GlobalTheory.TwistDet.cConj X g).toRingEquiv = cyclotomicCharacter N.Om l g.toRingEquiv`. Rewrite using `[e, map_mul, map_mul, map_inv, mul_inv_cancel_comm]`.
-/
theorem cycZ_cConj (l : ℕ) [Fact l.Prime] (g : GE N) :
    cycZ (F := D.host.E) (Ω := N.Om) l (GlobalTheory.TwistDet.cConj X g) = cycZ (F := D.host.E) (Ω := N.Om) l g := by
  have e : (GlobalTheory.TwistDet.cConj X g).toRingEquiv = X.cc * g.toRingEquiv * X.cc⁻¹ := by
    ext x; rfl
  change cyclotomicCharacter N.Om l (GlobalTheory.TwistDet.cConj X g).toRingEquiv = cyclotomicCharacter N.Om l g.toRingEquiv
  rw [e, map_mul, map_mul, map_inv, mul_inv_cancel_comm]

/- English proof (translation)
Simplify using `only [eps0, MonoidHom.comp_apply, cycZ_cConj]`.
-/
theorem auxiliaryCharacter_complexConj_invariant (i : X.Tw) (g : GE N) : eps0 X i (GlobalTheory.TwistDet.cConj X g) = eps0 X i g := by
  simp only [eps0, MonoidHom.comp_apply, cycZ_cConj]

/- English proof (translation)
Take `⟨A, hA⟩` from `hS`. Take `⟨h1, h2⟩` from `hg`. Establish `h3` using `hA g _ (GlobalTheory.TwistDet.cConj_apply X g)`. Use `⟨?_, by rw [auxiliaryCharacter_complexConj_invariant, h2]⟩` and prove the remaining obligations. Use `set φ := IsLocalRing.residue (X.O0 i) with hφ`.

Establish `hsm : ∀ (c : X.O0 i) (M : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)), φ c = 1 → (c • M).map φ = M.map φ`. Introduce `c M hc`. Use extensionality with `a b`. Simplify using `[hc]`. Establish `h4` using `congrArg (fun M => M.map φ) h3`.

Simplify using `only [Tdual] at h4`. Rewrite `h4` using `[hsm _ _ (by rw [auxiliaryCharacter_complexConj_invariant, h2]), Matrix.map_mul, Matrix.map_mul, hsm _ _ (by rw [map_pow, h2, one_pow]), h1, mul_one, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.transpose_map, Matrix.transpose_eq_one]`. Establish `hu : IsUnit (Tmat i s (GlobalTheory.TwistDet.cConj X g)).det`. Rewrite using `[← Tgl_coe]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)`.

Establish `h5` using `congrArg (fun M => M.map φ) (Matrix.mul_nonsing_inv _ hu)`. Rewrite `h5` using `[Matrix.map_mul, h4, mul_one, Matrix.map_one _ (map_zero φ) (map_one φ)]`. Then use the resulting hypothesis.
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
Introduce `_ _ X` and use `⟨continuous_cConj X, resTriv_cConj X⟩`.
-/
theorem continuous_cConj_and_resTriv : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N), Continuous (GlobalTheory.TwistDet.cConj X) ∧ ∀ (i : X.Tw) (s : X.Sig i), SelfDual i s → ∀ g : GE N, ResTriv i s g → ResTriv i s (GlobalTheory.TwistDet.cConj X g) :=
  fun _ _ X => ⟨continuous_cConj X, resTriv_cConj X⟩

end GlobalTheory.ResConjTriv
