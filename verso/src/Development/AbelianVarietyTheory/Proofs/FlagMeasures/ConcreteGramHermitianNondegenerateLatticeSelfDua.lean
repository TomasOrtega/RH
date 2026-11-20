import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Direct
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDom

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Simplify using `only [vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Module.Basis.equivFun_symm_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]`. Conclude with `Fintype.sum_equiv (ci X).symm _ _ fun j => by simp`.
-/
theorem vecOf_apply (x : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    vecOf X x = ∑ i, x i • X.bas (ci X i) := by
  simp only [vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Module.Basis.equivFun_symm_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  exact Fintype.sum_equiv (ci X).symm _ _ fun j => by simp

/- English proof (translation)
Unfold `vecOf`. Rewrite using `[LinearMap.coe_comp]`. Conclude with `X.bas.equivFun.symm.bijective.comp (LinearEquiv.funCongrLeft _ _ _).bijective`.
-/
theorem vecOf_bijective : Function.Bijective (vecOf X) := by
  unfold vecOf
  rw [LinearMap.coe_comp]
  exact X.bas.equivFun.symm.bijective.comp (LinearEquiv.funCongrLeft _ _ _).bijective

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem sig_eq_star' (a : D.host.E) : D.sp.cm.sig a = star a := by rfl

/- English proof (translation)
Rewrite using `[vecOf_apply, vecOf_apply]`. Simplify using `only [GlobalTheory.SgAlg.form, dotProduct, Matrix.mulVec, Jc, map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[AlgHom.coe_toRingHom, sig_eq_star', starRingEnd_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_Jc (x y : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    GlobalTheory.SgAlg.form (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) x y = (VS D).hT (vecOf X y) (vecOf X x) := by
  rw [vecOf_apply, vecOf_apply]
  simp only [GlobalTheory.SgAlg.form, dotProduct, Matrix.mulVec, Jc, map_sum, map_smulₛₗ,
    LinearMap.sum_apply, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [AlgHom.coe_toRingHom, sig_eq_star', starRingEnd_apply]
  ring

end GlobalTheory.CovDom

/- English proof (translation)
Introduce `D X`. Establish `hform` using `form_Jc X`. Establish `hinj` using `(vecOf_bijective X).1`. Establish `hsurj` using `(vecOf_bijective X).2`. Unfold `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND GlobalTheory.SgGlob.SelfDual`.

Use `⟨⟨fun i j => ?_, ?_⟩, ?_, fun v => ?_⟩` and prove the remaining obligations. Simplify using `only [Jc]`. Rewrite using `[sig_eq_star']`. Conclude with `(VS D).herm.eq _ _`. Introduce `hdet`.

Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`. Apply `hv0` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero]`. Apply `(VS D).nondeg.2` to reduce the goal to its premises.

Introduce `w`. Take `⟨y, rfl⟩` from `hsurj w`. Rewrite using `[← hform v y]`. Simplify using `[GlobalTheory.SgAlg.form, hv]`. Set `e : (Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) ≃ₗ[𝓞 D.host.E] (VS D).V` to `(LinearEquiv.ofBijective (vecOf X) (vecOf_bijective X)).restrictScalars (𝓞 D.host.E)`.

Establish `hc : Lc X = (VS D).L0.comap (e : _ →ₗ[𝓞 D.host.E] (VS D).V)` using `rfl`. Rewrite using `[hc, Submodule.comap_equiv_eq_map_symm]`. Conclude with `(VS D).standardTuple_isLattice.fg.map _`. Use `show vecOf X v ∈ (VS D).L0 ↔ _ conv_lhs => rw [← (VS D).baseLattice_isUnimodular]`. Simplify using `only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]`.

Prove the components needed by the constructor for the conclusion. Introduce `h w hw`. Rewrite using `[hform v w]`. Take `⟨a, ha⟩` from `Submodule.mem_one.mp (h _ hw)`. Conclude with `⟨a, ha⟩`.

Introduce `h y hy`. Take `⟨w, rfl⟩` from `hsurj y`. Establish `hw` using `h w hy`. Rewrite `hw` using `[hform v w]`. Take `⟨a, ha⟩` from `hw`.

Conclude with `Submodule.mem_one.mpr ⟨a, ha⟩`.
-/
theorem GlobalTheory.CovDom.herm_selfDual : ∀ (D : D7) (X : HidaSetting D), Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND D.sp.cm.sig (Jc X) ∧ GlobalTheory.SgGlob.SelfDual (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Lc X) := by
  intro D X
  have hform := form_Jc X
  have hinj := (vecOf_bijective X).1
  have hsurj := (vecOf_bijective X).2
  unfold Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND GlobalTheory.SgGlob.SelfDual
  refine ⟨⟨fun i j => ?_, ?_⟩, ?_, fun v => ?_⟩
  · simp only [Jc]
    rw [sig_eq_star']
    exact (VS D).herm.eq _ _
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    apply hv0
    apply hinj
    rw [map_zero]
    apply (VS D).nondeg.2
    intro w
    obtain ⟨y, rfl⟩ := hsurj w
    rw [← hform v y]
    simp [GlobalTheory.SgAlg.form, hv]
  · let e : (Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) ≃ₗ[𝓞 D.host.E] (VS D).V :=
      (LinearEquiv.ofBijective (vecOf X) (vecOf_bijective X)).restrictScalars (𝓞 D.host.E)
    have hc : Lc X = (VS D).L0.comap (e : _ →ₗ[𝓞 D.host.E] (VS D).V) := rfl
    rw [hc, Submodule.comap_equiv_eq_map_symm]
    exact (VS D).standardTuple_isLattice.fg.map _
  · show vecOf X v ∈ (VS D).L0 ↔ _
    conv_lhs => rw [← (VS D).baseLattice_isUnimodular]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply]
    constructor
    · intro h w hw
      rw [hform v w]
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp (h _ hw)
      exact ⟨a, ha⟩
    · intro h y hy
      obtain ⟨w, rfl⟩ := hsurj y
      have hw := h w hy
      rw [hform v w] at hw
      obtain ⟨a, ha⟩ := hw
      exact Submodule.mem_one.mpr ⟨a, ha⟩
