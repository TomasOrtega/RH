import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField

namespace Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def crd (V : HSp D) : (Fin V.rank → D.host.E) ≃ₗ[D.host.E] V.V := V.frame.equivFun.symm

def l0s (V : HSp D) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
  V.L0.comap ((crd V).toLinearMap.restrictScalars (𝓞 D.host.E))

/- English proof (translation)
Simplify using `[l0s, crd, L0c, Module.Basis.equivFun_symm_apply]`.
-/
theorem mem_self_dual_lattice_set (V : HSp D) (x : Fin V.rank → D.host.E) : x ∈ l0s V ↔ x ∈ L0c D V := by
  simp [l0s, crd, L0c, Module.Basis.equivFun_symm_apply]

/- English proof (translation)
Use extensionality with `x`. Conclude with `mem_self_dual_lattice_set V x`.
-/
theorem coe_self_dual_lattice_set (V : HSp D) : (l0s V : Set (Fin V.rank → D.host.E)) = L0c D V := by
  ext x; exact mem_self_dual_lattice_set V x

/- English proof (translation)
Simplify using `only [crd, Module.Basis.equivFun_symm_apply, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Formalism.BasicNotions.HSpace.gram]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [RingHom.id_apply, starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hT_crd (V : HSp D) (x y : Fin V.rank → D.host.E) :
    V.hT (crd V x) (crd V y) = ∑ i, ∑ j, star (x i) * V.gram i j * y j := by
  simp only [crd, Module.Basis.equivFun_symm_apply, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Formalism.BasicNotions.HSpace.gram]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RingHom.id_apply, starRingEnd_apply]
  ring

/- English proof (translation)
Use `⟨?_, fun y => ?_⟩` and prove the remaining obligations. Establish `hL` using `V.standardTuple_isLattice`. Set `f : V.V ≃ₗ[D.host.E] (Fin V.rank → D.host.E)` to `(crd V).symm`. Establish `heq : l0s V = V.L0.map (f.toLinearMap.restrictScalars (𝓞 D.host.E))`. Use extensionality with `x`.

Simplify using `only [l0s, Submodule.mem_comap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, f]`. Prove the components needed by the constructor for the conclusion. Introduce `hx; exact ⟨crd V x, hx, by simp⟩`. Introduce and unpack `⟨z, hz, rfl⟩`. Simplify using `using hz`.

Rewrite using `[heq]`. Use `⟨hL.fg.map _, ?_⟩` and prove the remaining obligations. Establish `hc : (↑(Submodule.map (f.toLinearMap.restrictScalars (𝓞 D.host.E)) V.L0) : Set (Fin V.rank → D.host.E)) = f.toLinearMap '' (V.L0 : Set V.V)` using `by ext; simp`. Rewrite using `[hc, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearEquiv.range]`. Establish `key : ∀ b : 𝓞 D.host.E, LinearMap.toSpanSingleton (𝓞 D.host.E) D.host.E 1 b = (b : D.host.E)` using `fun b => by`.

Simplify using `[LinearMap.toSpanSingleton_apply, Algebra.smul_def]`. Establish `hU` using `V.baseLattice_isUnimodular`. Unfold `Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual at hU`. Prove the components needed by the constructor for the conclusion. Introduce `hy x hx`.

Establish `hy' : crd V y ∈ Formalism.E.hdual V.hT V.L0` using `by rw [hU]; exact hy`. Simplify using `only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply] at hy'`. Take `⟨b, hb⟩` from `hy' (crd V x) hx`. Conclude with `⟨b, by rw [← hT_crd, ← hb, key]⟩`. Introduce `h show crd V y ∈ V.L0`.

Rewrite using `[← hU]`. Simplify using `only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]`. Introduce `z hz`. Take `⟨b, hb⟩` from `h ((crd V).symm z) (by simpa [l0s] using hz)`. Use `⟨b, ?_⟩` and prove the remaining obligations.

Rewrite using `[show z = crd V ((crd V).symm z) by simp, hT_crd, key]`. Conclude with `hb`.
-/
theorem self_dual_lattice_is_self_dual (V : HSp D) : Datum.IsSelfDualC V (l0s V) := by
  refine ⟨?_, fun y => ?_⟩
  · have hL := V.standardTuple_isLattice
    let f : V.V ≃ₗ[D.host.E] (Fin V.rank → D.host.E) := (crd V).symm
    have heq : l0s V = V.L0.map (f.toLinearMap.restrictScalars (𝓞 D.host.E)) := by
      ext x
      simp only [l0s, Submodule.mem_comap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, f]
      constructor
      · intro hx; exact ⟨crd V x, hx, by simp⟩
      · rintro ⟨z, hz, rfl⟩; simpa using hz
    rw [heq]
    refine ⟨hL.fg.map _, ?_⟩
    have hc : (↑(Submodule.map (f.toLinearMap.restrictScalars (𝓞 D.host.E)) V.L0) : Set (Fin V.rank → D.host.E)) =
        f.toLinearMap '' (V.L0 : Set V.V) := by ext; simp
    rw [hc, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearEquiv.range]
  · have key : ∀ b : 𝓞 D.host.E, LinearMap.toSpanSingleton (𝓞 D.host.E) D.host.E 1 b = (b : D.host.E) := fun b => by
      simp [LinearMap.toSpanSingleton_apply, Algebra.smul_def]
    have hU := V.baseLattice_isUnimodular
    unfold Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual at hU
    constructor
    · intro hy x hx
      have hy' : crd V y ∈ Formalism.E.hdual V.hT V.L0 := by rw [hU]; exact hy
      simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply] at hy'
      obtain ⟨b, hb⟩ := hy' (crd V x) hx
      exact ⟨b, by rw [← hT_crd, ← hb, key]⟩
    · intro h
      show crd V y ∈ V.L0
      rw [← hU]
      simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
      intro z hz
      obtain ⟨b, hb⟩ := h ((crd V).symm z) (by simpa [l0s] using hz)
      refine ⟨b, ?_⟩
      rw [show z = crd V ((crd V).symm z) by simp, hT_crd, key]
      exact hb

end Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces
