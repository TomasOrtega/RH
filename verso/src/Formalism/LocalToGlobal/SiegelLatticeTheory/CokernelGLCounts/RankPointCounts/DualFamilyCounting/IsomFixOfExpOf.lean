import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IncOInjective

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def extU {U W : Submodule K V} (hUc : IsCompl U W) (g : W ≃ₗ[K] W) : V ≃ₗ[K] V :=
  ((Submodule.prodEquivOfIsCompl U W hUc).symm.trans ((LinearEquiv.refl K U).prodCongr g)).trans
    (Submodule.prodEquivOfIsCompl U W hUc)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem extU_apply {U W : Submodule K V} (hUc : IsCompl U W) (g : W ≃ₗ[K] W) (x : U) (y : W) :
    extU hUc g ((x : V) + y) = x + g y := by
  have e : (Submodule.prodEquivOfIsCompl U W hUc).symm ((x : V) + y) = (x, y) := by
    rw [LinearEquiv.symm_apply_eq, Submodule.coe_prodEquivOfIsCompl']
  simp only [extU, LinearEquiv.trans_apply, e, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
    Submodule.coe_prodEquivOfIsCompl']

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem extU_mem {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {U : Submodule K V}
    (hUc : IsCompl U (orthK h U)) {g : orthK h U ≃ₗ[K] orthK h U} (hg : g ∈ Formalism.HermitianLatticesTheory.isom (resF h (orthK h U))) :
    extU hUc g ∈ isomFix h U := by
  have horth : ∀ u ∈ U, ∀ w ∈ orthK h U, h u w = 0 := by
    intro u hu w hw
    simp only [orthK, Submodule.mem_iInf, LinearMap.mem_ker] at hw
    exact hw u hu
  have horth' : ∀ u ∈ U, ∀ w ∈ orthK h U, h w u = 0 := by
    intro u hu w hw
    rw [← hs.eq u w, horth u hu w hw, map_zero]
  have hdec : ∀ x : V, ∃ a : U, ∃ b : orthK h U, (a : V) + b = x := by
    intro x
    have hx : x ∈ U ⊔ orthK h U := by rw [hUc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩
  have hg' : ∀ x y, resF h (orthK h U) (g x) (g y) = resF h (orthK h U) x y := hg
  change extU hUc g ∈ Formalism.HermitianLatticesTheory.isom h ∧ ∀ u ∈ U, extU hUc g u = u
  refine ⟨?_, ?_⟩
  · change ∀ x y, h (extU hUc g x) (extU hUc g y) = h x y
    intro x y
    obtain ⟨a, b, rfl⟩ := hdec x
    obtain ⟨c, d, rfl⟩ := hdec y
    rw [extU_apply, extU_apply]
    have hgb : h (g b) (g d) = h b d := by
      have := hg' b d
      simpa only [resF_apply] using this
    simp only [map_add, LinearMap.add_apply, horth _ a.2 _ (g d).2, horth _ a.2 _ d.2,
      horth' _ c.2 _ (g b).2, horth' _ c.2 _ b.2, hgb]
  · intro u hu
    have := extU_apply hUc g ⟨u, hu⟩ 0
    simpa using this

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Supply the required witnesses or components.
-/
theorem gmap_extU {U W : Submodule K V} (hUc : IsCompl U W) (g : W ≃ₗ[K] W) (X : Submodule (𝓞 K) W) :
    Formalism.HermitianLatticesTheory.gmap (extU hUc g) (X.map (incO W)) = (Formalism.HermitianLatticesTheory.gmap g X).map (incO W) := by
  have key : ∀ w : W, extU hUc g (w : V) = (g w : V) := by
    intro w
    have := extU_apply hUc g 0 w
    simpa using this
  ext v
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨g x, ⟨x, hx, rfl⟩, (key x).symm⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, ⟨x, hx, rfl⟩, key x⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Supply the required witnesses or components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isomFixOfExp_of (hJ : JordanIsom) : IsomFixOfExp := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hN U hUc hpos T T' hT hT' 𝔭 h𝔭 b a b' a' hb hb' hv
  haveI := h𝔭.isPrime
  have hs' : (resF h (orthK h U)).IsSymm := by
    exact ⟨fun x y => by simpa only [resF_apply] using hs.eq (x : V) y⟩
  have hd' : IsTotPosDef (resF h (orthK h U)) := by
    intro x hx φ
    rw [resF_apply]
    exact hpos x x.2 (by simpa using hx) φ
  obtain ⟨g, hg, hgL⟩ := hJ K F (orthK h U) hK hF (resF h (orthK h U)) hs' hd'
    (latW (orthK h U) T) (latW (orthK h U) T') (isLattice_latW hT) (isLattice_latW hT') 𝔭 h𝔭 _ _ _ _
    (isJordanIn_res hT hb) (isJordanIn_res hT' hb') (fun i => hv _)
  refine ⟨extU hUc g, extU_mem hs hUc hg, ?_⟩
  rw [← locF_latW hT 𝔭, gmap_extU, hgL, locF_latW hT' 𝔭]

end Formalism.L2.SG.Pf.G8
