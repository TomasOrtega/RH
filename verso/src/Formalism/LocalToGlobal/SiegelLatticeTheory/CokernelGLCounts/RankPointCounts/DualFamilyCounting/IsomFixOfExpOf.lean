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
Establish `e : (Submodule.prodEquivOfIsCompl U W hUc).symm ((x : V) + y) = (x, y)`. Rewrite using `[LinearEquiv.symm_apply_eq, Submodule.coe_prodEquivOfIsCompl']`. Simplify using `only [extU, LinearEquiv.trans_apply, e, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply, Submodule.coe_prodEquivOfIsCompl']`.
-/
theorem extU_apply {U W : Submodule K V} (hUc : IsCompl U W) (g : W ≃ₗ[K] W) (x : U) (y : W) :
    extU hUc g ((x : V) + y) = x + g y := by
  have e : (Submodule.prodEquivOfIsCompl U W hUc).symm ((x : V) + y) = (x, y) := by
    rw [LinearEquiv.symm_apply_eq, Submodule.coe_prodEquivOfIsCompl']
  simp only [extU, LinearEquiv.trans_apply, e, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
    Submodule.coe_prodEquivOfIsCompl']

/- English proof (translation)
Establish `horth : ∀ u ∈ U, ∀ w ∈ orthK h U, h u w = 0`. Introduce `u hu w hw`. Simplify using `only [orthK, Submodule.mem_iInf, LinearMap.mem_ker] at hw`. Conclude with `hw u hu`. Establish `horth' : ∀ u ∈ U, ∀ w ∈ orthK h U, h w u = 0`.

Introduce `u hu w hw`. Rewrite using `[← hs.eq u w, horth u hu w hw, map_zero]`. Establish `hdec : ∀ x : V, ∃ a : U, ∃ b : orthK h U, (a : V) + b = x`. Introduce `x`. Establish `hx : x ∈ U ⊔ orthK h U` using `by rw [hUc.sup_eq_top]; exact Submodule.mem_top`.

Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.mp hx`. Conclude with `⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩`. Establish `hg' : ∀ x y, resF h (orthK h U) (g x) (g y) = resF h (orthK h U) x y` using `hg`. Express the relevant statement in the definitionally equal form `extU hUc g ∈ Formalism.HermitianLatticesTheory.isom h ∧ ∀ u ∈ U, extU hUc g u = u`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `∀ x y, h (extU hUc g x) (extU hUc g y) = h x y`. Introduce `x y`. Take `⟨a, b, rfl⟩` from `hdec x`. Take `⟨c, d, rfl⟩` from `hdec y`. Rewrite using `[extU_apply, extU_apply]`.

Establish `hgb : h (g b) (g d) = h b d`. Use `hg' b d` as an intermediate fact. Simplify `this` using `only [resF_apply]`. Simplify using `only [map_add, LinearMap.add_apply, horth _ a.2 _ (g d).2, horth _ a.2 _ d.2, horth' _ c.2 _ (g b).2, horth' _ c.2 _ b.2, hgb]`. Introduce `u hu`.

Use `extU_apply hUc g ⟨u, hu⟩ 0` as an intermediate fact. Simplify using `using this`.
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
Establish `key : ∀ w : W, extU hUc g (w : V) = (g w : V)`. Introduce `w`. Use `extU_apply hUc g 0 w` as an intermediate fact. Simplify using `using this`. Use extensionality with `v`.

Simplify using `only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨x, hx, rfl⟩, rfl⟩`. Conclude with `⟨g x, ⟨x, hx, rfl⟩, (key x).symm⟩`. Introduce and unpack `⟨y, ⟨x, hx, rfl⟩, rfl⟩`.

Conclude with `⟨x, ⟨x, hx, rfl⟩, key x⟩`.
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
Introduce `K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hN U hUc hpos T T' hT hT' 𝔭 h𝔭 b a b' a' hb hb' hv`. Use `haveI := h𝔭.isPrime`. Establish `hs' : (resF h (orthK h U)).IsSymm`. Conclude with `⟨fun x y => by simpa only [resF_apply] using hs.eq (x : V) y⟩`. Establish `hd' : IsTotPosDef (resF h (orthK h U))`.

Introduce `x hx φ`. Rewrite using `[resF_apply]`. Conclude with `hpos x x.2 (by simpa using hx) φ`. Take `⟨g, hg, hgL⟩` from `hJ K F (orthK h U) hK hF (resF h (orthK h U)) hs' hd' (latW (orthK h U) T) (latW (orthK h U) T') (isLattice_latW hT) (isLattice_latW hT') 𝔭 h𝔭 _ _ _ _ (isJordanIn_res hT hb) (isJordanIn_res hT' hb') (fun i => hv _)`. Use `⟨extU hUc g, extU_mem hs hUc hg, ?_⟩` and prove the remaining obligations.

Rewrite using `[← locF_latW hT 𝔭, gmap_extU, hgL, locF_latW hT' 𝔭]`.
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
