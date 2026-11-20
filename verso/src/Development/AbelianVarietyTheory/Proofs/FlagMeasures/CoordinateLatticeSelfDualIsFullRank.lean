import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G

/- English proof (translation)
Establish `hcomb : ∀ x : Fin _ → D.host.E, Fintype.linearCombination D.host.E X.bas x = X.bas.equivFun.symm x`. Introduce `x`. Rewrite using `[Fintype.linearCombination_apply, Module.Basis.equivFun_symm_apply]`. Establish `heq : (VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E)) = (VS D).L0.map (X.bas.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap`. Use extensionality with `x`.

Simplify using `only [Submodule.mem_comap, LinearMap.restrictScalars_apply, hcomb, Submodule.mem_map, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨_, hx, X.bas.equivFun.apply_symm_apply x⟩`. Introduce and unpack `⟨y, hy, rfl⟩`.

Simplify using `using hy`. Rewrite using `[heq]`. Use `⟨Module.Finite.iff_fg.2 ((VS D).standardTuple_isLattice.fg.map _), ?_⟩` and prove the remaining obligations. Establish `: ((VS D).L0.map (X.bas.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap : Set (Fin _ → D.host.E)) = X.bas.equivFun.toLinearMap '' ((VS D).L0 : Set (VS D).V)` using `rfl`. Rewrite using `[this, ← Submodule.map_span, (VS D).standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]`.
-/
theorem coordLat_isLat (D : D7) (X : HidaSetting D) :
    IsLat ((VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E))) := by
  have hcomb : ∀ x : Fin _ → D.host.E,
      Fintype.linearCombination D.host.E X.bas x = X.bas.equivFun.symm x := by
    intro x
    rw [Fintype.linearCombination_apply, Module.Basis.equivFun_symm_apply]
  have heq : (VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E)) =
      (VS D).L0.map (X.bas.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap := by
    ext x
    simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, hcomb, Submodule.mem_map,
      LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply]
    constructor
    · intro hx
      exact ⟨_, hx, X.bas.equivFun.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [heq]
  refine ⟨Module.Finite.iff_fg.2 ((VS D).standardTuple_isLattice.fg.map _), ?_⟩
  have : ((VS D).L0.map (X.bas.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap : Set (Fin _ → D.host.E)) =
      X.bas.equivFun.toLinearMap '' ((VS D).L0 : Set (VS D).V) := rfl
  rw [this, ← Submodule.map_span, (VS D).standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]

end GlobalTheory.St.G
