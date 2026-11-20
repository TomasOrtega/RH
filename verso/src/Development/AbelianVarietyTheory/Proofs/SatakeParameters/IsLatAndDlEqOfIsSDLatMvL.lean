import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OrthSelfDual

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem toLE_mem_mvL {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (co : GL (Fin N) E)
    (M : Submodule (𝓞 E) (Fin N → E)) (y : Fin N → E) :
    toLE co y ∈ mvL co M ↔ y ∈ M := by
  constructor
  · rintro ⟨x, hx, hxy⟩
    have hxy' : x = y := (toLE co).injective hxy
    rw [hxy'] at hx
    exact hx
  · intro hy
    exact Submodule.mem_map.mpr ⟨y, hy, rfl⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem isLat_and_dl_eq_of_isSDLat_mvL : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)), IsOrthCo (sp.cm.sig : E →+* E) J (toLE co) → IsSDLat E N (mvL co M) → Formalism.L2.GlobalTheoryTheory.Comp.IsLat M ∧ Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J M = M := by
  intro R F E _ _ _ _ _ _ sp N J co M hco hsd
  obtain ⟨hfg, hspan, hdual⟩ := hsd

  have hkey : ∀ x z : Fin N → E, Formalism.BasicNotions.stdH E N (toLE co x) (toLE co z) =
      ∑ a, ∑ b, (sp.cm.sig : E →+* E) (x a) * J a b * z b := fun x z => hco x z
  have hinj : Function.Injective
      (((toLE co : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E)) :=
    (toLE co).injective
  refine ⟨⟨?_, ?_⟩, ?_⟩
  ·
    have hfin : Module.Finite (𝓞 E)
        (M.map ((((toLE co : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E))).restrictScalars (𝓞 E))) :=
      Module.Finite.iff_fg.mpr hfg
    exact Module.Finite.equiv (Submodule.equivMapOfInjective _ hinj M).symm
  ·
    rw [eq_top_iff]
    intro v _
    have hv : toLE co v ∈ Submodule.span E ((mvL co M : Submodule (𝓞 E) (Fin N → E)) : Set (Fin N → E)) := by
      rw [hspan]
      exact Submodule.mem_top
    have hset : ((mvL co M : Submodule (𝓞 E) (Fin N → E)) : Set (Fin N → E)) =
        ((toLE co : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)) '' (M : Set (Fin N → E)) := by
      unfold mvL
      rw [Submodule.map_coe]
      rfl
    rw [hset, Submodule.span_image] at hv
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp hv
    have hwv' : w = v := (toLE co).injective hwv
    rw [hwv'] at hw
    exact hw
  ·
    ext y
    rw [Formalism.L2.GlobalTheoryTheory.Comp.mem_dl, ← toLE_mem_mvL co M y, hdual (toLE co y)]
    constructor
    · intro h x' hx'
      obtain ⟨x, hx, hxx'⟩ := Submodule.mem_map.mp hx'
      have hx'' : x' = toLE co x := hxx'.symm
      rw [hx'', hkey]
      exact h x hx
    · intro h x hx
      have h1 := h (toLE co x) ((toLE_mem_mvL co M x).mpr hx)
      rw [hkey] at h1
      exact h1

end GlobalTheory.OrthSelfDual

end
