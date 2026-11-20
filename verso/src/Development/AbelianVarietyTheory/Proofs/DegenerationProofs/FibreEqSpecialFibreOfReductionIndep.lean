import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalPointLiftingResiduePointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicPropertiesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

/- English proof (translation)
Introduce `C hI p _ y τ x hx`. Take `⟨-, hlft, -, hint, hflat, -, -, -, -, -, -, hdom, htest⟩` from `GlobalTheory.T.abelianSchemeProperClosureData_basic_properties C`. Use `C.lft` as an intermediate fact. Establish `hne : ((C.GG.hom ⁻¹ᵁ C.U : C.G.toScheme.Opens) : Set C.G.toScheme).Nonempty`. Take `⟨w, hw⟩` from `hdom.denseRange.exists_mem_open C.U.isOpen C.ne`.

Conclude with `⟨w, hw⟩`. Establish `hlft' : LocallyOfFiniteType (C.GG.hom ≫ C.π)` using `inferInstance`. Take `⟨b', hb'x, hb'U⟩` from `(@GlobalTheory.T.exists_classical_point_lifting_residue_point C.G.toScheme hint (C.GG.hom ≫ C.π) hflat hlft' (C.GG.hom ⁻¹ᵁ C.U) hne p _).1 x`. Establish `hcl : C.Cl (b' ≫ C.GG.hom)`. Introduce and unpack `_ ⟨s, rfl⟩`.

Use `hb'U ⟨s, rfl⟩` as an intermediate fact. Rewrite using `[← Category.assoc, Scheme.Hom.comp_apply]`. Conclude with `this`. Take `⟨b, hby, hbx⟩` from `hI p (b' ≫ C.GG.hom) y hcl (htest p y τ).1 (by rw [← Category.assoc, hb'x, hx]) b' rfl`. Take `⟨c, hc, hcb⟩` from `τ.lift b hby`.

Use `⟨rPt p ≫ c, by rw [Category.assoc, hc], ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hcb, hbx, hb'x]`.
-/
theorem Core.fib_of_indep : ∀ C : Core, C.Indep → C.Fib := by
  intro C hI p _ y τ x hx
  obtain ⟨-, hlft, -, hint, hflat, -, -, -, -, -, -, hdom, htest⟩ := GlobalTheory.T.abelianSchemeProperClosureData_basic_properties C
  have := C.lft
  have hne : ((C.GG.hom ⁻¹ᵁ C.U : C.G.toScheme.Opens) : Set C.G.toScheme).Nonempty := by
    obtain ⟨w, hw⟩ := hdom.denseRange.exists_mem_open C.U.isOpen C.ne
    exact ⟨w, hw⟩
  have hlft' : LocallyOfFiniteType (C.GG.hom ≫ C.π) := inferInstance
  obtain ⟨b', hb'x, hb'U⟩ :=
    (@GlobalTheory.T.exists_classical_point_lifting_residue_point C.G.toScheme hint (C.GG.hom ≫ C.π) hflat hlft' (C.GG.hom ⁻¹ᵁ C.U) hne p _).1 x
  have hcl : C.Cl (b' ≫ C.GG.hom) := by
    rintro _ ⟨s, rfl⟩
    have := hb'U ⟨s, rfl⟩
    rw [← Category.assoc, Scheme.Hom.comp_apply]
    exact this
  obtain ⟨b, hby, hbx⟩ := hI p (b' ≫ C.GG.hom) y hcl (htest p y τ).1
    (by rw [← Category.assoc, hb'x, hx]) b' rfl
  obtain ⟨c, hc, hcb⟩ := τ.lift b hby
  refine ⟨rPt p ≫ c, by rw [Category.assoc, hc], ?_⟩
  rw [Category.assoc, hcb, hbx, hb'x]

end GlobalTheory.ZJ
