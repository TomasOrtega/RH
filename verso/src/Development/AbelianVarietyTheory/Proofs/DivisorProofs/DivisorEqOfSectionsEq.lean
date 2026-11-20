import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsLocallyGeneratedAffineStatement
open CategoryTheory AlgebraicGeometry GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv

namespace GlobalTheory.Cartier.CartierDiv

/- English proof (translation)
Establish `h1 : RegAt x ((g : X.functionField)⁻¹ * g)`. Rewrite using `[inv_mul_cancel₀ g.ne_zero]`. Conclude with `(unitAt_one x).regAt`. Take `⟨s, hs, hmem⟩` from `GlobalTheory.T.sections_locally_generated_affine X D x g hD _ h1`. Establish `hE' : E.RegularAt x (s • (g : X.functionField)⁻¹)` using `(mem_sections.1 (hle hmem)) x`.

Rewrite `hE'` using `[hE.regularAt_iff, Algebra.smul_def, algebraMap_top]`. Establish `hu : UnitAt x (fnOf ⊤ trivial s)` using `(unitAt_fnOf_iff (U := ⊤) (x := x) trivial trivial s).2 hs`. Establish `e : (g' : X.functionField) / g = (fnOf ⊤ trivial s)⁻¹ * (fnOf ⊤ trivial s * (g : X.functionField)⁻¹ * g')`. Use `hu.ne_zero` as an intermediate fact. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e]`. Conclude with `hu.inv.regAt.mul hE'`.
-/
theorem regAt_div_of_sections_le {X : Scheme.{0}} [IsIntegral X] [IsAffine X] {D E : CartierDiv X}
    (hle : D.sections ≤ E.sections) {x : X} {g g' : X.functionFieldˣ}
    (hD : D.IsEqn x g) (hE : E.IsEqn x g') :
    RegAt x ((g' : X.functionField) / g) := by
  have h1 : RegAt x ((g : X.functionField)⁻¹ * g) := by
    rw [inv_mul_cancel₀ g.ne_zero]; exact (unitAt_one x).regAt
  obtain ⟨s, hs, hmem⟩ := GlobalTheory.T.sections_locally_generated_affine X D x g hD _ h1
  have hE' : E.RegularAt x (s • (g : X.functionField)⁻¹) := (mem_sections.1 (hle hmem)) x
  rw [hE.regularAt_iff, Algebra.smul_def, algebraMap_top] at hE'
  have hu : UnitAt x (fnOf ⊤ trivial s) := (unitAt_fnOf_iff (U := ⊤) (x := x) trivial trivial s).2 hs
  have e : (g' : X.functionField) / g =
      (fnOf ⊤ trivial s)⁻¹ * (fnOf ⊤ trivial s * (g : X.functionField)⁻¹ * g') := by
    have := hu.ne_zero
    field_simp
  rw [e]
  exact hu.inv.regAt.mul hE'

/- English proof (translation)
Introduce `X _ _ D E h`. Use `ext_of_isEqn fun x => ?_` and prove the remaining obligations. Take `⟨g, hg⟩` from `D.exists_isEqn x`. Take `⟨g', hg'⟩` from `E.exists_isEqn x`. Establish `r1` using `regAt_div_of_sections_le h.le hg hg'`.

Establish `r2` using `regAt_div_of_sections_le h.ge hg' hg`. Establish `hne : (g' : X.functionField) / g ≠ 0` using `div_ne_zero g'.ne_zero g.ne_zero`. Establish `hu : UnitAt x ((g' : X.functionField) / g)` using `(unitAt_iff hne).2 ⟨r1, by rw [inv_div]; exact r2⟩`. Conclude with `⟨g', hg.iff_unitAt.2 hu, hg'⟩`.
-/
theorem eq_of_sections_eq : ∀ (X : Scheme.{0}) [IsIntegral X] [IsAffine X] (D E : CartierDiv X),
    D.sections = E.sections → D = E := by
  intro X _ _ D E h
  refine ext_of_isEqn fun x => ?_
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  obtain ⟨g', hg'⟩ := E.exists_isEqn x
  have r1 := regAt_div_of_sections_le h.le hg hg'
  have r2 := regAt_div_of_sections_le h.ge hg' hg
  have hne : (g' : X.functionField) / g ≠ 0 := div_ne_zero g'.ne_zero g.ne_zero
  have hu : UnitAt x ((g' : X.functionField) / g) := (unitAt_iff hne).2 ⟨r1, by rw [inv_div]; exact r2⟩
  exact ⟨g', hg.iff_unitAt.2 hu, hg'⟩

end GlobalTheory.Cartier.CartierDiv
