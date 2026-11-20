import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `X Z f hf x hx`. Rewrite using `[← closure_subset_iff_isClosed]`. Introduce `w hw`. Establish `h : x ⤳ w` using `specializes_iff_mem_closure.mpr hw`. Establish `e : f w = f x` using `(h.map f.continuous).mem_closed hx rfl`.

Establish `hd` using `(f.isDiscrete_preimage_singleton (f x)).to_subtype`. Establish `hs : (⟨x, rfl⟩ : f ⁻¹' {f x}) ⤳ ⟨w, e⟩` using `Topology.IsInducing.subtypeVal.specializes_iff.mp h`. Conclude with `congrArg Subtype.val hs.eq.symm`.
-/
theorem isClosed_singleton_of_isFinite : ∀ (X Z : Scheme.{0}) (f : X ⟶ Z), IsFinite f → ∀ x : X,
    IsClosed ({f x} : Set Z) → IsClosed ({x} : Set X) := by
  intro X Z f hf x hx
  rw [← closure_subset_iff_isClosed]
  intro w hw
  have h : x ⤳ w := specializes_iff_mem_closure.mpr hw
  have e : f w = f x := (h.map f.continuous).mem_closed hx rfl
  have hd := (f.isDiscrete_preimage_singleton (f x)).to_subtype
  have hs : (⟨x, rfl⟩ : f ⁻¹' {f x}) ⤳ ⟨w, e⟩ := Topology.IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val hs.eq.symm

end GlobalTheory
