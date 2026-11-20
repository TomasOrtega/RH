import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Take `⟨x, hx⟩` from `hV`. Take `⟨_, ⟨f, rfl⟩, hxf, hfV⟩` from `(PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open (a := x) (u := (V : Set (Sp R))) hx V.isOpen`. Establish `hf0 : (f : Ω) ≠ 0`. Introduce `h0`. Establish `: f = 0` using `Subtype.ext h0`.

Substitute `this` using the available equality. Conclude with `hxf (Ideal.zero_mem _)`. Set `R' : Subalgebra o Ω` to `R ⊔ Algebra.adjoin o (({(f : Ω)⁻¹} : Finset Ω) : Set Ω)`. Establish `h : R ≤ R'` using `le_sup_left`. Establish `hinv : (f : Ω)⁻¹ ∈ R'` using `(le_sup_right : _ ≤ R') (Algebra.subset_adjoin (by simp))`.

Use `⟨R', h, hR.sup (Subalgebra.fg_adjoin_finset _), ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit ((Subalgebra.inclusion h).toRingHom f)` using `IsUnit.of_mul_eq_one (⟨(f : Ω)⁻¹, hinv⟩ : R') (Subtype.ext (mul_inv_cancel₀ hf0))`. Use `⟨IsOpenImmersion.lift V.ι (spMap (Subalgebra.inclusion h).toRingHom) ?_, IsOpenImmersion.lift_fac _ _ _⟩` and prove the remaining obligations. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨y, rfl⟩`.

Apply `hfV` to reduce the goal to its premises. Introduce `hm`. Conclude with `y.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)`.
-/
theorem exists_fg_subalgebra_spec_factors_open (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω]
    (R : Subalgebra o Ω) (hR : R.FG) (V : (Sp R).Opens) (hV : (V : Set (Sp R)).Nonempty) :
    ∃ (R' : Subalgebra o Ω) (h : R ≤ R'), R'.FG ∧
      ∃ τ : Sp R' ⟶ V.toScheme, τ ≫ V.ι = spMap (Subalgebra.inclusion h).toRingHom := by
  classical
  obtain ⟨x, hx⟩ := hV
  obtain ⟨_, ⟨f, rfl⟩, hxf, hfV⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open
      (a := x) (u := (V : Set (Sp R))) hx V.isOpen
  have hf0 : (f : Ω) ≠ 0 := by
    intro h0
    have : f = 0 := Subtype.ext h0
    subst this
    exact hxf (Ideal.zero_mem _)
  let R' : Subalgebra o Ω := R ⊔ Algebra.adjoin o (({(f : Ω)⁻¹} : Finset Ω) : Set Ω)
  have h : R ≤ R' := le_sup_left
  have hinv : (f : Ω)⁻¹ ∈ R' :=
    (le_sup_right : _ ≤ R') (Algebra.subset_adjoin (by simp))
  refine ⟨R', h, hR.sup (Subalgebra.fg_adjoin_finset _), ?_⟩
  have hu : IsUnit ((Subalgebra.inclusion h).toRingHom f) :=
    IsUnit.of_mul_eq_one (⟨(f : Ω)⁻¹, hinv⟩ : R') (Subtype.ext (mul_inv_cancel₀ hf0))
  refine ⟨IsOpenImmersion.lift V.ι (spMap (Subalgebra.inclusion h).toRingHom) ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨y, rfl⟩
  apply hfV
  intro hm
  exact y.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)

end GlobalTheory
