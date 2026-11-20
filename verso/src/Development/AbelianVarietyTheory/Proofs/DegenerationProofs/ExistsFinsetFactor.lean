import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.PointDescentFactorization

/- English proof (translation)
Equip the data with the indicated structure. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Proceed by induction. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem exists_finset_factor {R Ω : Type} [CommRing R] [Field Ω] (g : ℚ →+* R) (hg : g.FiniteType)
    (φ : R →+* Ω) :
    ∃ s : Finset Ω, ∀ (k : Type) [Field k] (β : k →+* Ω), (↑s : Set Ω) ⊆ Set.range β →
      ∃ ψ : R →+* k, β.comp ψ = φ := by
  classical
  letI : Algebra ℚ R := g.toAlgebra
  have hft : Algebra.FiniteType ℚ R := hg
  obtain ⟨t, ht⟩ := hft.out
  refine ⟨t.image φ, fun k _ β hs => ?_⟩
  have hq : ∀ q : ℚ, φ (g q) ∈ β.fieldRange := by
    intro q
    have h := map_ratCast (φ.comp g) q
    rw [Rat.cast_id, RingHom.comp_apply] at h
    rw [h]
    exact SubfieldClass.ratCast_mem _ q
  have hall : ∀ x : R, φ x ∈ β.fieldRange := by
    intro x
    have hx : x ∈ Algebra.adjoin ℚ (t : Set R) := ht ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs (by simpa using ⟨x, hx, rfl⟩)
    | algebraMap q => exact hq q
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨(β.rangeRestrictFieldEquiv.symm.toRingHom).comp (φ.codRestrict β.fieldRange hall), ?_⟩
  ext x
  have h := β.rangeRestrictFieldEquiv.apply_symm_apply ⟨φ x, hall x⟩
  exact congrArg Subtype.val h

/- English proof (translation)
Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

A detailed English derivation is pending.
-/
theorem point_descends {Ω : Type} [Field Ω] {X : Scheme}
    (p : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℚ) [LocallyOfFiniteType p]
    (a : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω ⟶ X) :
    ∃ s : Finset Ω, ∀ (k : Type) [Field k] (β : k →+* Ω), (↑s : Set Ω) ⊆ Set.range (⇑β : k → Ω) →
      ∃ b : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k ⟶ X, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap β ≫ b = a := by
  let x₀ : (Spec (CommRingCat.of Ω)) := IsLocalRing.closedPoint Ω
  obtain ⟨R, j, hj, hx⟩ : ∃ (R : CommRingCat.{0}) (j : Spec R ⟶ X), IsOpenImmersion j ∧
      a x₀ ∈ Set.range j := by
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := a x₀) (U := ⊤) trivial
    exact ⟨_, hU.fromSpec, inferInstance, by rw [hU.range_fromSpec]; exact hxU⟩
  have hr : Set.range a ⊆ Set.range j := by
    rintro _ ⟨y, rfl⟩
    have : y = x₀ := Subsingleton.elim (α := PrimeSpectrum Ω) _ _
    rw [this]; exact hx
  let a' := IsOpenImmersion.lift j a hr
  have ha' : a' ≫ j = a := IsOpenImmersion.lift_fac j a hr
  obtain ⟨φ, hφ⟩ := Spec.map_surjective a'
  obtain ⟨g, hg⟩ := Spec.map_surjective (j ≫ p)
  have hl : LocallyOfFiniteType (Spec.map g) := by rw [hg]; infer_instance
  have hft : g.hom.FiniteType := HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType).mp hl
  obtain ⟨s, hs⟩ := exists_finset_factor g.hom hft φ.hom
  refine ⟨s, fun k _ β hβ => ?_⟩
  obtain ⟨ψ, hψ⟩ := hs k β hβ
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ j, ?_⟩
  rw [← ha', ← hφ, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext1
  exact hψ

end GlobalTheory.PointDescentFactorization
