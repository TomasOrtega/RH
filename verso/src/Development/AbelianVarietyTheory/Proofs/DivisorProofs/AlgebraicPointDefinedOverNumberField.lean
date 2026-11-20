import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AlgPt

/- English proof (translation)
Use `letI : Algebra F A := g.toAlgebra`. Use `letI : Algebra F Qb := (φ.comp g).toAlgebra`. Use `haveI : Algebra.FiniteType F A := hg`. Use `haveI : IsScalarTower ℚ F Qb := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)`. Use `haveI : Algebra.IsAlgebraic ℚ Qb := algebraicClosure.isAlgebraic ℚ ℂ`.

Use `haveI : Algebra.IsAlgebraic F Qb := Algebra.IsAlgebraic.tower_top (K := ℚ) F`. Set `φa : A →ₐ[F] Qb` to `{ φ with commutes' := fun _ => rfl }`. Take `⟨s, hs⟩` from `Algebra.FiniteType.out (R := F) (A := A)`. Set `K : IntermediateField F Qb` to `IntermediateField.adjoin F (φa '' (s : Set A))`. Use `haveI : Finite (φa '' (s : Set A)) := (s.finite_toSet.image _).to_subtype`.

Use `haveI : FiniteDimensional F K := IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x`. Establish `hmem : ∀ a, φ a ∈ K`. Introduce `a`. Establish `ha : a ∈ Algebra.adjoin F (s : Set A)` using `hs ▸ Algebra.mem_top`. Establish `h1 : φa a ∈ (Algebra.adjoin F (s : Set A)).map φa` using `⟨a, ha, rfl⟩`.

Rewrite `h1` using `[AlgHom.map_adjoin]`. Conclude with `IntermediateField.algebra_adjoin_le_adjoin F _ h1`. Use `haveI : NumberField K := NumberField.of_module_finite F K`. Conclude with `⟨K, inferInstance, inferInstance, K.val.toRingHom, φ.codRestrict K.toSubring hmem, rfl⟩`.
-/
theorem exists_numberField_ringHom (F : Type) [Field F] [NumberField F] (A : Type) [CommRing A]
    (g : F →+* A) (hg : g.FiniteType) (φ : A →+* Qb) :
    ∃ (K₀ : Type) (_ : Field K₀) (_ : NumberField K₀) (io₀ : K₀ →+* Qb) (ψ : A →+* K₀),
      io₀.comp ψ = φ := by
  letI : Algebra F A := g.toAlgebra
  letI : Algebra F Qb := (φ.comp g).toAlgebra
  haveI : Algebra.FiniteType F A := hg
  haveI : IsScalarTower ℚ F Qb := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Algebra.IsAlgebraic ℚ Qb := algebraicClosure.isAlgebraic ℚ ℂ
  haveI : Algebra.IsAlgebraic F Qb := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  let φa : A →ₐ[F] Qb := { φ with commutes' := fun _ => rfl }
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := F) (A := A)
  let K : IntermediateField F Qb := IntermediateField.adjoin F (φa '' (s : Set A))
  haveI : Finite (φa '' (s : Set A)) := (s.finite_toSet.image _).to_subtype
  haveI : FiniteDimensional F K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hmem : ∀ a, φ a ∈ K := by
    intro a
    have ha : a ∈ Algebra.adjoin F (s : Set A) := hs ▸ Algebra.mem_top
    have h1 : φa a ∈ (Algebra.adjoin F (s : Set A)).map φa := ⟨a, ha, rfl⟩
    rw [AlgHom.map_adjoin] at h1
    exact IntermediateField.algebra_adjoin_le_adjoin F _ h1
  haveI : NumberField K := NumberField.of_module_finite F K
  exact ⟨K, inferInstance, inferInstance, K.val.toRingHom, φ.codRestrict K.toSubring hmem, rfl⟩

/- English proof (translation)
Introduce `F _ _ W p hp w`. Take `⟨_, ⟨U, hU, rfl⟩, hx, -⟩` from `W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (w (IsLocalRing.closedPoint Qb))) isOpen_univ`. Establish `hU' : IsAffineOpen U` using `hU`. Establish `hr : Set.range w ⊆ Set.range hU'.fromSpec`. Rewrite using `[hU'.range_fromSpec]`.

Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[Subsingleton.elim y (IsLocalRing.closedPoint Qb)]`. Conclude with `hx`. Set `w' : Sp Qb ⟶ Spec Γ(W, U)` to `IsOpenImmersion.lift hU'.fromSpec w hr`. Establish `hw' : w' ≫ hU'.fromSpec = w` using `IsOpenImmersion.lift_fac _ _ _`.

Set `g` to `Spec.preimage (hU'.fromSpec ≫ p)`. Establish `hg : g.hom.FiniteType`. Rewrite using `[← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), Spec.map_preimage]`. Use `infer_instance`. Take `⟨K, i1, i2, io, ψ, h⟩` from `exists_numberField_ringHom F Γ(W, U) g.hom hg (Spec.preimage w').hom`.

Use `⟨K, i1, i2, io, Spec.map (CommRingCat.ofHom ψ) ≫ hU'.fromSpec, ?_⟩` and prove the remaining obligations. Rewrite using `[← hw', ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]`. Simplify using the standard rewrite rules.
-/
theorem exists_numberField_point :
    ∀ (F : Type) [Field F] [NumberField F] (W : Scheme.{0}) (p : W ⟶ Sp F), LocallyOfFiniteType p → ∀ w : Sp Qb ⟶ W, ∃ (K₀ : Type) (_ : Field K₀) (_ : NumberField K₀) (io₀ : K₀ →+* Qb) (w₀ : Sp K₀ ⟶ W), spMap io₀ ≫ w₀ = w := by
  intro F _ _ W p hp w
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (w (IsLocalRing.closedPoint Qb))) isOpen_univ
  have hU' : IsAffineOpen U := hU
  have hr : Set.range w ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y (IsLocalRing.closedPoint Qb)]
    exact hx
  let w' : Sp Qb ⟶ Spec Γ(W, U) := IsOpenImmersion.lift hU'.fromSpec w hr
  have hw' : w' ≫ hU'.fromSpec = w := IsOpenImmersion.lift_fac _ _ _
  let g := Spec.preimage (hU'.fromSpec ≫ p)
  have hg : g.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), Spec.map_preimage]
    infer_instance
  obtain ⟨K, i1, i2, io, ψ, h⟩ := exists_numberField_ringHom F Γ(W, U) g.hom hg
    (Spec.preimage w').hom
  refine ⟨K, i1, i2, io, Spec.map (CommRingCat.ofHom ψ) ≫ hU'.fromSpec, ?_⟩
  rw [← hw', ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
  simp

end GlobalTheory.AlgPt
