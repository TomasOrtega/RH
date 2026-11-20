import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToXQFst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.FiniteSurjectivePointLift

/- English proof (translation)
Equip the data with the indicated structure. Extract witnesses or component facts from the available result. Equip the data with the indicated structure. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem exists_ringHom (L A : Type) [Field L] [CommRing A] [Nontrivial A] (φ : L →+* A) (hφ : φ.Finite) :
    ∃ ψ : A →+* AlgebraicClosure L, ψ.comp φ = algebraMap L (AlgebraicClosure L) := by
  letI := φ.toAlgebra
  haveI : Module.Finite L A := hφ
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI := Ideal.Quotient.field m
  haveI : Module.Finite L (A ⧸ m) := inferInstance
  haveI : Algebra.IsAlgebraic L (A ⧸ m) := inferInstance
  let j : (A ⧸ m) →ₐ[L] AlgebraicClosure L := IsAlgClosed.lift
  refine ⟨(j.comp (Ideal.Quotient.mkₐ L m)).toRingHom, ?_⟩
  ext x
  exact (j.comp (Ideal.Quotient.mkₐ L m)).commutes x

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components.

A detailed English derivation is pending.
-/
theorem exists_point (L : Type) [Field L] (P : Scheme.{0}) [Nonempty P] (g : P ⟶ Spec (CommRingCat.of L))
    [IsFinite g] : ∃ x : Spec (CommRingCat.of (AlgebraicClosure L)) ⟶ P,
      x ≫ g = Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L))) := by
  haveI hA : IsAffine P := isAffine_of_isAffineHom g
  have hfin : (g.appTop).hom.Finite := g.finite_app ⊤ (isAffineOpen_top _)
  let φ : L →+* Γ(P, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ g.appTop).hom
  have hφ : φ.Finite := by
    refine RingHom.Finite.comp hfin ?_
    exact RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of L)).inv).2
  haveI : Nonempty (⊤ : P.Opens) := ⟨⟨Classical.arbitrary P, trivial⟩⟩
  obtain ⟨ψ, hψ⟩ := exists_ringHom L Γ(P, ⊤) φ hφ
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ P.isoSpec.inv, ?_⟩
  rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv]
  simp only [← Spec.map_comp]
  congr 1
  ext x
  exact congrArg (fun f => f x) hψ

end PositivityTheory.Xgn.FiniteSurjectivePointLift

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem PositivityTheory.Xgn.finite_surjective_point_lift : ∀ (Z' Z : Scheme.{0}) (π : Z' ⟶ Z), IsFinite π → Surjective π → ∀ (L : Type) [Field L] (zZ : Sp L ⟶ Z),
    ∃ x : Sp (AlgebraicClosure L) ⟶ Z', x ≫ π = spMap (algebraMap L (AlgebraicClosure L)) ≫ zZ := by
  intro Z' Z π hfin hsurj L _ zZ
  haveI : Surjective (pullback.snd π zZ) := inferInstance
  obtain ⟨p, -⟩ := (pullback.snd π zZ).surjective (IsLocalRing.closedPoint L)
  haveI : Nonempty ↥(pullback π zZ) := ⟨p⟩
  obtain ⟨x, hx⟩ := FiniteSurjectivePointLift.exists_point L (pullback π zZ) (pullback.snd π zZ)
  refine ⟨x ≫ pullback.fst π zZ, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hx]
