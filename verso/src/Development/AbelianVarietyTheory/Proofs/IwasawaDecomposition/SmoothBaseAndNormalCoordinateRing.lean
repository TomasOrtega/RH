import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem smooth_cbase {X : Scheme.{0}} {T : Type} [Finite T] (m : T → ℕ) (U : X.affineOpens) : Smooth (cbase m U) := by
  have h : Smooth (spMap (MvPolynomial.C : Γ(X, U.1) →+* CR m U)) := by
    refine (HasRingHomProperty.Spec_iff (P := @Smooth)).2 ?_
    exact RingHom.smooth_algebraMap.2 (⟨inferInstance, inferInstance⟩ : Algebra.Smooth Γ(X, U.1) (MvPolynomial (CellVar m) Γ(X, U.1)))
  have h' : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have h'' : Smooth U.2.fromSpec := inferInstance
  exact MorphismProperty.comp_mem @Smooth _ _ h h''

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem cell_smooth_normal : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (T : Type) [Finite T] (m : T → ℕ) (U : X.affineOpens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → Smooth (cbase m U) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp (CR m U)) := by
  intro X _ T _ m U hX
  have := smooth_cbase m U
  exact ⟨this, forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (cbase m U) hX⟩

end GlobalTheory.FlagEmb
