import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.AdeleComp

open TensorProduct

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts.
-/
theorem coord_zero {F A B E ι : Type*} [Field F] [AddCommGroup E] [Module F E]
    [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]
    (ℬ : Module.Basis ι F E) (f : A →ₗ[F] B) (c : ι →₀ A)
    (h : LinearMap.rTensor E f (c.sum fun i m => m ⊗ₜ[F] ℬ i) = 0) (i : ι) : f (c i) = 0 := by
  have h1 : (c.mapRange f (map_zero f)).sum (fun i m => m ⊗ₜ[F] ℬ i) = 0 := by
    rw [Finsupp.sum_mapRange_index (by intro i; simp)]
    rw [← h, Finsupp.sum, Finsupp.sum, map_sum]
    simp
  have h2 := TensorProduct.sum_tmul_basis_right_eq_zero ℬ _ h1
  simpa using DFunLike.congr_fun h2 i

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem adele_eq_zero {F : Type} [Field F] [NumberField F] (x : AF F)
    (hi : ∀ w, evInf F w x = 0) (hf : ∀ v, evFin F v x = 0) : x = 0 := by
  refine Prod.ext (funext fun w => hi w) ?_
  exact RestrictedProduct.ext _ _ fun v => hf v

/- English proof (translation)
Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Establish an intermediate fact. By extensionality, compare the relevant components. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Simplify using the standard rewrite rules.
-/
theorem tensor_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (a : AF F ⊗[F] E) (hi : ∀ w, compInf F E w a = 0) (hf : ∀ v, compFin F E v a = 0) : a = 0 := by
  let ℬ := Module.Basis.ofVectorSpace F E
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_right ℬ a
  have hc : c = 0 := by
    ext i
    refine adele_eq_zero _ (fun w => ?_) (fun v => ?_)
    · refine coord_zero ℬ (evInf F w).toLinearMap c ?_ i
      rw [← hi w]
      simp only [compInf, Finsupp.sum, map_sum]
      rfl
    · refine coord_zero ℬ (evFin F v).toLinearMap c ?_ i
      rw [← hf v]
      simp only [compFin, Finsupp.sum, map_sum]
      rfl
  simp [hc]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem eq_zero_of_comps (D : D7) (a : AE D) (hi : ∀ w, compInf D.host.F D.host.E w a = 0)
    (hf : ∀ v, cv D v a = 0) : a = 0 :=
  tensor_eq_zero a hi hf

end GlobalTheory.CompanionTheory.AdeleComp
