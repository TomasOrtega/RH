import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Use `(Set.finite_Iic (Finsupp.equivFunOnFinite.symm fun v : (Σ k, ι k) => m v.1)).subset ?_` and prove the remaining obligations. Introduce `d hd`. Simplify using `only [Set.mem_ofPred_eq] at hd`. Simplify using `only [Set.mem_Iic]`. Introduce `v`.

Establish `hcoord : (Finsupp.weight (blockWeight ι) d) v.1 = Finsupp.weight (fun x => blockWeight ι x v.1) d`. Simplify using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]`. Establish `hle : d v ≤ Finsupp.weight (fun x => blockWeight ι x v.1) d` using `Finsupp.le_weight _ (by simp [blockWeight]) d`. Rewrite `hle` using `[← hcoord, hd]`. Simplify using `using hle`.
-/
theorem finite_blockWeight_eq {K : Type} [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (m : K → ℕ) :
    {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m}.Finite := by
  classical
  refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm fun v : (Σ k, ι k) => m v.1)).subset ?_
  intro d hd
  simp only [Set.mem_ofPred_eq] at hd
  simp only [Set.mem_Iic]
  intro v
  have hcoord : (Finsupp.weight (blockWeight ι) d) v.1 =
      Finsupp.weight (fun x => blockWeight ι x v.1) d := by
    simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  have hle : d v ≤ Finsupp.weight (fun x => blockWeight ι x v.1) d :=
    Finsupp.le_weight _ (by simp [blockWeight]) d
  rw [← hcoord, hd] at hle
  simpa using hle

/- English proof (translation)
Rewrite using `[weightedHomogeneousSubmodule_eq_finsupp_supported]`. Use `(finite_blockWeight_eq ι m).to_subtype` as an intermediate fact. Conclude with `Module.Finite.of_basis (basisRestrictSupport F {d | Finsupp.weight (blockWeight ι) d = m})`.
-/
theorem finiteDimensional_weightedHomogeneousSubmodule (F : Type u) [Field F] {K : Type}
    [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (m : K → ℕ) :
    FiniteDimensional F (weightedHomogeneousSubmodule F (blockWeight ι) m) := by
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  have := (finite_blockWeight_eq ι m).to_subtype
  exact Module.Finite.of_basis
    (basisRestrictSupport F {d | Finsupp.weight (blockWeight ι) d = m})

/- English proof (translation)
Introduce `F _ K _ _ ι _ I m`. Use `finiteDimensional_weightedHomogeneousSubmodule F ι m` as an intermediate fact. Use `set S := weightedHomogeneousSubmodule F (blockWeight ι) m with hS`. Use `set J : Submodule F (MRing ι F) := I.restrictScalars F with hJ`. Set `π : MRing ι F →ₗ[F] MRing ι F ⧸ I` to `(Ideal.Quotient.mkₐ F I).toLinearMap`.

Set `q : S →ₗ[F] MRing ι F ⧸ I` to `π ∘ₗ S.subtype`. Establish `hrange : LinearMap.range q = gradedPiece I m`. Rewrite using `[LinearMap.range_comp, Submodule.range_subtype]`. Both sides reduce to the same expression. Establish `hkerπ : LinearMap.ker π = J`.

Use extensionality with `x`. Simplify using `[π, hJ, Ideal.Quotient.eq_zero_iff_mem]`. Establish `hker : (LinearMap.ker q).map S.subtype = S ⊓ J`. Rewrite using `[LinearMap.ker_comp, hkerπ, Submodule.map_comap_subtype]`. Establish `hkerdim : Module.finrank F (LinearMap.ker q) = Module.finrank F ↥(S ⊓ J)`.

Rewrite using `[← hker]`. Conclude with `(Submodule.equivMapOfInjective S.subtype S.injective_subtype _).finrank_eq`. Establish `hrn` using `LinearMap.finrank_range_add_finrank_ker q`. Rewrite `hrn` using `[hrange, hkerdim]`. Use linear arithmetic over natural numbers and integers.
-/
theorem GradedPieceQuot.proof : GradedPieceQuot.Statement.{u} := by
  intro F _ K _ _ ι _ I m
  have := finiteDimensional_weightedHomogeneousSubmodule F ι m
  set S := weightedHomogeneousSubmodule F (blockWeight ι) m with hS
  set J : Submodule F (MRing ι F) := I.restrictScalars F with hJ
  let π : MRing ι F →ₗ[F] MRing ι F ⧸ I := (Ideal.Quotient.mkₐ F I).toLinearMap
  let q : S →ₗ[F] MRing ι F ⧸ I := π ∘ₗ S.subtype
  have hrange : LinearMap.range q = gradedPiece I m := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have hkerπ : LinearMap.ker π = J := by
    ext x
    simp [π, hJ, Ideal.Quotient.eq_zero_iff_mem]
  have hker : (LinearMap.ker q).map S.subtype = S ⊓ J := by
    rw [LinearMap.ker_comp, hkerπ, Submodule.map_comap_subtype]
  have hkerdim : Module.finrank F (LinearMap.ker q) = Module.finrank F ↥(S ⊓ J) := by
    rw [← hker]
    exact (Submodule.equivMapOfInjective S.subtype S.injective_subtype _).finrank_eq
  have hrn := LinearMap.finrank_range_add_finrank_ker q
  rw [hrange, hkerdim] at hrn
  omega

end GroundTheory.Heights₂.Heights.NumbersDVR
