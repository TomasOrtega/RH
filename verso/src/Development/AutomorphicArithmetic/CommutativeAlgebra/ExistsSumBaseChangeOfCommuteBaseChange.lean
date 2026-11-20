import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ComplexUniformizationSigOne
import Development.AutomorphicArithmetic.RealSpanData.RealData
import Development.AutomorphicArithmetic.RealSpanData.JSpan

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

/- English proof (translation)
Introduce `κ V V' R _ _ _ _ _ _ _ _ a a' T hT`. Use `set bV' := Module.finBasis ℚ V'`. Use `set bV := Module.finBasis ℚ V`. Use `set B := Algebra.TensorProduct.basis R bV`. Set `M : Fin (Module.finrank ℚ V') × Fin (Module.finrank ℚ V) → R` to `fun p => B.repr (T (1 ⊗ₜ bV' p.1)) p.2`.

Set `S : Submodule ℚ R` to `Submodule.span ℚ (Set.range M)`. Use `haveI : FiniteDimensional ℚ S := FiniteDimensional.span_of_finite ℚ (Set.finite_range M)`. Set `bS` to `Module.finBasis ℚ S`. Set `r : Fin (Module.finrank ℚ S) → R` to `fun l => (bS l : R)`. Establish `hr : LinearIndependent ℚ r` using `bS.linearIndependent.map' S.subtype (Submodule.ker_subtype S)`.

Set `c : Fin (Module.finrank ℚ S) → Fin (Module.finrank ℚ V') × Fin (Module.finrank ℚ V) → ℚ` to `fun l p => bS.repr ⟨M p, Submodule.subset_span ⟨p, rfl⟩⟩ l`. Establish `hM : ∀ p, M p = ∑ l, c l p • r l`. Introduce `p`. Establish `e` using `congrArg Subtype.val (bS.sum_repr ⟨M p, Submodule.subset_span ⟨p, rfl⟩⟩)`. Rewrite `e` using `[Submodule.coe_sum]`.

Conclude with `e.symm`. Set `h : Fin (Module.finrank ℚ S) → V' →ₗ[ℚ] V` to `fun l => bV'.constr ℚ (fun j => ∑ i, c l (j, i) • bV i)`. Establish `key : ∀ w : Fin (Module.finrank ℚ S) → V, ∑ l, r l ⊗ₜ[ℚ] w l = 0 → ∀ l, w l = 0`. Introduce `w hw l`. Apply `bV.ext_elem` to reduce the goal to its premises.

Introduce `i`. Establish `h1` using `congrArg (fun x => B.repr x i) hw`. Simplify using `only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, B, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h1`. Establish `h2 : ∑ l, bV.repr (w l) i • r l = 0`. Rewrite using `[← h1]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, mul_comm]`. Establish `h3` using `Fintype.linearIndependent_iff.1 hr (fun l => bV.repr (w l) i) h2 l`. Simplify using `using h3`. Establish `hT1 : ∀ x : V', T (1 ⊗ₜ x) = ∑ l, r l ⊗ₜ[ℚ] h l x`.

Establish `e : (T.restrictScalars ℚ).comp (TensorProduct.mk ℚ R V' 1) = ∑ l, (TensorProduct.mk ℚ R V (r l)).comp (h l)`. Use `bV'.ext fun j => ?_` and prove the remaining obligations. Establish `hs : T (1 ⊗ₜ bV' j) = ∑ i, M (j, i) ⊗ₜ[ℚ] bV i` using `by conv_lhs => rw [← B.sum_repr (T (1 ⊗ₜ bV' j))]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Conclude with `Algebra.TensorProduct.basis_repr_symm_apply' bV _ i`.

Simplify using `only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, TensorProduct.mk_apply, LinearMap.sum_apply, h, Module.Basis.constr_basis]`. Rewrite using `[hs]`. Simplify using `only [hM, TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.smul_tmul]`. Conclude with `Finset.sum_comm`. Introduce `x`.

Establish `e2` using `LinearMap.congr_fun e x`. Simplify using `using e2`. Use `⟨Module.finrank ℚ S, r, h, ?_, ?_⟩` and prove the remaining obligations. Introduce `l i`. Establish `hw : ∀ v : V', ∑ l, r l ⊗ₜ[ℚ] (h l (a' i v) - a i (h l v)) = 0`.

Introduce `v`. Establish `e` using `LinearMap.congr_fun (hT i) (1 ⊗ₜ v)`. Simplify using `only [LinearMap.comp_apply, LinearMap.baseChange_tmul] at e`. Rewrite `e` using `[hT1, hT1, map_sum]`. Simplify using `only [LinearMap.baseChange_tmul] at e`.

Simplify using `only [TensorProduct.tmul_sub, Finset.sum_sub_distrib, e, sub_self]`. Use extensionality with `v`. Establish `h4` using `key _ (hw v) l`. Simplify `h4` using `[sub_eq_zero]`. Use extensionality with `m`.

Simplify using `only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply, LinearMap.restrictScalars_apply]`. Rewrite using `[hT1]`. Simplify using `[LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.baseChange_tmul, TensorProduct.smul_tmul']`.
-/
theorem UpperTheory.exists_sum_baseChange_of_commute_baseChange :
    ∀ (κ V V' R : Type) [AddCommGroup V] [Module ℚ V] [AddCommGroup V'] [Module ℚ V'] [FiniteDimensional ℚ V] [FiniteDimensional ℚ V'] [CommRing R] [Algebra ℚ R] (a : κ → Module.End ℚ V) (a' : κ → Module.End ℚ V') (T : (R ⊗[ℚ] V') →ₗ[R] (R ⊗[ℚ] V)), (∀ i, T ∘ₗ (a' i).baseChange R = (a i).baseChange R ∘ₗ T) → ∃ (k : ℕ) (r : Fin k → R) (h : Fin k → V' →ₗ[ℚ] V), (∀ l i, h l ∘ₗ a' i = a i ∘ₗ h l) ∧ T = ∑ l, r l • (h l).baseChange R := by
  intro κ V V' R _ _ _ _ _ _ _ _ a a' T hT
  classical
  set bV' := Module.finBasis ℚ V'
  set bV := Module.finBasis ℚ V
  set B := Algebra.TensorProduct.basis R bV
  let M : Fin (Module.finrank ℚ V') × Fin (Module.finrank ℚ V) → R :=
    fun p => B.repr (T (1 ⊗ₜ bV' p.1)) p.2
  let S : Submodule ℚ R := Submodule.span ℚ (Set.range M)
  haveI : FiniteDimensional ℚ S := FiniteDimensional.span_of_finite ℚ (Set.finite_range M)
  let bS := Module.finBasis ℚ S
  let r : Fin (Module.finrank ℚ S) → R := fun l => (bS l : R)
  have hr : LinearIndependent ℚ r := bS.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  let c : Fin (Module.finrank ℚ S) → Fin (Module.finrank ℚ V') × Fin (Module.finrank ℚ V) → ℚ :=
    fun l p => bS.repr ⟨M p, Submodule.subset_span ⟨p, rfl⟩⟩ l
  have hM : ∀ p, M p = ∑ l, c l p • r l := by
    intro p
    have e := congrArg Subtype.val (bS.sum_repr ⟨M p, Submodule.subset_span ⟨p, rfl⟩⟩)
    rw [Submodule.coe_sum] at e
    exact e.symm
  let h : Fin (Module.finrank ℚ S) → V' →ₗ[ℚ] V :=
    fun l => bV'.constr ℚ (fun j => ∑ i, c l (j, i) • bV i)
  have key : ∀ w : Fin (Module.finrank ℚ S) → V, ∑ l, r l ⊗ₜ[ℚ] w l = 0 → ∀ l, w l = 0 := by
    intro w hw l
    apply bV.ext_elem
    intro i
    have h1 := congrArg (fun x => B.repr x i) hw
    simp only [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, B,
      Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h1
    have h2 : ∑ l, bV.repr (w l) i • r l = 0 := by
      rw [← h1]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Algebra.smul_def, mul_comm]
    have h3 := Fintype.linearIndependent_iff.1 hr (fun l => bV.repr (w l) i) h2 l
    simpa using h3
  have hT1 : ∀ x : V', T (1 ⊗ₜ x) = ∑ l, r l ⊗ₜ[ℚ] h l x := by
    have e : (T.restrictScalars ℚ).comp (TensorProduct.mk ℚ R V' 1) =
        ∑ l, (TensorProduct.mk ℚ R V (r l)).comp (h l) := by
      refine bV'.ext fun j => ?_
      have hs : T (1 ⊗ₜ bV' j) = ∑ i, M (j, i) ⊗ₜ[ℚ] bV i := by
        conv_lhs => rw [← B.sum_repr (T (1 ⊗ₜ bV' j))]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact Algebra.TensorProduct.basis_repr_symm_apply' bV _ i
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, TensorProduct.mk_apply,
        LinearMap.sum_apply, h, Module.Basis.constr_basis]
      rw [hs]
      simp only [hM, TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
      exact Finset.sum_comm
    intro x
    have e2 := LinearMap.congr_fun e x
    simpa using e2
  refine ⟨Module.finrank ℚ S, r, h, ?_, ?_⟩
  · intro l i
    have hw : ∀ v : V', ∑ l, r l ⊗ₜ[ℚ] (h l (a' i v) - a i (h l v)) = 0 := by
      intro v
      have e := LinearMap.congr_fun (hT i) (1 ⊗ₜ v)
      simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul] at e
      rw [hT1, hT1, map_sum] at e
      simp only [LinearMap.baseChange_tmul] at e
      simp only [TensorProduct.tmul_sub, Finset.sum_sub_distrib, e, sub_self]
    ext v
    have h4 := key _ (hw v) l
    simpa [sub_eq_zero] using h4
  · ext m
    simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.restrictScalars_apply]
    rw [hT1]
    simp [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.baseChange_tmul,
      TensorProduct.smul_tmul']
