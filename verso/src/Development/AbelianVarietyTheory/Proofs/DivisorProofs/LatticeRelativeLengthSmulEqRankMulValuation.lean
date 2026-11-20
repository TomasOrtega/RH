import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsSaturatedSubmoduleIffExistsIsComplOfValuationR
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory.ScalLen

/- English proof (translation)
Introduce `C _ v M _ _ htf X hX c r hr`. Establish `hc : c ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hr`. Use `haveI : Module.IsTorsionFree (Int0 v) X := ⟨fun s hs x y hxy => by`.

Establish `hs0 : s ≠ 0` using `hs.ne_zero`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1 : s • ((x : M) - (y : M)) = 0`. Rewrite using `[smul_sub]`. Use `congrArg Subtype.val hxy` as an intermediate fact.

Simplify using `only [Submodule.coe_smul] at this`. Rewrite using `[this, sub_self]`. Conclude with `sub_eq_zero.1 (htf s _ hs0 h1)⟩`. Use `haveI : Module.Free (Int0 v) X := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing _ _`. Use `set n := finrank (Int0 v) X with hn`.

Set `b : Basis (Fin n) (Int0 v) X` to `Module.finBasis _ _`. Set `g : X →ₗ[Int0 v] M` to `(LinearMap.lsmul (Int0 v) M c).comp X.subtype`. Establish `hg : Function.Injective g`. Introduce `x y hxy`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `h1 : c • ((x : M) - (y : M)) = 0`. Rewrite using `[smul_sub]`. Simplify using `only [g, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.lsmul_apply] at hxy`. Rewrite using `[hxy, sub_self]`. Conclude with `sub_eq_zero.1 (htf c _ hc h1)`.

Establish `hrange : LinearMap.range g = X.map (LinearMap.lsmul (Int0 v) M c)`. Simplify using `only [g, LinearMap.range_comp, Submodule.range_subtype]`. Set `e : X ≃ₗ[Int0 v] X.map (LinearMap.lsmul (Int0 v) M c)` to `(LinearEquiv.ofInjective g hg).trans (LinearEquiv.ofEq _ _ hrange)`. Use `⟨n, b, b.map e, Matrix.diagonal (fun _ => c), fun k => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Basis.map_apply, Matrix.diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Both sides reduce to the same expression. Rewrite using `[Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Subring.coe_pow, AddValuation.map_pow, hr, ← WithTop.coe_nsmul, nsmul_eq_mul]`.
-/
theorem relLen_map_lsmul : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type)
    [AddCommGroup M] [Module (Int0 v) M], (∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0) →
    ∀ (X : Submodule (Int0 v) M), Module.Finite (Int0 v) X → ∀ (c : Int0 v) (r : ℝ),
      v (c : C) = r →
      RelLen v (X.map (LinearMap.lsmul (Int0 v) M c)) X ((finrank (Int0 v) X : ℝ) * r) := by
  intro C _ v M _ _ htf X hX c r hr
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hr
  haveI : Module.IsTorsionFree (Int0 v) X := ⟨fun s hs x y hxy => by
    have hs0 : s ≠ 0 := hs.ne_zero
    apply Subtype.ext
    have h1 : s • ((x : M) - (y : M)) = 0 := by
      rw [smul_sub]
      have := congrArg Subtype.val hxy
      simp only [Submodule.coe_smul] at this
      rw [this, sub_self]
    exact sub_eq_zero.1 (htf s _ hs0 h1)⟩
  haveI : Module.Free (Int0 v) X := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing _ _
  set n := finrank (Int0 v) X with hn
  let b : Basis (Fin n) (Int0 v) X := Module.finBasis _ _
  let g : X →ₗ[Int0 v] M := (LinearMap.lsmul (Int0 v) M c).comp X.subtype
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    have h1 : c • ((x : M) - (y : M)) = 0 := by
      rw [smul_sub]
      simp only [g, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.lsmul_apply] at hxy
      rw [hxy, sub_self]
    exact sub_eq_zero.1 (htf c _ hc h1)
  have hrange : LinearMap.range g = X.map (LinearMap.lsmul (Int0 v) M c) := by
    simp only [g, LinearMap.range_comp, Submodule.range_subtype]
  let e : X ≃ₗ[Int0 v] X.map (LinearMap.lsmul (Int0 v) M c) :=
    (LinearEquiv.ofInjective g hg).trans (LinearEquiv.ofEq _ _ hrange)
  refine ⟨n, b, b.map e, Matrix.diagonal (fun _ => c), fun k => ?_, ?_⟩
  · simp only [Basis.map_apply, Matrix.diagonal_apply, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  · rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Subring.coe_pow, AddValuation.map_pow, hr, ← WithTop.coe_nsmul, nsmul_eq_mul]

end GlobalTheory.ScalLen
