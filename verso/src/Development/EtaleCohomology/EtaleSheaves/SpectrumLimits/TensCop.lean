import Development.EtaleCohomology.EtaleSheaves.SpectrumLimits
import Mathlib.RingTheory.PiTensorProduct

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LevelsGenPf
open LateralTheory.E.CechLevelsPf LateralTheory.E.LevelsPf

open PiTensorProduct in
/- English proof (translation)
Introduce `A A' _ _ φ n`. Use `letI : Algebra A A' := φ.toAlgebra`. Use `⟨PiTensorProduct A (fun _ : Fin (n + 1) => A'), inferInstance, algebraMap A _, fun i => (singleAlgHom (A := fun _ => A') i).toRingHom, fun i => ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(singleAlgHom (A := fun _ => A') i).comp_algebraMap`. Rewrite using `[eq_top_iff]`.

Introduce `x _`. Proceed by induction on `x using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r f`. Rewrite using `[Algebra.smul_def]`. Use `Subring.mul_mem _ ?_ ?_` and prove the remaining obligations.

Rewrite using `[← (singleAlgHom (A := fun _ => A') 0).commutes r]`. Conclude with `Subring.subset_closure (Set.mem_iUnion.2 ⟨0, _, rfl⟩)`. Establish `: tprod A f = ∏ i, singleAlgHom (A` using `fun _ => A') i (f i) := by`. Simplify using `only [singleAlgHom_apply, ← tprod_prod]`. Use `congr 1`.

Conclude with `(Finset.univ_prod_mulSingle f).symm`. Rewrite using `[this]`. Conclude with `Subring.prod_mem _ fun i _ => Subring.subset_closure (Set.mem_iUnion.2 ⟨i, _, rfl⟩)`. Consider the case `add x y hx hy => exact Subring.add_mem _ (hx trivial) (hy trivial)`. Introduce `R _ g c hg`.

Use `letI : Algebra A R := c.toAlgebra`. Establish `hc : ∀ i r, g i (algebraMap A A' r) = algebraMap A R r` using `fun i r => by`. Express the relevant statement in the definitionally equal form `g i (φ r) = c r`. Rewrite using `[← RingHom.comp_apply, hg i]`. Set `ga : Fin (n + 1) → (A' →ₐ[A] R)` to `fun i => AlgHom.mk (g i) (hc i)`.

Set `F : MultilinearMap A (fun _ : Fin (n + 1) => A') R` to `(MultilinearMap.mkPiAlgebra A (Fin (n + 1)) R).compLinearMap (fun i => (ga i).toLinearMap)`. Set `H` to `liftAlgHom F (by simp [F]) (by intro x y; simp [F, Finset.prod_mul_distrib])`. Establish `hH : ∀ i a, H (singleAlgHom (A` using `fun _ => A') i a) = g i a := by`. Introduce `i a`. Express the relevant statement in the definitionally equal form `lift F (tprod A (MonoidHom.mulSingle (fun _ => A') i a)) = _`.

Rewrite using `[lift.tprod]`. Simplify using `only [F, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]`. Rewrite using `[Finset.prod_eq_single i]`. Simplify using `[ga]`. Introduce `j _ hj`.

Simplify using `[ga, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj]`. Simplify using the standard rewrite rules. Use `⟨H.toRingHom, ⟨fun i => ?_, ?_⟩, fun h2 ⟨h2l, h2c⟩ => ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Conclude with `hH i a`.

Use extensionality with `a`. Conclude with `H.commutes a`. Establish `hc2 : ∀ r, h2 (algebraMap A (PiTensorProduct A (fun _ : Fin (n + 1) => A')) r) = algebraMap A R r` using `fun r => by`. Express the relevant statement in the definitionally equal form `h2 (algebraMap A _ r) = c r`. Rewrite using `[← RingHom.comp_apply, h2c]`.

Set `H2 : (PiTensorProduct A (fun _ : Fin (n + 1) => A')) →ₐ[A] R` to `AlgHom.mk h2 hc2`. Establish `: H2 = H`. Apply `PiTensorProduct.algHom_ext` to reduce the goal to its premises. Introduce `i`. Use extensionality with `a`.

Express the relevant statement in the definitionally equal form `h2 (singleAlgHom (A := fun _ => A') i a) = H (singleAlgHom (A := fun _ => A') i a)`. Rewrite using `[hH]`. Conclude with `RingHom.congr_fun (h2l i) a`. Conclude with `congrArg AlgHom.toRingHom this`.
-/
theorem tensCop : TensCop := by
  intro A A' _ _ φ n
  letI : Algebra A A' := φ.toAlgebra
  refine ⟨PiTensorProduct A (fun _ : Fin (n + 1) => A'), inferInstance, algebraMap A _, fun i => (singleAlgHom (A := fun _ => A') i).toRingHom,
    fun i => ?_, ?_, ?_⟩
  · exact (singleAlgHom (A := fun _ => A') i).comp_algebraMap
  · rw [eq_top_iff]
    intro x _
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      rw [Algebra.smul_def]
      refine Subring.mul_mem _ ?_ ?_
      · rw [← (singleAlgHom (A := fun _ => A') 0).commutes r]
        exact Subring.subset_closure (Set.mem_iUnion.2 ⟨0, _, rfl⟩)
      · have : tprod A f = ∏ i, singleAlgHom (A := fun _ => A') i (f i) := by
          simp only [singleAlgHom_apply, ← tprod_prod]
          congr 1
          exact (Finset.univ_prod_mulSingle f).symm
        rw [this]
        exact Subring.prod_mem _ fun i _ => Subring.subset_closure (Set.mem_iUnion.2 ⟨i, _, rfl⟩)
    | add x y hx hy => exact Subring.add_mem _ (hx trivial) (hy trivial)
  · intro R _ g c hg
    letI : Algebra A R := c.toAlgebra
    have hc : ∀ i r, g i (algebraMap A A' r) = algebraMap A R r := fun i r => by
      change g i (φ r) = c r
      rw [← RingHom.comp_apply, hg i]
    let ga : Fin (n + 1) → (A' →ₐ[A] R) := fun i => AlgHom.mk (g i) (hc i)
    let F : MultilinearMap A (fun _ : Fin (n + 1) => A') R :=
      (MultilinearMap.mkPiAlgebra A (Fin (n + 1)) R).compLinearMap (fun i => (ga i).toLinearMap)
    let H := liftAlgHom F (by simp [F]) (by intro x y; simp [F, Finset.prod_mul_distrib])
    have hH : ∀ i a, H (singleAlgHom (A := fun _ => A') i a) = g i a := by
      intro i a
      change lift F (tprod A (MonoidHom.mulSingle (fun _ => A') i a)) = _
      rw [lift.tprod]
      simp only [F, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
      rw [Finset.prod_eq_single i]
      · simp [ga]
      · intro j _ hj
        simp [ga, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj]
      · simp
    refine ⟨H.toRingHom, ⟨fun i => ?_, ?_⟩, fun h2 ⟨h2l, h2c⟩ => ?_⟩
    · ext a
      exact hH i a
    · ext a
      exact H.commutes a
    · have hc2 : ∀ r, h2 (algebraMap A (PiTensorProduct A (fun _ : Fin (n + 1) => A')) r) = algebraMap A R r := fun r => by
        change h2 (algebraMap A _ r) = c r
        rw [← RingHom.comp_apply, h2c]
      let H2 : (PiTensorProduct A (fun _ : Fin (n + 1) => A')) →ₐ[A] R := AlgHom.mk h2 hc2
      have : H2 = H := by
        apply PiTensorProduct.algHom_ext
        intro i
        ext a
        change h2 (singleAlgHom (A := fun _ => A') i a) = H (singleAlgHom (A := fun _ => A') i a)
        rw [hH]
        exact RingHom.congr_fun (h2l i) a
      exact congrArg AlgHom.toRingHom this

end LateralTheory.E.LevelsGenPf
