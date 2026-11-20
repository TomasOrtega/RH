import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MSplitDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TopNilDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SpBasis

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

/- English proof (translation)
Introduce `κ _ _ n R _ P hm hd`. Establish `hb` using `fun j => (UpperTheory.V.AlgebraTools.splitAlg_basis n R (P j) (hm j) (hd j)).1`. Use `choose bj hbj using hb`. Set `f : ∀ j, SplitAlg (P j) n →ₐ[R] MSplitAlg P n` to `fun j => SplitAlg.lift (P j) n (MSplitAlg.root P n j) (MSplitAlg.prod_root P n j)`. Set `M : MultilinearMap R (fun j => SplitAlg (P j) n) (MSplitAlg P n)` to `(MultilinearMap.mkPiAlgebra R κ (MSplitAlg P n)).compLinearMap (fun j => (f j).toLinearMap)`.

Establish `hM : ∀ x, M x = ∏ j, f j (x j)` using `fun x => by`. Simplify using `[M, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]`. Set `ψ : (⨂[R] j, SplitAlg (P j) n) →ₐ[R] MSplitAlg P n` to `PiTensorProduct.liftAlgHom M (by rw [hM]; simp) (fun x y => by rw [hM, hM, hM]; simp [Finset.prod_mul_distrib])`. Establish `hψt : ∀ x, ψ (PiTensorProduct.tprod R x) = ∏ j, f j (x j)` using `fun x => by`. Simplify using `[ψ, hM]`.

Establish `hψs : ∀ j x, ψ (PiTensorProduct.singleAlgHom j x) = f j x` using `fun j x => by`. Rewrite using `[PiTensorProduct.singleAlgHom_apply, hψt, Fintype.prod_eq_single j (fun k hk => by simp [Pi.mulSingle_eq_of_ne hk])]`. Simplify using the standard rewrite rules. Set `φ : MSplitAlg P n →ₐ[R] (⨂[R] j, SplitAlg (P j) n)` to `MSplitAlg.lift P n (fun j i => PiTensorProduct.singleAlgHom j (SplitAlg.root (P j) n i)) (fun j => by`. Use `congrArg (Polynomial.map (PiTensorProduct.singleAlgHom (R := R) (A := fun j => SplitAlg (P j) n) j).toRingHom) (SplitAlg.prod_root (P j) n)` as an intermediate fact.

Simplify using `only [Polynomial.map_prod, Polynomial.map_map, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.coe_coe] at this`. Conclude with `this)`. Establish `h1 : ψ.comp φ = AlgHom.id R (MSplitAlg P n)` using `MSplitAlg.hom_ext P n (fun j i => by`. Simplify using `only [AlgHom.comp_apply, AlgHom.id_apply, φ, MSplitAlg.lift_root, hψs, f, SplitAlg.lift_root])`. Establish `h2 : φ.comp ψ = AlgHom.id R _` using `PiTensorProduct.algHom_ext (fun j => SplitAlg.hom_ext (P j) n (fun i => by`.

Simplify using `only [AlgHom.comp_apply, AlgHom.id_apply, hψs, f, SplitAlg.lift_root, φ, MSplitAlg.lift_root]))`. Set `e : MSplitAlg P n ≃ₐ[R] (⨂[R] j, SplitAlg (P j) n)` to `AlgEquiv.ofAlgHom φ ψ h2 h1`. Use `⟨(Basis.piTensorProduct bj).map e.symm.toLinearEquiv, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.map_apply, Basis.piTensorProduct_apply]`. Use `show ψ _ = _`.

Rewrite using `[hψt]`. Use `Finset.prod_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[hbj j (c j), map_prod]`. Simplify using `only [map_pow, f, SplitAlg.lift_root]`.
-/
theorem UpperTheory.V.AlgebraTools.mSplitAlg_basis :
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (n : ℕ) (R : Type) [CommRing R] (P : κ → Polynomial R), (∀ j, (P j).Monic) → (∀ j, (P j).natDegree = n) →
      ∃ b : Module.Basis (κ → ∀ i : Fin n, Fin (n - i)) R (MSplitAlg P n), ∀ c, b c = ∏ j, ∏ i, MSplitAlg.root P n j i ^ (c j i : ℕ) := by
  intro κ _ _ n R _ P hm hd
  have hb := fun j => (UpperTheory.V.AlgebraTools.splitAlg_basis n R (P j) (hm j) (hd j)).1
  choose bj hbj using hb
  let f : ∀ j, SplitAlg (P j) n →ₐ[R] MSplitAlg P n := fun j =>
    SplitAlg.lift (P j) n (MSplitAlg.root P n j) (MSplitAlg.prod_root P n j)
  let M : MultilinearMap R (fun j => SplitAlg (P j) n) (MSplitAlg P n) :=
    (MultilinearMap.mkPiAlgebra R κ (MSplitAlg P n)).compLinearMap (fun j => (f j).toLinearMap)
  have hM : ∀ x, M x = ∏ j, f j (x j) := fun x => by
    simp [M, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  let ψ : (⨂[R] j, SplitAlg (P j) n) →ₐ[R] MSplitAlg P n :=
    PiTensorProduct.liftAlgHom M (by rw [hM]; simp)
      (fun x y => by rw [hM, hM, hM]; simp [Finset.prod_mul_distrib])
  have hψt : ∀ x, ψ (PiTensorProduct.tprod R x) = ∏ j, f j (x j) := fun x => by
    simp [ψ, hM]
  have hψs : ∀ j x, ψ (PiTensorProduct.singleAlgHom j x) = f j x := fun j x => by
    rw [PiTensorProduct.singleAlgHom_apply, hψt,
      Fintype.prod_eq_single j (fun k hk => by simp [Pi.mulSingle_eq_of_ne hk])]
    simp
  let φ : MSplitAlg P n →ₐ[R] (⨂[R] j, SplitAlg (P j) n) :=
    MSplitAlg.lift P n (fun j i => PiTensorProduct.singleAlgHom j (SplitAlg.root (P j) n i)) (fun j => by
      have := congrArg (Polynomial.map
        (PiTensorProduct.singleAlgHom (R := R) (A := fun j => SplitAlg (P j) n) j).toRingHom)
        (SplitAlg.prod_root (P j) n)
      simp only [Polynomial.map_prod, Polynomial.map_map, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap,
        Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.coe_coe] at this
      exact this)
  have h1 : ψ.comp φ = AlgHom.id R (MSplitAlg P n) := MSplitAlg.hom_ext P n (fun j i => by
    simp only [AlgHom.comp_apply, AlgHom.id_apply, φ, MSplitAlg.lift_root, hψs, f, SplitAlg.lift_root])
  have h2 : φ.comp ψ = AlgHom.id R _ := PiTensorProduct.algHom_ext (fun j => SplitAlg.hom_ext (P j) n (fun i => by
    simp only [AlgHom.comp_apply, AlgHom.id_apply, hψs, f, SplitAlg.lift_root, φ, MSplitAlg.lift_root]))
  let e : MSplitAlg P n ≃ₐ[R] (⨂[R] j, SplitAlg (P j) n) := AlgEquiv.ofAlgHom φ ψ h2 h1
  refine ⟨(Basis.piTensorProduct bj).map e.symm.toLinearEquiv, fun c => ?_⟩
  rw [Module.Basis.map_apply, Basis.piTensorProduct_apply]
  show ψ _ = _
  rw [hψt]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [hbj j (c j), map_prod]
  simp only [map_pow, f, SplitAlg.lift_root]
