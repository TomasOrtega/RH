import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.DinvExact

open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis F L`. Set `e : L ⊗[F] X ≃ₗ[F] (Module.Free.ChooseBasisIndex F L →₀ X)` to `(TensorProduct.congr b.repr (LinearEquiv.refl F X)).trans (finsuppScalarLeft F X _)`. Establish `nat : ∀ (f : X →ₗ[F] X) (w : L ⊗[F] X) j, e (f.baseChange L w) j = f (e w j)`. Introduce `f w j`. Proceed by induction on `w using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a x => simp [e, finsuppScalarLeft_apply_tmul_apply]`. Consider the case `add u v hu hv => simp only [map_add, Finsupp.add_apply, hu, hv]`. Establish `hmem : ∀ j, e z j ∈ ⨅ k, LinearMap.ker (A k - LinearMap.id)`. Introduce `j`.

Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`. Introduce `k`. Establish `h` using `congrArg (fun w => e w j) (hz k)`. Simplify `h` using `only [nat]`. Establish `hsingle : ∀ j (x : X), e.symm (Finsupp.single j x) = b j ⊗ₜ[F] x`.

Introduce `j x`. Simplify using `[e]`. Establish `hz' : z = (e z).sum (fun j x => b j ⊗ₜ[F] x)` using `by conv_lhs => rw [← e.symm_apply_apply z, ← Finsupp.sum_single (e z)]`. Simplify using `only [Finsupp.sum, map_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => hsingle j _`.

Rewrite using `[hz']`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.tmul_mem_baseChange_of_mem _ (hmem j)`.
-/
private theorem mem_baseChange_iInf_ker_sub_id_of_baseChange_eq {F L X ι : Type} [Field F] [Field L] [Algebra F L]
    [AddCommGroup X] [Module F X] (A : ι → X →ₗ[F] X) (z : L ⊗[F] X)
    (hz : ∀ k, (A k).baseChange L z = z) :
    z ∈ (⨅ k, LinearMap.ker (A k - LinearMap.id)).baseChange L := by
  let b := Module.Free.chooseBasis F L
  let e : L ⊗[F] X ≃ₗ[F] (Module.Free.ChooseBasisIndex F L →₀ X) :=
    (TensorProduct.congr b.repr (LinearEquiv.refl F X)).trans (finsuppScalarLeft F X _)
  have nat : ∀ (f : X →ₗ[F] X) (w : L ⊗[F] X) j, e (f.baseChange L w) j = f (e w j) := by
    intro f w j
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [e, finsuppScalarLeft_apply_tmul_apply]
    | add u v hu hv => simp only [map_add, Finsupp.add_apply, hu, hv]
  have hmem : ∀ j, e z j ∈ ⨅ k, LinearMap.ker (A k - LinearMap.id) := by
    intro j
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    intro k
    have h := congrArg (fun w => e w j) (hz k)
    simpa only [nat] using h
  have hsingle : ∀ j (x : X), e.symm (Finsupp.single j x) = b j ⊗ₜ[F] x := by
    intro j x
    simp [e]
  have hz' : z = (e z).sum (fun j x => b j ⊗ₜ[F] x) := by
    conv_lhs => rw [← e.symm_apply_apply z, ← Finsupp.sum_single (e z)]
    simp only [Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => hsingle j _
  rw [hz']
  exact Submodule.sum_mem _ fun j _ => Submodule.tmul_mem_baseChange_of_mem _ (hmem j)

/- English proof (translation)
Unfold `DinvExt`. Introduce `F G B _ _ _ _ σ L _ _ V _ _ ρ`. Set `T : G → (V ⊗[F] B) →ₗ[F] (V ⊗[F] B)` to `fun g => AlgebraTensorModule.map (ρ g) (σ g)`. Establish `hD : Dinv σ ρ = ⨅ g, LinearMap.ker (T g - LinearMap.id)` using `rfl`. Establish `comm : ∀ g (w : (L ⊗[F] V) ⊗[F] B), AlgebraTensorModule.assoc F F L L V B (AlgebraTensorModule.map (extRep L ρ g) (σ g) w) = (T g).baseChange L (AlgebraTensorModule.assoc F F L L V B w)`.

Introduce `g w`. Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul u c`. Proceed by induction on `u using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a v => simp [T, extRep, AlgebraTensorModule.map_tmul]`. Consider the case `add u₁ u₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add, h₁, h₂]`. Consider the case `add u v hu hv => simp only [map_add, hu, hv]`. Use extensionality with `z`.

Rewrite using `[Submodule.mem_map_equiv]`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Rewrite using `[hD]`. Apply `mem_baseChange_iInf_ker_sub_id_of_baseChange_eq` to reduce the goal to its premises.

Introduce `g`. Establish `h : AlgebraTensorModule.map (extRep L ρ g) (σ g) ((AlgebraTensorModule.assoc F F L L V B).symm z) = (AlgebraTensorModule.assoc F F L L V B).symm z`. Simplify using `only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hz`. Conclude with `hz g`. Establish `h2` using `congrArg (AlgebraTensorModule.assoc F F L L V B) h`.

Rewrite `h2` using `[comm, LinearEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Introduce `hz`. Simplify using `only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`. Introduce `g`. Apply `(AlgebraTensorModule.assoc F F L L V B).injective` to reduce the goal to its premises.

Rewrite using `[comm, LinearEquiv.apply_symm_apply]`. Take `⟨w, rfl⟩` from `hz`. Establish `hfix : T g ∘ₗ (Dinv σ ρ).subtype = (Dinv σ ρ).subtype`. Use `LinearMap.ext fun s => ?_` and prove the remaining obligations. Establish `hs` using `s.2`.

Simplify using `only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hs`. Conclude with `hs g`. Rewrite using `[← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hfix]`.
-/
theorem UpperTheory.Gal.crystallineComparison.dinvExt_of :
    DinvExt := by
  unfold DinvExt
  intro F G B _ _ _ _ σ L _ _ V _ _ ρ
  let T : G → (V ⊗[F] B) →ₗ[F] (V ⊗[F] B) := fun g => AlgebraTensorModule.map (ρ g) (σ g)
  have hD : Dinv σ ρ = ⨅ g, LinearMap.ker (T g - LinearMap.id) := rfl
  have comm : ∀ g (w : (L ⊗[F] V) ⊗[F] B),
      AlgebraTensorModule.assoc F F L L V B (AlgebraTensorModule.map (extRep L ρ g) (σ g) w) =
        (T g).baseChange L (AlgebraTensorModule.assoc F F L L V B w) := by
    intro g w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul u c =>
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul a v => simp [T, extRep, AlgebraTensorModule.map_tmul]
      | add u₁ u₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add, h₁, h₂]
    | add u v hu hv => simp only [map_add, hu, hv]
  ext z
  rw [Submodule.mem_map_equiv]
  constructor
  · intro hz
    rw [hD]
    apply mem_baseChange_iInf_ker_sub_id_of_baseChange_eq
    intro g
    have h : AlgebraTensorModule.map (extRep L ρ g) (σ g)
        ((AlgebraTensorModule.assoc F F L L V B).symm z) =
          (AlgebraTensorModule.assoc F F L L V B).symm z := by
      simp only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hz
      exact hz g
    have h2 := congrArg (AlgebraTensorModule.assoc F F L L V B) h
    rwa [comm, LinearEquiv.apply_symm_apply] at h2
  · intro hz
    simp only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro g
    apply (AlgebraTensorModule.assoc F F L L V B).injective
    rw [comm, LinearEquiv.apply_symm_apply]
    obtain ⟨w, rfl⟩ := hz
    have hfix : T g ∘ₗ (Dinv σ ρ).subtype = (Dinv σ ρ).subtype := by
      refine LinearMap.ext fun s => ?_
      have hs := s.2
      simp only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hs
      exact hs g
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hfix]
