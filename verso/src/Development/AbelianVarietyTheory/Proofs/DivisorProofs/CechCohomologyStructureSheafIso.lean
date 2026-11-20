import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechFiniteAffineCoverModelsStructureSheafStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a m => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem lid_baseChange_self {K M N : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N]
    [Module K N] (f : M →ₗ[K] N) (x : K ⊗[K] M) :
    TensorProduct.lid K N (f.baseChange K x) = f (TensorProduct.lid K M x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Establish `hmem : ∀ x : LinearMap.ker S.g.hom, (TensorProduct.lid K S.X₂).symm x.1 ∈ LinearMap.ker (S.g.hom.baseChange K)`. Introduce `x`. Rewrite using `[LinearMap.mem_ker]`. Apply `(TensorProduct.lid K S.X₃).injective` to reduce the goal to its premises. Rewrite using `[lid_baseChange_self, LinearEquiv.apply_symm_apply, map_zero]`.

Conclude with `x.2`. Set `q : LinearMap.ker S.g.hom →ₗ[K] H` to `θ ∘ₗ ((((TensorProduct.lid K S.X₂).symm : S.X₂ →ₗ[K] K ⊗[K] S.X₂) ∘ₗ (LinearMap.ker S.g.hom).subtype).codRestrict _ hmem)`. Establish `hq : ∀ x, q x = θ ⟨(TensorProduct.lid K S.X₂).symm x.1, hmem x⟩` using `fun x => rfl`. Establish `hsurj : Function.Surjective q`. Introduce `h`.

Take `⟨z, rfl⟩` from `hs h`. Establish `hz : TensorProduct.lid K S.X₂ z.1 ∈ LinearMap.ker S.g.hom`. Rewrite using `[LinearMap.mem_ker, ← lid_baseChange_self, z.2, map_zero]`. Use `⟨⟨_, hz⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hq]`.

Use `congr 1`. Conclude with `Subtype.ext (LinearEquiv.symm_apply_apply _ _)`. Establish `hker : LinearMap.range S.moduleCatToCycles = LinearMap.ker q`. Use extensionality with `x`. Rewrite using `[LinearMap.mem_ker, hq, hk]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Use `⟨(TensorProduct.lid K S.X₁).symm y, ?_⟩` and prove the remaining obligations. Apply `(TensorProduct.lid K S.X₂).injective` to reduce the goal to its premises. Rewrite using `[lid_baseChange_self, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`.

Both sides reduce to the same expression. Introduce and unpack `⟨y, hy⟩`. Use `⟨TensorProduct.lid K S.X₁ y, Subtype.ext ?_⟩` and prove the remaining obligations. Use `congrArg (TensorProduct.lid K S.X₂) hy` as an intermediate fact. Rewrite `this` using `[lid_baseChange_self, LinearEquiv.apply_symm_apply]`.

Conclude with `this`. Conclude with `⟨((q.quotKerEquivOfSurjective hsurj).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ S.moduleCatHomologyIso.toLinearEquiv.symm)⟩`.
-/
theorem nonempty_equiv_homology_of_baseChange_self {K : Type} [Field K]
    (S : ShortComplex (ModuleCat.{0} K)) {H : Type} [AddCommGroup H] [Module K H]
    (θ : LinearMap.ker (S.g.hom.baseChange K) →ₗ[K] H) (hs : Function.Surjective θ)
    (hk : ∀ z, θ z = 0 ↔ z.1 ∈ LinearMap.range (S.f.hom.baseChange K)) :
    Nonempty (H ≃ₗ[K] S.homology) := by
  have hmem : ∀ x : LinearMap.ker S.g.hom,
      (TensorProduct.lid K S.X₂).symm x.1 ∈ LinearMap.ker (S.g.hom.baseChange K) := by
    intro x
    rw [LinearMap.mem_ker]
    apply (TensorProduct.lid K S.X₃).injective
    rw [lid_baseChange_self, LinearEquiv.apply_symm_apply, map_zero]
    exact x.2
  let q : LinearMap.ker S.g.hom →ₗ[K] H :=
    θ ∘ₗ ((((TensorProduct.lid K S.X₂).symm : S.X₂ →ₗ[K] K ⊗[K] S.X₂) ∘ₗ
      (LinearMap.ker S.g.hom).subtype).codRestrict _ hmem)
  have hq : ∀ x, q x = θ ⟨(TensorProduct.lid K S.X₂).symm x.1, hmem x⟩ := fun x => rfl
  have hsurj : Function.Surjective q := by
    intro h
    obtain ⟨z, rfl⟩ := hs h
    have hz : TensorProduct.lid K S.X₂ z.1 ∈ LinearMap.ker S.g.hom := by
      rw [LinearMap.mem_ker, ← lid_baseChange_self, z.2, map_zero]
    refine ⟨⟨_, hz⟩, ?_⟩
    rw [hq]
    congr 1
    exact Subtype.ext (LinearEquiv.symm_apply_apply _ _)
  have hker : LinearMap.range S.moduleCatToCycles = LinearMap.ker q := by
    ext x
    rw [LinearMap.mem_ker, hq, hk]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨(TensorProduct.lid K S.X₁).symm y, ?_⟩
      apply (TensorProduct.lid K S.X₂).injective
      rw [lid_baseChange_self, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      rfl
    · rintro ⟨y, hy⟩
      refine ⟨TensorProduct.lid K S.X₁ y, Subtype.ext ?_⟩
      have := congrArg (TensorProduct.lid K S.X₂) hy
      rw [lid_baseChange_self, LinearEquiv.apply_symm_apply] at this
      exact this
  exact ⟨((q.quotKerEquivOfSurjective hsurj).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ
    S.moduleCatHomologyIso.toLinearEquiv.symm)⟩

/- English proof (translation)
Introduce `K _ X s κ _ _ D hsep haff hcov`. Take `⟨M⟩` from `GlobalTheory.T.orderedCech_finiteAffineCover_models_structureSheafCohomology K X s κ D hsep haff hcov`. Establish `hsp : spMap (algebraMap K K) = 𝟙 (Sp K)`. Rewrite using `[Algebra.algebraMap_self]`. Conclude with `Spec.map_id _`.

Establish `hP : IsPullback (𝟙 X) s s (spMap (algebraMap K K))`. Rewrite using `[hsp]`. Conclude with `IsPullback.id_horiz s`. Take `⟨h1s, h1k, h2s, h2k⟩` from `M.exact hP`. Take `⟨e1⟩` from `nonempty_equiv_homology_of_baseChange_self ((cechLB s (LB.triv X) D).sc' 0 1 2) (M.θ1 hP) h1s h1k`.

Take `⟨e2⟩` from `nonempty_equiv_homology_of_baseChange_self ((cechLB s (LB.triv X) D).sc' 1 2 3) (M.θ2 hP) h2s h2k`. Conclude with `⟨⟨e1 ≪≫ₗ ((cechLB s (LB.triv X) D).homologyIsoSc' 0 1 2 (by simp) (by simp)).toLinearEquiv.symm⟩, ⟨e2 ≪≫ₗ ((cechLB s (LB.triv X) D).homologyIsoSc' 1 2 3 (by simp) (by simp)).toLinearEquiv.symm⟩⟩`.
-/
theorem hO_equiv_cech : ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Sp K) (κ : Type) [LinearOrder κ]
    [Fintype κ] (D : κ → X.Opens), IsSeparated s → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ →
    Nonempty (HO1 s ≃ₗ[K] (cechLB s (LB.triv X) D).homology 1) ∧
      Nonempty (HO2 s ≃ₗ[K] (cechLB s (LB.triv X) D).homology 2) := by
  intro K _ X s κ _ _ D hsep haff hcov
  obtain ⟨M⟩ := GlobalTheory.T.orderedCech_finiteAffineCover_models_structureSheafCohomology K X s κ D hsep haff hcov
  have hsp : spMap (algebraMap K K) = 𝟙 (Sp K) := by
    rw [Algebra.algebraMap_self]; exact Spec.map_id _
  have hP : IsPullback (𝟙 X) s s (spMap (algebraMap K K)) := by
    rw [hsp]; exact IsPullback.id_horiz s
  obtain ⟨h1s, h1k, h2s, h2k⟩ := M.exact hP
  obtain ⟨e1⟩ := nonempty_equiv_homology_of_baseChange_self ((cechLB s (LB.triv X) D).sc' 0 1 2) (M.θ1 hP) h1s h1k
  obtain ⟨e2⟩ := nonempty_equiv_homology_of_baseChange_self ((cechLB s (LB.triv X) D).sc' 1 2 3) (M.θ2 hP) h2s h2k
  exact ⟨⟨e1 ≪≫ₗ ((cechLB s (LB.triv X) D).homologyIsoSc' 0 1 2 (by simp) (by simp)).toLinearEquiv.symm⟩,
    ⟨e2 ≪≫ₗ ((cechLB s (LB.triv X) D).homologyIsoSc' 1 2 3 (by simp) (by simp)).toLinearEquiv.symm⟩⟩

end GlobalTheory.AbCoh
