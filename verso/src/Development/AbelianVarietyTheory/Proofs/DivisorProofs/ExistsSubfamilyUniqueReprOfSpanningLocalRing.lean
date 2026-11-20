import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce and unpack `⟨b⟩ w hw`. Use `haveI : Module.Finite R M := Module.Finite.of_basis b`. Set `V` to `IsLocalRing.ResidueField R ⊗[R] M`. Set `v : Fin g → V` to `fun a => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] w a`. Establish `hsp : Submodule.span (IsLocalRing.ResidueField R) (Set.range v) = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce and unpack `x -`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `tmul c m`.

Take `⟨cf, rfl⟩` from `hw m`. Establish `: c ⊗ₜ[R] (∑ a, cf a • w a) = c • ∑ a, cf a • v a`. Simplify using `only [v, TensorProduct.tmul_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_comm c (cf a) (1 : IsLocalRing.ResidueField R), smul_eq_mul, _root_.mul_one]`.

Rewrite using `[this]`. Use `Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => ?_)` and prove the remaining obligations. Conclude with `Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`. Consider the case `add x y hx hy => exact Submodule.add_mem _ hx hy`. Take `⟨κ, a, ha, hspa, hli⟩` from `exists_linearIndependent' (IsLocalRing.ResidueField R) v`.

Set `bk : Module.Basis κ (IsLocalRing.ResidueField R) V` to `Module.Basis.mk hli (by rw [hspa, hsp])`. Set `bV : Module.Basis (Fin d) (IsLocalRing.ResidueField R) V` to `Algebra.TensorProduct.basis (IsLocalRing.ResidueField R) b`. Set `eq : Fin d ≃ κ` to `bV.indexEquiv bk`. Use `⟨a ∘ eq, ?_⟩` and prove the remaining obligations. Establish `hspR : Submodule.span R (Set.range (w ∘ a ∘ eq)) = ⊤` using `IsLocalRing.span_eq_top_of_tmul_eq_basis (w ∘ a ∘ eq) (bk.reindex eq.symm) (fun i => by`.

Simplify using `[bk, v])`. Set `f : (Fin d → R) →ₗ[R] M` to `Fintype.linearCombination R (w ∘ a ∘ eq)`. Establish `hf : Function.Surjective f`. Rewrite using `[← LinearMap.range_eq_top, Fintype.range_linearCombination]`. Conclude with `hspR`.

Establish `hfi : Function.Injective f` using `OrzechProperty.injective_of_surjective_of_injective b.equivFun.symm.toLinearMap f b.equivFun.symm.injective hf`. Introduce `u`. Take `⟨cf, hcf⟩` from `hf u`. Use `⟨cf, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hcf]`.

Simplify using `[f, Fintype.linearCombination_apply]`. Introduce `cf' hcf'`. Apply `hfi` to reduce the goal to its premises. Rewrite using `[hcf]`. Simplify using `[f, Fintype.linearCombination_apply, hcf']`.
-/
theorem exists_subfamily_unique_repr_of_spanning_localRing
    (R : Type) [CommRing R] [IsLocalRing R] (M : Type) [AddCommGroup M] [Module R M] (d g : ℕ) :
    Nonempty (Module.Basis (Fin d) R M) → ∀ w : Fin g → M,
      (∀ u : M, ∃ cf : Fin g → R, u = ∑ a, cf a • w a) →
      ∃ e : Fin d → Fin g, ∀ u : M, ∃! cf : Fin d → R, u = ∑ a, cf a • w (e a) := by
  rintro ⟨b⟩ w hw
  haveI : Module.Finite R M := Module.Finite.of_basis b
  let V := IsLocalRing.ResidueField R ⊗[R] M
  let v : Fin g → V := fun a => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] w a
  have hsp : Submodule.span (IsLocalRing.ResidueField R) (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul c m =>
      obtain ⟨cf, rfl⟩ := hw m
      have : c ⊗ₜ[R] (∑ a, cf a • w a) = c • ∑ a, cf a • v a := by
        simp only [v, TensorProduct.tmul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
          TensorProduct.smul_tmul', smul_comm c (cf a) (1 : IsLocalRing.ResidueField R),
          smul_eq_mul, _root_.mul_one]
      rw [this]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => ?_)
      exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  obtain ⟨κ, a, ha, hspa, hli⟩ := exists_linearIndependent' (IsLocalRing.ResidueField R) v
  let bk : Module.Basis κ (IsLocalRing.ResidueField R) V :=
    Module.Basis.mk hli (by rw [hspa, hsp])
  let bV : Module.Basis (Fin d) (IsLocalRing.ResidueField R) V :=
    Algebra.TensorProduct.basis (IsLocalRing.ResidueField R) b
  let eq : Fin d ≃ κ := bV.indexEquiv bk
  refine ⟨a ∘ eq, ?_⟩
  have hspR : Submodule.span R (Set.range (w ∘ a ∘ eq)) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis (w ∘ a ∘ eq) (bk.reindex eq.symm) (fun i => by
      simp [bk, v])
  let f : (Fin d → R) →ₗ[R] M := Fintype.linearCombination R (w ∘ a ∘ eq)
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact hspR
  have hfi : Function.Injective f :=
    OrzechProperty.injective_of_surjective_of_injective b.equivFun.symm.toLinearMap f
      b.equivFun.symm.injective hf
  intro u
  obtain ⟨cf, hcf⟩ := hf u
  refine ⟨cf, ?_, ?_⟩
  · rw [← hcf]; simp [f, Fintype.linearCombination_apply]
  · intro cf' hcf'
    apply hfi
    rw [hcf]; simp [f, Fintype.linearCombination_apply, hcf']

end GlobalTheory
