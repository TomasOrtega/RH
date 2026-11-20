import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory.AdicColimit

namespace GlobalTheory.FlatComplete

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `Submodule.smul_induction_on (p := fun y => ∀ i, b.repr y i ∈ J) hx ?_ ?_` and prove the remaining obligations. Introduce `r hr y _ i`. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul]`.

Conclude with `J.mul_mem_right _ hr`. Introduce `y z hy hz i`. Rewrite using `[map_add, Finsupp.add_apply]`. Conclude with `J.add_mem (hy i) (hz i)`. Introduce `h`.

Rewrite using `[← b.sum_repr x]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top`.
-/
theorem mem_smul_top_iff_repr {O M ι : Type} [CommRing O] [AddCommGroup M] [Module O M] [Fintype ι]
    (b : Module.Basis ι O M) (J : Ideal O) (x : M) :
    x ∈ J • (⊤ : Submodule O M) ↔ ∀ i, b.repr x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on (p := fun y => ∀ i, b.repr y i ∈ J) hx ?_ ?_
    · intro r hr y _ i
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact J.mul_mem_right _ hr
    · intro y z hy hz i
      rw [map_add, Finsupp.add_apply]
      exact J.add_mem (hy i) (hz i)
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

/- English proof (translation)
Establish `hR : ∀ (n : ℕ) (r : O), r ∈ (J ^ n • ⊤ : Submodule O O) ↔ r ∈ J ^ n` using `fun n r => by`. Rewrite using `[smul_eq_mul, Ideal.mul_top]`. Establish `key : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD (J ^ n • ⊤ : Submodule O M)] ↔ ∀ i, b.repr x i ≡ b.repr y i [SMOD (J ^ n • ⊤ : Submodule O O)]` using `fun n x y => by`. Simplify using `only [SModEq.sub_mem, hR, mem_smul_top_iff_repr b (J ^ n), map_sub, Finsupp.sub_apply]`. Rewrite using `[isAdicComplete_iff]`.

Use `⟨isHausdorff_iff.2 fun x hx => ?_, isPrecomplete_iff.2 fun f hf => ?_⟩` and prove the remaining obligations. Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `i`. Rewrite using `[map_zero, Finsupp.zero_apply]`. Use `IsHausdorff.haus (inferInstance : IsHausdorff J O) _ fun n => ?_` and prove the remaining obligations.

Use `(key n x 0).1 (hx n) i` as an intermediate fact. Rewrite `this` using `[map_zero, Finsupp.zero_apply]`. Then use the resulting hypothesis. Establish `hc : ∀ i, ∃ L : O, ∀ n, b.repr (f n) i ≡ L [SMOD (J ^ n • ⊤ : Submodule O O)]` using `fun i => IsPrecomplete.prec (inferInstance : IsPrecomplete J O) fun hmn => (key _ _ _).1 (hf hmn) i choose L hL using hc`. Use `⟨b.equivFun.symm L, fun n => (key n _ _).2 fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← b.equivFun_apply (b.equivFun.symm L), LinearEquiv.apply_symm_apply]`.

Conclude with `hL i n`.
-/
theorem isAdicComplete_of_finite_basis {O M ι : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [Fintype ι] (b : Module.Basis ι O M) (J : Ideal O) [hO : IsAdicComplete J O] :
    IsAdicComplete J M := by
  have hR : ∀ (n : ℕ) (r : O), r ∈ (J ^ n • ⊤ : Submodule O O) ↔ r ∈ J ^ n := fun n r => by
    rw [smul_eq_mul, Ideal.mul_top]
  have key : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD (J ^ n • ⊤ : Submodule O M)] ↔
      ∀ i, b.repr x i ≡ b.repr y i [SMOD (J ^ n • ⊤ : Submodule O O)] := fun n x y => by
    simp only [SModEq.sub_mem, hR, mem_smul_top_iff_repr b (J ^ n), map_sub, Finsupp.sub_apply]
  rw [isAdicComplete_iff]
  refine ⟨isHausdorff_iff.2 fun x hx => ?_, isPrecomplete_iff.2 fun f hf => ?_⟩
  · apply b.repr.injective
    ext i
    rw [map_zero, Finsupp.zero_apply]
    refine IsHausdorff.haus (inferInstance : IsHausdorff J O) _ fun n => ?_
    have := (key n x 0).1 (hx n) i
    rwa [map_zero, Finsupp.zero_apply] at this
  · have hc : ∀ i, ∃ L : O, ∀ n, b.repr (f n) i ≡ L [SMOD (J ^ n • ⊤ : Submodule O O)] := fun i =>
      IsPrecomplete.prec (inferInstance : IsPrecomplete J O) fun hmn => (key _ _ _).1 (hf hmn) i
    choose L hL using hc
    refine ⟨b.equivFun.symm L, fun n => (key n _ _).2 fun i => ?_⟩
    rw [← b.equivFun_apply (b.equivFun.symm L), LinearEquiv.apply_symm_apply]
    exact hL i n

/- English proof (translation)
Establish `: Module.Free O A` using `Module.free_of_flat_of_isLocalRing`. Use `hO` as an intermediate fact. Conclude with `(IsAdicComplete.map_algebraMap_iff (I := J) (M := A)).2 (isAdicComplete_of_finite_basis (Module.Free.chooseBasis O A) J)`.
-/
theorem isAdicComplete_of_finite_flat (O : Type) [CommRing O] [IsLocalRing O] (J : Ideal O)
    (hO : IsAdicComplete J O) (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A]
    [Module.Flat O A] : IsAdicComplete (J.map (algebraMap O A)) A := by
  have : Module.Free O A := Module.free_of_flat_of_isLocalRing
  have := hO
  exact (IsAdicComplete.map_algebraMap_iff (I := J) (M := A)).2
    (isAdicComplete_of_finite_basis (Module.Free.chooseBasis O A) J)

end GlobalTheory.FlatComplete
