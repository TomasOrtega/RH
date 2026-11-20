import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx i`. Use `Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun y z hy hz => ?_)` and prove the remaining obligations. Simplify using `using J.mul_mem_right _ hr`. Simplify using `using J.add_mem hy hz`.

Introduce `h`. Rewrite using `[← b.sum_repr x]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top`.
-/
theorem mem_smul_top_iff_repr {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (J : Ideal R) (x : M) :
    x ∈ (J • ⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ J := by
  constructor
  · intro hx i
    refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun y z hy hz => ?_)
    · simpa using J.mul_mem_right _ hr
    · simpa using J.add_mem hy hz
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis R M`. Establish `key : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)] ↔ ∀ i, b.repr x i ≡ b.repr y i [SMOD (I ^ n • ⊤ : Submodule R R)]`. Introduce `n x y`. Rewrite using `[SModEq.sub_mem, mem_smul_top_iff_repr b]`. Use `forall_congr' fun i => ?_` and prove the remaining obligations.

Rewrite using `[SModEq.sub_mem]`. Simplify using the standard rewrite rules. Establish `hH : IsHausdorff I M`. Use `⟨fun x hx => ?_⟩` and prove the remaining obligations. Use `b.repr.injective (Finsupp.ext fun i => ?_)` and prove the remaining obligations.

Use `h.toIsHausdorff.haus (b.repr x i) fun n => by` as an intermediate fact. Simplify using `using (key n x 0).1 (hx n) i`. Simplify using `using this`. Establish `hP : IsPrecomplete I M`. Use `⟨fun f hf => ?_⟩` and prove the remaining obligations.

Establish `hc : ∀ i, ∃ L : R, ∀ n, b.repr (f n) i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)]` using `fun i => h.toIsPrecomplete.prec (f := fun n => b.repr (f n) i) fun {m n} hmn => (key m _ _).1 (hf hmn) i`. Use `choose L hL using hc`. Use `⟨b.equivFun.symm L, fun n => (key n _ _).2 fun i => ?_⟩` and prove the remaining obligations. Establish `: b.repr (b.equivFun.symm L) i = L i`. Rewrite using `[← b.equivFun_apply, LinearEquiv.apply_symm_apply]`.

Rewrite using `[this]`. Conclude with `hL i n`. Conclude with `{ toIsHausdorff := hH, toIsPrecomplete := hP }`.
-/
theorem isAdicComplete_of_free_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (I : Ideal R) (h : IsAdicComplete I R) :
    IsAdicComplete I M := by
  classical
  let b := Module.Free.chooseBasis R M
  have key : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)] ↔
      ∀ i, b.repr x i ≡ b.repr y i [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro n x y
    rw [SModEq.sub_mem, mem_smul_top_iff_repr b]
    refine forall_congr' fun i => ?_
    rw [SModEq.sub_mem]
    simp
  have hH : IsHausdorff I M := by
    refine ⟨fun x hx => ?_⟩
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    have := h.toIsHausdorff.haus (b.repr x i) fun n => by
      simpa using (key n x 0).1 (hx n) i
    simpa using this
  have hP : IsPrecomplete I M := by
    refine ⟨fun f hf => ?_⟩
    have hc : ∀ i, ∃ L : R, ∀ n, b.repr (f n) i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] :=
      fun i => h.toIsPrecomplete.prec (f := fun n => b.repr (f n) i)
        fun {m n} hmn => (key m _ _).1 (hf hmn) i
    choose L hL using hc
    refine ⟨b.equivFun.symm L, fun n => (key n _ _).2 fun i => ?_⟩
    have : b.repr (b.equivFun.symm L) i = L i := by
      rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [this]
    exact hL i n
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

/- English proof (translation)
Introduce `R O _ _ _ _ _ t h`. Establish `h1 : IsAdicComplete (Ideal.span {t}) O` using `isAdicComplete_of_free_finite _ h`. Establish `h2 : Ideal.span {algebraMap R O t} = (Ideal.span {t}).map (algebraMap R O)`. Rewrite using `[Ideal.map_span, Set.image_singleton]`. Rewrite using `[h2]`.

Conclude with `(IsAdicComplete.map_algebraMap_iff _ O).2 h1`.
-/
theorem isAdicComplete_span_algebraMap_of_free_finite :
    ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra R O] [Module.Free R O] [Module.Finite R O]
      (t : R), IsAdicComplete (Ideal.span {t}) R →
        IsAdicComplete (Ideal.span {algebraMap R O t}) O := by
  intro R O _ _ _ _ _ t h
  have h1 : IsAdicComplete (Ideal.span {t}) O := isAdicComplete_of_free_finite _ h
  have h2 : Ideal.span {algebraMap R O t} = (Ideal.span {t}).map (algebraMap R O) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [h2]
  exact (IsAdicComplete.map_algebraMap_iff _ O).2 h1

end GlobalTheory.CNorm
