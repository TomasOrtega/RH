import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

/- English proof (translation)
Take `⟨lam, hlam⟩` from `(finrank_eq_one_iff_of_nonzero' y hy).mp hW (ι x)`. Establish `hιx : ι x ≠ 0`. Introduce `h`. Conclude with `hx (hι (h.trans ι.map_zero.symm))`. Establish `hl : lam ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hlam` using `[zero_smul]`. Conclude with `hιx hlam.symm`. Establish `key : ∀ t : O, ι (t • x) = lam • (t • y)`. Introduce `t`.

Rewrite using `[← algebraMap_smul C t x, ι.map_smul, ← hlam, ← algebraMap_smul C t y, smul_smul, smul_smul, mul_comm]`. Use `⟨lam, hl, hlam.symm, ?_⟩` and prove the remaining obligations. Use extensionality with `w`. Simplify using `only [Set.mem_image, SetLike.mem_coe, Submodule.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨v, ⟨t, rfl⟩, rfl⟩`. Conclude with `⟨t • y, ⟨t, rfl⟩, (key t).symm⟩`. Introduce and unpack `⟨v, ⟨t, rfl⟩, rfl⟩`. Conclude with `⟨t • x, ⟨t, rfl⟩, key t⟩`.
-/
theorem injective_into_line_span_eq_smul_span (C : Type) [Field C] (O : Type) [CommRing O]
    [Algebra O C] (V W : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
    [AddCommGroup W] [Module C W] [Module O W] [IsScalarTower O C W] (ι : V →ₗ[C] W) (x : V)
    (y : W) (hι : Function.Injective ι) (hW : Module.finrank C W = 1) (hx : x ≠ 0)
    (hy : y ≠ 0) :
    ∃ lam : C, lam ≠ 0 ∧ ι x = lam • y ∧
      ι '' (Submodule.span O {x} : Set V) = (fun w => lam • w) '' (Submodule.span O {y} : Set W) := by
  obtain ⟨lam, hlam⟩ := (finrank_eq_one_iff_of_nonzero' y hy).mp hW (ι x)
  have hιx : ι x ≠ 0 := by
    intro h
    exact hx (hι (h.trans ι.map_zero.symm))
  have hl : lam ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hlam
    exact hιx hlam.symm
  have key : ∀ t : O, ι (t • x) = lam • (t • y) := by
    intro t
    rw [← algebraMap_smul C t x, ι.map_smul, ← hlam, ← algebraMap_smul C t y, smul_smul,
      smul_smul, mul_comm]
  refine ⟨lam, hl, hlam.symm, ?_⟩
  ext w
  simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨v, ⟨t, rfl⟩, rfl⟩
    exact ⟨t • y, ⟨t, rfl⟩, (key t).symm⟩
  · rintro ⟨v, ⟨t, rfl⟩, rfl⟩
    exact ⟨t • x, ⟨t, rfl⟩, key t⟩

/- English proof (translation)
The claim follows from `@injective_into_line_span_eq_smul_span`.
-/
example : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (V W : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] [AddCommGroup W] [Module C W] [Module O W] [IsScalarTower O C W] (ι : V →ₗ[C] W) (x : V) (y : W), Function.Injective ι → Module.finrank C W = 1 → x ≠ 0 → y ≠ 0 → ∃ lam : C, lam ≠ 0 ∧ ι x = lam • y ∧ ι '' (Submodule.span O {x} : Set V) = (fun w => lam • w) '' (Submodule.span O {y} : Set W) :=
  @injective_into_line_span_eq_smul_span

end GlobalTheory
