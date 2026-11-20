import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. A detailed English derivation is pending.
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
A detailed English derivation is pending.
-/
example : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (V W : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] [AddCommGroup W] [Module C W] [Module O W] [IsScalarTower O C W] (ι : V →ₗ[C] W) (x : V) (y : W), Function.Injective ι → Module.finrank C W = 1 → x ≠ 0 → y ≠ 0 → ∃ lam : C, lam ≠ 0 ∧ ι x = lam • y ∧ ι '' (Submodule.span O {x} : Set V) = (fun w => lam • w) '' (Submodule.span O {y} : Set W) :=
  @injective_into_line_span_eq_smul_span

end GlobalTheory
