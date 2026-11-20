import Mathlib

namespace GlobalTheory

open scoped MonoidAlgebra

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem asAlgebraHom_surjective_of_finrank_intertwiningMap_eq_one :
    ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (τ : Representation K G V), Module.finrank K (Representation.IntertwiningMap τ τ) = 1 → Nontrivial V ∧ Function.Surjective τ.asAlgebraHom := by
  intro K _ _ G _ _ V _ _ _ τ h
  classical
  have : NeZero (Nat.card G : K) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  have hV : Nontrivial V := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have : Subsingleton (Representation.IntertwiningMap τ τ) :=
      ⟨fun f g => Representation.IntertwiningMap.ext (Subsingleton.elim _ _)⟩
    rw [Module.finrank_zero_of_subsingleton] at h
    exact zero_ne_one h
  refine ⟨hV, ?_⟩
  have : Nontrivial τ.asModule := hV
  have hE : Module.finrank K (Module.End K[G] τ.asModule) = 1 := by
    rw [← (Representation.IntertwiningMap.equivAlgEnd τ).toLinearEquiv.finrank_eq]
    exact h
  have hscalar : ∀ φ : Module.End K[G] τ.asModule, ∃ c : K, c • (1 : Module.End K[G] τ.asModule) = φ :=
    (finrank_eq_one_iff_of_nonzero' _ one_ne_zero).mp hE
  have : IsScalarTower K (Module.End K[G] τ.asModule) τ.asModule := ⟨fun _ _ _ => rfl⟩
  have : Module.Finite (Module.End K[G] τ.asModule) τ.asModule :=
    Module.Finite.of_restrictScalars_finite K _ _
  intro f
  let F : Module.End (Module.End K[G] τ.asModule) τ.asModule :=
    { toFun := fun m => f m
      map_add' := fun x y => f.map_add x y
      map_smul' := fun φ m => by
        obtain ⟨c, rfl⟩ := hscalar φ
        exact f.map_smul c m }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := K[G]) (M := τ.asModule) F
  refine ⟨a, LinearMap.ext fun v => ?_⟩
  exact congrArg (fun g => g v) ha

end GlobalTheory
