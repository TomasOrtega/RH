import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeInfLatticeEqSubspace
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FBaseChangeInfLatticeEqSubspace.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_injective_baseChange_inf_restrictScalars_range_eq : ∀ {O V : Type} [CommRing O] [IsDomain O] [AddCommGroup V] [Module (FractionRing O) V] [Module O V]
    [IsScalarTower O (FractionRing O) V] (N : Submodule O V),
    Submodule.span (FractionRing O) (N : Set V) = ⊤ → ∀ (W : Submodule (FractionRing O) V),
    ∃ e : FractionRing O ⊗[O] ↥(N ⊓ W.restrictScalars O) →ₗ[FractionRing O] V,
      Function.Injective e ∧ LinearMap.range e = W ∧
      ∀ (c : FractionRing O) (x : ↥(N ⊓ W.restrictScalars O)), e (c ⊗ₜ[O] x) = c • (x : V) := by
  first | exact @GlobalTheory.baseChange_inf_lattice_eq_subspace | exact GlobalTheory.baseChange_inf_lattice_eq_subspace | (intros; apply GlobalTheory.baseChange_inf_lattice_eq_subspace <;> assumption)
