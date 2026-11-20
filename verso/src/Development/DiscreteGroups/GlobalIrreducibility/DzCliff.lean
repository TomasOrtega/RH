import Mathlib

open Module Polynomial

set_option linter.all false

namespace DiscreteGroups.sglob.DzCliff

variable {W V : Type*} [Group W] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem eig_unique {f : End ℂ V} {u : V} (hu : u ≠ 0) {a b : ℂ} (ha : f u = a • u) (hb : f u = b • u) : a = b :=
  smul_left_injective ℂ hu (ha.symm.trans hb)

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem pow_apply_of_eig {f : End ℂ V} {v : V} {c : ℂ} (hv : f v = c • v) (m : ℕ) : (f ^ m) v = c ^ m • v := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, Module.End.mul_apply, hv, map_smul, ih, smul_smul, pow_succ, mul_comm]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem rho_inv_apply (ρ : Representation ℂ W V) (a : W) (v : V) : ρ a⁻¹ (ρ a v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem rho_apply_inv (ρ : Representation ℂ W V) (a : W) (v : V) : ρ a (ρ a⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem rho_ne_zero (ρ : Representation ℂ W V) (a : W) {v : V} (hv : v ≠ 0) : ρ a v ≠ 0 := by
  intro h
  apply hv
  rw [← rho_inv_apply ρ a v, h, map_zero]

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem exists_common_eigenvector (S : Set (End ℂ V)) (hS : ∀ f ∈ S, ∀ g ∈ S, f * g = g * f)
    (U : Submodule ℂ V) (hU : U ≠ ⊥) (hUS : ∀ f ∈ S, ∀ v ∈ U, f v ∈ U) :
    ∃ u ∈ U, u ≠ 0 ∧ ∀ f ∈ S, ∃ c : ℂ, f u = c • u := by
  classical
  let P : Submodule ℂ V → Prop := fun X => X ≤ U ∧ X ≠ ⊥ ∧ ∀ f ∈ S, ∀ v ∈ X, f v ∈ X
  have hex : ∃ k, ∃ X, P X ∧ finrank ℂ X = k := ⟨_, U, ⟨le_rfl, hU, hUS⟩, rfl⟩
  obtain ⟨X, hX, hXk⟩ := Nat.find_spec hex
  have hmin : ∀ Y, P Y → finrank ℂ X ≤ finrank ℂ Y := fun Y hY => hXk ▸ Nat.find_min' hex ⟨Y, hY, rfl⟩
  obtain ⟨u, huX, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX.2.1
  refine ⟨u, hX.1 huX, hu0, fun f hf => ?_⟩
  haveI : Nontrivial X := Submodule.nontrivial_iff_ne_bot.mpr hX.2.1
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (f.restrict (fun v hv => hX.2.2 f hf v hv))
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  have hx' : f (x : V) = c • (x : V) := by
    have := Module.End.mem_eigenspace_iff.mp hx.1
    simpa [LinearMap.restrict_apply] using congrArg Subtype.val this
  let Y : Submodule ℂ V := X ⊓ f.eigenspace c
  have hY : P Y := by
    refine ⟨le_trans inf_le_left hX.1, ?_, fun g hg v hv => ⟨hX.2.2 g hg v hv.1, Module.End.mem_eigenspace_iff.mpr
      (by rw [← Module.End.mul_apply, hS f hf g hg, Module.End.mul_apply, Module.End.mem_eigenspace_iff.mp hv.2,
        map_smul])⟩⟩
    intro hbot
    have hxY : (x : V) ∈ Y := ⟨x.2, Module.End.mem_eigenspace_iff.mpr hx'⟩
    rw [hbot, Submodule.mem_bot] at hxY
    exact hx.2 (Subtype.ext hxY)
  have hYX : Y = X := Submodule.eq_of_le_of_finrank_le inf_le_left (hmin Y hY)
  have huY : u ∈ Y := hYX ▸ huX
  exact ⟨c, Module.End.mem_eigenspace_iff.mp huY.2⟩

/- English proof (translation)
Introduce a local definition for the expression. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem eq_top_of_stable (ρ : Representation ℂ W V) (hρ : ρ.IsIrreducible) (S : Submodule ℂ V) (hS : S ≠ ⊥)
    (hst : ∀ σ : W, ∀ v ∈ S, ρ σ v ∈ S) : S = ⊤ := by
  let X : Subrepresentation ρ := ⟨S, fun σ v hv => hst σ v hv⟩
  rcases hρ.eq_bot_or_eq_top X with h | h
  · exact absurd (congrArg Subrepresentation.toSubmodule h) hS
  · exact congrArg Subrepresentation.toSubmodule h

end DiscreteGroups.sglob.DzCliff
