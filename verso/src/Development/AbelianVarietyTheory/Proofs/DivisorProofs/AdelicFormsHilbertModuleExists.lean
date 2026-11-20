import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftModelsOn

open Formalism.IndefR Formalism.IndefR.Links
open scoped InnerProductSpace

namespace GlobalTheory.AdFormsModel

section

variable {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {ι : Γ →* G} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {I : Type} {y : I → G}

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem eq_zero_of_reps (hy : Bridge.IsReps ι J y) {F : G → W} (hF : F ∈ Bridge.AdForms ι ρ J χ)
    (h0 : ∀ i, F (y i) = 0) : F = 0 := by
  funext h
  obtain ⟨i, ⟨γ, k, rfl⟩, -⟩ := hy h
  have := hF γ (y i) k
  rw [this, h0 i]
  simp

/- English proof (translation)
Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem finiteDimensional_adForms [FiniteDimensional ℂ W] [Finite I] (hy : Bridge.IsReps ι J y) :
    FiniteDimensional ℂ (Bridge.AdForms ι ρ J χ) := by
  let ev : Bridge.AdForms ι ρ J χ →ₗ[ℂ] (I → W) :=
    (LinearMap.funLeft ℂ W y).comp (Bridge.AdForms ι ρ J χ).subtype
  refine FiniteDimensional.of_injective ev ?_
  rw [injective_iff_map_eq_zero]
  intro F hF
  exact Subtype.ext (eq_zero_of_reps hy F.2 fun i => congrFun hF i)

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Assume the negation of the conclusion and derive a contradiction.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Check the signs of the components of the expression. A detailed English derivation is pending.
-/
theorem adInner_self_pos [Fintype I] (hy : Bridge.IsReps ι J y) (hs : ∀ i, Finite (Bridge.stab ι J (y i)))
    {F : G → W} (hF : F ∈ Bridge.AdForms ι ρ J χ) (hne : F ≠ 0) : 0 < (Bridge.adInner ι J y F F).re := by
  have hre : (Bridge.adInner ι J y F F).re =
      ∑ i, ((Nat.card (Bridge.stab ι J (y i)) : ℝ))⁻¹ * ‖F (y i)‖ ^ 2 := by
    unfold Bridge.adInner
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_self_eq_norm_sq_to_K]
    have : ((Nat.card (Bridge.stab ι J (y i)) : ℂ))⁻¹ * ((‖F (y i)‖ : ℝ) : ℂ) ^ 2 =
        ((((Nat.card (Bridge.stab ι J (y i)) : ℝ))⁻¹ * ‖F (y i)‖ ^ 2 : ℝ) : ℂ) := by
      push_cast; rfl
    exact (congrArg Complex.re this).trans (Complex.ofReal_re _)
  rw [hre]
  obtain ⟨i, hi⟩ : ∃ i, F (y i) ≠ 0 := by
    by_contra hcon
    exact hne (eq_zero_of_reps hy hF fun i => by
      by_contra h
      exact hcon ⟨i, h⟩)
  refine Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ _, ?_⟩
  haveI := hs i
  have h1 : (0 : ℝ) < (Nat.card (Bridge.stab ι J (y i)) : ℝ) := by exact_mod_cast Nat.card_pos
  have h2 : 0 < ‖F (y i)‖ := norm_pos_iff.2 hi
  positivity

end

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
theorem exists_hmod_adForms : ∀ (G Γ W : Type) [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (I : Type)
    [Fintype I] (y : I → G), Bridge.IsReps ι J y → (∀ i, Finite (Bridge.stab ι J (y i))) →
    ∃ M : HMod (G → W), M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J y) := by
  intro G Γ W _ _ _ _ _ ι ρ J χ I _ y hy hs
  refine GlobalTheory.HilbertModel.exists_hmod (G → W) _ _ (finiteDimensional_adForms hy) ?_
    (fun F hF hne => adInner_self_pos hy hs hF hne)
  intro a _ b _ d _ c
  constructor
  · simp only [Bridge.adInner, Pi.add_apply, Pi.smul_apply, inner_add_right, inner_smul_right, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · simp only [Bridge.adInner, star_sum, star_mul', star_inv₀, star_natCast]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← inner_conj_symm (b (y i)) (a (y i))]
    rfl

end GlobalTheory.AdFormsModel
