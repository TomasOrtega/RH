import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.CuspGenericWhittaker.CuspGeneric
import GroundTheory.AutomorphicForms.WhittakerCriterion

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Whit

namespace GlobalTheory.CompanionTheory.TwistedDual

/- English proof (translation)
Distinguish the cases in `hW : Module.Finite ℂ W`. Establish `h : Module.rank ℂ (Module.Dual ℂ W) = Module.rank ℂ W`. Rewrite using `[← Module.finrank_eq_rank, ← Module.finrank_eq_rank, Subspace.dual_finrank_eq]`. Rewrite using `[h]`. Establish `hinf : Cardinal.aleph0 ≤ Module.rank ℂ W`.

Assume the negation of the conclusion as `hlt`. Conclude with `hW (Module.rank_lt_aleph0_iff.1 (not_le.1 hlt))`. Establish `hone : (1 : Cardinal) < Module.rank ℂ W` using `lt_of_lt_of_le Cardinal.one_lt_aleph0 hinf`. Establish `hdual : Module.rank ℂ W < Module.rank ℂ (Module.Dual ℂ W)`. Simplify using `using lift_rank_lt_rank_dual (K := ℂ) (V := W) hinf`.

Conclude with `iff_of_false (not_le.2 hone) (not_le.2 (hone.trans hdual))`.
-/
theorem rank_le_one_iff_rank_dual_le_one (W : Type) [AddCommGroup W] [Module ℂ W] :
    Module.rank ℂ W ≤ 1 ↔ Module.rank ℂ (Module.Dual ℂ W) ≤ 1 := by
  by_cases hW : Module.Finite ℂ W
  · have h : Module.rank ℂ (Module.Dual ℂ W) = Module.rank ℂ W := by
      rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank, Subspace.dual_finrank_eq]
    rw [h]
  · have hinf : Cardinal.aleph0 ≤ Module.rank ℂ W := by
      by_contra hlt
      exact hW (Module.rank_lt_aleph0_iff.1 (not_le.1 hlt))
    have hone : (1 : Cardinal) < Module.rank ℂ W :=
      lt_of_lt_of_le Cardinal.one_lt_aleph0 hinf
    have hdual : Module.rank ℂ W < Module.rank ℂ (Module.Dual ℂ W) := by
      simpa using lift_rank_lt_rank_dual (K := ℂ) (V := W) hinf
    exact iff_of_false (not_le.2 hone) (not_le.2 (hone.trans hdual))

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Use extensionality with `ℓ`. Rewrite using `[GroundTheory.Automorphic.Whittaker.mem_equivariantFunctionals, Submodule.mem_dualAnnihilator]`. Prove the components needed by the constructor for the conclusion. Introduce `h w hw`. Establish `hle : twKer ρ N θ ≤ LinearMap.ker ℓ`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `w ⟨n, v, rfl⟩`. Simplify using `[h n v]`. Conclude with `hle hw`. Introduce `h n v`.

Establish `hmem : ρ (n : G) v - ((θ n : ℂˣ) : ℂ) • v ∈ twKer ρ N θ` using `Submodule.subset_span ⟨n, v, rfl⟩`. Establish `h0` using `h _ hmem`. Simplify using `only [map_sub, map_smul, smul_eq_mul] at h0`. Conclude with `sub_eq_zero.1 h0`.
-/
theorem equivariantFunctionals_eq_dualAnnihilator (ρ : Representation ℂ G V) (N : Subgroup G)
    (θ : N →* ℂˣ) :
    GroundTheory.Automorphic.Whittaker.equivariantFunctionals ρ (fun u : N => ((θ u : ℂˣ) : ℂ)) =
      (twKer ρ N θ).dualAnnihilator := by
  ext ℓ
  rw [GroundTheory.Automorphic.Whittaker.mem_equivariantFunctionals, Submodule.mem_dualAnnihilator]
  constructor
  · intro h w hw
    have hle : twKer ρ N θ ≤ LinearMap.ker ℓ := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨n, v, rfl⟩
      simp [h n v]
    exact hle hw
  · intro h n v
    have hmem : ρ (n : G) v - ((θ n : ℂˣ) : ℂ) • v ∈ twKer ρ N θ :=
      Submodule.subset_span ⟨n, v, rfl⟩
    have h0 := h _ hmem
    simp only [map_sub, map_smul, smul_eq_mul] at h0
    exact sub_eq_zero.1 h0

/- English proof (translation)
Rewrite using `[equivariantFunctionals_eq_dualAnnihilator, ← (twKer ρ N θ).dualQuotEquivDualAnnihilator.rank_eq]`. Conclude with `rank_le_one_iff_rank_dual_le_one _`.
-/
theorem rank_twJacquet_le_one_iff (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) :
    Module.rank ℂ (TwJacquet ρ N θ) ≤ 1 ↔
      Module.rank ℂ (GroundTheory.Automorphic.Whittaker.equivariantFunctionals ρ
        (fun u : N => ((θ u : ℂˣ) : ℂ))) ≤ 1 := by
  rw [equivariantFunctionals_eq_dualAnnihilator,
    ← (twKer ρ N θ).dualQuotEquivDualAnnihilator.rank_eq]
  exact rank_le_one_iff_rank_dual_le_one _

end GlobalTheory.CompanionTheory.TwistedDual

end
