import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.R4.lift_eigen :
    ∀ {T V : Type} [inst : CommGroup T]
    [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ T V) {ψ μ : T →* ℂˣ} {v y : V},
    (∀ (t : T), ((ρ : T → V →ₗ[ℂ] V) t : V → V) v = (↑((ψ : T → ℂˣ) t) : ℂ) • v) →
      μ ≠ ψ →
        y ∉ ℂ ∙ v →
          (∀ (t : T), ((ρ : T → V →ₗ[ℂ] V) t : V → V) y - (↑((μ : T → ℂˣ) t) : ℂ) • y ∈ ℂ ∙ v) →
            v ≠ (0 : V) →
              ∃ (z : V), z ≠ (0 : V) ∧ ∀ (t : T), ((ρ : T → V →ₗ[ℂ] V) t : V → V) z = (↑((μ : T → ℂˣ) t) : ℂ) • z := by
  intro T V _ _ _ ρ ψ μ v y hv hne hy hmod _
  obtain ⟨s, hs⟩ : ∃ s, μ s ≠ ψ s := DFunLike.ne_iff.mp hne
  have hs' : ((μ s : ℂˣ) : ℂ) - ((ψ s : ℂˣ) : ℂ) ≠ 0 :=
    sub_ne_zero.mpr fun h => hs (Units.ext h)
  refine ⟨ρ s y - ((ψ s : ℂˣ) : ℂ) • y, ?_, ?_⟩
  · intro h0
    apply hy
    have h1 := hmod s
    rw [sub_eq_zero.mp h0, ← sub_smul, ← neg_sub, neg_smul, neg_mem_iff] at h1
    exact (Submodule.smul_mem_iff _ hs').mp h1
  · intro t
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hmod t)
    have hty : ρ t y = ((μ t : ℂˣ) : ℂ) • y + b • v := by
      rw [hb]; abel
    have hcomm : ρ t (ρ s y) = ρ s (ρ t y) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
    rw [map_sub, map_smul, hcomm, hty, map_add, map_smul, map_smul, hv s]
    module
