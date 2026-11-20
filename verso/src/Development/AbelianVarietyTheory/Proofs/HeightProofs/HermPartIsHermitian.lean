import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightFamilies
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.TotallyPositiveExponents

noncomputable section

namespace GlobalTheory.CuspAlgComparison

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions NumberField GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TotallyPositiveExponents
open Matrix hiding vec
open scoped ComplexOrder

section Host

variable {R : Ranks} (H : Host R)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem tau_injective : Function.Injective (tau H) := fun _ _ h =>
  Subtype.ext ((factEmb R H).1.1 h)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tau_sqrt (τ : Pl R) : tau H τ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) :=
  ((factEmb R H).2 _).2 τ.2

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sqrt_d_pos : 0 < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)

/- English proof (translation)
Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Supply the required witnesses or components. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem emb_cases (σ : H.E →+* ℂ) :
    ∃ τ : Pl R, σ = tau H τ ∨ σ = (starRingEnd ℂ).comp (tau H τ) := by
  obtain ⟨g, rfl⟩ := (factEmb R H).1.2 σ
  by_cases hg : g ∈ R.Psi
  · exact ⟨⟨g, hg⟩, Or.inl rfl⟩
  · rw [Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem, not_not] at hg
    refine ⟨⟨_, hg⟩, Or.inr (RingHom.ext fun x => ?_)⟩
    change H.emb g x = starRingEnd ℂ (H.emb (g * R.cc) x)
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    change _ = starRingEnd ℂ (H.emb g (H.conj x))
    rw [show H.emb g (H.conj x) = _ from H.conjE_apply _ x]
    simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem tau_ne_conj (τ τ' : Pl R) : tau H τ ≠ (starRingEnd ℂ).comp (tau H τ') := by
  intro h
  have h1 := congrArg Complex.im (DFunLike.congr_fun h H.sqrtMinusD)
  rw [RingHom.comp_apply, tau_sqrt, tau_sqrt] at h1
  have := sqrt_d_pos H
  simp at h1
  linarith

end Host

section Forms

variable {R : Ranks} {H : Host R} {n : ℕ}

def mulR (c : Pl R → ℂ) (u : XR R n) : XR R n := fun τ i => c τ * u τ i

open Classical in
/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem sum_single_left (b : Pl R → Matrix (Fin n) (Fin n) ℂ) (τ : Pl R) (z : Fin n → ℂ) (v : XR R n) :
    ∑ τ', 2 * (star ((Pi.single τ z : XR R n) τ') ⬝ᵥ b τ' *ᵥ v τ').re = 2 * (star z ⬝ᵥ b τ *ᵥ v τ).re := by
  rw [Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp)]
  simp

end Forms

end GlobalTheory.CuspAlgComparison

end
