import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import GroundTheory.GlobalFields.Artin.LogCharpoly

open Formalism.MainNotions.N

namespace GlobalTheory.QuadKernelConj

section Restrict

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

def tr (ρ : Γ →* GL (Fin n) k) (g : Γ) (U : Submodule k (Fin n → k)) : Submodule k (Fin n → k) :=
  U.map (Matrix.toLin' ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem tr_mul (ρ : Γ →* GL (Fin n) k) (g h : Γ) (U : Submodule k (Fin n → k)) :
    tr ρ (g * h) U = tr ρ g (tr ρ h U) := by
  unfold tr
  rw [map_mul, Units.val_mul, Matrix.toLin'_mul, Submodule.map_comp]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tr_mono (ρ : Γ →* GL (Fin n) k) (g : Γ) {U V : Submodule k (Fin n → k)} (h : U ≤ V) :
    tr ρ g U ≤ tr ρ g V := Submodule.map_mono h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tr_sup (ρ : Γ →* GL (Fin n) k) (g : Γ) (U V : Submodule k (Fin n → k)) :
    tr ρ g (U ⊔ V) = tr ρ g U ⊔ tr ρ g V := Submodule.map_sup _ _ _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tr_inf_le (ρ : Γ →* GL (Fin n) k) (g : Γ) (U V : Submodule k (Fin n → k)) :
    tr ρ g (U ⊓ V) ≤ tr ρ g U ⊓ tr ρ g V :=
  le_inf (tr_mono ρ g inf_le_left) (tr_mono ρ g inf_le_right)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem tr_le_iff (ρ : Γ →* GL (Fin n) k) (g : Γ) (U : Submodule k (Fin n → k)) :
    tr ρ g U ≤ U ↔ ∀ v ∈ U, ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v ∈ U := by
  unfold tr
  rw [Submodule.map_le_iff_le_comap]
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isInv_iff (ρ : Γ →* GL (Fin n) k) (U : Submodule k (Fin n → k)) :
    IsInv ρ U ↔ ∀ g, tr ρ g U ≤ U :=
  forall_congr' fun g => (tr_le_iff ρ g U).symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem isInv_ker_iff (ρ : Γ →* GL (Fin n) k) (η : Γ →* ℤˣ) (U : Submodule k (Fin n → k)) :
    IsInv (ρ.comp η.ker.subtype) U ↔ ∀ g, η g = 1 → tr ρ g U ≤ U := by
  constructor
  · intro h g hg
    exact (tr_le_iff ρ g U).2 (h ⟨g, hg⟩)
  · intro h g
    exact (tr_le_iff ρ g.1 U).1 (h g.1 g.2)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isSSRep_ker (ρ : Γ →* GL (Fin n) k) (η : Γ →* ℤˣ) (hρ : IsSSRep ρ) :
    IsSSRep (ρ.comp η.ker.subtype) := by
  intro W hW
  rw [isInv_ker_iff] at hW
  by_cases hη : ∀ g, η g = 1
  · obtain ⟨W', h1, h2⟩ := hρ W ((isInv_iff ρ W).2 fun g => hW g (hη g))
    exact ⟨W', (isInv_ker_iff ρ η W').2 fun g _ => (isInv_iff ρ W').1 h1 g, h2⟩
  obtain ⟨t, ht⟩ := not_forall.1 hη
  have ht' : η t = -1 := (Int.units_eq_one_or (η t)).resolve_left ht

  have hconj : ∀ U, (∀ g, η g = 1 → tr ρ g U ≤ U) → ∀ g, η g = 1 → tr ρ g (tr ρ t U) ≤ tr ρ t U := by
    intro U hU g hg
    have e : g * t = t * (t⁻¹ * g * t) := by group
    rw [← tr_mul, e, tr_mul]
    refine tr_mono ρ t (hU _ ?_)
    rw [map_mul, map_mul, hg, map_inv, mul_one, inv_mul_cancel]
  have hall : ∀ U, (∀ g, η g = 1 → tr ρ g U ≤ U) → tr ρ t U ≤ U → IsInv ρ U := by
    intro U hU hUt
    rw [isInv_iff]
    intro g
    rcases Int.units_eq_one_or (η g) with hg | hg
    · exact hU g hg
    · have e : g = t * (t⁻¹ * g) := by group
      rw [e, tr_mul]
      refine (tr_mono ρ t (hU _ ?_)).trans hUt
      rw [map_mul, map_inv, hg, ht', inv_mul_cancel]
  have htt : tr ρ t (tr ρ t W) ≤ W := by
    rw [← tr_mul]
    refine hW _ ?_
    rw [map_mul, ht']
    simp
  have hAt : tr ρ t (W ⊓ tr ρ t W) ≤ W ⊓ tr ρ t W :=
    (tr_inf_le ρ t _ _).trans (le_inf (inf_le_right.trans htt) inf_le_left)
  have hA : IsInv ρ (W ⊓ tr ρ t W) :=
    hall _ (fun g hg => (tr_inf_le ρ g _ _).trans (inf_le_inf (hW g hg) (hconj W hW g hg))) hAt
  have hB : IsInv ρ (W ⊔ tr ρ t W) := by
    refine hall _ (fun g hg => ?_) ?_
    · rw [tr_sup]
      exact sup_le_sup (hW g hg) (hconj W hW g hg)
    · rw [tr_sup]
      exact sup_le le_sup_right (htt.trans le_sup_left)
  obtain ⟨D, hD, hAD⟩ := hρ _ hA
  obtain ⟨C, hC, hBC⟩ := hρ _ hB
  rw [isInv_iff] at hD hC
  have hW1 : ∀ g, η g = 1 → tr ρ g (W ⊓ D) ≤ W ⊓ D := fun g hg =>
    (tr_inf_le ρ g _ _).trans (inf_le_inf (hW g hg) (hD g))
  have hWeq : (W ⊓ tr ρ t W) ⊔ (W ⊓ D) = W := by
    rw [inf_comm W D, ← sup_inf_assoc_of_le D (inf_le_left : W ⊓ tr ρ t W ≤ W), hAD.sup_eq_top,
      top_inf_eq]
  have hsup : W ⊔ tr ρ t (W ⊓ D) = W ⊔ tr ρ t W := by
    refine le_antisymm (sup_le_sup_left (tr_mono ρ t inf_le_left) _) (sup_le le_sup_left ?_)
    calc tr ρ t W = tr ρ t ((W ⊓ tr ρ t W) ⊔ (W ⊓ D)) := by rw [hWeq]
      _ ≤ W ⊔ tr ρ t (W ⊓ D) := by
        rw [tr_sup]
        exact sup_le_sup_right (hAt.trans inf_le_left) _
  have hdis : Disjoint W (tr ρ t (W ⊓ D)) := by
    rw [disjoint_iff_inf_le, ← hAD.inf_eq_bot]
    exact le_inf (inf_le_inf_left _ (tr_mono ρ t inf_le_left))
      (inf_le_right.trans ((tr_mono ρ t inf_le_right).trans (hD t)))
  refine ⟨tr ρ t (W ⊓ D) ⊔ C, (isInv_ker_iff ρ η _).2 fun g hg => ?_, ?_, ?_⟩
  · rw [tr_sup]
    exact sup_le_sup (hconj _ hW1 g hg) (hC g)
  · exact hdis.disjoint_sup_right_of_disjoint_sup_left (hsup ▸ hBC.disjoint)
  · rw [codisjoint_iff, ← sup_assoc, hsup, hBC.sup_eq_top]

end Restrict

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem charpoly_eq_of_trace_pow {k : Type} [Field k] [CharZero k] {n : ℕ} (A B : Matrix (Fin n) (Fin n) k)
    (h : ∀ m : ℕ, (A ^ m).trace = (B ^ m).trace) : A.charpoly = B.charpoly := by
  have h1 := GroundTheory.Global.reverse_charpoly_eq_of_trace_pow_eq (Matrix.toLin' A) (Matrix.toLin' B)
    (fun m _ => by
      rw [← Matrix.toLin'_pow, ← Matrix.toLin'_pow, Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, h m])
  rw [Matrix.charpoly_toLin', Matrix.charpoly_toLin', Polynomial.reverse, Polynomial.reverse,
    Matrix.charpoly_natDegree_eq_dim, Matrix.charpoly_natDegree_eq_dim] at h1
  have h2 := congrArg (Polynomial.reflect (Fintype.card (Fin n))) h1
  rwa [Polynomial.reflect_reflect, Polynomial.reflect_reflect] at h2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem conj_on_ker_inf_ker : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (ρ ρ' : Γ →* GL (Fin n) k) (χ₁ χ₂ : Γ →* ℤˣ), IsSSRep ρ → IsSSRep ρ' → (∀ g, χ₁ g = 1 → χ₂ g = 1 → ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → ∃ P : GL (Fin n) k, ∀ g, χ₁ g = 1 → χ₂ g = 1 → ρ' g = P⁻¹ * ρ g * P := by
  intro Γ k _ _ _ n ρ ρ' χ₁ χ₂ hρ hρ' htr
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix _ _
    (isSSRep_ker _ (χ₁.comp χ₂.ker.subtype) (isSSRep_ker ρ χ₂ hρ))
    (isSSRep_ker _ (χ₁.comp χ₂.ker.subtype) (isSSRep_ker ρ' χ₂ hρ')) (fun g => by
      refine charpoly_eq_of_trace_pow _ _ fun m => ?_
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]
      exact htr (g ^ m).1.1 (g ^ m).2 (g ^ m).1.2)
  exact ⟨P, fun g h1 h2 => hP ⟨⟨g, h2⟩, h1⟩⟩

end GlobalTheory.QuadKernelConj
