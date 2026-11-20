import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryToSpecialUnitaryLocalStatement
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

namespace GlobalTheory.SURestrict

variable {n : ℕ}

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem one_mem_SUset (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε := by
  refine ⟨?_, by simp⟩
  show inUJ ε 1
  simp [inUJ]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mul_mem_SUset {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ SUset ε)
    (hb : b ∈ SUset ε) : a * b ∈ SUset ε := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  refine ⟨?_, by rw [Matrix.det_mul, ha2, hb2, one_mul]⟩
  have ha1' : aᴴ * Jm ε * a = Jm ε := ha1
  have hb1' : bᴴ * Jm ε * b = Jm ε := hb1
  show (a * b)ᴴ * Jm ε * (a * b) = Jm ε
  calc (a * b)ᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Jm ε := by rw [ha1', hb1']

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem Kset_sub_UJset {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    g ∈ UJset ε := by
  obtain ⟨hu, hc⟩ := hg
  have h1 : star g * g = 1 := (Matrix.mem_unitaryGroup_iff').mp hu
  show gᴴ * Jm ε * g = Jm ε
  calc gᴴ * Jm ε * g = gᴴ * (g * Jm ε) := by rw [Matrix.mul_assoc, hc]
    _ = (star g * g) * Jm ε := by rw [← Matrix.mul_assoc]; rfl
    _ = Jm ε := by rw [h1, Matrix.one_mul]

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem KS_sub_SUset {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ KS ε) :
    g ∈ SUset ε := ⟨Kset_sub_UJset hg.1, hg.2⟩

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem eq_on_SU {ε : Fin n → Bool} {m : ℤ} {π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (he : Ext ε m π' π) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ SUset ε) : π g = π' g := by
  have := he 1 (by simp) g hg
  simpa using this

end

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem restrict_main : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Ext ε m π' π → (IsURepOn (UJset ε) π → IsURepOn (SUset ε) π') ∧ (IsIrredOn (UJset ε) π ↔ IsIrredOn (SUset ε) π') ∧ (∀ S : Submodule ℂ H, Stable (Kset ε) π S ↔ Stable (KS ε) π' S) ∧ ∀ v, IsKFin ε π v ↔ IsKFinS ε π' v := by
  intro n hn ε H _ _ m π' π he
  obtain ⟨hsplit, -, -⟩ := GlobalTheory.T.unitary_to_special_unitary_local n hn ε
  have heq : ∀ g ∈ SUset ε, π g = π' g := fun g hg => eq_on_SU he hg
  have hSU : ∀ g ∈ SUset ε, g ∈ UJset ε := fun g hg => hg.1

  have hstab : ∀ S : Submodule ℂ H, (∀ g ∈ UJset ε, ∀ v ∈ S, π g v ∈ S) ↔
      (∀ g ∈ SUset ε, ∀ v ∈ S, π' g v ∈ S) := by
    intro S
    constructor
    · intro h g hg v hv
      rw [← heq g hg]; exact h g (hSU g hg) v hv
    · intro h g hg v hv
      obtain ⟨z, hz, g₀, hg₀, rfl, -⟩ := hsplit g hg
      rw [he z hz g₀ hg₀]
      exact S.smul_mem _ (h g₀ hg₀ v hv)
  have hK : ∀ S : Submodule ℂ H, Stable (Kset ε) π S ↔ Stable (KS ε) π' S := by
    intro S
    constructor
    · intro h g hg v hv
      rw [← heq g (KS_sub_SUset hg)]; exact h g hg.1 v hv
    · intro h g hg v hv
      obtain ⟨z, hz, g₀, hg₀, rfl, hiff⟩ := hsplit g (Kset_sub_UJset hg)
      rw [he z hz g₀ hg₀]
      exact S.smul_mem _ (h g₀ (hiff.mp hg) v hv)
  refine ⟨?_, ?_, hK, ?_⟩
  · rintro ⟨⟨h1, hmul⟩, hiso, hcont⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [← heq 1 (one_mem_SUset ε)]; exact h1
    · intro a ha b hb
      rw [← heq _ (mul_mem_SUset ha hb), ← heq a ha, ← heq b hb]
      exact hmul a (hSU a ha) b (hSU b hb)
    · intro g hg v
      rw [← heq g hg]; exact hiso g (hSU g hg) v
    · intro v
      exact ((hcont v).mono (fun g hg => hSU g hg)).congr (fun g hg => by simp only [heq g hg])
  · constructor
    · intro h S hS hst
      exact h S hS ((hstab S).mpr hst)
    · intro h S hS hst
      exact h S hS ((hstab S).mp hst)
  · intro v
    constructor
    · rintro ⟨S, hfd, hv, hs⟩
      exact ⟨S, hfd, hv, (hK S).mp hs⟩
    · rintro ⟨S, hfd, hv, hs⟩
      exact ⟨S, hfd, hv, (hK S).mpr hs⟩

end GlobalTheory.SURestrict
