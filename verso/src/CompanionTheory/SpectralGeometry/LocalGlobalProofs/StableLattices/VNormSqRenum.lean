import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgFarRen

open Formalism.REAL (GlRel IsUnitary KHighest IsWeight qdet qminor Tm sgn)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (LocFin)
open PI.UpqRep (vNormSq rhoC nsq)

variable {n : ℕ}

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem glRel_renum {A : Type*} [Ring A] {E : Fin n → Fin n → A} (hE : GlRel E) (s : Equiv.Perm (Fin n)) :
    GlRel (fun a b => E (s a) (s b)) := by
  intro a b c d
  have h := hE (s a) (s b) (s c) (s d)
  simpa only [Equiv.apply_eq_iff_eq] using h

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem tm_renum {A : Type*} [Ring A] [Algebra ℂ A] (E : Fin n → Fin n → A) (s : Equiv.Perm (Fin n)) (u : ℂ)
    (a b : Fin n) : Tm (fun a b => E (s a) (s b)) u a b = Tm E u (s a) (s b) := by
  simp only [Formalism.REAL.Tm, Equiv.apply_eq_iff_eq]

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem qminor_renum {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin n → Fin n → A) (s : Equiv.Perm (Fin n))
    (a b : Fin t → Fin n) (u : ℂ) :
    qminor (fun a b => E (s a) (s b)) a b u = qminor E (s ∘ a) (s ∘ b) u := by
  unfold Formalism.REAL.qminor
  simp only [tm_renum, Function.comp_apply]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem qdet_renum {A : Type} [Ring A] [Algebra ℂ A] {E : Fin n → Fin n → A} (hE : GlRel E)
    (s : Equiv.Perm (Fin n)) (u : ℂ) : qdet (fun a b => E (s a) (s b)) u = qdet E u := by
  have h1 : qdet (fun a b => E (s a) (s b)) u = qminor E (id ∘ ⇑s) (id ∘ ⇑s) u := by
    unfold Formalism.REAL.qdet
    rw [qminor_renum]
    rfl
  have hsq : ((Equiv.Perm.sign s : ℤ) : A) * ((Equiv.Perm.sign s : ℤ) : A) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  rw [h1, Formalism.REAL.quantumMinorRowSkew_holds, Formalism.REAL.quantumMinorColSkew_holds A n n E hE, ← mul_assoc, hsq, one_mul]
  rfl

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem symm_lt {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    s.symm a < s.symm b := by
  rcases lt_trichotomy (s.symm a) (s.symm b) with h | h | h
  · exact h
  · exact absurd (s.symm.injective h) (ne_of_lt hab)
  · have h' := hs (s.symm b) (s.symm a) h (by simp [he])
    simp only [Equiv.apply_symm_apply] at h'
    exact absurd h' (lt_asymm hab)

/- English proof (translation)
Replace the relevant objects with their definitions. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem kHighest_iff {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool}
    (E : Fin n → Fin n → Module.End ℂ V) {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) (γ : Fin n → ℝ) (u : V) :
    KHighest ε E γ u ↔ KHighest (ε ∘ s) (fun a b => E (s a) (s b)) (γ ∘ s) u := by
  unfold Formalism.REAL.KHighest Formalism.REAL.IsWeight
  constructor
  · rintro ⟨hw, hz⟩
    exact ⟨fun a => hw (s a), fun a b hab he => hz (s a) (s b) (hs a b hab he) he⟩
  · rintro ⟨hw, hz⟩
    refine ⟨fun a => ?_, fun a b hab he => ?_⟩
    · simpa using hw (s.symm a)
    · have h := hz (s.symm a) (s.symm b) (symm_lt hs hab he) (by simpa using he)
      simpa using h

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem rhoC_renum {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) : rhoC (ε ∘ s) = rhoC ε ∘ s := by
  funext a
  have h1 : (Finset.univ.filter (fun b => a < b ∧ ε (s b) = ε (s a))).card =
      (Finset.univ.filter (fun b => s a < b ∧ ε b = ε (s a))).card := by
    refine Finset.card_nbij' s s.symm ?_ ?_ ?_ ?_
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe] at hb ⊢
      exact ⟨hs a b hb.1 hb.2.symm, hb.2⟩
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe, Equiv.apply_symm_apply] at hc ⊢
      refine ⟨?_, hc.2⟩
      have h' := symm_lt hs hc.1 hc.2.symm
      simpa using h'
    · intro b _
      simp
    · intro c _
      simp
  have h2 : (Finset.univ.filter (fun b => b < a ∧ ε (s b) = ε (s a))).card =
      (Finset.univ.filter (fun b => b < s a ∧ ε b = ε (s a))).card := by
    refine Finset.card_nbij' s s.symm ?_ ?_ ?_ ?_
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe] at hb ⊢
      exact ⟨hs b a hb.1 hb.2, hb.2⟩
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe, Equiv.apply_symm_apply] at hc ⊢
      refine ⟨?_, hc.2⟩
      have h' := symm_lt hs hc.1 hc.2
      simpa using h'
    · intro b _
      simp
    · intro c _
      simp
  simp only [PI.UpqRep.rhoC, Function.comp_apply, h1, h2]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem vNormSq_renum {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) (γ : Fin n → ℝ) :
    vNormSq (ε ∘ s) (γ ∘ s) = vNormSq ε γ := by
  unfold PI.UpqRep.vNormSq PI.UpqRep.nsq PI.UpqRep.dot
  rw [rhoC_renum hs]
  exact Fintype.sum_equiv s _ _ (fun a => by simp)

/- English proof (translation)
Replace the relevant objects with their definitions. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem isMinG_iff {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool}
    (E : Fin n → Fin n → Module.End ℂ V) {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) (γ : Fin n → ℝ) :
    IsMinG ε E γ ↔ IsMinG (ε ∘ s) (fun a b => E (s a) (s b)) (γ ∘ s) := by
  unfold CompanionTheory.RgExh.U.IsMinG
  constructor
  · intro h μ x hx hk
    have hμ : μ = (μ ∘ s.symm) ∘ s := by
      funext a
      simp
    rw [hμ] at hk ⊢
    rw [vNormSq_renum hs, vNormSq_renum hs]
    exact h _ x hx ((kHighest_iff E hs _ x).mpr hk)
  · intro h μ x hx hk
    have h' := h (μ ∘ s) x hx ((kHighest_iff E hs μ x).mp hk)
    rwa [vNormSq_renum hs, vNormSq_renum hs] at h'

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem renumber : CompanionTheory.RgExh.U.Renumber := by
  intro n ε V _ _ E hE s hs
  refine ⟨glRel_renum hE s, fun hU a b x y => hU (s a) (s b) x y, ?_, ?_,
    fun γ u => kHighest_iff E hs γ u, fun γ => isMinG_iff E hs γ, rhoC_renum hs⟩
  · intro hL x
    obtain ⟨S, hS, hK, hx⟩ := hL x
    exact ⟨S, hS, fun a b hab v hv => hK (s a) (s b) hab v hv, hx⟩
  · intro χ hχ Y
    exact (qdet_renum hE s _).trans (hχ Y)

end GlobalTheory.CompanionTheory.RgFarRen
