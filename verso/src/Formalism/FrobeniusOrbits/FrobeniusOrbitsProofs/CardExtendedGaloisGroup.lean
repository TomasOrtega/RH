import Mathlib
import Formalism.FrobeniusOrbits.Statement
import Formalism.FrobeniusOrbits.DiscrMaximalRealCyclotomic
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.FrobMulInertia
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow

open NumberField IntermediateField Ideal

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace Misc2

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem galE_one {e q d : ℕ} (hqd : HypOdd q d) {L : Type} [Field L] [NumberField L]
    {ζ a b : L} (h : IsLayer (e + 2) q d ζ a b) :
    galE e ζ a b (1 : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) = 1 := by
  obtain ⟨-, -, hmulE, -⟩ := hostGalois e q d hqd L ζ a b h
  have := hmulE 1 1
  rw [mul_one] at this
  exact (mul_eq_left.mp this.symm)

/- English proof (translation)
Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem ne_one_of_galE {e q d : ℕ} (hqd : HypOdd q d) {L : Type} [Field L] [NumberField L]
    {ζ a b : L} (h : IsLayer (e + 2) q d ζ a b) (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)
    (hσ : galE e ζ a b σ ≠ 1) : σ ≠ 1 := by
  rintro rfl
  exact hσ (galE_one hqd h)

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem units_ne_one_iff (x : ℤˣ) : x ≠ 1 ↔ x = -1 := by
  rcases Int.units_eq_one_or x with rfl | rfl <;> decide

end Misc2

open Misc2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem hostRamified_of (hI : HostInertia) : HostRamified := by
  intro e q d he hH L _ _ ζ a b h p _ P _ _
  have hqd := hH.toHypOdd
  obtain ⟨-, -, -, hbij⟩ := hostGalois e q d hqd L ζ a b h
  constructor
  · rintro ⟨σ, hσ1, hσ⟩
    by_contra hp
    push Not at hp
    obtain ⟨hp2, hpq, hpd⟩ := hp
    have hF := hostFrob_of hostGalois hostGalSpec e q d hqd L ζ a b h p hp2 hpq hpd P
    exact hσ1 ((hF.2.2 σ).mp hσ)
  · rintro (rfl | rfl | rfl)
    · obtain ⟨σ, hσ⟩ := hbij.2 (((1, 1), hcl e (u5 (e + 2))) : GG e)
      refine ⟨σ, ne_one_of_galE hqd h σ ?_, ?_⟩
      · rw [hσ]
        intro h1
        have h2 : hcl e (u5 (e + 2)) = 1 := congrArg Prod.snd h1
        have h3 := (hostGroup e).2.2.2.2.2.2.2.1
        rw [h2, orderOf_one] at h3
        have : 2 ≤ 2 ^ e := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
        omega
      · have : P.LiesOver (span {(2 : ℤ)}) := by simpa using (inferInstance : P.LiesOver (span {((2 : ℕ) : ℤ)}))
        exact ((hI e q d hH L ζ a b h σ).1 P).mpr (by rw [hσ]; rfl)
    · obtain ⟨σ, hσ⟩ := hbij.2 (sg e)
      refine ⟨σ, ne_one_of_galE hqd h σ ?_, ?_⟩
      · rw [hσ]; simp [sg, Prod.ext_iff]
      · exact ((hI e p d hH L ζ a b h σ).2.1 P).mpr (Or.inr hσ)
    · obtain ⟨σ, hσ⟩ := hbij.2 (((1, -1), 1) : GG e)
      refine ⟨σ, ne_one_of_galE hqd h σ ?_, ?_⟩
      · rw [hσ]; simp [Prod.ext_iff]
      · exact ((hI e q p hH L ζ a b h σ).2.2 P).mpr (Or.inr hσ)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem hostPartner : HostPartner := by
  intro e τ hτ
  rw [mem_Psi_iff] at hτ
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [Set.mem_ofPred_eq, mem_Psi_iff, units_ne_one_iff] at hg
    show _ ∈ Psi e
    rw [mem_Psi_iff]
    simp [cc, c0, hg, hτ]
  · intro g _ g' _ hgg
    simpa using hgg
  · intro t ht
    rw [SetLike.mem_coe, mem_Psi_iff] at ht
    refine ⟨(cc e)⁻¹ * t * τ⁻¹, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, mem_Psi_iff]
      simp [cc, c0, ht, hτ]
    · simp only
      group

namespace Misc2

def conjHom {G : Type*} [Group G] (χ : G →* ℂˣ) : G →* ℂ :=
  (starRingEnd ℂ).toMonoidHom.comp ((Units.coeHom ℂ).comp χ)

def twHom (e : ℕ) (χ : GG e →* ℂˣ) : GG e →* ℂ :=
  (Units.coeHom ℂ).comp (chC e) * conjHom χ

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem chC_apply (e : ℕ) (g : GG e) : ((chC e g : ℂˣ) : ℂ) = (((g.1.2 : ℤˣ) : ℤ) : ℂ) := rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Assume the hypotheses and unpack their components. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem conjHom_eq_one_iff {G : Type*} [Group G] (χ : G →* ℂˣ) : conjHom χ = 1 ↔ χ = 1 := by
  constructor
  · intro h
    ext g
    have := DFunLike.congr_fun h g
    simp only [conjHom, MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, MonoidHom.one_apply] at this
    have := congrArg (starRingEnd ℂ) this
    simpa using this
  · rintro rfl
    ext g
    simp [conjHom]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem int_units_sq_C (x : ℤˣ) : (((x : ℤ) : ℂ)) * ((x : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or x with rfl | rfl <;> simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Assume the hypotheses and unpack their components. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem twHom_eq_one_iff (e : ℕ) (χ : GG e →* ℂˣ) : twHom e χ = 1 ↔ χ = chC e := by
  constructor
  · intro h
    ext g
    have := DFunLike.congr_fun h g
    simp only [twHom, conjHom, MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply,
      Units.coeHom_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MonoidHom.one_apply, chC_apply] at this
    have h2 : starRingEnd ℂ ((χ g : ℂˣ) : ℂ) = (((g.1.2 : ℤˣ) : ℤ) : ℂ) := by
      have := congrArg (fun z => (((g.1.2 : ℤˣ) : ℤ) : ℂ) * z) this
      simp only [← mul_assoc, int_units_sq_C, one_mul, mul_one] at this
      exact this
    have := congrArg (starRingEnd ℂ) h2
    rw [chC_apply]
    simpa using this
  · rintro rfl
    ext g
    simp only [twHom, conjHom, MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply,
      Units.coeHom_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MonoidHom.one_apply, chC_apply]
    simp [int_units_sq_C]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Evaluate the numerical expressions.
-/
theorem chC_ne_one (e : ℕ) : chC e ≠ 1 := by
  intro h
  have := DFunLike.congr_fun h (cc e)
  have h2 := congrArg (fun u : ℂˣ => (u : ℂ)) this
  simp only [chC_apply, MonoidHom.one_apply, Units.val_one] at h2
  simp [cc, c0] at h2
  norm_num at h2

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Both sides reduce to the same expression.
-/
theorem card_extended_galois_group (e : ℕ) [Fintype (GG e)] : (Fintype.card (GG e) : ℂ) = 2 ^ (e + 2) := by
  rw [← Nat.card_eq_fintype_card, (hostGroup e).1]
  push_cast; rfl

end Misc2

open Classical in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. Take a linear combination of the given relations to obtain the conclusion.

Take a linear combination of the given relations to obtain the conclusion. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem hostCharSum : HostCharSum := by
  intro e
  refine ⟨fun χ => ?_, fun g => ?_⟩
  · have hpt : ∀ g : GG e, 2 * (if g ∉ Psi e then starRingEnd ℂ ((χ g : ℂˣ) : ℂ) else 0) =
        conjHom χ g - twHom e χ g := by
      intro g
      simp only [twHom, conjHom, MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply,
        Units.coeHom_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, chC_apply, mem_Psi_iff]
      rcases Int.units_eq_one_or g.1.2 with h | h <;> rw [h] <;> simp <;> ring
    have hA := sum_hom_units (conjHom χ)
    have hB := sum_hom_units (twHom e χ)
    simp only [conjHom_eq_one_iff, twHom_eq_one_iff, Nat.cast_ite, Nat.cast_zero] at hA hB
    have hS : 2 * (∑ g ∈ Finset.univ.filter (fun g : GG e => g ∉ Psi e),
        starRingEnd ℂ ((χ g : ℂˣ) : ℂ)) =
        (∑ g : GG e, conjHom χ g) - ∑ g : GG e, twHom e χ g := by
      rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun g _ => hpt g)
    rw [hA, hB, card_extended_galois_group] at hS
    have hne := chC_ne_one e
    split_ifs at hS ⊢ with h1 h2 h2
    · exact absurd (h1.symm.trans h2) (Ne.symm hne)
    · linear_combination hS / 2
    · linear_combination hS / 2
    · linear_combination hS / 2
  · simp only [chD, chQ, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst,
      MonoidHom.coe_snd, Prod.ext_iff]
    rcases Int.units_eq_one_or g.1.1 with h | h <;> rcases Int.units_eq_one_or g.1.2 with h' | h' <;>
      rw [h, h'] <;> decide

end Formalism.FrobeniusOrbits
