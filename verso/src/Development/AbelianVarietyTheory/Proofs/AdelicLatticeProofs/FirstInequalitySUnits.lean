import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexFormulaNormsInvolutionStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsQuadraticSqrtExtensionBasicFactsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoMulCardPlacesLeCardOverQuadraticStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoMulCardInfinitePlaceLeQuadraticStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsQuadraticSqrtExtensionOfNotSquareStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsPlacesOverAndQuadraticConjStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Hilbert90SUnitsQuadraticExtensionStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSetStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexSquaresSUnitsNumberFieldStatement

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
private theorem index_sqs_top_eq {G : Type} [CommGroup G] (U : Subgroup G) :
    (sqs (⊤ : Subgroup U)).index = (sqs U).relIndex U := by
  unfold Subgroup.relIndex
  congr 1
  ext x
  simp only [sqs, Subgroup.mem_map, Subgroup.mem_top, true_and, Subgroup.mem_subgroupOf,
    powMonoidHom_apply]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.2, by simp⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using h)⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
private theorem relIndex_sqs_range_eq {U A : Type} [CommGroup U] [CommGroup A] (j : U →* A)
    (hj : Function.Injective j) :
    (sqs j.range).relIndex j.range = (sqs (⊤ : Subgroup U)).index := by
  rw [← Subgroup.index_comap]
  congr 1
  ext x
  simp only [sqs, Subgroup.mem_map, Subgroup.mem_top, true_and, Subgroup.mem_comap,
    powMonoidHom_apply, MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, h⟩
    exact ⟨y, hj (by simpa using h)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨j y, ⟨y, rfl⟩, by simp⟩

/- English proof (translation)
Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem arith_first_ineq (m n e s t : ℕ) (hd : m ∣ n) (h : 2 * 2 ^ e * n = (2 ^ s) ^ 2)
    (hs : 2 * s ≤ e + t) : m ≠ 0 ∧ 2 * m ≤ 2 ^ t := by
  have hn : n ≠ 0 := by
    rintro rfl
    have : 0 < (2 ^ s) ^ 2 := by positivity
    omega
  refine ⟨fun h0 => hn (by subst h0; simpa using hd), ?_⟩
  have hmn : m ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
  have h1 : 2 ^ e * (2 * n) ≤ 2 ^ e * 2 ^ t := by
    calc 2 ^ e * (2 * n) = (2 ^ s) ^ 2 := by rw [← h]; ring
      _ = 2 ^ (2 * s) := by ring
      _ ≤ 2 ^ (e + t) := Nat.pow_le_pow_right (by norm_num) hs
      _ = 2 ^ e * 2 ^ t := pow_add _ _ _
  have h2 : 2 * n ≤ 2 ^ t := Nat.le_of_mul_le_mul_left h1 (by positivity)
  omega

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Evaluate the numerical expressions.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative.

Prove the second alternative. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem first_inequality_sUnits :
    ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))),
      admitted F S → δ ∈ sUnits F S → ¬ IsSquare (δ : F) →
      (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≠ 0 ∧
        2 * (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≤
          2 ^ (tFin F δ S + tReal F δ) := by
  intro F _ _ δ S hS hδ hns
  obtain ⟨E, _, _, _, θ, σ, hq⟩ := GlobalTheory.T.exists_isQuadraticSqrtExtension_of_not_square F δ hns
  obtain ⟨SE, hSE⟩ := (GlobalTheory.T.heightOneSpectrum_places_over_finite_set F E).1 S
  obtain ⟨hinv, hfix, -, hnorm, -, -, -⟩ := GlobalTheory.T.isQuadraticSqrtExtension_basic_facts F E δ θ σ hq
  obtain ⟨hup, hσ⟩ := GlobalTheory.T.sUnits_places_over_and_quadratic_conj F E δ θ σ hq S SE hSE
  have h90 := GlobalTheory.T.hilbert90_sUnits_quadratic_extension_of_adm F E δ θ σ hq S SE hSE hS ((mem_sUnits F S δ).1 hδ)
  have hcf := GlobalTheory.T.two_mul_card_places_le_card_over_quadratic F E δ θ σ hq S SE hSE
  have hci := GlobalTheory.T.two_mul_card_infinitePlace_le_quadratic F E δ θ σ hq
  let τ : sUnits E SE →* sUnits E SE :=
    ((Units.map (σ : E →* E)).comp (sUnits E SE).subtype).codRestrict _ (fun y => hσ y y.2)
  have hτ : ∀ y : sUnits E SE, (((τ y : sUnits E SE) : Eˣ) : E) = σ ((y : Eˣ) : E) :=
    fun _ => rfl
  let j : sUnits F S →* sUnits E SE :=
    ((Units.map (algebraMap F E : F →* E)).comp (sUnits F S).subtype).codRestrict _
      (fun y => (hup y).2 y.2)
  have hj : ∀ y : sUnits F S, (((j y : sUnits E SE) : Eˣ) : E) = algebraMap F E ((y : Fˣ) : F) :=
    fun _ => rfl
  have hext : ∀ a b : sUnits E SE, ((a : Eˣ) : E) = ((b : Eˣ) : E) → a = b :=
    fun a b h => Subtype.ext (Units.ext h)
  have hjinj : Function.Injective j := by
    intro a b h
    apply Subtype.ext
    apply Units.ext
    apply (algebraMap F E).injective
    rw [← hj, ← hj, h]
  have hm : (-1 : Eˣ) ∈ sUnits E SE := by
    rw [mem_sUnits]
    intro v _
    simp
  have hrange : τ.eqLocus (MonoidHom.id _) = j.range := by
    ext y
    rw [MonoidHom.mem_range]
    change τ y = y ↔ _
    constructor
    · intro h
      obtain ⟨a, ha⟩ := hfix ((y : Eˣ) : E) (by rw [← hτ, h])
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact (y : Eˣ).ne_zero (by simpa using ha)
      have hy : Units.map (algebraMap F E : F →* E) (Units.mk0 a ha0) = y :=
        Units.ext (by simpa using ha.symm)
      refine ⟨⟨Units.mk0 a ha0, (hup _).1 (hy ▸ y.2)⟩, hext _ _ ?_⟩
      rw [hj, ha]; rfl
    · rintro ⟨x, rfl⟩
      apply hext
      rw [hτ, hj, AlgEquiv.commutes]
  have key := GlobalTheory.T.index_formula_norms_involution (sUnits E SE) τ ⟨-1, hm⟩
    (fun a => hext _ _ (by rw [hτ, hτ, hinv]))
    (fun a ha => by
      have h1 : ((a : Eˣ) : E) * σ ((a : Eˣ) : E) = 1 := by
        rw [← hτ]
        have := congrArg (fun z : sUnits E SE => ((z : Eˣ) : E)) ha
        simpa using this
      obtain ⟨y, hy, h⟩ := h90 a a.2 h1
      refine ⟨⟨y, hy⟩, hext _ _ ?_⟩
      rw [h, Subgroup.coe_div, Units.val_div_eq_div_val, hτ])
    (fun h => by
      have := congrArg (fun z : sUnits E SE => ((z : Eˣ) : E)) h
      simp only [Units.val_neg, Units.val_one, OneMemClass.coe_one] at this
      norm_num at this)
    (hext _ _ (by simp))
    (hext _ _ (by rw [hτ]; simp))
    (fun a ha => by
      have h1 : ((a : Eˣ) : E) ^ 2 = 1 := by
        have := congrArg (fun z : sUnits E SE => ((z : Eˣ) : E)) ha
        simpa using this
      rcases sq_eq_one_iff.1 h1 with h | h
      · exact Or.inl (hext _ _ (by simpa using h))
      · exact Or.inr (hext _ _ (by simpa using h)))
  rw [hrange, relIndex_sqs_range_eq j hjinj, index_sqs_top_eq, index_sqs_top_eq,
    GlobalTheory.T.relIndex_squares_sUnitsNumberField E SE, GlobalTheory.T.relIndex_squares_sUnitsNumberField F S, ← Subgroup.index_comap] at key
  refine arith_first_ineq _ _ _ _ _ ?_ key (by omega)
  apply Subgroup.index_dvd_of_le
  rintro x ⟨y, hy⟩
  rw [Subgroup.mem_subgroupOf, mem_normSub]
  obtain ⟨a, b, hab⟩ := hnorm ((y : Eˣ) : E)
  refine ⟨a, b, ?_⟩
  apply (algebraMap F E).injective
  simp only [RingHom.id_apply]
  rw [← hab, ← hj, ← hy, ← hτ]
  simp

end GlobalTheory.QNorm
