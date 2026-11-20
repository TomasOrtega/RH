import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueExtendRingOfIntegersHom
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem cmHost_rootNegDiscriminant_ne_zero (H : Host E) : H.rt0 ≠ 0 := by
  intro h
  have h2 := H.sqrt_neg_disc_sq
  rw [h] at h2
  have : (H.d : ℂ) = 0 := by simpa using h2.symm
  exact H.d_prime.ne_zero (by exact_mod_cast this)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem cmHost_rootNegDiscriminant_ne_neg_self (H : Host E) : H.rt0 ≠ -H.rt0 := by
  intro h
  apply cmHost_rootNegDiscriminant_ne_zero H
  linear_combination h / 2

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Use the polynomial consequences of the given equalities and inequalities. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem cmHost_conj_sqrtNegDisc (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  have h2 := H.sqrt_neg_disc_sq
  have him := congrArg Complex.im h2
  have hre := congrArg Complex.re h2
  simp [pow_two] at him hre
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h0 : H.rt0.re = 0 := by
    by_contra hne
    have : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext <;> simp [h0]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem host_emb_rt_sq (H : Host E) (τ : E →+* ℂ) : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
  have h := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
  rw [H.sqrt_neg_disc_sq]
  simpa using h

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem host_mem_compl_psiSet (H : Host E) (τ : E →+* ℂ) :
    τ ∈ (psiSet H)ᶜ ↔ τ (H.rt : E) = -H.rt0 := by
  change ¬ (τ (H.rt : E) = H.rt0) ↔ _
  constructor
  · intro h
    exact (sq_eq_sq_iff_eq_or_eq_neg.1 (host_emb_rt_sq H τ)).resolve_left h
  · intro h h'
    exact cmHost_rootNegDiscriminant_ne_neg_self H (h'.symm.trans h)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem card_psiSet_eq_card_compl (H : Host E) :
    Nat.card (psiSet H) = Nat.card ((psiSet H)ᶜ : Set (E →+* ℂ)) := by
  refine Nat.card_congr
    { toFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, ?_⟩
      invFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, ?_⟩
      left_inv := fun τ => Subtype.ext (star_star τ.1)
      right_inv := fun τ => Subtype.ext (star_star τ.1) }
  · rw [host_mem_compl_psiSet, ComplexEmbedding.conjugate_coe_eq, ← cmHost_conj_sqrtNegDisc]
    exact congrArg _ τ.2
  · have h := (host_mem_compl_psiSet H τ.1).1 τ.2
    change _ = H.rt0
    rw [ComplexEmbedding.conjugate_coe_eq, h, map_neg, cmHost_conj_sqrtNegDisc, neg_neg]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Use linear arithmetic over natural numbers and integers.
-/
theorem card_psiSet (H : Host E) : Nat.card (psiSet H) = Module.finrank ℚ E / 2 := by
  have h1 := Set.ncard_add_ncard_compl (psiSet H)
  have h2 := card_psiSet_eq_card_compl H
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h2
  rw [Nat.card_eq_fintype_card, Embeddings.card E ℂ] at h1
  rw [Nat.card_coe_set_eq]
  omega

variable {H : Host E} {l : Level H}

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem labK_eq_iff (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (τ : E →+* ℂ) (a : E) (x : c.F) :
    labK c K τ a = algebraMap c.F K x ↔ τ a = (x : ℂ) := by
  change algebraMap c.F K (Formalism.L2.Pj.embF c τ a) = _ ↔ _
  rw [(algebraMap c.F K).injective.eq_iff, Subtype.ext_iff]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem labK_injective (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] : Function.Injective (labK c K) := by
  intro τ τ' h
  refine RingHom.ext fun a => ?_
  exact (labK_eq_iff c K τ a (Formalism.L2.Pj.embF c τ' a)).1 (DFunLike.congr_fun h a)

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem labK_bijective (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] :
    Function.Bijective (labK c K) := by
  have : Finite (E →+* K) := Finite.of_equiv _ (RingHom.equivRatAlgHom E K).symm
  refine (labK_injective c K).bijective_of_nat_card_le ?_
  rw [Nat.card_eq_fintype_card (α := E →+* ℂ), Embeddings.card E ℂ]
  exact card_ringHom_le_finrank

end

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem labK_spec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K], Function.Bijective (labK c K) ∧ Splits E K ∧ (∀ τ, ∃ t : 𝓞 E →+* 𝓞 K, ∀ a : 𝓞 E, (t a : K) = labK c K τ (a : E)) ∧ ∃ ρ : 𝓞 K, ρ ^ 2 = -(H.d : 𝓞 K) ∧ (∀ τ, τ ∈ psiSet H ↔ labK c K τ (H.rt : E) = (ρ : K)) ∧ (∀ τ, τ ∈ (psiSet H)ᶜ ↔ labK c K τ (H.rt : E) = ((-ρ : 𝓞 K) : K)) ∧ Nat.card (psiSet H) = Module.finrank ℚ E / 2 ∧ Nat.card ((psiSet H)ᶜ : Set (E →+* ℂ)) = Module.finrank ℚ E / 2 := by
  intro E _ _ _ H l c K _ _ _
  have hb := labK_bijective c K
  refine ⟨hb, ?_, fun τ => ⟨RingOfIntegers.mapRingHom (labK c K τ), fun a => rfl⟩, ?_⟩
  · rw [splits_iff_card, ← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Embeddings.card E ℂ]
  let r : c.F := ⟨H.rt0, c.le (baseKA l).ρ.2⟩
  have hr : r ^ 2 = -(H.d : c.F) := Subtype.ext (by simpa [r] using H.sqrt_neg_disc_sq)
  have hK : (algebraMap c.F K r) ^ 2 = -(H.d : K) := by
    rw [← map_pow, hr]; simp
  have hint : IsIntegral ℤ (algebraMap c.F K r) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hK]
    exact (isIntegral_natCast H.d).neg
  obtain ⟨ρ, hρ⟩ : ∃ ρ : 𝓞 K, algebraMap (𝓞 K) K ρ = algebraMap c.F K r := ⟨⟨_, hint⟩, rfl⟩
  refine ⟨ρ, RingOfIntegers.ext ?_, fun τ => ?_, fun τ => ?_, card_psiSet H, ?_⟩
  · change algebraMap (𝓞 K) K (_ ^ 2) = algebraMap (𝓞 K) K (-_)
    rw [map_pow, map_neg, map_natCast, hρ]
    exact hK
  · change _ ↔ _ = algebraMap (𝓞 K) K ρ
    rw [hρ]
    exact (labK_eq_iff c K τ _ r).symm
  · rw [host_mem_compl_psiSet]
    have := (labK_eq_iff c K τ (H.rt : E) (-r)).symm
    rw [map_neg, ← hρ, ← map_neg] at this
    exact this
  · rw [← card_psiSet_eq_card_compl, card_psiSet]

end GlobalTheory.LamF
