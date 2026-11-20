import Mathlib
import Formalism.FrobeniusOrbits.HostOrbitCountSg
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Orbits

noncomputable section

namespace Formalism.FrobeniusOrbits

namespace OrbitSg

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
lemma orderOf_negOne : orderOf (-1 : ℤˣ) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by decide) (by decide)

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
lemma orderOf_oneNeg : orderOf (((1 : ℤˣ), (-1 : ℤˣ)) : G0) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by decide) (by decide)

def emb {e : ℕ} (τ : GG e) (x : ℤˣ × HGrp e) : GG e :=
  ((if x.1 = 1 then 1 else (sg e).1) * τ.1, x.2 * τ.2)

/- English proof (translation)
Simplify using the standard rewrite rules. Evaluate the decidable proposition.
-/
lemma sg_fst_ne_one (e : ℕ) : (sg e).1 ≠ 1 := by
  simp only [sg]; decide

/- English proof (translation)
Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Apply the first step, then apply the next step to every resulting obligation. Both sides reduce to the same expression. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
lemma emb_injective {e : ℕ} (τ : GG e) : Function.Injective (emb τ) := by
  rintro ⟨s, t⟩ ⟨s', t'⟩ h
  simp only [emb, Prod.mk.injEq, mul_left_inj] at h
  obtain ⟨h1, h2⟩ := h
  refine Prod.ext ?_ h2
  have hne := sg_fst_ne_one e
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or s' with rfl | rfl
  · rfl
  · simp at h1; exact absurd h1.symm hne
  · simp at h1; exact absurd h1 hne
  · rfl

end OrbitSg

open OrbitSg

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Reduce the equality to equality of the corresponding arguments. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem hostOrbitCountSg : HostOrbitCountSg := by
  intro e φ h0 τ hτ
  have hord : orderOf φ = Nat.lcm 2 (orderOf φ.2) := by
    rw [Prod.orderOf, h0, orderOf_oneNeg]
  refine ⟨hord, ?_⟩
  have hpl : (fun i : ℕ => placeOf (φ ^ i * τ)) =
      emb τ ∘ (fun i : ℕ => (((-1 : ℤˣ), φ.2) : ℤˣ × HGrp e) ^ i) := by
    funext i
    have hP := hostOrbitsPlaces e φ (Or.inr h0) τ hτ i
    refine Prod.ext ?_ ?_
    · rw [hP.2.2 h0]
      simp only [Function.comp_apply, emb, Prod.pow_fst]
      congr 1
      rcases Nat.even_or_odd i with he | ho
      · rw [if_pos he, if_pos he.neg_one_pow]
      · rw [if_neg (Nat.not_even_iff_odd.2 ho), if_neg (by rw [ho.neg_one_pow]; decide)]
    · rw [hP.1]
      simp [emb]
  rw [hpl, Set.range_comp, Set.ncard_image_of_injective _ (emb_injective τ),
    ← Submonoid.coe_powers, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, Nat.card_submonoidPowers,
    hord, Prod.orderOf, orderOf_negOne]

end Formalism.FrobeniusOrbits
