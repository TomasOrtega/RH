import Mathlib
import Formalism.FrobeniusOrbits.HostOrbitCountSg
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Orbits

noncomputable section

namespace Formalism.FrobeniusOrbits

namespace OrbitSg

/- English proof (translation)
Establish `: Fact (Nat.Prime 2)` using `⟨Nat.prime_two⟩`. Conclude with `orderOf_eq_prime (by decide) (by decide)`.
-/
lemma orderOf_negOne : orderOf (-1 : ℤˣ) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by decide) (by decide)

/- English proof (translation)
Establish `: Fact (Nat.Prime 2)` using `⟨Nat.prime_two⟩`. Conclude with `orderOf_eq_prime (by decide) (by decide)`.
-/
lemma orderOf_oneNeg : orderOf (((1 : ℤˣ), (-1 : ℤˣ)) : G0) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by decide) (by decide)

def emb {e : ℕ} (τ : GG e) (x : ℤˣ × HGrp e) : GG e :=
  ((if x.1 = 1 then 1 else (sg e).1) * τ.1, x.2 * τ.2)

/- English proof (translation)
Simplify using `only [sg]`. Evaluate the decidable proposition.
-/
lemma sg_fst_ne_one (e : ℕ) : (sg e).1 ≠ 1 := by
  simp only [sg]; decide

/- English proof (translation)
Introduce and unpack `⟨s, t⟩ ⟨s', t'⟩ h`. Simplify using `only [emb, Prod.mk.injEq, mul_left_inj] at h`. Take `⟨h1, h2⟩` from `h`. Use `Prod.ext ?_ h2` and prove the remaining obligations. Establish `hne` using `sg_fst_ne_one e`.

Apply the tactic sequence `rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or s' with rfl | rfl`. Both sides reduce to the same expression. Simplify using `at h1`. Conclude with `absurd h1.symm hne`. Simplify using `at h1`.

Conclude with `absurd h1 hne`. Both sides reduce to the same expression.
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
Introduce `e φ h0 τ hτ`. Establish `hord : orderOf φ = Nat.lcm 2 (orderOf φ.2)`. Rewrite using `[Prod.orderOf, h0, orderOf_oneNeg]`. Use `⟨hord, ?_⟩` and prove the remaining obligations. Establish `hpl : (fun i : ℕ => placeOf (φ ^ i * τ)) = emb τ ∘ (fun i : ℕ => (((-1 : ℤˣ), φ.2) : ℤˣ × HGrp e) ^ i)`.

Use function extensionality and compare the values at `i`. Establish `hP` using `hostOrbitsPlaces e φ (Or.inr h0) τ hτ i`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Rewrite using `[hP.2.2 h0]`. Simplify using `only [Function.comp_apply, emb, Prod.pow_fst]`.

Use `congr 1`. Break down `Nat.even_or_odd i with he | ho` into its components or cases. Rewrite using `[if_pos he, if_pos he.neg_one_pow]`. Rewrite using `[if_neg (Nat.not_even_iff_odd.2 ho), if_neg (by rw [ho.neg_one_pow]; decide)]`. Rewrite using `[hP.1]`.

Simplify using `[emb]`. Rewrite using `[hpl, Set.range_comp, Set.ncard_image_of_injective _ (emb_injective τ), ← Submonoid.coe_powers, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, Nat.card_submonoidPowers, hord, Prod.orderOf, orderOf_negOne]`.
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
