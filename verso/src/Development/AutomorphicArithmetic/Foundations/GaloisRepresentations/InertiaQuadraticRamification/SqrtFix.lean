import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertSplitAlt

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

/- English proof (translation)
Introduce `F Ω _ _ _ _ A x a hx`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Establish `hsq : ∀ g : G F Ω, g x = x ∨ g x = -x`. Introduce `g`. Establish `hgx : (g x) ^ 2 = x ^ 2` using `by rw [← map_pow, hx, map_intCast]`.

Establish `h0 : (g x - x) * (g x + x) = 0` using `by linear_combination hgx`. Break down `mul_eq_zero.1 h0 with h | h` into its components or cases. Conclude with `Or.inl (sub_eq_zero.1 h)`. Conclude with `Or.inr (eq_neg_of_add_eq_zero_left h)`. Establish `hint : ∀ k : ℤ, A.valuation (k : Ω) ≤ 1` using `fun k => by`.

Conclude with `A.valuation_le_one (k : A)` after adjusting the coercions. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `t _ hvt hdiv g hg`. Break down `hsq g with h | h` into its components or cases. Conclude with `h`.

It suffices to derive a contradiction. Take `⟨k, hk⟩` from `hdiv`. Establish `hk' : (a : Ω) - 1 = 8 * (t : Ω) * (k : Ω)`. Establish `hc` using `congrArg (fun z : ℤ => (z : Ω)) hk`. Move the coercions through the operations in `at hc`.

Take the linear combination `hc`. Use `set y : Ω := (x - 1) / 2 with hy`. Use `set y' : Ω := (-x - 1) / 2 with hy'`. Establish `hgy : g y = y'`. Rewrite using `[hy, hy', map_div₀, map_sub, map_one, map_ofNat, h]`.

Establish `hsum : y + y' = -1`. Rewrite using `[hy, hy']`. Expand and normalize the polynomial expressions, which then agree. Establish `hprod : y * y' = ((-2 * k : ℤ) : Ω) * (t : Ω)`. Rewrite using `[hy, hy']`.

Use `push_cast`. Take the linear combination `(-1 / 4 : Ω) * hx - (1 / 4 : Ω) * hk'`. Establish `hvp : A.valuation (y * y') < 1`. Rewrite using `[hprod, map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (hint _)) hvt`.

Establish `hvs : A.valuation (y + y') = 1`. Rewrite using `[hsum, Valuation.map_neg, Valuation.map_one]`. Establish `hiff` using `valuation_apply_lt_one_iff hg y`. Rewrite `hiff` using `[hgy]`. Distinguish the cases in `hyl : A.valuation y < 1`.

Establish `hs` using `Valuation.map_add_lt A.valuation hyl (hiff.2 hyl)`. Rewrite `hs` using `[hvs]`. Conclude with `lt_irrefl _ hs`. Establish `hyl' : ¬ A.valuation y' < 1` using `fun h' => hyl (hiff.1 h') push_neg at hyl hyl'`. Establish `hge : 1 ≤ A.valuation (y * y')`.

Rewrite using `[map_mul]`. Conclude with `one_le_mul hyl hyl'`. Conclude with `absurd hvp (not_lt.2 hge)`. Introduce `h2a τ hτ`. Take `⟨-, hI⟩ : τ ∈ ValuationSubring.decompositionSubgroup F A ∧ ∀ (y : Ω), A.valuation y ≤ 1 → A.valuation (τ y - y) < 1` from `hτ`.

Break down `hsq τ with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Establish `hv2 : A.valuation (2 : Ω) ≤ 1` using `by simpa using hint 2`. Establish `hva : A.valuation (a : Ω) ≤ 1` using `hint a`.

Establish `e2a : A.valuation (2 : Ω) * A.valuation (a : Ω) = 1`. Rewrite using `[← map_mul]`. Move the coercions through the operations in `at h2a`. Conclude with `h2a`. Establish `hv2' : A.valuation (2 : Ω) = 1` using `le_antisymm hv2 (e2a ▸ mul_le_of_le_one_right' hva)`.

Establish `hva' : A.valuation (a : Ω) = 1` using `le_antisymm hva (e2a ▸ mul_le_of_le_one_left' hv2)`. Establish `hvx2 : A.valuation x ^ 2 = 1`. Rewrite using `[← Valuation.map_pow, hx, hva']`. Establish `hvx : A.valuation x = 1`. Break down `lt_trichotomy (A.valuation x) 1 with hl | he | hg` into its components or cases.

Conclude with `absurd hvx2 (ne_of_lt (pow_lt_one' hl two_ne_zero))`. Conclude with `he`. Conclude with `absurd hvx2 (ne_of_gt (one_lt_pow' hg two_ne_zero))`. Establish `key` using `hI x hvx.le`. Rewrite `key` using `[h, show -x - x = -(2 * x) by ring, Valuation.map_neg, map_mul, hv2', hvx, one_mul]`.

Conclude with `lt_irrefl _ key`.
-/
theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.sqrtFix :
    SqrtFix := by
  intro F Ω _ _ _ _ A x a hx
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hsq : ∀ g : G F Ω, g x = x ∨ g x = -x := by
    intro g
    have hgx : (g x) ^ 2 = x ^ 2 := by rw [← map_pow, hx, map_intCast]
    have h0 : (g x - x) * (g x + x) = 0 := by linear_combination hgx
    rcases mul_eq_zero.1 h0 with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hint : ∀ k : ℤ, A.valuation (k : Ω) ≤ 1 := fun k => by
    exact_mod_cast A.valuation_le_one (k : A)
  refine ⟨?_, ?_⟩
  · intro t _ hvt hdiv g hg
    rcases hsq g with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := hdiv
      have hk' : (a : Ω) - 1 = 8 * (t : Ω) * (k : Ω) := by
        have hc := congrArg (fun z : ℤ => (z : Ω)) hk
        push_cast at hc
        linear_combination hc
      set y : Ω := (x - 1) / 2 with hy
      set y' : Ω := (-x - 1) / 2 with hy'
      have hgy : g y = y' := by
        rw [hy, hy', map_div₀, map_sub, map_one, map_ofNat, h]
      have hsum : y + y' = -1 := by
        rw [hy, hy']
        ring
      have hprod : y * y' = ((-2 * k : ℤ) : Ω) * (t : Ω) := by
        rw [hy, hy']
        push_cast
        linear_combination (-1 / 4 : Ω) * hx - (1 / 4 : Ω) * hk'
      have hvp : A.valuation (y * y') < 1 := by
        rw [hprod, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint _)) hvt
      have hvs : A.valuation (y + y') = 1 := by
        rw [hsum, Valuation.map_neg, Valuation.map_one]
      have hiff := valuation_apply_lt_one_iff hg y
      rw [hgy] at hiff
      by_cases hyl : A.valuation y < 1
      · have hs := Valuation.map_add_lt A.valuation hyl (hiff.2 hyl)
        rw [hvs] at hs
        exact lt_irrefl _ hs
      · have hyl' : ¬ A.valuation y' < 1 := fun h' => hyl (hiff.1 h')
        push_neg at hyl hyl'
        have hge : 1 ≤ A.valuation (y * y') := by
          rw [map_mul]
          exact one_le_mul hyl hyl'
        exact absurd hvp (not_lt.2 hge)
  · intro h2a τ hτ
    obtain ⟨-, hI⟩ : τ ∈ ValuationSubring.decompositionSubgroup F A ∧
        ∀ (y : Ω), A.valuation y ≤ 1 → A.valuation (τ y - y) < 1 := hτ
    rcases hsq τ with h | h
    · exact h
    · exfalso
      have hv2 : A.valuation (2 : Ω) ≤ 1 := by simpa using hint 2
      have hva : A.valuation (a : Ω) ≤ 1 := hint a
      have e2a : A.valuation (2 : Ω) * A.valuation (a : Ω) = 1 := by
        rw [← map_mul]
        push_cast at h2a
        exact h2a
      have hv2' : A.valuation (2 : Ω) = 1 :=
        le_antisymm hv2 (e2a ▸ mul_le_of_le_one_right' hva)
      have hva' : A.valuation (a : Ω) = 1 :=
        le_antisymm hva (e2a ▸ mul_le_of_le_one_left' hv2)
      have hvx2 : A.valuation x ^ 2 = 1 := by
        rw [← Valuation.map_pow, hx, hva']
      have hvx : A.valuation x = 1 := by
        rcases lt_trichotomy (A.valuation x) 1 with hl | he | hg
        · exact absurd hvx2 (ne_of_lt (pow_lt_one' hl two_ne_zero))
        · exact he
        · exact absurd hvx2 (ne_of_gt (one_lt_pow' hg two_ne_zero))
      have key := hI x hvx.le
      rw [h, show -x - x = -(2 * x) by ring, Valuation.map_neg, map_mul, hv2', hvx, one_mul] at key
      exact lt_irrefl _ key
