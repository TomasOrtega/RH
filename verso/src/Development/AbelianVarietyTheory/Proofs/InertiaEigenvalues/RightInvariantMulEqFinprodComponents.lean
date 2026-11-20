import Mathlib
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

/- English proof (translation)
Introduce `Γ _ K ι c a hK hfin hidem horth hinv ha1 hmul`. Establish `haK : ∀ k, k ∈ K → a k = 1`. Introduce `k hk`. Use `hinv 1 k hk` as an intermediate fact. Rewrite `this` using `[one_mul]`.

Rewrite using `[this, ha1]`. Establish `key : ∀ (s : Finset ι) (g : Γ), {v | c v g ∉ K} ⊆ (s : Set ι) → a g = ∏ v ∈ s, a (c v g)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`.

Introduce `g hg`. Establish `hgK : g ∈ K` using `(hK g).2 (fun v => by`. Assume the negation of the conclusion as `h`. Simplify using `using hg h)`. Simplify using `[haK g hgK]`.

Consider the case `@insert v s hv ih`. Introduce `g hg`. Use `set g' := g * (c v g)⁻¹ with hg'`. Establish `hcv : c v g' = 1`. Rewrite using `[hg', map_mul, map_inv, hidem, mul_inv_cancel]`.

Establish `hcw : ∀ w, w ≠ v → c w g' = c w g`. Introduce `w hw`. Rewrite using `[hg', map_mul, map_inv, horth v w g (Ne.symm hw), inv_one, mul_one]`. Establish `hsupp : {w | c w g' ∉ K} ⊆ (s : Set ι)`. Introduce `w hw`.

Simplify using `only [Set.mem_setOf_eq] at hw`. Distinguish the cases in `hwv : w = v`. Substitute `hwv` using the available equality. Conclude with `absurd (hcv ▸ K.one_mem) hw`. Rewrite `hw` using `[hcw w hwv]`.

Use `hg hw` as an intermediate fact. Simplify using `only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at this`. Conclude with `this.resolve_left hwv`. Establish `ih'` using `ih g' hsupp`. Establish `hprod : ∏ w ∈ s, a (c w g') = ∏ w ∈ s, a (c w g)`.

Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `w hw`. Rewrite using `[hcw w (fun h => hv (h ▸ hw))]`. Establish `hsplit : g = g' * c v g`. Rewrite using `[hg', inv_mul_cancel_right]`.

Establish `hag : a g = a g' * a (c v g)` using `by conv_lhs => rw [hsplit]`. Conclude with `hmul v g' (c v g) hcv (hidem v g)`. Rewrite using `[hag, ih', hprod, Finset.prod_insert hv, mul_comm]`. Introduce `g`. Establish `hsub : Function.mulSupport (fun v => a (c v g)) ⊆ ((hfin g).toFinset : Set ι)`.

Introduce `w hw`. Simplify using `only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]`. Introduce `hwK`. Conclude with `hw (haK _ hwK)`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset _ hsub]`.

Conclude with `key _ g (by simp)`.
-/
theorem finprod_components_of_rightInvariant_mul :
    ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (ι : Type) (c : ι → Γ →* Γ) (a : Γ → ℂ),
      (∀ g, g ∈ K ↔ ∀ v, c v g ∈ K) → (∀ g, {v | c v g ∉ K}.Finite) →
      (∀ v g, c v (c v g) = c v g) → (∀ v w g, v ≠ w → c w (c v g) = 1) →
      (∀ g k, k ∈ K → a (g * k) = a g) → a 1 = 1 →
      (∀ v g h, c v g = 1 → c v h = h → a (g * h) = a g * a h) →
      ∀ g, a g = ∏ᶠ v, a (c v g) := by
  intro Γ _ K ι c a hK hfin hidem horth hinv ha1 hmul
  classical

  have haK : ∀ k, k ∈ K → a k = 1 := by
    intro k hk
    have := hinv 1 k hk
    rw [one_mul] at this
    rw [this, ha1]
  have key : ∀ (s : Finset ι) (g : Γ), {v | c v g ∉ K} ⊆ (s : Set ι) →
      a g = ∏ v ∈ s, a (c v g) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro g hg
      have hgK : g ∈ K := (hK g).2 (fun v => by
        by_contra h
        simpa using hg h)
      simp [haK g hgK]
    | @insert v s hv ih =>
      intro g hg
      set g' := g * (c v g)⁻¹ with hg'
      have hcv : c v g' = 1 := by
        rw [hg', map_mul, map_inv, hidem, mul_inv_cancel]
      have hcw : ∀ w, w ≠ v → c w g' = c w g := by
        intro w hw
        rw [hg', map_mul, map_inv, horth v w g (Ne.symm hw), inv_one, mul_one]
      have hsupp : {w | c w g' ∉ K} ⊆ (s : Set ι) := by
        intro w hw
        simp only [Set.mem_setOf_eq] at hw
        by_cases hwv : w = v
        · subst hwv
          exact absurd (hcv ▸ K.one_mem) hw
        · rw [hcw w hwv] at hw
          have := hg hw
          simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at this
          exact this.resolve_left hwv
      have ih' := ih g' hsupp
      have hprod : ∏ w ∈ s, a (c w g') = ∏ w ∈ s, a (c w g) := by
        apply Finset.prod_congr rfl
        intro w hw
        rw [hcw w (fun h => hv (h ▸ hw))]
      have hsplit : g = g' * c v g := by
        rw [hg', inv_mul_cancel_right]
      have hag : a g = a g' * a (c v g) := by
        conv_lhs => rw [hsplit]
        exact hmul v g' (c v g) hcv (hidem v g)
      rw [hag, ih', hprod, Finset.prod_insert hv, mul_comm]
  intro g
  have hsub : Function.mulSupport (fun v => a (c v g)) ⊆ ((hfin g).toFinset : Set ι) := by
    intro w hw
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro hwK
    exact hw (haK _ hwK)
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  exact key _ g (by simp)

end GlobalTheory
