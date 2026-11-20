import Mathlib
open scoped ENNReal Classical

namespace GlobalTheory

/- English proof (translation)
Set `c : A → MulAction.orbitRel.Quotient G X` to `fun a => Quotient.mk (MulAction.orbitRel G X) (ι a)`. Establish `hc : Function.Injective c`. Introduce `a b hab`. Establish `h : (MulAction.orbitRel G X) (ι a) (ι b)` using `Quotient.exact hab`. Rewrite `h` using `[MulAction.orbitRel_apply]`.

Take `⟨g, hg⟩` from `h`. Conclude with `(hinj b a ⟨g, hg⟩).symm`. Establish `hout : ∀ a, ∃ g : G, g • ι a = (c a).out`. Introduce `a`. Establish `h : (MulAction.orbitRel G X) ((c a).out) (ι a)` using `Quotient.exact (Quotient.out_eq (c a))`.

Rewrite `h` using `[MulAction.orbitRel_apply]`. Conclude with `h`. Establish `hsupp : Function.support (fun o : MulAction.orbitRel.Quotient G X => if T o.out then φ o.out else 0) ⊆ Set.range c`. Introduce `o ho`. Establish `hTo : T o.out`.

Assume the negation of the conclusion as `hn`. Conclude with `ho (if_neg hn)`. Take `⟨a, g, hg⟩` from `hsurj _ hTo`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[← Quotient.out_eq o]`.

Apply `Quotient.sound` to reduce the goal to its premises. Establish `h : (MulAction.orbitRel G X) o.out (ι a)`. Rewrite using `[MulAction.orbitRel_apply]`. Conclude with `⟨g, hg⟩`. Conclude with `(MulAction.orbitRel G X).symm h`.

Rewrite using `[← hc.tsum_eq hsupp]`. Use `tsum_congr fun a => ?_` and prove the remaining obligations. Take `⟨g, hg⟩` from `hout a`. Rewrite using `[← hg, if_pos (hT g _ (hι a)), hφ g _ (hι a)]`.
-/
theorem tsum_transversal_eq_tsum_orbitQuotient_general {G X A M : Type} [Group G] [MulAction G X]
    [AddCommMonoid M] [TopologicalSpace M] (ι : A → X) (T : X → Prop)
    (hT : ∀ g : G, ∀ x, T x → T (g • x)) (hι : ∀ a, T (ι a))
    (hsurj : ∀ x, T x → ∃ a, ∃ g : G, g • ι a = x)
    (hinj : ∀ a b, (∃ g : G, g • ι a = ι b) → a = b)
    (φ : X → M) (hφ : ∀ g : G, ∀ x, T x → φ (g • x) = φ x) :
    ∑' a, φ (ι a) = ∑' o : MulAction.orbitRel.Quotient G X, if T o.out then φ o.out else 0 := by
  let c : A → MulAction.orbitRel.Quotient G X := fun a => Quotient.mk (MulAction.orbitRel G X) (ι a)
  have hc : Function.Injective c := by
    intro a b hab
    have h : (MulAction.orbitRel G X) (ι a) (ι b) := Quotient.exact hab
    rw [MulAction.orbitRel_apply] at h
    obtain ⟨g, hg⟩ := h
    exact (hinj b a ⟨g, hg⟩).symm
  have hout : ∀ a, ∃ g : G, g • ι a = (c a).out := by
    intro a
    have h : (MulAction.orbitRel G X) ((c a).out) (ι a) := Quotient.exact (Quotient.out_eq (c a))
    rw [MulAction.orbitRel_apply] at h
    exact h
  have hsupp : Function.support
      (fun o : MulAction.orbitRel.Quotient G X => if T o.out then φ o.out else 0) ⊆ Set.range c := by
    intro o ho
    have hTo : T o.out := by
      by_contra hn
      exact ho (if_neg hn)
    obtain ⟨a, g, hg⟩ := hsurj _ hTo
    refine ⟨a, ?_⟩
    rw [← Quotient.out_eq o]
    apply Quotient.sound
    have h : (MulAction.orbitRel G X) o.out (ι a) := by
      rw [MulAction.orbitRel_apply]
      exact ⟨g, hg⟩
    exact (MulAction.orbitRel G X).symm h
  rw [← hc.tsum_eq hsupp]
  refine tsum_congr fun a => ?_
  obtain ⟨g, hg⟩ := hout a
  rw [← hg, if_pos (hT g _ (hι a)), hφ g _ (hι a)]

/- English proof (translation)
Introduce `G X A _ _ ι T hT hι hsurj hinj`. Conclude with `⟨fun φ hφ => tsum_transversal_eq_tsum_orbitQuotient_general ι T hT hι hsurj hinj φ hφ, fun φ hφ => tsum_transversal_eq_tsum_orbitQuotient_general ι T hT hι hsurj hinj φ hφ⟩`.
-/
theorem tsum_transversal_eq_tsum_orbitQuotient : ∀ {G X A : Type} [Group G] [MulAction G X] (ι : A → X) (T : X → Prop), (∀ g : G, ∀ x, T x → T (g • x)) → (∀ a, T (ι a)) → (∀ x, T x → ∃ a, ∃ g : G, g • ι a = x) → (∀ a b, (∃ g : G, g • ι a = ι b) → a = b) → (∀ φ : X → ℂ, (∀ g : G, ∀ x, T x → φ (g • x) = φ x) → ∑' a, φ (ι a) = ∑' o : MulAction.orbitRel.Quotient G X, if T o.out then φ o.out else 0) ∧ ∀ φ : X → ℝ≥0∞, (∀ g : G, ∀ x, T x → φ (g • x) = φ x) → ∑' a, φ (ι a) = ∑' o : MulAction.orbitRel.Quotient G X, if T o.out then φ o.out else 0 := by
  intro G X A _ _ ι T hT hι hsurj hinj
  exact ⟨fun φ hφ => tsum_transversal_eq_tsum_orbitQuotient_general ι T hT hι hsurj hinj φ hφ,
    fun φ hφ => tsum_transversal_eq_tsum_orbitQuotient_general ι T hT hι hsurj hinj φ hφ⟩

end GlobalTheory
