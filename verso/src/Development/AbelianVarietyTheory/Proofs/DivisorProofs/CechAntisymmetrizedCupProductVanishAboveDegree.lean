import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

/- English proof (translation)
Proceed by induction on `vs generalizing t with`. Consider the case `nil`. Simplify using `only [prodL, List.foldr_nil, oneC]`. Simplify using `only [List.length_nil] at ht`. Rewrite using `[if_neg (by omega)]`.

Consider the case `cons v vs ih`. Express the relevant statement in the definitionally equal form `Lop f h v (prodL f h vs) t = 0`. Simplify using `only [List.length_cons] at ht`. Unfold `Lop`. Use `split_ifs with h1 h2`.

Establish `e1` using `ih t (by omega)`. Establish `e2` using `ih (t.erase (t.min' h1)) (by rw [Finset.card_erase_of_mem (Finset.min'_mem _ _)]; omega)`. Rewrite using `[e1, e2, mul_zero, smul_zero, smul_zero, add_zero]`. Establish `e1` using `ih t (by omega)`. Rewrite using `[e1, mul_zero, smul_zero, add_zero]`.

Both sides reduce to the same expression.
-/
theorem prodL_eq_zero_of_card {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type}
    [LinearOrder ι] (f : ι → V →+ V) (h : ι → ι → V →+ K) (vs : List V) (t : Finset ι)
    (ht : vs.length + 1 < t.card) : prodL f h vs t = 0 := by
  induction vs generalizing t with
  | nil =>
    simp only [prodL, List.foldr_nil, oneC]
    simp only [List.length_nil] at ht
    rw [if_neg (by omega)]
  | cons v vs ih =>
    change Lop f h v (prodL f h vs) t = 0
    simp only [List.length_cons] at ht
    unfold Lop
    split_ifs with h1 h2
    · have e1 := ih t (by omega)
      have e2 := ih (t.erase (t.min' h1))
        (by rw [Finset.card_erase_of_mem (Finset.min'_mem _ _)]; omega)
      rw [e1, e2, mul_zero, smul_zero, smul_zero, add_zero]
    · have e1 := ih t (by omega)
      rw [e1, mul_zero, smul_zero, add_zero]
    · rfl

/- English proof (translation)
Introduce `K _ V _ _ ι _ p f h`. Establish `halt : ∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), a + 1 < t.card → alt f h a v t = 0`. Introduce `a v t ht`. Simplify using `only [alt, Finset.sum_apply, Pi.smul_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `σ _`. Rewrite using `[prodL_eq_zero_of_card f h _ t (by simpa using ht), smul_zero]`. Use `⟨halt, ?_⟩` and prove the remaining obligations. Introduce `Φ hΦ a x hx t ht`. Proceed by induction on `hx using AddSubgroup.closure_induction with`.

Consider the case `mem x hx`. Take `⟨b, -, v, -, rfl⟩` from `hx`. Rewrite using `[hΦ, Pi.smul_apply, halt a v t ht, smul_zero]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp [hx, hy]`.

Consider the case `neg x _ hx => simp [hx]`.
-/
theorem alt_and_phi_vanish_above_degree : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K), (∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), a + 1 < t.card → alt f h a v t = 0) ∧ ∀ (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)), IsPhi p f h Φ → ∀ a, ∀ x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a, ∀ t : Finset ι, a + 1 < t.card → Φ x t = 0 := by
  intro K _ V _ _ ι _ p f h
  have halt : ∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), a + 1 < t.card → alt f h a v t = 0 := by
    intro a v t ht
    simp only [alt, Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_eq_zero
    intro σ _
    rw [prodL_eq_zero_of_card f h _ t (by simpa using ht), smul_zero]
  refine ⟨halt, ?_⟩
  intro Φ hΦ a x hx t ht
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, -, v, -, rfl⟩ := hx
    rw [hΦ, Pi.smul_apply, halt a v t ht, smul_zero]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | neg x _ hx => simp [hx]

end GlobalTheory.DI
