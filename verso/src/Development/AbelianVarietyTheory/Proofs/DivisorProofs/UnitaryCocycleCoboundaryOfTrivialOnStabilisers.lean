import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `X G _ mv z h1 hmul hn hz hs`. Establish `key : ∀ b h h', mv b h = mv b h' → z b h = z b h'`. Introduce `b h h' e`. Establish `e1 : mv b (h * h'⁻¹) = b`. Rewrite using `[hmul, e, ← hmul, mul_inv_cancel, h1]`.

Establish `e2` using `hz b (h * h'⁻¹) h'`. Rewrite `e2` using `[hs b _ e1, e1, one_mul, inv_mul_cancel_right]`. Conclude with `e2`. Set `s : Setoid X` to `{ r := fun x y => ∃ g, mv x g = y iseqv := { refl := fun x => ⟨1, h1 x⟩`. Use symmetry as in `:= by`.

Introduce and unpack `x y ⟨g, rfl⟩`. Conclude with `⟨g⁻¹, by rw [← hmul, mul_inv_cancel, h1]⟩`. Use `trans := by`. Introduce and unpack `x y w ⟨g, rfl⟩ ⟨g', rfl⟩`. Conclude with `⟨g * g', hmul _ _ _⟩ } }`.

Set `b : X → X` to `fun x => (Quotient.mk s x).out`. Establish `hb : ∀ x, ∃ g, mv (b x) g = x` using `fun x => Quotient.mk_out (s := s) x`. Establish `hbe : ∀ x g, b (mv x g) = b x`. Introduce `x g`. Establish `: Quotient.mk s (mv x g) = Quotient.mk s x` using `(Quotient.sound (s := s) (⟨g, rfl⟩ : ∃ g', mv x g' = mv x g)).symm`.

Simplify using `only [b, this]`. Use `choose γ hγ using hb`. Use `⟨fun x => z (b x) (γ x), fun x => hn _ _, fun x g => ?_⟩` and prove the remaining obligations. Establish `e` using `hz (b x) (γ x) g`. Rewrite `e` using `[hγ]`.

Establish `e'` using `hγ (mv x g)`. Use `show z (b x) (γ x) * z x g = z (b (mv x g)) (γ (mv x g))`. Rewrite `e'`, the goal using `[hbe]`. Rewrite using `[← e]`. Apply `key` to reduce the goal to its premises.

Rewrite using `[hmul, hγ, e']`.
-/
theorem unitary_cocycle_coboundary_of_trivial_on_stabilisers :
    ∀ {X G : Type} [Group G] (mv : X → G → X) (z : X → G → ℂ), (∀ x, mv x 1 = x) →
      (∀ x g g', mv x (g * g') = mv (mv x g) g') → (∀ x g, ‖z x g‖ = 1) →
      (∀ x g g', z x (g * g') = z x g * z (mv x g) g') → (∀ x g, mv x g = x → z x g = 1) →
      ∃ c : X → ℂ, (∀ x, ‖c x‖ = 1) ∧ ∀ x g, c x * z x g = c (mv x g) := by
  intro X G _ mv z h1 hmul hn hz hs
  have key : ∀ b h h', mv b h = mv b h' → z b h = z b h' := by
    intro b h h' e
    have e1 : mv b (h * h'⁻¹) = b := by
      rw [hmul, e, ← hmul, mul_inv_cancel, h1]
    have e2 := hz b (h * h'⁻¹) h'
    rw [hs b _ e1, e1, one_mul, inv_mul_cancel_right] at e2
    exact e2
  let s : Setoid X :=
    { r := fun x y => ∃ g, mv x g = y
      iseqv :=
        { refl := fun x => ⟨1, h1 x⟩
          symm := by
            rintro x y ⟨g, rfl⟩
            exact ⟨g⁻¹, by rw [← hmul, mul_inv_cancel, h1]⟩
          trans := by
            rintro x y w ⟨g, rfl⟩ ⟨g', rfl⟩
            exact ⟨g * g', hmul _ _ _⟩ } }
  let b : X → X := fun x => (Quotient.mk s x).out
  have hb : ∀ x, ∃ g, mv (b x) g = x := fun x => Quotient.mk_out (s := s) x
  have hbe : ∀ x g, b (mv x g) = b x := by
    intro x g
    have : Quotient.mk s (mv x g) = Quotient.mk s x :=
      (Quotient.sound (s := s) (⟨g, rfl⟩ : ∃ g', mv x g' = mv x g)).symm
    simp only [b, this]
  choose γ hγ using hb
  refine ⟨fun x => z (b x) (γ x), fun x => hn _ _, fun x g => ?_⟩
  have e := hz (b x) (γ x) g
  rw [hγ] at e
  have e' := hγ (mv x g)
  show z (b x) (γ x) * z x g = z (b (mv x g)) (γ (mv x g))
  rw [hbe] at e' ⊢
  rw [← e]
  apply key
  rw [hmul, hγ, e']

end GlobalTheory
