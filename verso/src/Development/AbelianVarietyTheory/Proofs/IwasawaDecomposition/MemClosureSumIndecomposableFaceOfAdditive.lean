import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark

/- English proof (translation)
Establish `hone : ∀ x, InFace bar ψ lab β x → x ≠ 0 → 1 ≤ ψ.evalZ x`. Introduce `x hx h0`. Take `⟨n, hn⟩` from `hint x hx`. Establish `hp` using `hpos x hx h0`. Rewrite `hp`, the goal using `[hn]`.

Establish `: (0 : ℤ) < n` using `by exact_mod_cast hp`. Conclude with `this` after adjusting the coercions. Establish `key : ∀ N : ℕ, ∀ x, InFace bar ψ lab β x → x ≠ 0 → ψ.evalZ x < N → x ∈ AddSubmonoid.closure {y | IsIndec bar ψ lab β y}`. Introduce `N`. Proceed by induction on `N with`.

Consider the case `zero`. Introduce `x hx h0 hN`. Use `hpos x hx h0` as an intermediate fact. Simplify using `only [Nat.cast_zero] at hN`. Combine the linear equalities and inequalities to obtain the conclusion.

Consider the case `succ N ih`. Introduce `x hx h0 hN`. Distinguish the cases in `hI : IsIndec bar ψ lab β x`. Conclude with `AddSubmonoid.subset_closure hI`. Establish `: ∃ y z, InFace bar ψ lab β y ∧ InFace bar ψ lab β z ∧ y ≠ 0 ∧ z ≠ 0 ∧ y + z = x`.

Assume the negation of the conclusion as `hc`. Conclude with `hI ⟨hx, h0, fun y z hy hz hy0 hz0 e => hc ⟨y, z, hy, hz, hy0, hz0, e⟩⟩`. Take `⟨y, z, hy, hz, hy0, hz0, rfl⟩` from `this`. Establish `hs` using `(hadd y z hy hz).2`. Establish `h1` using `hone y hy hy0`.

Establish `h2` using `hone z hz hz0`. Move the coercions through the operations in `at hN`. Conclude with `add_mem (ih y hy hy0 (by linarith)) (ih z hz hz0 (by linarith))`. Introduce `x hx`. Distinguish the cases in `h0 : x = 0`.

Rewrite using `[h0]`. Conclude with `zero_mem _`. Take `⟨N, hN⟩` from `exists_nat_gt (ψ.evalZ x)`. Conclude with `key N x hx h0 hN`.
-/
theorem mem_closure_isIndec (O : Type) [CommRing O] (bar : O → O) (ψ lab : InvFun O) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X)
    (hadd : ∀ x y, InFace bar ψ lab β x → InFace bar ψ lab β y →
      InFace bar ψ lab β (x + y) ∧ ψ.evalZ (x + y) = ψ.evalZ x + ψ.evalZ y)
    (hint : ∀ x, InFace bar ψ lab β x → ∃ n : ℤ, ψ.evalZ x = n)
    (hpos : ∀ x, InFace bar ψ lab β x → x ≠ 0 → 0 < ψ.evalZ x) :
    ∀ x, InFace bar ψ lab β x → x ∈ AddSubmonoid.closure {y | IsIndec bar ψ lab β y} := by
  have hone : ∀ x, InFace bar ψ lab β x → x ≠ 0 → 1 ≤ ψ.evalZ x := by
    intro x hx h0
    obtain ⟨n, hn⟩ := hint x hx
    have hp := hpos x hx h0
    rw [hn] at hp ⊢
    have : (0 : ℤ) < n := by exact_mod_cast hp
    exact_mod_cast this
  have key : ∀ N : ℕ, ∀ x, InFace bar ψ lab β x → x ≠ 0 → ψ.evalZ x < N →
      x ∈ AddSubmonoid.closure {y | IsIndec bar ψ lab β y} := by
    intro N
    induction N with
    | zero =>
      intro x hx h0 hN
      have := hpos x hx h0
      simp only [Nat.cast_zero] at hN
      linarith
    | succ N ih =>
      intro x hx h0 hN
      by_cases hI : IsIndec bar ψ lab β x
      · exact AddSubmonoid.subset_closure hI
      · have : ∃ y z, InFace bar ψ lab β y ∧ InFace bar ψ lab β z ∧ y ≠ 0 ∧ z ≠ 0 ∧ y + z = x := by
          by_contra hc
          exact hI ⟨hx, h0, fun y z hy hz hy0 hz0 e => hc ⟨y, z, hy, hz, hy0, hz0, e⟩⟩
        obtain ⟨y, z, hy, hz, hy0, hz0, rfl⟩ := this
        have hs := (hadd y z hy hz).2
        have h1 := hone y hy hy0
        have h2 := hone z hz hz0
        push_cast at hN
        exact add_mem (ih y hy hy0 (by linarith)) (ih z hz hz0 (by linarith))
  intro x hx
  by_cases h0 : x = 0
  · rw [h0]; exact zero_mem _
  · obtain ⟨N, hN⟩ := exists_nat_gt (ψ.evalZ x)
    exact key N x hx h0 hN

end GlobalTheory.PolFan.Mark
