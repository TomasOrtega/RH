import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CBCardNC

namespace HalfIntGap₂

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `a b h`. Establish `: a = b` using `Fin.ext (by omega)`.

Substitute `this` using the available equality. Simplify using the standard rewrite rules. Consider the case `succ d ih`. Introduce `a b h`. Establish `hb' : a.val + d < N` using `by have := b.isLt; omega`.

Establish `h1` using `ih a ⟨a.val + d, hb'⟩ rfl`. Establish `hlt : (⟨a.val + d, hb'⟩ : Fin N) < b`. Rewrite using `[Fin.lt_def]`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Establish `h2` using `hm hlt`. Use `push_cast`. Use linear arithmetic over natural numbers and integers.
-/
theorem int_gap {N : ℕ} (m : Fin N → ℤ) (hm : StrictAnti m) :
    ∀ d : ℕ, ∀ a b : Fin N, b.val = a.val + d → (d : ℤ) ≤ m a - m b := by
  intro d
  induction d with
  | zero =>
    intro a b h
    have : a = b := Fin.ext (by omega)
    subst this
    simp
  | succ d ih =>
    intro a b h
    have hb' : a.val + d < N := by have := b.isLt; omega
    have h1 := ih a ⟨a.val + d, hb'⟩ rfl
    have hlt : (⟨a.val + d, hb'⟩ : Fin N) < b := by
      rw [Fin.lt_def]; simp; omega
    have h2 := hm hlt
    push_cast
    omega

/- English proof (translation)
Use `choose m hm using hc`. Establish `hanti : StrictAnti m`. Introduce `x y hxy`. Establish `h` using `hlam hxy`. Establish `hx : lam x = c + m x` using `by linarith [hm x]`.

Establish `hy : lam y = c + m y` using `by linarith [hm y]`. Rewrite `h` using `[hx, hy]`. Conclude with `(by linarith : (m y : ℝ) < m x)` after adjusting the coercions. Establish `hle : a.val ≤ b.val` using `le_of_lt (Fin.lt_def.mp hab)`. Establish `key` using `int_gap m hanti (b.val - a.val) a b (by omega)`.

Establish `key' : ((b.val : ℤ) - a.val) ≤ m a - m b`. Establish `: ((b.val - a.val : ℕ) : ℤ) = (b.val : ℤ) - a.val` using `by omega`. Use linear arithmetic over natural numbers and integers. Establish `hreal : ((b.val : ℝ) - a.val) ≤ (m a : ℝ) - m b` using `by exact_mod_cast key'`. Establish `ha : lam a = c + m a` using `by linarith [hm a]`.

Establish `hb : lam b = c + m b` using `by linarith [hm b]`. Rewrite using `[ha, hb]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gap (N : ℕ) (lam : Fin N → ℝ) (c : ℝ) (hlam : StrictAnti lam)
    (hc : ∀ a, ∃ m : ℤ, lam a - c = m) (a b : Fin N) (hab : a < b) :
    ((b.val : ℝ) - a.val) ≤ lam a - lam b := by
  choose m hm using hc
  have hanti : StrictAnti m := by
    intro x y hxy
    have h := hlam hxy
    have hx : lam x = c + m x := by linarith [hm x]
    have hy : lam y = c + m y := by linarith [hm y]
    rw [hx, hy] at h
    exact_mod_cast (by linarith : (m y : ℝ) < m x)
  have hle : a.val ≤ b.val := le_of_lt (Fin.lt_def.mp hab)
  have key := int_gap m hanti (b.val - a.val) a b (by omega)
  have key' : ((b.val : ℤ) - a.val) ≤ m a - m b := by
    have : ((b.val - a.val : ℕ) : ℤ) = (b.val : ℤ) - a.val := by omega
    omega
  have hreal : ((b.val : ℝ) - a.val) ≤ (m a : ℝ) - m b := by exact_mod_cast key'
  have ha : lam a = c + m a := by linarith [hm a]
  have hb : lam b = c + m b := by linarith [hm b]
  rw [ha, hb]
  linarith

/- English proof (translation)
Introduce `N lam c hlam hc a b hab`. Conclude with `gap N lam c hlam hc a b hab`.
-/
theorem main : Formalism.MainNotions.Ext.CutB.cBHCGap := by
  intro N lam c hlam hc a b hab
  exact gap N lam c hlam hc a b hab

end HalfIntGap₂
