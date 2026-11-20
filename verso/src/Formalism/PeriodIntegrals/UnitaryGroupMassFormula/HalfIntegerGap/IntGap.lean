import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CBCardNC

namespace HalfIntGap₂

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Substitute using the available equality. Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Establish an intermediate fact. Move the embeddings inside the algebraic operations. Use linear arithmetic over natural numbers and integers.
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
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem main : Formalism.MainNotions.Ext.CutB.cBHCGap := by
  intro N lam c hlam hc a b hab
  exact gap N lam c hlam hc a b hab

end HalfIntGap₂
