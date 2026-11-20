import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqOneOfStrictMono

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

/- English proof (translation)
Introduce `n p h1 hstep`. Take `⟨hA, hB, -, -, -⟩` from `UpperTheory.V.AlgebraTools.hkInv n`. Establish `red : ∀ w : Perm (Fin n), w ≠ 1 → ∃ w', invN w = invN w' + 1 ∧ (p w' → p w)`. Introduce `w hw`. Take `⟨a, c, hac, hlt⟩` from `hB w hw`.

Establish `hlt' : (swap a c * w)⁻¹ a < (swap a c * w)⁻¹ c`. Rewrite using `[mul_inv_rev, swap_inv, Perm.mul_apply, Perm.mul_apply, swap_apply_left, swap_apply_right]`. Conclude with `hlt`. Establish `hw' : swap a c * (swap a c * w) = w` using `swap_mul_self_mul a c w`. Use `⟨swap a c * w, ?_, fun hp => ?_⟩` and prove the remaining obligations.

Use `(hA a c hac _ hlt').2.2` as an intermediate fact. Rewrite `this` using `[hw']`. Then use the resulting hypothesis. Use `hstep a c hac _ hlt' hp` as an intermediate fact. Rewrite `this` using `[hw']`. Then use the resulting hypothesis. Establish `key : ∀ k, ∀ w : Perm (Fin n), invN w = k → p w`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `w hw`. Distinguish the cases in `h : w = 1`.

Substitute `h` using the available equality. Conclude with `h1`. Take `⟨w', e, -⟩` from `red w h`. It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers.

Consider the case `succ k ih`. Introduce `w hw`. Distinguish the cases in `h : w = 1`. Substitute `h` using the available equality. Conclude with `h1`.

Take `⟨w', e, hp⟩` from `red w h`. Conclude with `hp (ih w' (by omega))`. Conclude with `fun w => key _ w rfl`.
-/
theorem UpperTheory.V.AlgebraTools.hkInd :
    ∀ (n : ℕ) (p : Perm (Fin n) → Prop), p 1 →
      (∀ (a c : Fin n), a.val + 1 = c.val → ∀ w : Perm (Fin n), w⁻¹ a < w⁻¹ c → p w → p (swap a c * w)) → ∀ w, p w := by
  intro n p h1 hstep
  obtain ⟨hA, hB, -, -, -⟩ := UpperTheory.V.AlgebraTools.hkInv n
  have red : ∀ w : Perm (Fin n), w ≠ 1 → ∃ w', invN w = invN w' + 1 ∧ (p w' → p w) := by
    intro w hw
    obtain ⟨a, c, hac, hlt⟩ := hB w hw
    have hlt' : (swap a c * w)⁻¹ a < (swap a c * w)⁻¹ c := by
      rw [mul_inv_rev, swap_inv, Perm.mul_apply, Perm.mul_apply, swap_apply_left,
        swap_apply_right]
      exact hlt
    have hw' : swap a c * (swap a c * w) = w := swap_mul_self_mul a c w
    refine ⟨swap a c * w, ?_, fun hp => ?_⟩
    · have := (hA a c hac _ hlt').2.2
      rwa [hw'] at this
    · have := hstep a c hac _ hlt' hp
      rwa [hw'] at this
  have key : ∀ k, ∀ w : Perm (Fin n), invN w = k → p w := by
    intro k
    induction k with
    | zero =>
      intro w hw
      by_cases h : w = 1
      · subst h
        exact h1
      · obtain ⟨w', e, -⟩ := red w h
        exfalso
        omega
    | succ k ih =>
      intro w hw
      by_cases h : w = 1
      · subst h
        exact h1
      · obtain ⟨w', e, hp⟩ := red w h
        exact hp (ih w' (by omega))
  exact fun w => key _ w rfl
