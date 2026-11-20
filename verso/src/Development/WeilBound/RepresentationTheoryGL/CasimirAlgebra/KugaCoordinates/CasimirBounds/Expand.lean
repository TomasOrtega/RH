import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CasimirBounds.ReSwapSumLe

open Finset

set_option linter.unusedSectionVars false

namespace PositivityTheory.Rg.Cz

section
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]

/- English proof (translation)
Simplify using `only [eAt, LinearMap.pi_apply]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem eAt_applyC (p : Q) (a c : Fin n) (f : TV n ℂ Q) (I : Q → Fin n) :
    (eAt p a c : Module.End ℂ (TV n ℂ Q)) f I = if I p = a then f (Function.update I p c) else 0 := by
  simp only [eAt, LinearMap.pi_apply]
  split_ifs <;> rfl

/- English proof (translation)
Simplify using `[tE, lift, LinearMap.add_apply, LinearMap.sum_apply, Finset.sum_apply]`.
-/
theorem tE_zero_apply (S : Finset Q) (a c : Fin n) (f : TV n ℂ Q) (I : Q → Fin n) :
    (tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) a c : Module.End ℂ (TV n ℂ Q)) f I =
      ∑ p ∈ S, (eAt p a c : Module.End ℂ (TV n ℂ Q)) f I := by
  simp [tE, lift, LinearMap.add_apply, LinearMap.sum_apply, Finset.sum_apply]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun a _ => Finset.sum_comm` and prove the remaining obligations. Use `_ = ∑ p ∈ s, ∑ a, ∑ c, ∑ q ∈ t, F a c p q := Finset.sum_comm`. Use `_ = ∑ p ∈ s, ∑ a, ∑ q ∈ t, ∑ c, F a c p q := by`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm` and prove the remaining obligations.

Use `_ = _ := by`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_comm` and prove the remaining obligations.
-/
theorem sum4 {α β : Type} (s : Finset α) (t : Finset β) (F : Fin n → Fin n → α → β → ℂ) :
    ∑ a, ∑ c, ∑ p ∈ s, ∑ q ∈ t, F a c p q = ∑ p ∈ s, ∑ q ∈ t, ∑ a, ∑ c, F a c p q := by
  calc _ = ∑ a, ∑ p ∈ s, ∑ c, ∑ q ∈ t, F a c p q := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ p ∈ s, ∑ a, ∑ c, ∑ q ∈ t, F a c p q := Finset.sum_comm
    _ = ∑ p ∈ s, ∑ a, ∑ q ∈ t, ∑ c, F a c p q := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_comm

/- English proof (translation)
Simplify using `only [eAt_applyC]`. Rewrite using `[Finset.sum_eq_single (I p)]`. Distinguish the cases in `hpq : p = q`. Substitute `hpq` using the available equality. Simplify using `[Function.update_idem, Finset.card_univ]`.

Establish `hqp : q ≠ p` using `Ne.symm hpq`. Simplify using `only [if_true, Function.update_of_ne hqp, hpq, if_false]`. Rewrite using `[Finset.sum_ite_eq]`. Simplify using `only [Finset.mem_univ, if_true]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : x = q`. Substitute `hx` using the available equality. Simplify using `[Equiv.swap_apply_right]`. Distinguish the cases in `hx' : x = p`.

Substitute `hx'` using the available equality. Simplify using `[Function.update_apply, hx, Equiv.swap_apply_left]`. Simplify using `[Function.update_apply, hx, hx', Equiv.swap_apply_of_ne_of_ne hx' hx]`. Introduce `b _ hb`. Simplify using `[Ne.symm hb]`.

Simplify using the standard rewrite rules.
-/
theorem pair_apply (p q : Q) (f : TV n ℂ Q) (I : Q → Fin n) :
    ∑ a, ∑ c, (eAt p a c : Module.End ℂ (TV n ℂ Q)) ((eAt q c a : Module.End ℂ (TV n ℂ Q)) f) I =
      if p = q then (n : ℂ) * f I else f (I ∘ Equiv.swap p q) := by
  simp only [eAt_applyC]
  rw [Finset.sum_eq_single (I p)]
  · by_cases hpq : p = q
    · subst hpq
      simp [Function.update_idem, Finset.card_univ]
    · have hqp : q ≠ p := Ne.symm hpq
      simp only [if_true, Function.update_of_ne hqp, hpq, if_false]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true]
      congr 1
      funext x
      by_cases hx : x = q
      · subst hx
        simp [Equiv.swap_apply_right]
      · by_cases hx' : x = p
        · subst hx'
          simp [Function.update_apply, hx, Equiv.swap_apply_left]
        · simp [Function.update_apply, hx, hx', Equiv.swap_apply_of_ne_of_ne hx' hx]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `f`. Use function extensionality and compare the values at `I`. Rewrite using `[tE_zero_apply]`. Simplify using `[LinearMap.sum_apply, Finset.sum_apply]`.
-/
private theorem tE_zero_eq_sum_eAt (S : Finset Q) (a c : Fin n) :
    (tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) a c : Module.End ℂ (TV n ℂ Q)) =
      ∑ p ∈ S, (eAt p a c : Module.End ℂ (TV n ℂ Q)) := by
  apply LinearMap.ext
  intro f
  funext I
  rw [tE_zero_apply]
  simp [LinearMap.sum_apply, Finset.sum_apply]

/- English proof (translation)
Repeatedly rewrite using `[tE_zero_eq_sum_eAt, Finset.sum_mul_sum]`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `f`. Use function extensionality and compare the values at `I`. Simplify using `only [LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply, Module.End.one_apply]`.

Rewrite using `[sum4]`. Repeatedly rewrite using `[pair_apply]`. Establish `hpm : ∀ p q : Q, (pm (Equiv.swap p q) : Module.End ℂ (TV n ℂ Q)) f I = f (I ∘ Equiv.swap p q)`. Introduce `p q`. Simplify using `[pm]`.

Repeatedly rewrite using `[hpm]`. Establish `hsplit : ∀ p ∈ S, (∑ q ∈ S, if p = q then (n : ℂ) * f I else f (I ∘ Equiv.swap p q)) = (n : ℂ) * f I + ∑ q ∈ S.erase p, f (I ∘ Equiv.swap p q)`. Introduce `p hp`. Rewrite using `[← Finset.add_sum_erase S _ hp]`. Use `congr 1`.

Simplify using the standard rewrite rules. Use `Finset.sum_congr rfl fun q hq => ?_` and prove the remaining obligations. Rewrite using `[if_neg (Finset.ne_of_mem_erase hq).symm]`. Rewrite using `[Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]`. Simplify using `[Finset.sum_const, nsmul_eq_mul, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem cas_expand' (S : Finset Q) :
    (∑ a, ∑ c, tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) a c * tE S 0 c a : Module.End ℂ (TV n ℂ Q)) =
      ((n * S.card : ℕ) : ℂ) • (1 : Module.End ℂ (TV n ℂ Q)) +
        ∑ p ∈ S, ∑ q ∈ S.erase p, pm (Equiv.swap p q) := by
  simp_rw [tE_zero_eq_sum_eAt, Finset.sum_mul_sum]
  apply LinearMap.ext
  intro f
  funext I
  simp only [LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply, Module.End.one_apply]
  rw [sum4]
  simp_rw [pair_apply]
  have hpm : ∀ p q : Q, (pm (Equiv.swap p q) : Module.End ℂ (TV n ℂ Q)) f I = f (I ∘ Equiv.swap p q) := by
    intro p q
    simp [pm]
  simp_rw [hpm]
  have hsplit : ∀ p ∈ S, (∑ q ∈ S, if p = q then (n : ℂ) * f I else f (I ∘ Equiv.swap p q)) =
      (n : ℂ) * f I + ∑ q ∈ S.erase p, f (I ∘ Equiv.swap p q) := by
    intro p hp
    rw [← Finset.add_sum_erase S _ hp]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun q hq => ?_
      rw [if_neg (Finset.ne_of_mem_erase hq).symm]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  simp [Finset.sum_const, nsmul_eq_mul, smul_eq_mul]
  ring

end

end PositivityTheory.Rg.Cz
