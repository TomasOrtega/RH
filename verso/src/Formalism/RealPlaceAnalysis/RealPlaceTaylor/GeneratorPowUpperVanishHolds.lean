import Formalism.RealPlaceAnalysis.StatementB

open Finset

noncomputable section

namespace Formalism.REAL

/- English proof (translation)
Introduce `A _ n E hE k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `a b c d`. Simplify using `only [epow, @eq_comm _ b c, @eq_comm _ a d]`.

Apply the tactic sequence `have hl : E c d * (if a = b then (1 : A) else 0) - (if a = b then (1 : A) else 0) * E c d = 0 := by split_ifs <;> simp`. Rewrite using `[hl]`. Apply the tactic sequence `by_cases h2 : d = a <;> by_cases h3 : c = b <;> simp [h2, h3]`. Consider the case `succ k ih`. Introduce `a b c d`.

Simplify using `only [epow]`. Rewrite using `[Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]`. Establish `step : ∀ e, E c d * (epow E k a e * E e b) - epow E k a e * E e b * E c d = ((if d = a then epow E k c e else 0) - (if e = c then epow E k a d else 0)) * E e b + epow E k a e * ((if d = e then E c b else 0) - (if b = c then E e d else 0))`. Introduce `e`. Rewrite using `[← ih a e c d, ← hE c d e b]`.

Use `noncomm_ring`. Simplify using `only [step]`. Apply the tactic sequence `by_cases hda : d = a <;> by_cases hbc : b = c <;>`. Apply the tactic sequence `simp [hda, hbc, Finset.sum_add_distrib, Finset.sum_sub_distrib, sub_mul, mul_sub, ite_mul, mul_ite] <;> abel`.
-/
theorem generatorPowCovariance_holds : EpowCov := by
  intro A _ n E hE k
  induction k with
  | zero =>
    intro a b c d
    simp only [epow, @eq_comm _ b c, @eq_comm _ a d]
    have hl : E c d * (if a = b then (1 : A) else 0) - (if a = b then (1 : A) else 0) * E c d = 0 := by
      split_ifs <;> simp
    rw [hl]
    by_cases h2 : d = a <;> by_cases h3 : c = b <;> simp [h2, h3]
  | succ k ih =>
    intro a b c d
    simp only [epow]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    have step : ∀ e, E c d * (epow E k a e * E e b) - epow E k a e * E e b * E c d =
        ((if d = a then epow E k c e else 0) - (if e = c then epow E k a d else 0)) * E e b +
        epow E k a e * ((if d = e then E c b else 0) - (if b = c then E e d else 0)) := by
      intro e
      rw [← ih a e c d, ← hE c d e b]
      noncomm_ring
    simp only [step]
    by_cases hda : d = a <;> by_cases hbc : b = c <;>
      simp [hda, hbc, Finset.sum_add_distrib, Finset.sum_sub_distrib, sub_mul, mul_sub, ite_mul, mul_ite] <;> abel

/- English proof (translation)
Introduce `A _ n E hE k c d`. Establish `hc` using `generatorPowCovariance_holds A n E hE k`. Unfold `etr`. Rewrite using `[Finset.sum_mul, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]`. Establish `h1 : ∀ a, epow E k a a * E c d - E c d * epow E k a a = -((if d = a then epow E k c a else 0) - (if a = c then epow E k a d else 0))`.

Introduce `a`. Rewrite using `[← hc a a c d]`. Normalize the expressions using the abelian group laws. Simplify using `only [h1, Finset.sum_neg_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self, neg_zero]`.
-/
theorem generatorTraceCentral_holds : EtrCentral := by
  intro A _ n E hE k c d
  have hc := generatorPowCovariance_holds A n E hE k
  unfold etr
  rw [Finset.sum_mul, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  have h1 : ∀ a, epow E k a a * E c d - E c d * epow E k a a =
      -((if d = a then epow E k c a else 0) - (if a = c then epow E k a d else 0)) := by
    intro a
    rw [← hc a a c d]
    abel
  simp only [h1, Finset.sum_neg_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, sub_self, neg_zero]

/- English proof (translation)
Introduce `V _ _ n E ν v hE hv k`. Take `⟨hd, hu⟩` from `hv`. Proceed by induction on `k with`. Consider the case `zero => intro a b hab`. Simplify using `[epow, ne_of_lt hab]`.

Consider the case `succ k ih`. Introduce `a b hab`. Simplify using `only [epow, LinearMap.sum_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `c _`.

Rewrite using `[Module.End.mul_apply]`. Break down `lt_trichotomy c b with hcb | hcb | hcb` into its components or cases. Rewrite using `[hu c b hcb, map_zero]`. Substitute `hcb` using the available equality. Rewrite using `[hd c, map_smul, ih a c hab, smul_zero]`.

Establish `hcov` using `generatorPowCovariance_holds (Module.End ℂ V) n E hE k a c c b`. Rewrite `hcov` using `[if_neg (ne_of_gt hab), if_pos rfl, zero_sub]`. Establish `h2 : epow E k a c * E c b = E c b * epow E k a c + epow E k a b`. Rewrite using `[← neg_neg (epow E k a b), ← hcov]`. Normalize the expressions using the abelian group laws.

Establish `h3 : (epow E k a c) (E c b v) = (epow E k a c * E c b) v` using `rfl`. Rewrite using `[h3, h2, LinearMap.add_apply, Module.End.mul_apply, ih a c (hab.trans hcb), map_zero, ih a b hab, zero_add]`.
-/
theorem generatorPowUpperVanish_holds : UpperKill := by
  intro V _ _ n E ν v hE hv k
  obtain ⟨hd, hu⟩ := hv
  induction k with
  | zero => intro a b hab; simp [epow, ne_of_lt hab]
  | succ k ih =>
    intro a b hab
    simp only [epow, LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro c _
    rw [Module.End.mul_apply]
    rcases lt_trichotomy c b with hcb | hcb | hcb
    · rw [hu c b hcb, map_zero]
    · subst hcb
      rw [hd c, map_smul, ih a c hab, smul_zero]
    · have hcov := generatorPowCovariance_holds (Module.End ℂ V) n E hE k a c c b
      rw [if_neg (ne_of_gt hab), if_pos rfl, zero_sub] at hcov
      have h2 : epow E k a c * E c b = E c b * epow E k a c + epow E k a b := by
        rw [← neg_neg (epow E k a b), ← hcov]
        abel
      have h3 : (epow E k a c) (E c b v) = (epow E k a c * E c b) v := rfl
      rw [h3, h2, LinearMap.add_apply, Module.End.mul_apply, ih a c (hab.trans hcb), map_zero, ih a b hab,
        zero_add]

end Formalism.REAL
