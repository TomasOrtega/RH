import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

/- English proof (translation)
Introduce `ι M _ _ _ _ s F α β x y hq hs ht hf a`. Establish `hall : ∀ c, ∑ b, F c b (y b) = x • y c`. Introduce `c`. Consider the cases of `hc : s c`. Rewrite using `[hf c hc, hs c hc, smul_zero]`.

Conclude with `ht c hc`. Consider the cases of `ha : s a`. Rewrite using `[hs a ha, smul_zero]`. Establish `key : ∑ b, qop F α β a b (y b) = 0` using `by simp [hq]`. Establish `pt : ∀ b, qop F α β a b (y b) = ∑ c, F a c (F c b (y b)) - α • F a b (y b) - (if a = b then β • y b else 0)`.

Introduce `b`. Simplify using `only [qop, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `expand : ∑ b, qop F α β a b (y b) = ∑ c, F a c (∑ b, F c b (y b)) - α • ∑ b, F a b (y b) - β • y a`. Rewrite using `[Finset.sum_congr rfl (fun b _ => pt b), Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_comm, Finset.sum_ite_eq, ← Finset.smul_sum]`.

Simplify using `[map_sum]`. Rewrite `key` using `[expand, ht a ha]`. Simplify using `only [hall, map_smul] at key`. Rewrite `key` using `[← Finset.smul_sum, ht a ha]`. Rewrite using `[sub_smul, sub_smul, pow_two, mul_smul, mul_smul]`.

Conclude with `key`.
-/
theorem qop_quadratic_on_eigenvector : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (α β x : ℂ) (y : ι → M), (∀ a b, qop F α β a b = 0) → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = x • y a) → (∀ j, s j = false → ∑ b, F j b (y b) = 0) → ∀ a, (x ^ 2 - α * x - β) • y a = 0 := by
  intro ι M _ _ _ _ s F α β x y hq hs ht hf a
  have hall : ∀ c, ∑ b, F c b (y b) = x • y c := by
    intro c
    cases hc : s c
    · rw [hf c hc, hs c hc, smul_zero]
    · exact ht c hc
  cases ha : s a
  · rw [hs a ha, smul_zero]
  · have key : ∑ b, qop F α β a b (y b) = 0 := by simp [hq]
    have pt : ∀ b, qop F α β a b (y b)
        = ∑ c, F a c (F c b (y b)) - α • F a b (y b) - (if a = b then β • y b else 0) := by
      intro b
      simp only [qop, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply]
      split_ifs <;> simp
    have expand : ∑ b, qop F α β a b (y b)
        = ∑ c, F a c (∑ b, F c b (y b)) - α • ∑ b, F a b (y b) - β • y a := by
      rw [Finset.sum_congr rfl (fun b _ => pt b), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_comm, Finset.sum_ite_eq, ← Finset.smul_sum]
      simp [map_sum]
    rw [expand, ht a ha] at key
    simp only [hall, map_smul] at key
    rw [← Finset.smul_sum, ht a ha] at key
    rw [sub_smul, sub_smul, pow_two, mul_smul, mul_smul]
    exact key

end GlobalTheory.HoweR
