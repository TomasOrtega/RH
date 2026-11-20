import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [conv, tens]`. Rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib]`.

Both sides reduce to the same expression.
-/
theorem conv_tens {ι G : Type} [Fintype ι] [Group G] [Fintype G] (a b : ι → G → ℂ) :
    conv (tens a) (tens b) = tens fun v => conv (a v) (b v) := by
  funext x
  simp only [conv, tens]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.prod_mul_distrib]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [conv, tens2]`. Rewrite using `[Fintype.sum_prod_type, Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations. Simplify using `only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem conv_tens2 {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] (a a' : G → ℂ) (b b' : G' → ℂ) :
    conv (tens2 a b) (tens2 a' b') = tens2 (conv a a') (conv b b') := by
  funext x
  simp only [conv, tens2]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
  ring

/- English proof (translation)
Introduce `ι G G' _ _ _ _ _`. Use `⟨conv_tens, fun a h => ⟨?_, fun x => ?_⟩, conv_tens2, fun a b ha hb => ⟨?_, fun x => ?_⟩, ?_, fun a a' b b' => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[conv_tens]`. Use `congr 1`. Use function extensionality and compare the values at `v`.

Conclude with `(h v).1`. Simplify using `only [tens, map_prod]`. Conclude with `Finset.prod_congr rfl fun v _ => (h v).2 (x v)`. Rewrite using `[conv_tens2, ha.1, hb.1]`. Simplify using `only [tens2, map_mul, Prod.fst_inv, Prod.snd_inv, ha.2, hb.2]`.

Use function extensionality and compare the values at `⟨x, y⟩`. Simplify using `only [tens2, dirac, Prod.mk_eq_one]`. Apply the tactic sequence `by_cases hx : x = 1 <;> by_cases hy : y = 1 <;> simp [hx, hy]`. Use function extensionality and compare the values at `x`. Simplify using `only [tens2, Pi.sub_apply, sub_mul]`.

Use function extensionality and compare the values at `x`. Simplify using `only [tens2, Pi.sub_apply, mul_sub]`.
-/
theorem tens_calculus : ∀ (ι G G' : Type) [Fintype ι] [Group G] [Fintype G] [Group G'] [Fintype G'], (∀ a b : ι → G → ℂ, conv (tens a) (tens b) = tens fun v => conv (a v) (b v)) ∧ (∀ a : ι → G → ℂ, (∀ v, IsProj (a v)) → IsProj (tens a)) ∧ (∀ (a a' : G → ℂ) (b b' : G' → ℂ), conv (tens2 a b) (tens2 a' b') = tens2 (conv a a') (conv b b')) ∧ (∀ (a : G → ℂ) (b : G' → ℂ), IsProj a → IsProj b → IsProj (tens2 a b)) ∧ tens2 (dirac : G → ℂ) (dirac : G' → ℂ) = dirac ∧ ∀ (a a' : G → ℂ) (b b' : G' → ℂ), tens2 (a - a') b = tens2 a b - tens2 a' b ∧ tens2 a (b - b') = tens2 a b - tens2 a b' := by
  intro ι G G' _ _ _ _ _
  refine ⟨conv_tens, fun a h => ⟨?_, fun x => ?_⟩, conv_tens2, fun a b ha hb => ⟨?_, fun x => ?_⟩, ?_,
    fun a a' b b' => ⟨?_, ?_⟩⟩
  · rw [conv_tens]
    congr 1
    funext v
    exact (h v).1
  · simp only [tens, map_prod]
    exact Finset.prod_congr rfl fun v _ => (h v).2 (x v)
  · rw [conv_tens2, ha.1, hb.1]
  · simp only [tens2, map_mul, Prod.fst_inv, Prod.snd_inv, ha.2, hb.2]
  · funext ⟨x, y⟩
    simp only [tens2, dirac, Prod.mk_eq_one]
    by_cases hx : x = 1 <;> by_cases hy : y = 1 <;> simp [hx, hy]
  · funext x
    simp only [tens2, Pi.sub_apply, sub_mul]
  · funext x
    simp only [tens2, Pi.sub_apply, mul_sub]

end GlobalTheory.BadShare
