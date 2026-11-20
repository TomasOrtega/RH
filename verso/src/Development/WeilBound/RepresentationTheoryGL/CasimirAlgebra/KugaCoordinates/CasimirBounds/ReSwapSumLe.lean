import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.KTypeData

open Finset Matrix

set_option linter.unusedSectionVars false

namespace PositivityTheory.Rg.Cz

section
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pm_apply' (σ : Equiv.Perm Q) (f : TV n ℂ Q) (I : Q → Fin n) :
    (pm σ : Module.End ℂ (TV n ℂ Q)) f I = f (I ∘ σ) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pm_pm (σ τ : Equiv.Perm Q) (f : TV n ℂ Q) :
    (pm σ : Module.End ℂ (TV n ℂ Q)) (pm τ f) = pm (σ * τ) f := rfl

/- English proof (translation)
Set `e : (Q → Fin n) ≃ (Q → Fin n)` to `{ toFun := fun I => I ∘ Equiv.swap a c, invFun := fun I => I ∘ Equiv.swap a c, left_inv := fun I => by funext x; simp, right_inv := fun I => by funext x; simp }`. Simplify using `only [dotProduct, Pi.star_apply, pm_apply']`. Use `Fintype.sum_equiv e _ _ fun I => ?_` and prove the remaining obligations. Establish `: (I ∘ Equiv.swap a c) ∘ Equiv.swap a c = I` using `by funext x; simp`. Simplify using `[e, this]`.
-/
theorem dot_pm_swap (a c : Q) (u v : TV n ℂ Q) :
    star u ⬝ᵥ (pm (Equiv.swap a c) : Module.End ℂ (TV n ℂ Q)) v =
      star ((pm (Equiv.swap a c) : Module.End ℂ (TV n ℂ Q)) u) ⬝ᵥ v := by
  let e : (Q → Fin n) ≃ (Q → Fin n) :=
    { toFun := fun I => I ∘ Equiv.swap a c, invFun := fun I => I ∘ Equiv.swap a c,
      left_inv := fun I => by funext x; simp, right_inv := fun I => by funext x; simp }
  simp only [dotProduct, Pi.star_apply, pm_apply']
  refine Fintype.sum_equiv e _ _ fun I => ?_
  have : (I ∘ Equiv.swap a c) ∘ Equiv.swap a c = I := by funext x; simp
  simp [e, this]

/- English proof (translation)
Use `set Y : Module.End ℂ (TV n ℂ Q) := ∑ q ∈ B, pm (Equiv.swap p q) with hY`. Establish `hYf : Y f = ∑ q ∈ B, pm (Equiv.swap p q) f` using `by simp [hY, LinearMap.sum_apply]`. Establish `hsa : ∀ u v : TV n ℂ Q, star u ⬝ᵥ Y v = star (Y u) ⬝ᵥ v`. Introduce `u v`. Simplify using `only [hY, LinearMap.sum_apply, dotProduct_sum, star_sum, sum_dotProduct, dot_pm_swap]`.

Establish `hq : ∀ q ∈ B, (pm (Equiv.swap p q) : Module.End ℂ (TV n ℂ Q)) (Y f) = f - Y f + pm (Equiv.swap p q) f`. Introduce `q hqB`. Establish `hpq : p ≠ q` using `fun h => hp (h ▸ hqB)`. Rewrite using `[hYf, ← Finset.add_sum_erase B _ hqB, map_add, map_sum, pm_pm, Equiv.swap_mul_self]`. Establish `: ∀ q' ∈ B.erase q, (pm (Equiv.swap p q) : Module.End ℂ (TV n ℂ Q)) (pm (Equiv.swap p q') f) = -(pm (Equiv.swap p q') f)`.

Introduce `q' hq'`. Take `⟨hne, hq'B⟩` from `Finset.mem_erase.mp hq'`. Establish `hpq' : p ≠ q'` using `fun h => hp (h ▸ hq'B)`. Establish `hperm : Equiv.swap p q * Equiv.swap p q' = Equiv.swap p q' * Equiv.swap q q'`. Use extensionality with `x`.

Simplify using `only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_def]`. Apply the tactic sequence `split_ifs <;> simp_all`. Rewrite using `[pm_pm, hperm, ← pm_pm, hf q hqB q' hq'B (Ne.symm hne), map_neg]`. Rewrite using `[Finset.sum_congr rfl this, Finset.sum_neg_distrib]`. Establish `h1 : (pm 1 : Module.End ℂ (TV n ℂ Q)) f = f` using `rfl`.

Rewrite using `[h1]`. Normalize the expressions using the abelian group laws. Establish `hYY : Y (Y f) = (B.card : ℂ) • f - (B.card : ℂ) • Y f + Y f` using `by conv_lhs => rw [hY, LinearMap.sum_apply]`. Rewrite using `[Finset.sum_congr rfl hq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const, ← hYf]`. Simplify using `[Nat.cast_smul_eq_nsmul]`.

Use `set g := f - Y f with hg`. Establish `hYg : Y g = -((B.card : ℂ) • g)`. Rewrite using `[hg, map_sub, hYY, smul_sub]`. Normalize the expressions using the abelian group laws. Establish `hgg : star g ⬝ᵥ g = (1 + (B.card : ℂ)) * (star f ⬝ᵥ g)` using `by conv_lhs => rw [hg]`.

Rewrite using `[star_sub, sub_dotProduct, ← hsa, ← hg, hYg, dotProduct_neg, dotProduct_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hnn : 0 ≤ (star g ⬝ᵥ g).re`. Simplify using `only [dotProduct, Pi.star_apply, Complex.re_sum]`. Use `Finset.sum_nonneg fun I _ => ?_` and prove the remaining obligations.

Simplify using `only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]`. Use polynomial arithmetic with `[sq_nonneg (g I).re, sq_nonneg (g I).im]`. Establish `hre : (star g ⬝ᵥ g).re = (1 + (B.card : ℝ)) * (star f ⬝ᵥ g).re`. Rewrite using `[hgg]`. Simplify using `[Complex.mul_re]`.

Establish `hpos : 0 ≤ (star f ⬝ᵥ g).re`. Establish `h1 : (0 : ℝ) < 1 + (B.card : ℝ)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hfg : star f ⬝ᵥ g = star f ⬝ᵥ f - ∑ q ∈ B, star f ⬝ᵥ pm (Equiv.swap p q) f`. Rewrite using `[hg, dotProduct_sub, hYf, dotProduct_sum]`.

Rewrite `hpos` using `[hfg, Complex.sub_re]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem re_swapSum_le' (f : TV n ℂ Q) (B : Finset Q) (p : Q)
    (hp : p ∉ B) (hf : ∀ q ∈ B, ∀ q' ∈ B, q ≠ q' → pm (Equiv.swap q q') f = -f) :
    (∑ q ∈ B, star f ⬝ᵥ pm (Equiv.swap p q) f).re ≤ (star f ⬝ᵥ f).re := by
  set Y : Module.End ℂ (TV n ℂ Q) := ∑ q ∈ B, pm (Equiv.swap p q) with hY
  have hYf : Y f = ∑ q ∈ B, pm (Equiv.swap p q) f := by simp [hY, LinearMap.sum_apply]
  have hsa : ∀ u v : TV n ℂ Q, star u ⬝ᵥ Y v = star (Y u) ⬝ᵥ v := by
    intro u v
    simp only [hY, LinearMap.sum_apply, dotProduct_sum, star_sum, sum_dotProduct, dot_pm_swap]
  have hq : ∀ q ∈ B, (pm (Equiv.swap p q) : Module.End ℂ (TV n ℂ Q)) (Y f) =
      f - Y f + pm (Equiv.swap p q) f := by
    intro q hqB
    have hpq : p ≠ q := fun h => hp (h ▸ hqB)
    rw [hYf, ← Finset.add_sum_erase B _ hqB, map_add, map_sum, pm_pm, Equiv.swap_mul_self]
    have : ∀ q' ∈ B.erase q, (pm (Equiv.swap p q) : Module.End ℂ (TV n ℂ Q)) (pm (Equiv.swap p q') f) =
        -(pm (Equiv.swap p q') f) := by
      intro q' hq'
      obtain ⟨hne, hq'B⟩ := Finset.mem_erase.mp hq'
      have hpq' : p ≠ q' := fun h => hp (h ▸ hq'B)
      have hperm : Equiv.swap p q * Equiv.swap p q' = Equiv.swap p q' * Equiv.swap q q' := by
        ext x
        simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_def]
        split_ifs <;> simp_all
      rw [pm_pm, hperm, ← pm_pm, hf q hqB q' hq'B (Ne.symm hne), map_neg]
    rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib]
    have h1 : (pm 1 : Module.End ℂ (TV n ℂ Q)) f = f := rfl
    rw [h1]
    abel
  have hYY : Y (Y f) = (B.card : ℂ) • f - (B.card : ℂ) • Y f + Y f := by
    conv_lhs => rw [hY, LinearMap.sum_apply]
    rw [Finset.sum_congr rfl hq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.sum_const, ← hYf]
    simp [Nat.cast_smul_eq_nsmul]
  set g := f - Y f with hg
  have hYg : Y g = -((B.card : ℂ) • g) := by
    rw [hg, map_sub, hYY, smul_sub]
    abel
  have hgg : star g ⬝ᵥ g = (1 + (B.card : ℂ)) * (star f ⬝ᵥ g) := by
    conv_lhs => rw [hg]
    rw [star_sub, sub_dotProduct, ← hsa, ← hg, hYg, dotProduct_neg, dotProduct_smul, smul_eq_mul]
    ring
  have hnn : 0 ≤ (star g ⬝ᵥ g).re := by
    simp only [dotProduct, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_nonneg fun I _ => ?_
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    nlinarith [sq_nonneg (g I).re, sq_nonneg (g I).im]
  have hre : (star g ⬝ᵥ g).re = (1 + (B.card : ℝ)) * (star f ⬝ᵥ g).re := by
    rw [hgg]
    simp [Complex.mul_re]
  have hpos : 0 ≤ (star f ⬝ᵥ g).re := by
    have h1 : (0 : ℝ) < 1 + (B.card : ℝ) := by positivity
    nlinarith
  have hfg : star f ⬝ᵥ g = star f ⬝ᵥ f - ∑ q ∈ B, star f ⬝ᵥ pm (Equiv.swap p q) f := by
    rw [hg, dotProduct_sub, hYf, dotProduct_sum]
  rw [hfg, Complex.sub_re] at hpos
  linarith

end

end PositivityTheory.Rg.Cz
