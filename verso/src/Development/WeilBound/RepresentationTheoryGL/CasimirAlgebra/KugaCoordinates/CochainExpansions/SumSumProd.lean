import Mathlib

noncomputable section

open Complex

namespace PositivityTheory.Rg.Cz.Coch

variable {H V : Type*} [AddCommGroup V] [Module ℂ V]

def cEv {N : ℕ} (F : (Fin N → H) → V) (A B : Fin N → H) : V :=
  ∑ S : Fin N → Bool, (∏ k, if S k then (1 : ℂ) else -I) • F (fun k => if S k then A k else B k)

/- English proof (translation)
Simplify using `[cEv]`.
-/
theorem cEv_zero {N : ℕ} (A B : Fin N → H) : cEv (fun _ => (0 : V)) A B = 0 := by
  simp [cEv]

/- English proof (translation)
Unfold `cEv`. Simplify using `only [Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun S _ => ?_` and prove the remaining obligations. Conclude with `smul_comm _ _ _`.
-/
theorem cEv_sum {N : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℤ) (F : ι → (Fin N → H) → V) (A B : Fin N → H) :
    cEv (fun v => ∑ i ∈ s, c i • F i v) A B = ∑ i ∈ s, c i • cEv (F i) A B := by
  unfold cEv
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun S _ => ?_
  exact smul_comm _ _ _

/- English proof (translation)
Unfold `cEv`. Use `Fintype.sum_equiv ⟨fun S => S ∘ σ, fun T => T ∘ σ.symm, fun S => by funext x; simp, fun T => by funext x; simp⟩ _ _ fun S => ?_` and prove the remaining obligations. Simplify using `only [Equiv.coe_fn_mk, Function.comp_apply]`. Use `congr 1`. Conclude with `(Equiv.prod_comp σ (fun k => if S k then (1 : ℂ) else -I)).symm`.
-/
theorem cEv_perm {N : ℕ} (F : (Fin N → H) → V) (σ : Equiv.Perm (Fin N)) (A B : Fin N → H) :
    cEv (fun v => F (fun i => v (σ i))) A B = cEv F (fun i => A (σ i)) (fun i => B (σ i)) := by
  unfold cEv
  refine Fintype.sum_equiv ⟨fun S => S ∘ σ, fun T => T ∘ σ.symm, fun S => by funext x; simp,
    fun T => by funext x; simp⟩ _ _ fun S => ?_
  simp only [Equiv.coe_fn_mk, Function.comp_apply]
  congr 1
  exact (Equiv.prod_comp σ (fun k => if S k then (1 : ℂ) else -I)).symm

/- English proof (translation)
Unfold `cEv`. Simplify using `only [Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul]`. Use `congr 1`. Repeatedly rewrite using `[← Finset.prod_mul_distrib]`. Establish `e : ∀ k, f x y k (A k) - I * f x y k (B k) = ∑ b : Bool, (if b then (1 : ℂ) else -I) * f x y k (if b then A k else B k)`.

Introduce `k`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e]`. Rewrite using `[Fintype.prod_sum]`.
-/
theorem cEv_prod2 {N : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ → Fin N → H → ℂ) (c : ι → κ → V)
    (A B : Fin N → H) :
    cEv (fun v => ∑ x, ∑ y, (∏ k, f x y k (v k)) • c x y) A B =
      ∑ x, ∑ y, (∏ k, (f x y k (A k) - I * f x y k (B k))) • c x y := by
  unfold cEv
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp_rw [← Finset.prod_mul_distrib]
  have e : ∀ k, f x y k (A k) - I * f x y k (B k) =
      ∑ b : Bool, (if b then (1 : ℂ) else -I) * f x y k (if b then A k else B k) := by
    intro k; simp; ring
  simp_rw [e]
  rw [Fintype.prod_sum]

/- English proof (translation)
Rewrite using `[Fintype.prod_sum]`. Use `Finset.sum_congr rfl fun A _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.prod_sum]`.
-/
theorem sum_sum_prod {N : ℕ} {α β R : Type*} [Fintype α] [Fintype β] [CommSemiring R] (g : Fin N → α → β → R) :
    ∑ A : Fin N → α, ∑ B : Fin N → β, ∏ k, g k (A k) (B k) = ∏ k, ∑ a, ∑ b, g k a b := by
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Fintype.prod_sum]

end PositivityTheory.Rg.Cz.Coch

end
