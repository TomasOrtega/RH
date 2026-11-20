import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightDerivativeRulePsi

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

section poly

variable {A : Type} [Ring A] [Algebra ℂ A]

def PolyLe (t : ℕ) (f : ℂ → A) : Prop :=
  ∃ C : Fin t → A, ∀ u, f u = ∑ l : Fin t, algebraMap ℂ A (u ^ (l : ℕ)) * C l

/- English proof (translation)
Take `⟨C, hC⟩` from `hf`. Conclude with `⟨C, fun u => by rw [← h u]; exact hC u⟩`.
-/
theorem pl_congr {t : ℕ} {f g : ℂ → A} (h : ∀ u, f u = g u) (hf : PolyLe t f) : PolyLe t g := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, fun u => by rw [← h u]; exact hC u⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, fun u => by simp⟩`.
-/
theorem pl_zero (t : ℕ) : PolyLe t (fun _ => (0 : A)) := ⟨0, fun u => by simp⟩

/- English proof (translation)
Take `⟨C, hC⟩` from `hf`. Take `⟨D, hD⟩` from `hg`. Use `⟨C + D, fun u => ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hC, hD, ← Finset.sum_add_distrib]`.

Simplify using `only [Pi.add_apply, mul_add]`.
-/
theorem pl_add {t : ℕ} {f g : ℂ → A} (hf : PolyLe t f) (hg : PolyLe t g) : PolyLe t (fun u => f u + g u) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨C + D, fun u => ?_⟩
  dsimp only
  rw [hC, hD, ← Finset.sum_add_distrib]
  simp only [Pi.add_apply, mul_add]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact pl_congr (fun u => by simp) (pl_zero t)`. Consider the case `insert i s hi ih`. Conclude with `pl_congr (fun u => by simp [Finset.sum_insert hi]) (pl_add (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj)))`.
-/
theorem pl_sum {t : ℕ} {ι : Type} (s : Finset ι) (f : ι → ℂ → A) (hf : ∀ i ∈ s, PolyLe t (f i)) :
    PolyLe t (fun u => ∑ i ∈ s, f i u) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact pl_congr (fun u => by simp) (pl_zero t)
  | insert i s hi ih =>
    exact pl_congr (fun u => by simp [Finset.sum_insert hi])
      (pl_add (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/- English proof (translation)
Take `⟨C, hC⟩` from `hf`. Use `⟨fun l => c * C l, fun u => ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hC, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun l _ => Algebra.left_comm _ _ _`.
-/
theorem pl_lmul {t : ℕ} {f : ℂ → A} (c : A) (hf : PolyLe t f) : PolyLe t (fun u => c * f u) := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨fun l => c * C l, fun u => ?_⟩
  dsimp only
  rw [hC, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => Algebra.left_comm _ _ _

/- English proof (translation)
Take `⟨C, hC⟩` from `hf`. Use `⟨fun l => C l * e, fun u => ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hC, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun l _ => mul_assoc _ _ _`.
-/
theorem pl_rmul {t : ℕ} {f : ℂ → A} (e : A) (hf : PolyLe t f) : PolyLe t (fun u => f u * e) := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨fun l => C l * e, fun u => ?_⟩
  dsimp only
  rw [hC, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => mul_assoc _ _ _

/- English proof (translation)
Take `⟨C, hC⟩` from `hf`. Use `⟨Fin.snoc (α := fun _ => A) C 0, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[hC, Fin.sum_univ_castSucc]`. Simplify using `[Fin.snoc_castSucc, Fin.snoc_last]`.
-/
theorem pl_mono {t : ℕ} {f : ℂ → A} (hf : PolyLe t f) : PolyLe (t + 1) f := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨Fin.snoc (α := fun _ => A) C 0, fun u => ?_⟩
  rw [hC, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/- English proof (translation)
Take `⟨C, hC⟩` from `hf`. Use `⟨Fin.cons (α := fun _ => A) 0 C, fun u => ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hC, Fin.sum_univ_succ, Finset.sum_mul]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add, Fin.val_succ]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, ← Algebra.commutes, ← mul_assoc, ← map_mul, pow_succ]`.
-/
theorem pl_mulu {t : ℕ} {f : ℂ → A} (hf : PolyLe t f) : PolyLe (t + 1) (fun u => f u * algebraMap ℂ A u) := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨Fin.cons (α := fun _ => A) 0 C, fun u => ?_⟩
  dsimp only
  rw [hC, Fin.sum_univ_succ, Finset.sum_mul]
  simp only [Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add, Fin.val_succ]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_assoc, ← Algebra.commutes, ← mul_assoc, ← map_mul, pow_succ]

/- English proof (translation)
Use `⟨Fin.snoc (α := fun _ => A) 0 x, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `[Fin.snoc_castSucc, Fin.snoc_last]`.
-/
theorem pl_mono_const (t : ℕ) (x : A) : PolyLe (t + 1) (fun u => algebraMap ℂ A (u ^ t) * x) := by
  refine ⟨Fin.snoc (α := fun _ => A) 0 x, fun u => ?_⟩
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/- English proof (translation)
Introduce `t`. Proceed by induction on `t with`. Consider the case `zero`. Introduce `c δ F`. Conclude with `⟨Fin.elim0, fun u => by simp⟩`.

Consider the case `succ t ih`. Introduce `c δ F`. Take `⟨C, hC⟩` from `ih (fun k => c k.succ) (fun k => δ k.succ) (fun k => F k.succ)`. Set `Q : ℂ → A` to `fun u => ∑ l : Fin t, algebraMap ℂ A (u ^ (l : ℕ)) * C l`. Establish `hQpl : PolyLe t Q` using `⟨C, fun u => rfl⟩`.

Establish `hR : ∀ u, (List.ofFn fun k : Fin t => algebraMap ℂ A ((u + c k.succ) * δ k.succ) + F k.succ).prod = algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ) + Q u`. Introduce `u`. Use `show _ = _ + ∑ l : Fin t, algebraMap ℂ A (u ^ (l : ℕ)) * C l`. Establish `h` using `hC u`. Simplify using `only at h`.

Rewrite using `[← h]`. Normalize the expressions using the abelian group laws. Use `pl_congr (f := fun u => algebraMap ℂ A (δ 0) * (Q u * algebraMap ℂ A u) + ((algebraMap ℂ A (c 0 * δ 0) + F 0) * Q u + algebraMap ℂ A (u ^ t) * ((algebraMap ℂ A (c 0 * δ 0) + F 0) * algebraMap ℂ A (∏ k : Fin t, δ k.succ)))) ?_ (pl_add (pl_lmul _ (pl_mulu hQpl)) (pl_add (pl_mono (p …` and prove the remaining obligations. Introduce `u`. Simplify using `only [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]`.

Rewrite using `[hR u]`. Establish `e1 : algebraMap ℂ A (u * δ 0) * algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ) = algebraMap ℂ A (u ^ (t + 1) * (δ 0 * ∏ k : Fin t, δ k.succ))`. Rewrite using `[← map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `e2 : algebraMap ℂ A (u * δ 0) * Q u = algebraMap ℂ A (δ 0) * (Q u * algebraMap ℂ A u)`. Rewrite using `[← Algebra.commutes, ← mul_assoc, ← map_mul, mul_comm (δ 0) u]`. Establish `e3 : (algebraMap ℂ A (c 0 * δ 0) + F 0) * algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ) = algebraMap ℂ A (u ^ t) * ((algebraMap ℂ A (c 0 * δ 0) + F 0) * algebraMap ℂ A (∏ k : Fin t, δ k.succ))`. Rewrite using `[map_mul (algebraMap ℂ A) (u ^ t), Algebra.left_comm]`. Rewrite using `[add_mul u (c 0) (δ 0), map_add, add_assoc, mul_add (algebraMap ℂ A (u * δ 0) + (algebraMap ℂ A (c 0 * δ 0) + F 0)), add_mul (algebraMap ℂ A (u * δ 0)) _ (algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ)), add_mul (algebraMap ℂ A (u * δ 0)) _ (Q u), e1, e2, e3]`.

Normalize the expressions using the abelian group laws.
-/
theorem prod_poly : ∀ (t : ℕ) (c δ : Fin t → ℂ) (F : Fin t → A),
    PolyLe t (fun u => (List.ofFn fun k => algebraMap ℂ A ((u + c k) * δ k) + F k).prod -
      algebraMap ℂ A (u ^ t * ∏ k, δ k)) := by
  intro t
  induction t with
  | zero =>
    intro c δ F
    exact ⟨Fin.elim0, fun u => by simp⟩
  | succ t ih =>
    intro c δ F
    obtain ⟨C, hC⟩ := ih (fun k => c k.succ) (fun k => δ k.succ) (fun k => F k.succ)
    let Q : ℂ → A := fun u => ∑ l : Fin t, algebraMap ℂ A (u ^ (l : ℕ)) * C l
    have hQpl : PolyLe t Q := ⟨C, fun u => rfl⟩
    have hR : ∀ u, (List.ofFn fun k : Fin t => algebraMap ℂ A ((u + c k.succ) * δ k.succ) + F k.succ).prod =
        algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ) + Q u := by
      intro u
      show _ = _ + ∑ l : Fin t, algebraMap ℂ A (u ^ (l : ℕ)) * C l
      have h := hC u
      dsimp only at h
      rw [← h]
      abel
    refine pl_congr (f := fun u => algebraMap ℂ A (δ 0) * (Q u * algebraMap ℂ A u) +
        ((algebraMap ℂ A (c 0 * δ 0) + F 0) * Q u + algebraMap ℂ A (u ^ t) *
          ((algebraMap ℂ A (c 0 * δ 0) + F 0) * algebraMap ℂ A (∏ k : Fin t, δ k.succ)))) ?_
      (pl_add (pl_lmul _ (pl_mulu hQpl)) (pl_add (pl_mono (pl_lmul _ hQpl)) (pl_mono_const t _)))
    intro u
    simp only [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    rw [hR u]
    have e1 : algebraMap ℂ A (u * δ 0) * algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ) =
        algebraMap ℂ A (u ^ (t + 1) * (δ 0 * ∏ k : Fin t, δ k.succ)) := by
      rw [← map_mul]
      congr 1
      ring
    have e2 : algebraMap ℂ A (u * δ 0) * Q u = algebraMap ℂ A (δ 0) * (Q u * algebraMap ℂ A u) := by
      rw [← Algebra.commutes, ← mul_assoc, ← map_mul, mul_comm (δ 0) u]
    have e3 : (algebraMap ℂ A (c 0 * δ 0) + F 0) * algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ) =
        algebraMap ℂ A (u ^ t) * ((algebraMap ℂ A (c 0 * δ 0) + F 0) *
          algebraMap ℂ A (∏ k : Fin t, δ k.succ)) := by
      rw [map_mul (algebraMap ℂ A) (u ^ t), Algebra.left_comm]
    rw [add_mul u (c 0) (δ 0), map_add, add_assoc,
      mul_add (algebraMap ℂ A (u * δ 0) + (algebraMap ℂ A (c 0 * δ 0) + F 0)),
      add_mul (algebraMap ℂ A (u * δ 0)) _ (algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ)),
      add_mul (algebraMap ℂ A (u * δ 0)) _ (Q u), e1, e2, e3]
    abel

/- English proof (translation)
Use `pl_congr (f := fun u => ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : A) * ((List.ofFn fun k : Fin t => algebraMap ℂ A ((u + (s0 - (k : ℂ))) * (if a (σ k) = b k then (1 : ℂ) else 0)) + E (a (σ k)) (b k)).prod - algebraMap ℂ A (u ^ t * ∏ k, (if a (σ k) = b k then (1 : ℂ) el …` and prove the remaining obligations. Introduce `u`. Establish `hT : ∀ (σ : Equiv.Perm (Fin t)) (k : Fin t), Tm E (u + s0 - (k : ℂ)) (a (σ k)) (b k) = algebraMap ℂ A ((u + (s0 - (k : ℂ))) * (if a (σ k) = b k then (1 : ℂ) else 0)) + E (a (σ k)) (b k)`. Introduce `σ k`. Unfold `Tm`.

Apply the tactic sequence `split_ifs <;> simp [add_sub_assoc]`. Simplify using `only [mul_sub]`. Rewrite using `[Finset.sum_sub_distrib]`. Use `congr 1`. Unfold `qminor`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Simplify using `only [hT]`. Rewrite using `[Finset.mul_sum, map_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm (u ^ t) (((Equiv.Perm.sign σ : ℤ) : ℂ)), map_mul (algebraMap ℂ A) (((Equiv.Perm.sign σ : ℤ) : ℂ)), map_intCast]`.
-/
theorem qminor_poly {n t : ℕ} (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (s0 : ℂ) :
    PolyLe t (fun u => qminor E a b (u + s0) - algebraMap ℂ A (u ^ t *
      ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if a (σ k) = b k then (1 : ℂ) else 0))) := by
  classical
  refine pl_congr (f := fun u => ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : A) *
      ((List.ofFn fun k : Fin t => algebraMap ℂ A ((u + (s0 - (k : ℂ))) *
          (if a (σ k) = b k then (1 : ℂ) else 0)) + E (a (σ k)) (b k)).prod -
        algebraMap ℂ A (u ^ t * ∏ k, (if a (σ k) = b k then (1 : ℂ) else 0)))) ?_
    (pl_sum _ _ fun σ _ => pl_lmul _ (prod_poly t _ _ _))
  intro u
  have hT : ∀ (σ : Equiv.Perm (Fin t)) (k : Fin t), Tm E (u + s0 - (k : ℂ)) (a (σ k)) (b k) =
      algebraMap ℂ A ((u + (s0 - (k : ℂ))) * (if a (σ k) = b k then (1 : ℂ) else 0)) + E (a (σ k)) (b k) := by
    intro σ k
    unfold Tm
    split_ifs <;> simp [add_sub_assoc]
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · unfold qminor
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [hT]
  · rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [mul_left_comm (u ^ t) (((Equiv.Perm.sign σ : ℤ) : ℂ)),
      map_mul (algebraMap ℂ A) (((Equiv.Perm.sign σ : ℤ) : ℂ)), map_intCast]

end poly

end Formalism.FourierDecayAlt.P.SignAntidiagonal
