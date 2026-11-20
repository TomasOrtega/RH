import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DvdPowZeroIff
open Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `L _ _ ϖ hϖ n n' x V a H d hd hdiv j`. Establish `hϖ0 : ϖ ≠ 0`. Introduce `h`. Rewrite `hϖ` using `[h, map_zero]`. Conclude with `WithZero.zero_ne_coe hϖ`.

Establish `hϖi : ϖ ∈ Formalism.UG.intL L` using `by show Valued.v ϖ ≤ 1`. Rewrite using `[hϖ, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]`. Evaluate the numerical expressions. Use `set c : Fin n → L := fun k => if h : 0 < a k then d ⟨k, h⟩ * ϖ ^ (a k - 1) else 0 with hc`. Establish `hcint : ∀ k, c k ∈ Formalism.UG.intL L`.

Introduce `k`. Simplify using `only [hc]`. Use `split_ifs`. Conclude with `mul_mem (hd _) (pow_mem hϖi _)`. Conclude with `zero_mem _`.

Establish `hsum : ϖ • c = ∑ i : {j : Fin n // 0 < a j}, d i • Pi.single (i : Fin n) (ϖ ^ a (i : Fin n))`. Use function extensionality and compare the values at `k`. Rewrite using `[Finset.sum_apply]`. Distinguish the cases in `hk : 0 < a k`. Rewrite using `[Finset.sum_eq_single ⟨k, hk⟩]`.

Take `⟨m, hm⟩ : ∃ m, a k = m + 1` from `Nat.exists_eq_succ_of_ne_zero hk.ne'`. Simplify using `[hc, hk, hm]`. Expand and normalize the polynomial expressions, which then agree. Introduce `b _ hb`. Establish `: k ≠ (b : Fin n)` using `fun h => hb (Subtype.ext h.symm)`.

Simplify using `[Pi.single_apply, this]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_eq_zero]`. Simplify using `[hc, hk]`. Introduce `i _`.

Establish `: k ≠ (i : Fin n)` using `fun h => hk (h ▸ i.2)`. Simplify using `[Pi.single_apply, this]`. Establish `hlin : ϖ • (x *ᵥ (V *ᵥ c)) = ∑ i : {j : Fin n // 0 < a j}, d i • (x *ᵥ (V *ᵥ Pi.single (i : Fin n) (ϖ ^ a (i : Fin n))))`. Rewrite using `[← Matrix.mulVec_smul, ← Matrix.mulVec_smul, hsum, Matrix.mulVec_sum, Matrix.mulVec_sum]`. Simplify using `[Matrix.mulVec_smul]`.

Establish `hw : ∀ r, (x *ᵥ (V *ᵥ c)) r ∈ Formalism.UG.intL L`. Introduce `r`. Take `⟨b, hb, hbe⟩` from `hdiv r`. Establish `h1` using `congrFun hlin r`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at h1`.

Rewrite `hbe` using `[← h1, pow_one]`. Rewrite using `[mul_left_cancel₀ hϖ0 hbe]`. Conclude with `hb`. Take `⟨b, hb, hbe⟩` from `(H c hcint).1 hw j`. Use `⟨b, hb, ?_⟩` and prove the remaining obligations.

Take `⟨m, hm⟩ : ∃ m, a j = m + 1` from `Nat.exists_eq_succ_of_ne_zero j.2.ne'`. Simplify using `only [hc, dif_pos j.2, hm, Nat.add_sub_cancel] at hbe`. Apply `mul_right_cancel₀ (pow_ne_zero m hϖ0)` to reduce the goal to its premises. Rewrite using `[hbe]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem columns_indepMod :
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (n n' : ℕ) (x : Matrix (Fin n') (Fin n) L) (V : Matrix (Fin n) (Fin n) L) (a : Fin n → ℕ),
    (∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
      ((∀ i, (x *ᵥ (V *ᵥ c)) i ∈ Formalism.UG.intL L) ↔ ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j))) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ (fun j : {j : Fin n // 0 < a j} => x *ᵥ (V *ᵥ Pi.single (j : Fin n) (ϖ ^ a (j : Fin n)))) := by
  intro L _ _ ϖ hϖ n n' x V a H d hd hdiv j
  classical
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  have hϖi : ϖ ∈ Formalism.UG.intL L := by
    show Valued.v ϖ ≤ 1
    rw [hϖ, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
    norm_num
  set c : Fin n → L := fun k => if h : 0 < a k then d ⟨k, h⟩ * ϖ ^ (a k - 1) else 0 with hc
  have hcint : ∀ k, c k ∈ Formalism.UG.intL L := by
    intro k; simp only [hc]; split_ifs
    · exact mul_mem (hd _) (pow_mem hϖi _)
    · exact zero_mem _
  have hsum : ϖ • c = ∑ i : {j : Fin n // 0 < a j}, d i • Pi.single (i : Fin n) (ϖ ^ a (i : Fin n)) := by
    funext k
    rw [Finset.sum_apply]
    by_cases hk : 0 < a k
    · rw [Finset.sum_eq_single ⟨k, hk⟩]
      · obtain ⟨m, hm⟩ : ∃ m, a k = m + 1 := Nat.exists_eq_succ_of_ne_zero hk.ne'
        simp [hc, hk, hm]; ring
      · intro b _ hb
        have : k ≠ (b : Fin n) := fun h => hb (Subtype.ext h.symm)
        simp [Pi.single_apply, this]
      · simp
    · rw [Finset.sum_eq_zero]
      · simp [hc, hk]
      · intro i _
        have : k ≠ (i : Fin n) := fun h => hk (h ▸ i.2)
        simp [Pi.single_apply, this]
  have hlin : ϖ • (x *ᵥ (V *ᵥ c)) = ∑ i : {j : Fin n // 0 < a j}, d i • (x *ᵥ (V *ᵥ Pi.single (i : Fin n) (ϖ ^ a (i : Fin n)))) := by
    rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, hsum, Matrix.mulVec_sum, Matrix.mulVec_sum]
    simp [Matrix.mulVec_smul]
  have hw : ∀ r, (x *ᵥ (V *ᵥ c)) r ∈ Formalism.UG.intL L := by
    intro r
    obtain ⟨b, hb, hbe⟩ := hdiv r
    have h1 := congrFun hlin r
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at h1
    rw [← h1, pow_one] at hbe
    rw [mul_left_cancel₀ hϖ0 hbe]; exact hb
  obtain ⟨b, hb, hbe⟩ := (H c hcint).1 hw j
  refine ⟨b, hb, ?_⟩
  obtain ⟨m, hm⟩ : ∃ m, a j = m + 1 := Nat.exists_eq_succ_of_ne_zero j.2.ne'
  simp only [hc, dif_pos j.2, hm, Nat.add_sub_cancel] at hbe
  apply mul_right_cancel₀ (pow_ne_zero m hϖ0)
  rw [hbe]; ring

end GlobalTheory
