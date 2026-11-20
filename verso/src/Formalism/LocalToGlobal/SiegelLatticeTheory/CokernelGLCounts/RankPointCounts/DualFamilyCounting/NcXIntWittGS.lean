import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXIntWittAlg

noncomputable section

namespace Formalism.L2.SG.Pf.NcX.IntWittAlg

open Matrix Formalism.UG

section GS

variable {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (J : Matrix (Fin n) (Fin n) K)

/- English proof (translation)
Assume the negation of the conclusion as `H`. Use `push Not at H`. Establish `hexp : ∀ r t : K, hform σ J (r • u + t • w) (r • u + t • w) = σ r * r * hform σ J u u + σ r * t * hform σ J u w + σ t * r * hform σ J w u + σ t * t * hform σ J w w`. Introduce `r t`. Simplify using `only [hform_add_left, hform_add_right, hform_smul_left, hform_smul_right]`.

Expand and normalize the polynomial expressions, which then agree. Use `set q := hform σ J u w with hq`. Use `set t : K := 2⁻¹ / q with htdef`. Establish `h1` using `H 1 0`. Establish `h2'` using `H 0 1`.

Establish `h3` using `H 1 t`. Rewrite `h1`, `h2'` using `[hexp, map_one, map_zero]`. Rewrite `h3` using `[hexp, map_one]`. Establish `ht : t * q = 2⁻¹` using `div_mul_cancel₀ _ huw`. Establish `hst : σ t * hform σ J w u = 2⁻¹`.

Rewrite using `[← hform_conj σ J hσ hJ u w, ← hq, ← map_mul, ht, map_inv₀, map_ofNat]`. Establish `hinv : (2 : K) * 2⁻¹ = 1` using `mul_inv_cancel₀ h2`. Conclude with `one_ne_zero (by linear_combination h3 - h1 - (σ t * t) * h2' - ht - hst - hinv : (1 : K) = 0)`.
-/
theorem exists_aniso (hσ : ∀ z, σ (σ z) = z) (hJ : IsHerm σ J) (h2 : (2 : K) ≠ 0) (u w : Fin n → K)
    (huw : hform σ J u w ≠ 0) : ∃ r t : K, hform σ J (r • u + t • w) (r • u + t • w) ≠ 0 := by
  by_contra H
  push Not at H
  have hexp : ∀ r t : K, hform σ J (r • u + t • w) (r • u + t • w) =
      σ r * r * hform σ J u u + σ r * t * hform σ J u w + σ t * r * hform σ J w u +
        σ t * t * hform σ J w w := by
    intro r t
    simp only [hform_add_left, hform_add_right, hform_smul_left, hform_smul_right]
    ring
  set q := hform σ J u w with hq
  set t : K := 2⁻¹ / q with htdef
  have h1 := H 1 0
  have h2' := H 0 1
  have h3 := H 1 t
  rw [hexp, map_one, map_zero] at h1 h2'
  rw [hexp, map_one] at h3
  have ht : t * q = 2⁻¹ := div_mul_cancel₀ _ huw
  have hst : σ t * hform σ J w u = 2⁻¹ := by
    rw [← hform_conj σ J hσ hJ u w, ← hq, ← map_mul, ht, map_inv₀, map_ofNat]
  have hinv : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  exact one_ne_zero (by linear_combination h3 - h1 - (σ t * t) * h2' - ht - hst - hinv : (1 : K) = 0)

end GS

/- English proof (translation)
Introduce `K _ σ hσ h2 n J hJ a X0 hT`. Establish `hconj` using `hform_conj σ J hσ hJ`. Set `W : Submodule K (Fin n → K)` to `Submodule.span K (Set.range X0)`. Set `comb : (Fin a → K) → (Fin n → K)` to `fun c => ∑ l, c l • X0 l`. Establish `hN : ∀ c : Fin a → K, (∀ j, hform σ J (X0 j) (comb c) = 0) → c = 0`.

Introduce `c hc`. Use `Matrix.eq_zero_of_mulVec_eq_zero hT ?_` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Establish `e : hform σ J (X0 j) (∑ l, c l • X0 l) = 0` using `hc j`. Rewrite `e` using `[hform_sum_right]`.

Simplify using `only [mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]`. Rewrite using `[← e]`. Conclude with `Finset.sum_congr rfl fun l _ => mul_comm _ _`. Establish `hcW : ∀ c, comb c ∈ W` using `fun c => W.sum_mem fun l _ => W.smul_mem _ (Submodule.subset_span ⟨l, rfl⟩)`. Establish `main : ∀ k ≤ a, ∃ Z : Fin k → Fin n → K, (∀ i, Z i ∈ W) ∧ (∀ i j, i ≠ j → hform σ J (Z i) (Z j) = 0) ∧ ∀ i, hform σ J (Z i) (Z i) ≠ 0`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro _`. Conclude with `⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩`. Consider the case `succ k ih`.

Introduce `hk`. Take `⟨Z, hZW, hZo, hZd⟩` from `ih (by omega)`. Set `f : (Fin a → K) →ₗ[K] (Fin k → K)` to `{ toFun := fun c i => hform σ J (Z i) (comb c) map_add' := by`. Introduce `c d`. Use function extensionality and compare the values at `i`.

Simplify using `only [comb, Pi.add_apply, add_smul, Finset.sum_add_distrib, hform_add_right]`. Use the proof step `map_smul' := by`. Introduce `r c`. Use function extensionality and compare the values at `i`. Simplify using `only [comb, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← smul_smul, ← Finset.smul_sum, hform_smul_right] }`.

Establish `hlt : Module.finrank K (Fin k → K) < Module.finrank K (Fin a → K)`. Simplify using `only [Module.finrank_fin_fun]`. Use linear arithmetic over natural numbers and integers. Take `⟨c, hc, hc0⟩` from `(Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt)`. Establish `hcZ : ∀ i, hform σ J (Z i) (comb c) = 0` using `fun i => congrFun (LinearMap.mem_ker.1 hc) i`.

Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, hform σ J (X0 j) (comb c) ≠ 0 := by`. Assume the negation of the conclusion as `H`. Use `push Not at H`. Conclude with `hc0 (hN c H)`. Set `w` to `X0 j - ∑ i, (hform σ J (Z i) (X0 j) / hform σ J (Z i) (Z i)) • Z i`.

Establish `hwZ : ∀ m, hform σ J (Z m) w = 0`. Introduce `m`. Simplify using `only [w, hform_sub_right, hform_sum_right]`. Rewrite using `[Finset.sum_eq_single m]`. Rewrite using `[div_mul_cancel₀ _ (hZd m), sub_self]`.

Introduce `i _ him`. Rewrite using `[hZo m i (Ne.symm him), mul_zero]`. Simplify using the standard rewrite rules. Establish `hwc : hform σ J w (comb c) ≠ 0`. Simplify using `only [w, hform_sub_left, hform_sum_left]`.

Rewrite using `[Finset.sum_eq_zero, sub_zero]`. Conclude with `hj`. Introduce `i _`. Rewrite using `[hcZ i, mul_zero]`. Establish `hwW : w ∈ W` using `W.sub_mem (Submodule.subset_span ⟨j, rfl⟩) (W.sum_mem fun i _ => W.smul_mem _ (hZW i))`.

Take `⟨r, t, hz⟩` from `exists_aniso σ J hσ hJ h2 w (comb c) hwc`. Use `set z := r • w + t • comb c with hzdef`. Establish `hzZ : ∀ m, hform σ J (Z m) z = 0`. Introduce `m`. Rewrite using `[hzdef, hform_add_right, hform_smul_right, hform_smul_right, hwZ, hcZ, mul_zero, mul_zero, add_zero]`.

Use `⟨Fin.snoc Z z, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Use `Fin.lastCases ?_ (fun i => ?_) i` and prove the remaining obligations. Rewrite using `[Fin.snoc_last]`. Conclude with `W.add_mem (W.smul_mem _ hwW) (W.smul_mem _ (hcW c))`.

Rewrite using `[Fin.snoc_castSucc]`. Conclude with `hZW i`. Introduce `i j`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j`. Introduce `h`.

Conclude with `absurd rfl h`. Introduce `_`. Rewrite using `[Fin.snoc_last, Fin.snoc_castSucc, ← hconj, hzZ, map_zero]`. Introduce `_`. Rewrite using `[Fin.snoc_last, Fin.snoc_castSucc]`.

Conclude with `hzZ i`. Introduce `hij`. Rewrite using `[Fin.snoc_castSucc, Fin.snoc_castSucc]`. Conclude with `hZo i j (fun e => hij (by rw [e]))`. Introduce `i`.

Use `Fin.lastCases ?_ (fun i => ?_) i` and prove the remaining obligations. Rewrite using `[Fin.snoc_last]`. Conclude with `hz`. Rewrite using `[Fin.snoc_castSucc]`. Conclude with `hZd i`.

Take `⟨Z, hZW, hZo, hZd⟩` from `main a le_rfl`. Establish `hex : ∀ i, ∃ c : Fin a → K, ∑ l, c l • X0 l = Z i` using `fun i => (Submodule.mem_span_range_iff_exists_fun K).1 (hZW i)`. Use `choose C hC using hex`. Set `P : Matrix (Fin a) (Fin a) K` to `Matrix.of C`. Establish `hPX : ∀ i, ∑ l, P i l • X0 l = Z i` using `fun i => hC i`.

Establish `hdet : P.det ≠ 0`. Introduce `hd`. Take `⟨c, hc0, hcP⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 hd`. Apply `hc0` to reduce the goal to its premises. Use function extensionality and compare the values at `j`.

Establish `e : ∑ i, c i • Z i = 0`. Establish `hl : ∀ l, ∑ i, c i * P i l = 0` using `fun l => by`. Use `congrFun hcP l` as an intermediate fact. Simplify `this` using `[vecMul, dotProduct]`. Repeatedly rewrite using `[← hPX, Finset.smul_sum, smul_smul]`.

Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.sum_smul, hl, zero_smul, Finset.sum_const_zero]`. Establish `h` using `congrArg (hform σ J (Z j)) e`. Rewrite `h` using `[hform_sum_right, hform_zero_right, Finset.sum_eq_single j]`. Conclude with `(mul_eq_zero.1 h).resolve_right (hZd j)`.

Introduce `i _ hij`. Rewrite using `[hZo j i (Ne.symm hij), mul_zero]`. Simplify using the standard rewrite rules. Use `⟨P, P⁻¹, Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.2 hdet), ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`.

Rewrite using `[hPX, hPX]`. Conclude with `hZo i j hij`. Introduce `i`. Rewrite using `[hPX]`. Conclude with `hZd i`.
-/
theorem hermDiag : Formalism.L2.SG.Pf.NcX.IntWittPf.HermDiag := by
  intro K _ σ hσ h2 n J hJ a X0 hT
  classical
  have hconj := hform_conj σ J hσ hJ
  let W : Submodule K (Fin n → K) := Submodule.span K (Set.range X0)
  let comb : (Fin a → K) → (Fin n → K) := fun c => ∑ l, c l • X0 l
  have hN : ∀ c : Fin a → K, (∀ j, hform σ J (X0 j) (comb c) = 0) → c = 0 := by
    intro c hc
    refine Matrix.eq_zero_of_mulVec_eq_zero hT ?_
    funext j
    have e : hform σ J (X0 j) (∑ l, c l • X0 l) = 0 := hc j
    rw [hform_sum_right] at e
    simp only [mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← e]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hcW : ∀ c, comb c ∈ W := fun c => W.sum_mem fun l _ => W.smul_mem _ (Submodule.subset_span ⟨l, rfl⟩)
  have main : ∀ k ≤ a, ∃ Z : Fin k → Fin n → K, (∀ i, Z i ∈ W) ∧
      (∀ i j, i ≠ j → hform σ J (Z i) (Z j) = 0) ∧ ∀ i, hform σ J (Z i) (Z i) ≠ 0 := by
    intro k
    induction k with
    | zero => intro _; exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨Z, hZW, hZo, hZd⟩ := ih (by omega)
      let f : (Fin a → K) →ₗ[K] (Fin k → K) :=
        { toFun := fun c i => hform σ J (Z i) (comb c)
          map_add' := by
            intro c d
            funext i
            simp only [comb, Pi.add_apply, add_smul, Finset.sum_add_distrib, hform_add_right]
          map_smul' := by
            intro r c
            funext i
            simp only [comb, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← smul_smul, ← Finset.smul_sum,
              hform_smul_right] }
      have hlt : Module.finrank K (Fin k → K) < Module.finrank K (Fin a → K) := by
        simp only [Module.finrank_fin_fun]
        omega
      obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt)
      have hcZ : ∀ i, hform σ J (Z i) (comb c) = 0 := fun i => congrFun (LinearMap.mem_ker.1 hc) i
      obtain ⟨j, hj⟩ : ∃ j, hform σ J (X0 j) (comb c) ≠ 0 := by
        by_contra H
        push Not at H
        exact hc0 (hN c H)
      let w := X0 j - ∑ i, (hform σ J (Z i) (X0 j) / hform σ J (Z i) (Z i)) • Z i
      have hwZ : ∀ m, hform σ J (Z m) w = 0 := by
        intro m
        simp only [w, hform_sub_right, hform_sum_right]
        rw [Finset.sum_eq_single m]
        · rw [div_mul_cancel₀ _ (hZd m), sub_self]
        · intro i _ him
          rw [hZo m i (Ne.symm him), mul_zero]
        · simp
      have hwc : hform σ J w (comb c) ≠ 0 := by
        simp only [w, hform_sub_left, hform_sum_left]
        rw [Finset.sum_eq_zero, sub_zero]
        · exact hj
        · intro i _
          rw [hcZ i, mul_zero]
      have hwW : w ∈ W := W.sub_mem (Submodule.subset_span ⟨j, rfl⟩) (W.sum_mem fun i _ => W.smul_mem _ (hZW i))
      obtain ⟨r, t, hz⟩ := exists_aniso σ J hσ hJ h2 w (comb c) hwc
      set z := r • w + t • comb c with hzdef
      have hzZ : ∀ m, hform σ J (Z m) z = 0 := by
        intro m
        rw [hzdef, hform_add_right, hform_smul_right, hform_smul_right, hwZ, hcZ, mul_zero, mul_zero, add_zero]
      refine ⟨Fin.snoc Z z, ?_, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · rw [Fin.snoc_last]
          exact W.add_mem (W.smul_mem _ hwW) (W.smul_mem _ (hcW c))
        · rw [Fin.snoc_castSucc]
          exact hZW i
      · intro i j
        refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
        · intro h; exact absurd rfl h
        · intro _
          rw [Fin.snoc_last, Fin.snoc_castSucc, ← hconj, hzZ, map_zero]
        · intro _
          rw [Fin.snoc_last, Fin.snoc_castSucc]
          exact hzZ i
        · intro hij
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hZo i j (fun e => hij (by rw [e]))
      · intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · rw [Fin.snoc_last]
          exact hz
        · rw [Fin.snoc_castSucc]
          exact hZd i
  obtain ⟨Z, hZW, hZo, hZd⟩ := main a le_rfl
  have hex : ∀ i, ∃ c : Fin a → K, ∑ l, c l • X0 l = Z i :=
    fun i => (Submodule.mem_span_range_iff_exists_fun K).1 (hZW i)
  choose C hC using hex
  let P : Matrix (Fin a) (Fin a) K := Matrix.of C
  have hPX : ∀ i, ∑ l, P i l • X0 l = Z i := fun i => hC i
  have hdet : P.det ≠ 0 := by
    intro hd
    obtain ⟨c, hc0, hcP⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    apply hc0
    funext j
    have e : ∑ i, c i • Z i = 0 := by
      have hl : ∀ l, ∑ i, c i * P i l = 0 := fun l => by
        have := congrFun hcP l
        simpa [vecMul, dotProduct] using this
      simp_rw [← hPX, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, hl, zero_smul, Finset.sum_const_zero]
    have h := congrArg (hform σ J (Z j)) e
    rw [hform_sum_right, hform_zero_right, Finset.sum_eq_single j] at h
    · exact (mul_eq_zero.1 h).resolve_right (hZd j)
    · intro i _ hij
      rw [hZo j i (Ne.symm hij), mul_zero]
    · simp
  refine ⟨P, P⁻¹, Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.2 hdet), ?_, ?_⟩
  · intro i j hij
    rw [hPX, hPX]
    exact hZo i j hij
  · intro i
    rw [hPX]
    exact hZd i

end Formalism.L2.SG.Pf.NcX.IntWittAlg
