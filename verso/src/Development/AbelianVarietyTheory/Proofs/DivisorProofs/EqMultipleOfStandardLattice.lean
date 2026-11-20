import Mathlib
open IsDedekindDomain NumberField Matrix

namespace GlobalTheory.LatticeBetweenMultiples

/- English proof (translation)
Establish `h1 : (1 + N) * (1 - N) = 1`. Rewrite using `[add_mul, one_mul, mul_sub, mul_one, hN, sub_zero, sub_add_cancel]`. Establish `h2 : (1 - N) * (1 + N) = 1`. Rewrite using `[sub_mul, one_mul, mul_add, mul_one, hN, add_zero, add_sub_cancel_right]`. Establish `h1m : ∀ i j, (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F`.

Introduce `i j`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`.

Establish `hp : ∀ i j, (1 + N) i j ∈ v.adicCompletionIntegers F`. Introduce `i j`. Rewrite using `[Matrix.add_apply]`. Conclude with `add_mem (h1m i j) (hNi i j)`. Establish `hm : ∀ i j, (1 - N) i j ∈ v.adicCompletionIntegers F`.

Introduce `i j`. Rewrite using `[Matrix.sub_apply]`. Conclude with `sub_mem (h1m i j) (hNi i j)`. Conclude with `hGL ⟨1 + N, 1 - N, h1, h2⟩ hp hm w hw`.
-/
lemma one_add_mulVec_mem {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {n : ℕ}
    (S : AddSubgroup (Fin n → v.adicCompletion F))
    (hGL : ∀ x : GL (Fin n) (v.adicCompletion F), (∀ i j, x.1 i j ∈ v.adicCompletionIntegers F) →
      (∀ i j, (x⁻¹).1 i j ∈ v.adicCompletionIntegers F) → ∀ w ∈ S, x.1.mulVec w ∈ S)
    (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) (hN : N * N = 0)
    (hNi : ∀ i j, N i j ∈ v.adicCompletionIntegers F) {w : Fin n → v.adicCompletion F}
    (hw : w ∈ S) : (1 + N).mulVec w ∈ S := by
  have h1 : (1 + N) * (1 - N) = 1 := by
    rw [add_mul, one_mul, mul_sub, mul_one, hN, sub_zero, sub_add_cancel]
  have h2 : (1 - N) * (1 + N) = 1 := by
    rw [sub_mul, one_mul, mul_add, mul_one, hN, add_zero, add_sub_cancel_right]
  have h1m : ∀ i j, (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈
      v.adicCompletionIntegers F := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hp : ∀ i j, (1 + N) i j ∈ v.adicCompletionIntegers F := by
    intro i j; rw [Matrix.add_apply]; exact add_mem (h1m i j) (hNi i j)
  have hm : ∀ i j, (1 - N) i j ∈ v.adicCompletionIntegers F := by
    intro i j; rw [Matrix.sub_apply]; exact sub_mem (h1m i j) (hNi i j)
  exact hGL ⟨1 + N, 1 - N, h1, h2⟩ hp hm w hw

/- English proof (translation)
Introduce `F _ _ v n S hO ⟨tl, htl0, htl⟩ ⟨tu, htu0, htu⟩ hGL`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Use `⟨1, one_ne_zero, fun w => ?_⟩` and prove the remaining obligations. Establish `hw : w = 0` using `Subsingleton.elim _ _`. Substitute `hw` using the available equality.

Conclude with `⟨fun _ i => i.elim0, fun _ => S.zero_mem⟩`. Establish `memO : ∀ x : v.adicCompletion F, x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1` using `fun x => Iff.rfl`. Establish `hbd : ∀ w ∈ S, ∀ i, Valued.v (w i) ≤ (Valued.v tu)⁻¹`. Introduce `w hw i`. Establish `h` using `(memO _).1 (htu w hw i)`.

Rewrite `h` using `[map_mul]`. Establish `hu : Valued.v tu ≠ 0` using `(Valuation.ne_zero_iff _).2 htu0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, inv_mul_cancel₀ hu, one_mul]`. Use `_ ≤ (Valued.v tu)⁻¹ * 1 := by gcongr`.

Use `_ = (Valued.v tu)⁻¹ := mul_one _`. Set `P : ℤ → Prop` to `fun k => ∃ w ∈ S, ∃ i, Valued.v (w i) = ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero (Multiplicative ℤ))`. Take `⟨mB, hmB⟩ : ∃ m : Multiplicative ℤ, (m : WithZero (Multiplicative ℤ)) = (Valued.v tu)⁻¹` from `WithZero.ne_zero_iff_exists.1 (inv_ne_zero ((Valuation.ne_zero_iff _).2 htu0))`. Establish `hPb : ∃ b : ℤ, ∀ z, P z → z ≤ b`. Use `⟨Multiplicative.toAdd mB, fun z ⟨w, hw, i, hz⟩ => ?_⟩` and prove the remaining obligations.

Establish `h` using `hbd w hw i`. Rewrite `h` using `[hz, ← hmB, WithZero.coe_le_coe]`. Conclude with `Multiplicative.ofAdd_le.1 (by simpa using h)`. Set `i₀' : Fin n` to `⟨0, hn⟩`. Establish `hPn : ∃ z, P z`.

Establish `hmem : tl • (fun _ => (1 : v.adicCompletion F)) ∈ S` using `htl _ (fun _ => one_mem _)`. Take `⟨m, hm⟩ : ∃ m : Multiplicative ℤ, (m : WithZero (Multiplicative ℤ)) = Valued.v tl` from `WithZero.ne_zero_iff_exists.1 ((Valuation.ne_zero_iff _).2 htl0)`. Use `⟨Multiplicative.toAdd m, _, hmem, i₀', ?_⟩` and prove the remaining obligations. Simplify using `[← hm]`. Take `⟨lb, ⟨w₀, hw₀, i₀, hc⟩, hlb⟩` from `Int.exists_greatest_of_bdd hPb hPn`.

Use `set c := w₀ i₀ with hcdef`. Establish `hvc : Valued.v c ≠ 0` using `by rw [hc]; exact WithZero.coe_ne_zero`. Establish `hc0 : c ≠ 0` using `fun h => hvc (by rw [h, map_zero])`. Establish `hmax : ∀ w ∈ S, ∀ i, Valued.v (w i) ≤ Valued.v c`. Introduce `w hw i`.

Distinguish the cases in `h0 : w i = 0`. Rewrite using `[h0, map_zero]`. Conclude with `zero_le'`. Take `⟨m, hm⟩ : ∃ m : Multiplicative ℤ, (m : WithZero (Multiplicative ℤ)) = Valued.v (w i)` from `WithZero.ne_zero_iff_exists.1 ((Valuation.ne_zero_iff _).2 h0)`. Establish `hk` using `hlb (Multiplicative.toAdd m) ⟨w, hw, i, by simp [← hm]⟩`.

Rewrite using `[← hm, hc, WithZero.coe_le_coe]`. Conclude with `Multiplicative.toAdd_le.1 (by simpa using hk)`. Establish `hint : ∀ w ∈ S, ∀ i, c⁻¹ * w i ∈ v.adicCompletionIntegers F`. Introduce `w hw i`. Rewrite using `[memO, map_mul, map_inv₀]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hsingle0 : Pi.single i₀ c ∈ S`. Set `N : Matrix (Fin n) (Fin n) (v.adicCompletion F)` to `fun a b => if b = i₀ ∧ a ≠ i₀ then -(c⁻¹ * w₀ a) else 0`. Establish `hN : N * N = 0`. Use function extensionality and compare the values at `a b`.

Simplify using `only [Matrix.mul_apply, Matrix.zero_apply]`. Use `Finset.sum_eq_zero (fun m _ => ?_)` and prove the remaining obligations. Apply the tactic sequence `by_cases hm : m = i₀ <;> simp [N, hm]`. Establish `hNi : ∀ i j, N i j ∈ v.adicCompletionIntegers F`. Introduce `i j`.

Simplify using `only [N]`. Use `split_ifs`. Conclude with `neg_mem (hint w₀ hw₀ i)`. Conclude with `zero_mem _`. Establish `h` using `one_add_mulVec_mem v S hGL N hN hNi hw₀`.

Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `a`. Rewrite using `[Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]`. Distinguish the cases in `ha : a = i₀`. Substitute `ha` using the available equality.

Simplify using `[N, Matrix.mulVec, dotProduct, hcdef]`. Simplify using `[N, Matrix.mulVec, dotProduct, ha, Pi.single_apply, ← hcdef]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hsingle : ∀ j, Pi.single j c ∈ S`.

Introduce `j`. Distinguish the cases in `hj : j = i₀`. Substitute `hj` using the available equality. Conclude with `hsingle0`. Set `N : Matrix (Fin n) (Fin n) (v.adicCompletion F)` to `fun a b => if a = j ∧ b = i₀ then 1 else 0`.

Establish `hN : N * N = 0`. Use function extensionality and compare the values at `a b`. Simplify using `only [Matrix.mul_apply, Matrix.zero_apply]`. Use `Finset.sum_eq_zero (fun m _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hm : m = i₀`.

Substitute `hm` using the available equality. Simplify using `[N, Ne.symm hj]`. Simplify using `[N, hm]`. Establish `hNi : ∀ i k, N i k ∈ v.adicCompletionIntegers F`. Introduce `i k`.

Simplify using `only [N]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Establish `h` using `one_add_mulVec_mem v S hGL N hN hNi hsingle0`.

Establish `heq : (1 + N).mulVec (Pi.single i₀ c) = Pi.single i₀ c + Pi.single j c`. Use function extensionality and compare the values at `a`. Rewrite using `[Matrix.add_mulVec, Matrix.one_mulVec]`. Simplify using `[N, Matrix.mulVec, dotProduct, Pi.single_apply]`. Rewrite `h` using `[heq]`.

Simplify using `using S.sub_mem h hsingle0`. Use `⟨c⁻¹, inv_ne_zero hc0, fun w => ⟨fun hw i => hint w hw i, fun hw => ?_⟩⟩` and prove the remaining obligations. Establish `hsum : w = ∑ j, (c⁻¹ * w j) • Pi.single j c`. Use function extensionality and compare the values at `a`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single a]`.

Simplify using `only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Introduce `b _ hb`. Simplify using `[Pi.single_apply, Ne.symm hb]`. Simplify using the standard rewrite rules.

Rewrite using `[hsum]`. Conclude with `S.sum_mem (fun j _ => hO _ (hw j) _ (hsingle j))`.
-/
theorem eq_multiple_of_standard_lattice : ∀ {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {n : ℕ}
    (S : AddSubgroup (Fin n → v.adicCompletion F)),
    (∀ o ∈ v.adicCompletionIntegers F, ∀ w ∈ S, o • w ∈ S) →
    (∃ t : v.adicCompletion F, t ≠ 0 ∧ ∀ w : Fin n → v.adicCompletion F,
      (∀ i, w i ∈ v.adicCompletionIntegers F) → t • w ∈ S) →
    (∃ t : v.adicCompletion F, t ≠ 0 ∧ ∀ w ∈ S, ∀ i, t * w i ∈ v.adicCompletionIntegers F) →
    (∀ x : GL (Fin n) (v.adicCompletion F), (∀ i j, x.1 i j ∈ v.adicCompletionIntegers F) →
      (∀ i j, (x⁻¹).1 i j ∈ v.adicCompletionIntegers F) → ∀ w ∈ S, x.1.mulVec w ∈ S) →
    ∃ t : v.adicCompletion F, t ≠ 0 ∧ ∀ w, w ∈ S ↔ ∀ i, t * w i ∈ v.adicCompletionIntegers F := by
  intro F _ _ v n S hO ⟨tl, htl0, htl⟩ ⟨tu, htu0, htu⟩ hGL
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, one_ne_zero, fun w => ?_⟩
    have hw : w = 0 := Subsingleton.elim _ _
    subst hw
    exact ⟨fun _ i => i.elim0, fun _ => S.zero_mem⟩
  have memO : ∀ x : v.adicCompletion F, x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 :=
    fun x => Iff.rfl

  have hbd : ∀ w ∈ S, ∀ i, Valued.v (w i) ≤ (Valued.v tu)⁻¹ := by
    intro w hw i
    have h := (memO _).1 (htu w hw i)
    rw [map_mul] at h
    have hu : Valued.v tu ≠ 0 := (Valuation.ne_zero_iff _).2 htu0
    calc Valued.v (w i) = (Valued.v tu)⁻¹ * (Valued.v tu * Valued.v (w i)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hu, one_mul]
      _ ≤ (Valued.v tu)⁻¹ * 1 := by gcongr
      _ = (Valued.v tu)⁻¹ := mul_one _
  let P : ℤ → Prop := fun k => ∃ w ∈ S, ∃ i, Valued.v (w i) =
    ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  obtain ⟨mB, hmB⟩ : ∃ m : Multiplicative ℤ, (m : WithZero (Multiplicative ℤ)) = (Valued.v tu)⁻¹ :=
    WithZero.ne_zero_iff_exists.1 (inv_ne_zero ((Valuation.ne_zero_iff _).2 htu0))
  have hPb : ∃ b : ℤ, ∀ z, P z → z ≤ b := by
    refine ⟨Multiplicative.toAdd mB, fun z ⟨w, hw, i, hz⟩ => ?_⟩
    have h := hbd w hw i
    rw [hz, ← hmB, WithZero.coe_le_coe] at h
    exact Multiplicative.ofAdd_le.1 (by simpa using h)
  let i₀' : Fin n := ⟨0, hn⟩
  have hPn : ∃ z, P z := by
    have hmem : tl • (fun _ => (1 : v.adicCompletion F)) ∈ S := htl _ (fun _ => one_mem _)
    obtain ⟨m, hm⟩ : ∃ m : Multiplicative ℤ, (m : WithZero (Multiplicative ℤ)) = Valued.v tl :=
      WithZero.ne_zero_iff_exists.1 ((Valuation.ne_zero_iff _).2 htl0)
    refine ⟨Multiplicative.toAdd m, _, hmem, i₀', ?_⟩
    simp [← hm]
  obtain ⟨lb, ⟨w₀, hw₀, i₀, hc⟩, hlb⟩ := Int.exists_greatest_of_bdd hPb hPn
  set c := w₀ i₀ with hcdef
  have hvc : Valued.v c ≠ 0 := by rw [hc]; exact WithZero.coe_ne_zero
  have hc0 : c ≠ 0 := fun h => hvc (by rw [h, map_zero])
  have hmax : ∀ w ∈ S, ∀ i, Valued.v (w i) ≤ Valued.v c := by
    intro w hw i
    by_cases h0 : w i = 0
    · rw [h0, map_zero]; exact zero_le'
    obtain ⟨m, hm⟩ : ∃ m : Multiplicative ℤ, (m : WithZero (Multiplicative ℤ)) = Valued.v (w i) :=
      WithZero.ne_zero_iff_exists.1 ((Valuation.ne_zero_iff _).2 h0)
    have hk := hlb (Multiplicative.toAdd m) ⟨w, hw, i, by simp [← hm]⟩
    rw [← hm, hc, WithZero.coe_le_coe]
    exact Multiplicative.toAdd_le.1 (by simpa using hk)
  have hint : ∀ w ∈ S, ∀ i, c⁻¹ * w i ∈ v.adicCompletionIntegers F := by
    intro w hw i
    rw [memO, map_mul, map_inv₀]
    calc (Valued.v c)⁻¹ * Valued.v (w i) ≤ (Valued.v c)⁻¹ * Valued.v c :=
          by gcongr; exact hmax w hw i
      _ = 1 := inv_mul_cancel₀ hvc

  have hsingle0 : Pi.single i₀ c ∈ S := by
    let N : Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
      fun a b => if b = i₀ ∧ a ≠ i₀ then -(c⁻¹ * w₀ a) else 0
    have hN : N * N = 0 := by
      funext a b
      simp only [Matrix.mul_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero (fun m _ => ?_)
      by_cases hm : m = i₀ <;> simp [N, hm]
    have hNi : ∀ i j, N i j ∈ v.adicCompletionIntegers F := by
      intro i j
      simp only [N]
      split_ifs
      · exact neg_mem (hint w₀ hw₀ i)
      · exact zero_mem _
    have h := one_add_mulVec_mem v S hGL N hN hNi hw₀
    convert h using 1
    funext a
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
    by_cases ha : a = i₀
    · subst ha
      simp [N, Matrix.mulVec, dotProduct, hcdef]
    · simp [N, Matrix.mulVec, dotProduct, ha, Pi.single_apply, ← hcdef]
      field_simp
      ring
  have hsingle : ∀ j, Pi.single j c ∈ S := by
    intro j
    by_cases hj : j = i₀
    · subst hj; exact hsingle0
    let N : Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
      fun a b => if a = j ∧ b = i₀ then 1 else 0
    have hN : N * N = 0 := by
      funext a b
      simp only [Matrix.mul_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero (fun m _ => ?_)
      by_cases hm : m = i₀
      · subst hm; simp [N, Ne.symm hj]
      · simp [N, hm]
    have hNi : ∀ i k, N i k ∈ v.adicCompletionIntegers F := by
      intro i k
      simp only [N]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have h := one_add_mulVec_mem v S hGL N hN hNi hsingle0
    have heq : (1 + N).mulVec (Pi.single i₀ c) = Pi.single i₀ c + Pi.single j c := by
      funext a
      rw [Matrix.add_mulVec, Matrix.one_mulVec]
      simp [N, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [heq] at h
    simpa using S.sub_mem h hsingle0
  refine ⟨c⁻¹, inv_ne_zero hc0, fun w => ⟨fun hw i => hint w hw i, fun hw => ?_⟩⟩
  have hsum : w = ∑ j, (c⁻¹ * w j) • Pi.single j c := by
    funext a
    rw [Finset.sum_apply, Finset.sum_eq_single a]
    · simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
      field_simp
    · intro b _ hb
      simp [Pi.single_apply, Ne.symm hb]
    · simp
  rw [hsum]
  exact S.sum_mem (fun j _ => hO _ (hw j) _ (hsingle j))

end GlobalTheory.LatticeBetweenMultiples
