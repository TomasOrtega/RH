import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces

open scoped BigOperators
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Classical

/- English proof (translation)
Introduce `D L X K E ce C6 C hS hC hL p _ hp5 hcs _ i hi`. Establish `hc6 : (12 : ℝ) ≤ ce.c6` using `hL.1`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast (by omega : 1 < p)`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `ha : 1 < L.sc.a` using `hS.xa.2`.

Establish `hns : ¬ IsSg D p` using `fun h => by`. Establish `h3 : D.host.cls p = PrimeClass.inertClass` using `hcs.1`. Establish `h4 : D.host.cls p = PrimeClass.signal` using `h`. Rewrite `h3` using `[h4]`. Simplify using `at h3`.

Establish `eF : FInert D (i + 1) p = (∑ z ∈ kindA D p, FOrb D (i + 1) p z) / (nP D p : ℝ) + (∑ z ∈ kindBC D p, FOrb D (i + 1) p z) / (nP D p : ℝ)`. Unfold `FInert`. Rewrite using `[if_neg (fun h => hcs.2.2 h.2), ← add_div]`. Use `congr 1`. Establish `e : kindBC D p = (kindA D p)ᶜ`.

Use extensionality with `z`. Rewrite using `[Finset.mem_compl]`. Conclude with `OrbitPlaces.memBC_iff p z`. Rewrite using `[e, Finset.sum_add_sum_compl]`. Establish `eT : topsBC D p = ∅`.

Unfold `topsBC kindBC`. Rewrite using `[Finset.filter_eq_empty_iff]`. Introduce `z hz ht`. Rewrite `hz` using `[Finset.mem_filter]`. Break down `hz.2 with h | h` into its components or cases.

Conclude with `hns h`. Establish `h1` using `ht.1`. Rewrite `h1` using `[h]`. Simplify using `at h1`. Establish `hw : 0 ≤ ∑ z ∈ kindBC D p, wPl D (i + 1) z` using `Finset.sum_nonneg fun z _ => (hS.wpos i hi z).le`.

Establish `hl1 : 0 ≤ Real.logb p L.sc.a` using `Real.logb_nonneg hp1 ha.le`. Establish `hl2 : 0 ≤ Real.logb p (2 * L.sc.a)` using `Real.logb_nonneg hp1 (by linarith)`. Establish `hl3 : 0 ≤ Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a)`. Unfold `Nm`. Break down `Nat.eq_zero_or_pos (D.R.N D.R.m) with h | h` into its components or cases.

Rewrite using `[h]`. Simplify using the standard rewrite rules. Use `Real.logb_nonneg hp1 ?_` and prove the remaining obligations. Establish `h1 : (1 : ℝ) ≤ (nP D p : ℝ)` using `by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (nP D p))`. Establish `h2 : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ)` using `by exact_mod_cast h`.

Establish `h3 : (1 : ℝ) ≤ 4 * (nP D p : ℝ)` using `by linarith`. Conclude with `one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h3 h2) ha.le`. Establish `t1 : 0 ≤ ((kindBC D p).card : ℝ) * (D.R.N (i + 1 - 1) : ℝ) * (D.R.N (i + 1) : ℝ) * (Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) + 1)` using `by positivity`. Establish `t2 : 0 ≤ K.dl1 * ((kindBC D p).card : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a)`. Use `hC.dl1nn` as an intermediate fact.

Check the signs of the components of the expression. Establish `t3 : 8 * (∑ z ∈ kindBC D p, wPl D (i + 1) z) / (p : ℝ) ≤ ce.c6 * (∑ z ∈ kindBC D p, wPl D (i + 1) z) / (p : ℝ)` using `div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hw) hp0.le`. Establish `t4 : 3 * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a ≤ ce.c6 * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a` using `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)) (sq_nonneg _)) hl1`. Establish `hm` using `le_max_right (0 : ℝ) ((∑ z ∈ kindA D p, FOrb D (i + 1) p z) / (nP D p : ℝ))`. Rewrite using `[eF]`.

Unfold `EatI EatX`. Rewrite using `[if_pos hcs, eT]`. Simplify using `only [Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul, add_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.fInert_sub_eatI_le_orbit_average_sub_errors :
    ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (E : OrbitPlaces.Ent D) (ce : ErrC) (C6 C : ℝ),
    OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge C6 C K ce → ce.Large →
    ∀ p : ℕ, p.Prime → 5 ≤ p → IsCs D p → (p : ℝ) ≤ L.sc.X'' D.R.n → ∀ i < D.R.m,
    FInert D (i + 1) p - EatI L K ce (i + 1) p ≤
      (∑ z ∈ kindBC D p, FOrb D (i + 1) p z) / (nP D p : ℝ) -
        ((D.R.k : ℝ) - 1) * (∑ z ∈ kindBC D p, wPl D (i + 1) z) / (p : ℝ) ^ 3 - 8 * (∑ z ∈ kindBC D p, wPl D (i + 1) z) / p -
        3 * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a := by
  intro D L X K E ce C6 C hS hC hL p _ hp5 hcs _ i hi
  have hc6 : (12 : ℝ) ≤ ce.c6 := hL.1
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (0 : ℝ) < p := by linarith
  have ha : 1 < L.sc.a := hS.xa.2
  have hns : ¬ IsSg D p := fun h => by
    have h3 : D.host.cls p = PrimeClass.inertClass := hcs.1
    have h4 : D.host.cls p = PrimeClass.signal := h
    rw [h4] at h3; simp at h3
  have eF : FInert D (i + 1) p = (∑ z ∈ kindA D p, FOrb D (i + 1) p z) / (nP D p : ℝ) +
      (∑ z ∈ kindBC D p, FOrb D (i + 1) p z) / (nP D p : ℝ) := by
    unfold FInert
    rw [if_neg (fun h => hcs.2.2 h.2), ← add_div]
    congr 1
    have e : kindBC D p = (kindA D p)ᶜ := by
      ext z; rw [Finset.mem_compl]; exact OrbitPlaces.memBC_iff p z
    rw [e, Finset.sum_add_sum_compl]
  have eT : topsBC D p = ∅ := by
    unfold topsBC kindBC
    rw [Finset.filter_eq_empty_iff]
    intro z hz ht
    rw [Finset.mem_filter] at hz
    rcases hz.2 with h | h
    · exact hns h
    · have h1 := ht.1
      rw [h] at h1; simp at h1
  have hw : 0 ≤ ∑ z ∈ kindBC D p, wPl D (i + 1) z :=
    Finset.sum_nonneg fun z _ => (hS.wpos i hi z).le
  have hl1 : 0 ≤ Real.logb p L.sc.a := Real.logb_nonneg hp1 ha.le
  have hl2 : 0 ≤ Real.logb p (2 * L.sc.a) := Real.logb_nonneg hp1 (by linarith)
  have hl3 : 0 ≤ Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) := by
    unfold Nm
    rcases Nat.eq_zero_or_pos (D.R.N D.R.m) with h | h
    · rw [h]; simp
    · refine Real.logb_nonneg hp1 ?_
      have h1 : (1 : ℝ) ≤ (nP D p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (nP D p))
      have h2 : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast h
      have h3 : (1 : ℝ) ≤ 4 * (nP D p : ℝ) := by linarith
      exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h3 h2) ha.le
  have t1 : 0 ≤ ((kindBC D p).card : ℝ) * (D.R.N (i + 1 - 1) : ℝ) * (D.R.N (i + 1) : ℝ) *
      (Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) + 1) := by positivity
  have t2 : 0 ≤ K.dl1 * ((kindBC D p).card : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) := by
    have := hC.dl1nn
    positivity
  have t3 : 8 * (∑ z ∈ kindBC D p, wPl D (i + 1) z) / (p : ℝ) ≤
      ce.c6 * (∑ z ∈ kindBC D p, wPl D (i + 1) z) / (p : ℝ) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hw) hp0.le
  have t4 : 3 * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a ≤
      ce.c6 * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)) (sq_nonneg _)) hl1
  have hm := le_max_right (0 : ℝ) ((∑ z ∈ kindA D p, FOrb D (i + 1) p z) / (nP D p : ℝ))
  rw [eF]
  unfold EatI EatX
  rw [if_pos hcs, eT]
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul, add_zero]
  linarith
