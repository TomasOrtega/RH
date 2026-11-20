import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDifferentialMulLogCoordinateWedgeStatement
open GlobalTheory GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR.ChartMem

variable {K : Type} [Field K]

def wt {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n) : K :=
  if i ∈ J then 1 else (x i : K)

/- English proof (translation)
Unfold `frame wt`. Use `split_ifs with h`. Simplify using the standard rewrite rules. Simplify using `[dlog, smul_smul]`.
-/
theorem frame_eq {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n) :
    frame x J i = wt x J i • dlog (x i) := by
  unfold frame wt
  split_ifs with h
  · simp
  · simp [dlog, smul_smul]

/- English proof (translation)
Simplify using `only [wt]`. Rewrite using `[Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.sdiff_eq_filter]`.
-/
theorem prod_wt {n : ℕ} (x : Fin n → Kˣ) (J I : Finset (Fin n)) :
    ∏ i ∈ I, wt x J i = ∏ i ∈ I \ J, (x i : K) := by
  simp only [wt]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.sdiff_eq_filter]

/- English proof (translation)
Rewrite using `[← prod_wt, ← prod_wt, Finset.prod_insert hi]`.
-/
theorem wt_mul_prod {n : ℕ} (x : Fin n → Kˣ) (J I : Finset (Fin n)) (i : Fin n) (hi : i ∉ I) :
    wt x J i * ∏ j ∈ I \ J, (x j : K) = ∏ j ∈ insert i I \ J, (x j : K) := by
  rw [← prod_wt, ← prod_wt, Finset.prod_insert hi]

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.mpr fun j _ => Units.ne_zero _`.
-/
theorem prod_sdiff_ne_zero {n : ℕ} (x : Fin n → Kˣ) (J I : Finset (Fin n)) :
    ∏ j ∈ I \ J, (x j : K) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => Units.ne_zero _

/- English proof (translation)
The claim follows from `| 0, v, _ => ⟨∅, 1, fun _ => rfl, by simp [logWedge]⟩ | a + 1, v, hv => by obtain ⟨I, m, hc, he⟩ := ιMulti_frame x J a (Matrix.vecTail v) (fun i => hv _) obtain ⟨i0, hi0⟩ := hv 0 rw [ExteriorAlgebra.ιMulti_succ_apply, he, ← hi0, frame_eq, map_smul, smul_mul_smul_comm] by_cases hi …`.
-/
theorem ιMulti_frame {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) :
    ∀ (a : ℕ) (v : Fin a → Ω[K⁄ℤ]), (∀ i, v i ∈ Set.range (frame x J)) →
      ∃ (I : Finset (Fin n)) (m : ℤ), (m ≠ 0 → I.card = a) ∧
        ExteriorAlgebra.ιMulti K a v = ((m : K) * ∏ j ∈ I \ J, (x j : K)) • logWedge x I
  | 0, v, _ => ⟨∅, 1, fun _ => rfl, by simp [logWedge]⟩
  | a + 1, v, hv => by
    obtain ⟨I, m, hc, he⟩ := ιMulti_frame x J a (Matrix.vecTail v) (fun i => hv _)
    obtain ⟨i0, hi0⟩ := hv 0
    rw [ExteriorAlgebra.ιMulti_succ_apply, he, ← hi0, frame_eq, map_smul, smul_mul_smul_comm]
    by_cases hi : i0 ∈ I
    · refine ⟨∅, 0, fun h => absurd rfl h, ?_⟩
      rw [(GlobalTheory.T.logDifferential_mul_logCoordinateWedge K n x i0 I).1 hi]
      simp
    · obtain ⟨ε, hε, hw⟩ := (GlobalTheory.T.logDifferential_mul_logCoordinateWedge K n x i0 I).2 hi
      refine ⟨insert i0 I, m * ε, fun h => ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hi, hc (left_ne_zero_of_mul h)]
      · rw [hw, ← Int.cast_smul_eq_zsmul K, smul_smul, ← wt_mul_prod x J I i0 hi]
        push_cast
        ring_nf

/- English proof (translation)
The claim follows from `| [] => by simp | i :: l => by simp only [List.map_cons, List.prod_cons] rw [list_frame x J l, frame_eq, map_smul, smul_mul_smul_comm]`.
-/
theorem list_frame {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) : ∀ l : List (Fin n),
    (l.map fun i => ExteriorAlgebra.ι K (frame x J i)).prod =
      (l.map (wt x J)).prod • (l.map fun i => ExteriorAlgebra.ι K (dlog (x i))).prod
  | [] => by simp
  | i :: l => by
    simp only [List.map_cons, List.prod_cons]
    rw [list_frame x J l, frame_eq, map_smul, smul_mul_smul_comm]

/- English proof (translation)
Apply `List.ext_getElem` to reduce the goal to its premises. Simplify using `[h]`. Introduce `k h1 h2`. Simplify using `[Finset.orderEmbOfFin_apply]`.
-/
theorem ofFn_orderEmbOfFin {n a : ℕ} (I : Finset (Fin n)) (h : I.card = a) {β : Type} (f : Fin n → β) :
    List.ofFn (fun i => f (I.orderEmbOfFin h i)) = (I.sort (· ≤ ·)).map f := by
  apply List.ext_getElem
  · simp [h]
  · intro k h1 h2
    simp [Finset.orderEmbOfFin_apply]

/- English proof (translation)
Rewrite using `[ExteriorAlgebra.ιMulti_apply, show (List.ofFn fun i => ExteriorAlgebra.ι K (frame x J (I.orderEmbOfFin h i))) = _ from ofFn_orderEmbOfFin I h (fun j => ExteriorAlgebra.ι K (frame x J j)), list_frame, logWedge, ← prod_wt]`. Use `congr 1`. Rewrite using `[← Multiset.prod_coe, ← Multiset.map_coe, Finset.sort_eq, Finset.prod_eq_multiset_prod]`.
-/
theorem ιMulti_orderEmbOfFin {n a : ℕ} (x : Fin n → Kˣ) (J I : Finset (Fin n)) (h : I.card = a) :
    ExteriorAlgebra.ιMulti K a (fun i => frame x J (I.orderEmbOfFin h i)) =
      (∏ j ∈ I \ J, (x j : K)) • logWedge x I := by
  rw [ExteriorAlgebra.ιMulti_apply,
    show (List.ofFn fun i => ExteriorAlgebra.ι K (frame x J (I.orderEmbOfFin h i))) = _ from
      ofFn_orderEmbOfFin I h (fun j => ExteriorAlgebra.ι K (frame x J j)),
    list_frame, logWedge, ← prod_wt]
  congr 1
  rw [← Multiset.prod_coe, ← Multiset.map_coe, Finset.sort_eq, Finset.prod_eq_multiset_prod]

def coeffForms (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (a : ℕ) :
    AddSubgroup (abelian₂ K) where
  carrier := {η | ∃ c : Finset (Fin n) → K, (∀ I, I.card ≠ a → c I = 0) ∧
    (∀ I, c I * t / ∏ j ∈ I \ J, (x j : K) ∈ A) ∧ η = ∑ I, c I • logWedge x I}
  add_mem' := by
    rintro _ _ ⟨c, h1, h2, rfl⟩ ⟨d, g1, g2, rfl⟩
    refine ⟨c + d, fun I h => by simp [h1 I h, g1 I h], fun I => ?_, by
      simp [add_smul, Finset.sum_add_distrib]⟩
    simpa [add_mul, add_div] using A.add_mem (h2 I) (g2 I)
  zero_mem' := ⟨0, by simp, by simp, by simp⟩
  neg_mem' := by
    rintro _ ⟨c, h1, h2, rfl⟩
    refine ⟨-c, fun I h => by simp [h1 I h], fun I => ?_, by simp [neg_smul, Finset.sum_neg_distrib]⟩
    simpa [neg_mul, neg_div] using A.neg_mem (h2 I)

end GlobalTheory.LogDR.ChartMem

namespace GlobalTheory.LogDR

open ChartMem in

/- English proof (translation)
Introduce `K _ A n x J t a η`. Prove the components needed by the constructor for the conclusion. Introduce `hη`. Establish `hle : chartForms A x J t a ≤ coeffForms A x J t a`. Unfold `chartForms spanForms`.

Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `_ ⟨c, hc, v, hv, rfl⟩`. Take `⟨I, m, hm, he⟩` from `ιMulti_frame x J a v hv`. Use `⟨fun I' => if I' = I then c * ((m : K) * ∏ j ∈ I \ J, (x j : K)) else 0, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `I' h' dsimp only split_ifs with e`.

Substitute `e` using the available equality. Distinguish the cases in `h0 : m = 0`. Simplify using `[h0]`. Conclude with `absurd (hm h0) h'`. Both sides reduce to the same expression.

Introduce `I' dsimp only split_ifs with e`. Substitute `e` using the available equality. Establish `hp` using `prod_sdiff_ne_zero x J I'`. Establish `hq : c * ((m : K) * ∏ j ∈ I' \ J, (x j : K)) * t / ∏ j ∈ I' \ J, (x j : K) = (m : K) * (c * t)`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[hq]`. Conclude with `A.mul_mem (intCast_mem A m) hc`. Simplify using the standard rewrite rules. Rewrite using `[he, smul_smul]`. Simplify using `[ite_smul]`.

Conclude with `hle hη`. Introduce and unpack `⟨c, h1, h2, rfl⟩`. Use `AddSubgroup.sum_mem _ fun I _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : I.card = a`. Establish `hp` using `prod_sdiff_ne_zero x J I`.

Establish `e : c I • logWedge x I = (c I / ∏ j ∈ I \ J, (x j : K)) • ExteriorAlgebra.ιMulti K a (fun i => frame x J (I.orderEmbOfFin h i))`. Rewrite using `[ιMulti_orderEmbOfFin, smul_smul, div_mul_cancel₀ _ hp]`. Rewrite using `[e]`. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises. Use `⟨_, ?_, _, fun i => ⟨_, rfl⟩, rfl⟩` and prove the remaining obligations.

Use `show c I / _ * (t : K) ∈ A`. Rewrite using `[div_mul_eq_mul_div]`. Conclude with `h2 I`. Rewrite using `[h1 I h, zero_smul]`. Conclude with `zero_mem _`.
-/
theorem mem_chartForms_iff : ∀ (K : Type) [Field K] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (a : ℕ) (η : abelian₂ K), η ∈ chartForms A x J t a ↔ ∃ c : Finset (Fin n) → K, (∀ I, I.card ≠ a → c I = 0) ∧ (∀ I, c I * t / ∏ j ∈ I \ J, (x j : K) ∈ A) ∧ η = ∑ I, c I • logWedge x I := by
  intro K _ A n x J t a η
  constructor
  · intro hη
    have hle : chartForms A x J t a ≤ coeffForms A x J t a := by
      unfold chartForms spanForms
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, v, hv, rfl⟩
      obtain ⟨I, m, hm, he⟩ := ιMulti_frame x J a v hv
      refine ⟨fun I' => if I' = I then c * ((m : K) * ∏ j ∈ I \ J, (x j : K)) else 0, ?_, ?_, ?_⟩
      · intro I' h'
        dsimp only
        split_ifs with e
        · subst e
          by_cases h0 : m = 0
          · simp [h0]
          · exact absurd (hm h0) h'
        · rfl
      · intro I'
        dsimp only
        split_ifs with e
        · subst e
          have hp := prod_sdiff_ne_zero x J I'
          have hq : c * ((m : K) * ∏ j ∈ I' \ J, (x j : K)) * t / ∏ j ∈ I' \ J, (x j : K) =
              (m : K) * (c * t) := by
            field_simp
          rw [hq]
          exact A.mul_mem (intCast_mem A m) hc
        · simp
      · rw [he, smul_smul]
        simp [ite_smul]
    exact hle hη
  · rintro ⟨c, h1, h2, rfl⟩
    refine AddSubgroup.sum_mem _ fun I _ => ?_
    by_cases h : I.card = a
    · have hp := prod_sdiff_ne_zero x J I
      have e : c I • logWedge x I = (c I / ∏ j ∈ I \ J, (x j : K)) •
          ExteriorAlgebra.ιMulti K a (fun i => frame x J (I.orderEmbOfFin h i)) := by
        rw [ιMulti_orderEmbOfFin, smul_smul, div_mul_cancel₀ _ hp]
      rw [e]
      apply AddSubgroup.subset_closure
      refine ⟨_, ?_, _, fun i => ⟨_, rfl⟩, rfl⟩
      show c I / _ * (t : K) ∈ A
      rw [div_mul_eq_mul_div]
      exact h2 I
    · rw [h1 I h, zero_smul]
      exact zero_mem _

end GlobalTheory.LogDR
