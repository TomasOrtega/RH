import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleF

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

namespace LTF

open PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD PI.WGL.LTE

/- English proof (translation)
Establish `hH : IsWeightedHomogeneous (rowW N N) (Mlift h lam sg sz hsz L I) (w0r h lam sg + ∑ k, wk h (I k) (k ∈ L))` using `(constant_weighted_homogeneous h lam sg).mul (IsWeightedHomogeneous.prod _ _ _ (fun k _ => G_rowW h sz hsz L k (I k)))`. Use `hH using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `a`. Take `⟨av, hav⟩` from `a`. Simplify using `only [Pi.add_apply, Finset.sum_apply, wk, constant_weight_apply, Pi.single_apply, ite_apply, Pi.zero_apply, Finset.sum_add_distrib, liftWt]`.

Distinguish the cases in `ha : av < n`. Establish `hn : 0 < n` using `by omega`. Rewrite using `[dif_pos ha, dif_pos (by omega), dif_pos hn, if_pos ha, if_neg (by omega)]`. Establish `hS2 : (∑ k : Fin K, if k ∈ L then (if (⟨av, hav⟩ : Fin N) = ⟨N - 1, by omega⟩ then 1 else 0) else 0) = 0`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `k _`. Establish `hne : (⟨av, hav⟩ : Fin N) ≠ ⟨N - 1, by omega⟩` using `fun e => by rw [Fin.mk.injEq] at e; omega`. Simplify using `[hne]`. Establish `hS1 : (∑ k : Fin K, ∑ q : Fin (sz k), if (⟨av, hav⟩ : Fin N) = eRow h (I k q) then 1 else 0) = tupCnt I ⟨av, ha⟩`. Simplify using `only [tupCnt, Finset.card_filter]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `k _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `q _`. Establish `: ((⟨av, hav⟩ : Fin N) = eRow h (I k q)) ↔ (I k q = ⟨av, ha⟩)`.

Simplify using `only [eRow, Fin.ext_iff]`. Conclude with `eq_comm`. Distinguish the cases in `hq : I k q = ⟨av, ha⟩`. Rewrite using `[if_pos (this.2 hq), if_pos hq]`. Rewrite using `[if_neg (fun e => hq (this.1 e)), if_neg hq]`.

Rewrite using `[hS1, hS2]`. Establish `e3` using `aLast_val h lam sg hI hn`. Establish `e4` using `sg_detShift sg hn`. Establish `e5` using `lam_detShift h lam`. Use linear arithmetic over natural numbers and integers.

Establish `hav' : av = n` using `by omega`. Simplify using `only [dif_neg ha, if_neg ha, if_pos hav', mul_zero, mul_one]`. Establish `hS1 : (∑ k : Fin K, ∑ q : Fin (sz k), if (⟨av, hav⟩ : Fin N) = eRow h (I k q) then 1 else 0) = 0`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `k _`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `q _`. Rewrite using `[if_neg]`. Introduce `e`. Simplify using `only [eRow, Fin.ext_iff] at e`.

Use `(I k q).2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hS2 : (∑ k : Fin K, if k ∈ L then (if (⟨av, hav⟩ : Fin N) = ⟨N - 1, by omega⟩ then 1 else 0) else 0) = L.card`. Rewrite using `[Finset.sum_congr rfl (g := fun k => if k ∈ L then 1 else 0)]`. Rewrite using `[← Finset.card_filter]`.

Use `congr 1`. Use extensionality with `k`. Simplify using the standard rewrite rules. Introduce `k _`. Rewrite using `[if_pos (Fin.ext (by simp; omega))]`.

Rewrite using `[hS1, hS2, cardL h lam sg sz hsz hshape L hL]`. Establish `hsplit : (∑ i : Fin n, (bb h lam sg i).toNat) = (∑ i : Fin n, if i.1 = 0 then (bb h lam sg i).toNat else 0) + ∑ i : Fin n, (if i.1 = 0 then 0 else (bb h lam sg i).toNat)`. Rewrite using `[← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite `hsplit` using `[sum_ite_val (fun i : Fin n => (bb h lam sg i).toNat) 0]`. Establish `e6` using `sumB h lam sg hI`. Unfold `dLast`. Apply the tactic sequence `split_ifs at hsplit ⊢ with h1 h2 <;> omega`.
-/
theorem Mlift_rowW {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (hshape : shapeDeg sz = sg.natW) (L : Finset (Fin K))
    (hL : GoodL h lam sg sz L) (I : ∀ k, Fin (sz k) → Fin n) :
    IsWeightedHomogeneous (rowW N N) (Mlift h lam sg sz hsz L I) (liftWt h lam sg (tupCnt I)) := by
  classical
  have hH : IsWeightedHomogeneous (rowW N N) (Mlift h lam sg sz hsz L I)
      (w0r h lam sg + ∑ k, wk h (I k) (k ∈ L)) :=
    (constant_weighted_homogeneous h lam sg).mul (IsWeightedHomogeneous.prod _ _ _ (fun k _ => G_rowW h sz hsz L k (I k)))
  convert hH using 1
  funext a
  obtain ⟨av, hav⟩ := a
  simp only [Pi.add_apply, Finset.sum_apply, wk, constant_weight_apply, Pi.single_apply, ite_apply, Pi.zero_apply,
    Finset.sum_add_distrib, liftWt]
  by_cases ha : av < n
  · have hn : 0 < n := by omega
    rw [dif_pos ha, dif_pos (by omega), dif_pos hn, if_pos ha, if_neg (by omega)]
    have hS2 : (∑ k : Fin K, if k ∈ L then (if (⟨av, hav⟩ : Fin N) = ⟨N - 1, by omega⟩ then 1 else 0) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      have hne : (⟨av, hav⟩ : Fin N) ≠ ⟨N - 1, by omega⟩ := fun e => by rw [Fin.mk.injEq] at e; omega
      simp [hne]
    have hS1 : (∑ k : Fin K, ∑ q : Fin (sz k), if (⟨av, hav⟩ : Fin N) = eRow h (I k q) then 1 else 0) =
        tupCnt I ⟨av, ha⟩ := by
      simp only [tupCnt, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro q _
      have : ((⟨av, hav⟩ : Fin N) = eRow h (I k q)) ↔ (I k q = ⟨av, ha⟩) := by
        simp only [eRow, Fin.ext_iff]; exact eq_comm
      by_cases hq : I k q = ⟨av, ha⟩
      · rw [if_pos (this.2 hq), if_pos hq]
      · rw [if_neg (fun e => hq (this.1 e)), if_neg hq]
    rw [hS1, hS2]
    have e3 := aLast_val h lam sg hI hn
    have e4 := sg_detShift sg hn
    have e5 := lam_detShift h lam
    omega
  · have hav' : av = n := by omega
    simp only [dif_neg ha, if_neg ha, if_pos hav', mul_zero, mul_one]
    have hS1 : (∑ k : Fin K, ∑ q : Fin (sz k), if (⟨av, hav⟩ : Fin N) = eRow h (I k q) then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero; intro k _
      apply Finset.sum_eq_zero; intro q _
      rw [if_neg]
      intro e
      simp only [eRow, Fin.ext_iff] at e
      have := (I k q).2
      omega
    have hS2 : (∑ k : Fin K, if k ∈ L then (if (⟨av, hav⟩ : Fin N) = ⟨N - 1, by omega⟩ then 1 else 0) else 0) =
        L.card := by
      rw [Finset.sum_congr rfl (g := fun k => if k ∈ L then 1 else 0)]
      · rw [← Finset.card_filter]; congr 1; ext k; simp
      · intro k _
        rw [if_pos (Fin.ext (by simp; omega))]
    rw [hS1, hS2, cardL h lam sg sz hsz hshape L hL]
    have hsplit : (∑ i : Fin n, (bb h lam sg i).toNat) =
        (∑ i : Fin n, if i.1 = 0 then (bb h lam sg i).toNat else 0) +
          ∑ i : Fin n, (if i.1 = 0 then 0 else (bb h lam sg i).toNat) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    rw [sum_ite_val (fun i : Fin n => (bb h lam sg i).toNat) 0] at hsplit
    have e6 := sumB h lam sg hI
    unfold dLast
    split_ifs at hsplit ⊢ with h1 h2 <;> omega

end LTF

/- English proof (translation)
Introduce `n N h lam sg hI K sz hsz hshape`. Take `⟨L, hL⟩` from `LTD.goodL_exists h lam sg hI sz hshape`. Take `⟨htop, hstd1, hstd2, hstd3⟩` from `LTB.top_component_formula n N h lam sg hI K sz hsz hshape L hL`. Use `⟨LTM.Mlift h lam sg sz hsz L, fun I => ⟨?_, LTF.Mlift_rowW h lam sg hI sz hsz hshape L hL I, LTF.bidet_rowW sz hsz I⟩, fun I w hw => LTC.word_clause h lam sg sz hsz L I w hw, htop, ⟨LTM.stdT sz hsz, hstd1, hstd2, hstd3⟩⟩` and prove the remaining obligations. Establish `hm` using `LTE.Mlift_mem_colWt h lam sg sz hsz L I`.

Rewrite `hm` using `[LTE.colWt_eq h lam sg hI sz hsz hshape L hL]`. Conclude with `hm`.
-/
theorem tuple_decomposition_formula : TupleCore := by
  intro n N h lam sg hI K sz hsz hshape
  obtain ⟨L, hL⟩ := LTD.goodL_exists h lam sg hI sz hshape
  obtain ⟨htop, hstd1, hstd2, hstd3⟩ := LTB.top_component_formula n N h lam sg hI K sz hsz hshape L hL
  refine ⟨LTM.Mlift h lam sg sz hsz L, fun I => ⟨?_, LTF.Mlift_rowW h lam sg hI sz hsz hshape L hL I,
    LTF.bidet_rowW sz hsz I⟩, fun I w hw => LTC.word_clause h lam sg sz hsz L I w hw, htop,
    ⟨LTM.stdT sz hsz, hstd1, hstd2, hstd3⟩⟩
  have hm := LTE.Mlift_mem_colWt h lam sg sz hsz L I
  rw [LTE.colWt_eq h lam sg hI sz hsz hshape L hL] at hm
  exact hm

end PI.WGL
