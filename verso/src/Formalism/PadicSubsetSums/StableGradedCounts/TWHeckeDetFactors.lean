import Formalism.PadicSubsetSums.CentralIdempotents.CentralIdempotentIntegral

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.TW

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih`. Establish `ha : a ≠ 0` using `hs a (Multiset.mem_cons_self a s)`. Establish `ih'` using `ih (fun b hb => hs b (Multiset.mem_cons_of_mem hb))`.

Simplify using `only [Multiset.map_cons, Multiset.prod_cons]`. Rewrite using `[← ih', C_mul]`. Establish `h2 : ((1 : k[X]) - C a⁻¹ * X) * C (0 - a) = X - C a`. Establish `h1 : (C a⁻¹ : k[X]) * C a = 1` using `by rw [← C_mul, inv_mul_cancel₀ ha, C_1]`. Rewrite using `[zero_sub, C_neg]`.

Take the linear combination `X * h1`. Rewrite using `[← h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_one_sub_inv_mul_X {k : Type} [Field k] (s : Multiset k) (hs : ∀ a ∈ s, a ≠ 0) :
    (s.map (fun a => (1 : k[X]) - C a⁻¹ * X)).prod * C (s.map (fun a => 0 - a)).prod =
      (s.map (fun a => (X : k[X]) - C a)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : a ≠ 0 := hs a (Multiset.mem_cons_self a s)
    have ih' := ih (fun b hb => hs b (Multiset.mem_cons_of_mem hb))
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [← ih', C_mul]
    have h2 : ((1 : k[X]) - C a⁻¹ * X) * C (0 - a) = X - C a := by
      have h1 : (C a⁻¹ : k[X]) * C a = 1 := by rw [← C_mul, inv_mul_cancel₀ ha, C_1]
      rw [zero_sub, C_neg]; linear_combination X * h1
    rw [← h2]; ring

/- English proof (translation)
Introduce `k _ _ d r A hA`. Use `set M : Matrix (Fin d) (Fin d) k[X] := ∑ j : Fin (r + 1), (X : k[X]) ^ (j : ℕ) • (A j).map C with hM`. Apply the tactic sequence `have hentry : ∀ a b, (M a b).natDegree ≤ r := by`. Introduce `a b`. Rewrite using `[hM, Matrix.sum_apply]`.

Use `natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)` and prove the remaining obligations. Simplify using `only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]`. Use `(natDegree_mul_C_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[natDegree_X_pow]`. Use linear arithmetic over natural numbers and integers.

Establish `hdeg : M.det.natDegree ≤ r * d`. Rewrite using `[Matrix.det_apply]`. Use `natDegree_sum_le_of_forall_le _ _ (fun g _ => ?_)` and prove the remaining obligations. Establish `h1 : natDegree (Equiv.Perm.sign g • ∏ i, M (g i) i) ≤ natDegree (∏ i, M (g i) i)`. Break down `Int.units_eq_one_or (Equiv.Perm.sign g) with sg | sg` into its components or cases.

Rewrite using `[sg, one_smul]`. Rewrite using `[sg, Units.neg_smul, one_smul, natDegree_neg]`. Use `h1.trans ((natDegree_prod_le _ _).trans ?_)` and prove the remaining obligations. Apply the tactic sequence `refine (Finset.sum_le_card_nsmul _ _ r (fun i _ => hentry _ _)).trans ?_`. Simplify using `[mul_comm]`.

Establish `h0 : M.det.eval 0 = 1`. Establish `h1 : (evalRingHom (0 : k)) M.det = ((evalRingHom (0 : k)).mapMatrix M).det` using `RingHom.map_det _ _`. Establish `hm : (evalRingHom (0 : k)).mapMatrix M = 1`. Rewrite using `[← hA]`. Use extensionality with `a b`.

Simplify using `[hM, Matrix.sum_apply, eval_finsetSum, Fin.sum_univ_succ]`. Rewrite `h1` using `[hm, Matrix.det_one]`. Simplify using `using h1`. Establish `hne : M.det ≠ 0`. Introduce `h`.

Rewrite `h0` using `[h]`. Simplify using `at h0`. Establish `hs` using `IsAlgClosed.splits M.det`. Establish `hfac` using `hs.eq_prod_roots`. Establish `hev` using `hs.eval_eq_prod_roots 0`.

Rewrite `hev` using `[h0]`. Establish `hnz : ∀ a ∈ M.det.roots, a ≠ 0`. Introduce `a ha h`. Use `(mem_roots hne).1 ha` as an intermediate fact. Rewrite `this` using `[h, IsRoot.def, h0]`.

Conclude with `one_ne_zero this`. Establish `haux` using `prod_one_sub_inv_mul_X M.det.roots hnz`. Establish `hfin : M.det = (M.det.roots.map (fun a => (1 : k[X]) - C a⁻¹ * X)).prod` using `by conv_lhs => rw [hfac]`. Rewrite using `[← haux, mul_comm, mul_assoc, ← C_mul, mul_comm _ M.det.leadingCoeff, ← hev, C_1, mul_one]`. Use `⟨M.det.roots.toList.length, fun i => (M.det.roots.toList[i.1])⁻¹, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Multiset.length_toList]`. Conclude with `(card_roots' _).trans hdeg`. Rewrite using `[Fin.prod_univ_fun_getElem M.det.roots.toList (fun a => (1 : k[X]) - C a⁻¹ * X), ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]`. Conclude with `hfin`.
-/
theorem hecke_determinant_factors : HeckeDetFactors := by
  intro k _ _ d r A hA
  classical
  set M : Matrix (Fin d) (Fin d) k[X] :=
    ∑ j : Fin (r + 1), (X : k[X]) ^ (j : ℕ) • (A j).map C with hM
  have hentry : ∀ a b, (M a b).natDegree ≤ r := by
    intro a b
    rw [hM, Matrix.sum_apply]
    refine natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    refine (natDegree_mul_C_le _ _).trans ?_
    rw [natDegree_X_pow]
    omega
  have hdeg : M.det.natDegree ≤ r * d := by
    rw [Matrix.det_apply]
    refine natDegree_sum_le_of_forall_le _ _ (fun g _ => ?_)
    have h1 : natDegree (Equiv.Perm.sign g • ∏ i, M (g i) i) ≤ natDegree (∏ i, M (g i) i) := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign g) with sg | sg
      · rw [sg, one_smul]
      · rw [sg, Units.neg_smul, one_smul, natDegree_neg]
    refine h1.trans ((natDegree_prod_le _ _).trans ?_)
    refine (Finset.sum_le_card_nsmul _ _ r (fun i _ => hentry _ _)).trans ?_
    simp [mul_comm]
  have h0 : M.det.eval 0 = 1 := by
    have h1 : (evalRingHom (0 : k)) M.det = ((evalRingHom (0 : k)).mapMatrix M).det :=
      RingHom.map_det _ _
    have hm : (evalRingHom (0 : k)).mapMatrix M = 1 := by
      rw [← hA]
      ext a b
      simp [hM, Matrix.sum_apply, eval_finsetSum, Fin.sum_univ_succ]
    rw [hm, Matrix.det_one] at h1
    simpa using h1
  have hne : M.det ≠ 0 := by
    intro h; rw [h] at h0; simp at h0
  have hs := IsAlgClosed.splits M.det
  have hfac := hs.eq_prod_roots
  have hev := hs.eval_eq_prod_roots 0
  rw [h0] at hev
  have hnz : ∀ a ∈ M.det.roots, a ≠ 0 := by
    intro a ha h
    have := (mem_roots hne).1 ha
    rw [h, IsRoot.def, h0] at this
    exact one_ne_zero this
  have haux := prod_one_sub_inv_mul_X M.det.roots hnz
  have hfin : M.det = (M.det.roots.map (fun a => (1 : k[X]) - C a⁻¹ * X)).prod := by
    conv_lhs => rw [hfac]
    rw [← haux, mul_comm, mul_assoc, ← C_mul, mul_comm _ M.det.leadingCoeff, ← hev, C_1, mul_one]
  refine ⟨M.det.roots.toList.length, fun i => (M.det.roots.toList[i.1])⁻¹, ?_, ?_⟩
  · rw [Multiset.length_toList]
    exact (card_roots' _).trans hdeg
  · rw [Fin.prod_univ_fun_getElem M.det.roots.toList (fun a => (1 : k[X]) - C a⁻¹ * X),
      ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]
    exact hfin

end Formalism.IrreducibleCountingLemmas.TW
