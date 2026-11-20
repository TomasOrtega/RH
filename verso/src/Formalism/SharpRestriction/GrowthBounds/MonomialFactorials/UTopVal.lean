import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestTMSizeOf

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

section SI

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

/- English proof (translation)
Establish `hF` using `hS.hF`. Establish `h1` using `lLL_deg_le_chain hS a b x q`. Take `⟨-, hK1, hK2, -⟩` from `hK`. Use `set v := topOf q hq with hv`. Use `set P := SegData.P X.p (X.S C0 CE1 CE2) v with hPdef`.

Establish `hc : (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ (X.S C0 CE1 CE2).bTop v / P ∨ (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ a v / P`. Establish `hA : coarseA X.p (X.S C0 CE1 CE2) b v ≤ (X.S C0 CE1 CE2).bTop v / P` using `Nat.div_le_div_right (Nat.sub_le _ _)`. Establish `hC : coarseC X.p (X.S C0 CE1 CE2) a b v ≤ a v / P` using `Nat.div_le_div_right (Nat.sub_le _ _)`. Simplify using `only [segChain, dif_neg hq]`. Rewrite using `[← hv]`.

Use `split_ifs with h2 h3 h3`. Conclude with `Or.inl ((hK2 v h3).2.1.trans hA)`. Conclude with `Or.inl (((hK1 v (not_lt.mp h3)).1).trans hA)`. Conclude with `Or.inr ((Nat.sub_le _ _).trans hC)`. Conclude with `Or.inr hC`.

Establish `hbT : ((X.S C0 CE1 CE2).bTop v : ℝ) ≤ 2 * X.L.a`. Establish `h5` using `hS.bTop v`. Establish `hb0` using `hF.b0`. Establish `hlt` using `hF.b_lt`. Establish `hpm` using `hF.p_ge`.

Establish `hm` using `hF.m4`. Establish `hm' : (4 : ℝ) ≤ X.L.m` using `by exact_mod_cast hm`. Establish `hp25 : (25 : ℝ) ≤ X.L.p` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `haT : (a v : ℝ) ≤ 2 * X.L.a`.

Establish `hmem` using `Fintype.mem_piFinset.mp hT v`. Simplify using `only [flipOneThree.Inst.winA, Finset.mem_Icc] at hmem`. Establish `h2` using `Nat.floor_le hF.win0`. Establish `h3 : (a v : ℝ) ≤ (⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℕ)` using `by exact_mod_cast hmem.2`. Combine the linear relations using `[hF.win_le]`.

Establish `hfin : ∀ N : ℕ, (N : ℝ) ≤ 2 * X.L.a → (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ N / P → ((lLL C0 CE1 CE2 X a b x).deg q : ℝ) * (P : ℝ) ≤ 2 * X.L.a`. Introduce `N hN hd`. Establish `h4 : (lLL C0 CE1 CE2 X a b x).deg q * P ≤ N` using `(Nat.mul_le_mul_right P (h1.trans hd)).trans (Nat.div_mul_le_self N P)`. Establish `h5 : (((lLL C0 CE1 CE2 X a b x).deg q * P : ℕ) : ℝ) ≤ N` using `by exact_mod_cast h4`. Move the coercions through the operations in `at h5`.

Combine the linear equalities and inequalities to obtain the conclusion. Break down `hc with hc | hc` into its components or cases. Conclude with `hfin _ hbT hc`. Conclude with `hfin _ haT hc`.
-/
private theorem lLL_deg_mul_segP_le_two_mul_a_of_kept (a : Fin X.s → ℕ) (hT : a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA))
    (b : SegBlock X.s X.r) (hK : Kept X.p X.r (X.S C0 CE1 CE2) a b) (x : Lv C0 CE1 CE2 X)
    (q : Fin (2 * X.s + 1)) (hq : (q : ℕ) ≠ 2 * X.s) :
    ((lLL C0 CE1 CE2 X a b x).deg q : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) (topOf q hq) : ℝ) ≤ 2 * X.L.a := by
  have hF := hS.hF
  have h1 := lLL_deg_le_chain hS a b x q
  obtain ⟨-, hK1, hK2, -⟩ := hK
  set v := topOf q hq with hv
  set P := SegData.P X.p (X.S C0 CE1 CE2) v with hPdef
  have hc : (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ (X.S C0 CE1 CE2).bTop v / P ∨
      (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ a v / P := by
    have hA : coarseA X.p (X.S C0 CE1 CE2) b v ≤ (X.S C0 CE1 CE2).bTop v / P :=
      Nat.div_le_div_right (Nat.sub_le _ _)
    have hC : coarseC X.p (X.S C0 CE1 CE2) a b v ≤ a v / P :=
      Nat.div_le_div_right (Nat.sub_le _ _)
    simp only [segChain, dif_neg hq]
    rw [← hv]
    split_ifs with h2 h3 h3
    · exact Or.inl ((hK2 v h3).2.1.trans hA)
    · exact Or.inl (((hK1 v (not_lt.mp h3)).1).trans hA)
    · exact Or.inr ((Nat.sub_le _ _).trans hC)
    · exact Or.inr hC
  have hbT : ((X.S C0 CE1 CE2).bTop v : ℝ) ≤ 2 * X.L.a := by
    have h5 := hS.bTop v
    have hb0 := hF.b0
    have hlt := hF.b_lt
    have hpm := hF.p_ge
    have hm := hF.m4
    have hm' : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hm
    have hp25 : (25 : ℝ) ≤ X.L.p := by nlinarith
    nlinarith
  have haT : (a v : ℝ) ≤ 2 * X.L.a := by
    have hmem := Fintype.mem_piFinset.mp hT v
    simp only [flipOneThree.Inst.winA, Finset.mem_Icc] at hmem
    have h2 := Nat.floor_le hF.win0
    have h3 : (a v : ℝ) ≤ (⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℕ) := by exact_mod_cast hmem.2
    linarith [hF.win_le]
  have hfin : ∀ N : ℕ, (N : ℝ) ≤ 2 * X.L.a → (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ N / P →
      ((lLL C0 CE1 CE2 X a b x).deg q : ℝ) * (P : ℝ) ≤ 2 * X.L.a := by
    intro N hN hd
    have h4 : (lLL C0 CE1 CE2 X a b x).deg q * P ≤ N :=
      (Nat.mul_le_mul_right P (h1.trans hd)).trans (Nat.div_mul_le_self N P)
    have h5 : (((lLL C0 CE1 CE2 X a b x).deg q * P : ℕ) : ℝ) ≤ N := by exact_mod_cast h4
    push_cast at h5
    linarith
  rcases hc with hc | hc
  · exact hfin _ hbT hc
  · exact hfin _ haT hc

/- English proof (translation)
Establish `hF` using `hS.hF`. Establish `hK'` using `hK`. Take `⟨-, hK1, -, -⟩` from `hK'`. Use `set u := uTop (X.S C0 CE1 CE2) i with hu`. Establish `hus : (u : ℕ) < X.s` using `u.2`.

Establish `hσu : (X.S C0 CE1 CE2).sigma ≤ (u : ℕ)`. Simplify using `[hu, uTop]`. Establish `hSdef : (gT C0 CE1 CE2 X b).S (lLL C0 CE1 CE2 X a b x) i = ∑ q : Fin (2 * X.s + 1), if (q : ℕ) ≤ 2 * (u : ℕ) then (lLL C0 CE1 CE2 X a b x).deg q else 0` using `rfl`. Rewrite using `[hSdef]`. Use `push_cast`.

Rewrite using `[Finset.sum_mul]`. Establish `hm' : (4 : ℝ) ≤ X.L.m` using `by exact_mod_cast hF.m4`. Establish `hpm` using `hF.p_ge`. Establish `hp : (0 : ℝ) < X.p` using `by show (0 : ℝ) < X.L.p`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hb0` using `hF.b0`. Establish `hB : (0 : ℝ) ≤ 2 * X.L.a / X.p` using `by positivity`. Establish `key : ∀ q : Fin (2 * X.s + 1), (if (q : ℕ) ≤ 2 * (u : ℕ) then ((lLL C0 CE1 CE2 X a b x).deg q : ℝ) else 0) * (SegData.P X.p (X.S C0 CE1 CE2) u : ℝ) ≤ (if (q : ℕ) = 2 * (u : ℕ) then 5 / 2 * X.L.b' else 0) + 2 * X.L.a / X.p`. Introduce `q`. Distinguish the cases in `h : (q : ℕ) ≤ 2 * (u : ℕ)`.

Rewrite using `[if_pos h]`. Distinguish the cases in `he : (q : ℕ) = 2 * (u : ℕ)`. Rewrite using `[if_pos he]`. Establish `h1` using `lLL_deg_le_chain hS a b x q`. Rewrite `h1` using `[segChain_deg_even (X.S C0 CE1 CE2) a b q u he hσu]`.

Establish `hA : coarseA X.p (X.S C0 CE1 CE2) b u ≤ (X.S C0 CE1 CE2).bTop u / SegData.P X.p (X.S C0 CE1 CE2) u` using `Nat.div_le_div_right (Nat.sub_le _ _)`. Establish `h4 : (lLL C0 CE1 CE2 X a b x).deg q * SegData.P X.p (X.S C0 CE1 CE2) u ≤ (X.S C0 CE1 CE2).bTop u` using `(Nat.mul_le_mul_right _ ((h1.trans (hK1 u hσu).1).trans hA)).trans (Nat.div_mul_le_self _ _)`. Establish `h5 : (((lLL C0 CE1 CE2 X a b x).deg q * SegData.P X.p (X.S C0 CE1 CE2) u : ℕ) : ℝ) ≤ (X.S C0 CE1 CE2).bTop u` using `by exact_mod_cast h4`. Move the coercions through the operations in `at h5`. Combine the linear relations using `[hS.bTop u]`.

Rewrite using `[if_neg he, zero_add]`. Establish `hq : (q : ℕ) ≠ 2 * X.s` using `by omega`. Establish `h2` using `lLL_deg_mul_segP_le_two_mul_a_of_kept hS a hT b hK x q hq`. Establish `hvu : topOf q hq < u`. Rewrite using `[Fin.lt_iff_val_lt_val]`.

Simplify using `only [topOf]`. Use linear arithmetic over natural numbers and integers. Establish `h3` using `P_step (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X) _ _ hvu`. Establish `h3' : ((X.p : ℕ) : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) u : ℝ) ≤ (SegData.P X.p (X.S C0 CE1 CE2) (topOf q hq) : ℝ)` using `by exact_mod_cast h3`. Rewrite using `[le_div_iff₀ hp]`.

Establish `hd0 : (0 : ℝ) ≤ ((lLL C0 CE1 CE2 X a b x).deg q : ℝ)` using `Nat.cast_nonneg _`. Use the polynomial consequences of the given equalities and inequalities. Apply the tactic sequence `rw [if_neg h, zero_mul] split_ifs <;> positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_eq_single (⟨2 * (u : ℕ), by omega⟩ : Fin (2 * X.s + 1))]`.

Simplify using the standard rewrite rules. Introduce `c _ hc`. Rewrite using `[if_neg]`. Introduce `hc'`. Conclude with `hc (Fin.ext hc')`.

Introduce `hc`. Conclude with `absurd (Finset.mem_univ _) hc`.
-/
theorem S_bound (a : Fin X.s → ℕ) (hT : a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (b : SegBlock X.s X.r)
    (hK : Kept X.p X.r (X.S C0 CE1 CE2) a b) (x : Lv C0 CE1 CE2 X) (i : Fin (X.S C0 CE1 CE2).t) :
    ((gT C0 CE1 CE2 X b).S (lLL C0 CE1 CE2 X a b x) i : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
      5 / 2 * X.L.b' + (2 * X.s + 1) * (2 * X.L.a / X.p) := by
  have hF := hS.hF
  have hK' := hK
  obtain ⟨-, hK1, -, -⟩ := hK'
  set u := uTop (X.S C0 CE1 CE2) i with hu
  have hus : (u : ℕ) < X.s := u.2
  have hσu : (X.S C0 CE1 CE2).sigma ≤ (u : ℕ) := by
    simp [hu, uTop]
  have hSdef : (gT C0 CE1 CE2 X b).S (lLL C0 CE1 CE2 X a b x) i =
      ∑ q : Fin (2 * X.s + 1), if (q : ℕ) ≤ 2 * (u : ℕ) then (lLL C0 CE1 CE2 X a b x).deg q else 0 := rfl
  rw [hSdef]
  push_cast
  rw [Finset.sum_mul]
  have hm' : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hF.m4
  have hpm := hF.p_ge
  have hp : (0 : ℝ) < X.p := by
    show (0 : ℝ) < X.L.p
    nlinarith
  have hb0 := hF.b0
  have hB : (0 : ℝ) ≤ 2 * X.L.a / X.p := by positivity
  have key : ∀ q : Fin (2 * X.s + 1),
      (if (q : ℕ) ≤ 2 * (u : ℕ) then ((lLL C0 CE1 CE2 X a b x).deg q : ℝ) else 0) *
          (SegData.P X.p (X.S C0 CE1 CE2) u : ℝ) ≤
        (if (q : ℕ) = 2 * (u : ℕ) then 5 / 2 * X.L.b' else 0) + 2 * X.L.a / X.p := by
    intro q
    by_cases h : (q : ℕ) ≤ 2 * (u : ℕ)
    · rw [if_pos h]
      by_cases he : (q : ℕ) = 2 * (u : ℕ)
      · rw [if_pos he]
        have h1 := lLL_deg_le_chain hS a b x q
        rw [segChain_deg_even (X.S C0 CE1 CE2) a b q u he hσu] at h1
        have hA : coarseA X.p (X.S C0 CE1 CE2) b u ≤
            (X.S C0 CE1 CE2).bTop u / SegData.P X.p (X.S C0 CE1 CE2) u :=
          Nat.div_le_div_right (Nat.sub_le _ _)
        have h4 : (lLL C0 CE1 CE2 X a b x).deg q * SegData.P X.p (X.S C0 CE1 CE2) u ≤
            (X.S C0 CE1 CE2).bTop u :=
          (Nat.mul_le_mul_right _ ((h1.trans (hK1 u hσu).1).trans hA)).trans (Nat.div_mul_le_self _ _)
        have h5 : (((lLL C0 CE1 CE2 X a b x).deg q * SegData.P X.p (X.S C0 CE1 CE2) u : ℕ) : ℝ) ≤
            (X.S C0 CE1 CE2).bTop u := by exact_mod_cast h4
        push_cast at h5
        linarith [hS.bTop u]
      · rw [if_neg he, zero_add]
        have hq : (q : ℕ) ≠ 2 * X.s := by omega
        have h2 := lLL_deg_mul_segP_le_two_mul_a_of_kept hS a hT b hK x q hq
        have hvu : topOf q hq < u := by
          rw [Fin.lt_iff_val_lt_val]
          simp only [topOf]
          omega
        have h3 := P_step (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X) _ _ hvu
        have h3' : ((X.p : ℕ) : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) u : ℝ) ≤
            (SegData.P X.p (X.S C0 CE1 CE2) (topOf q hq) : ℝ) := by exact_mod_cast h3
        rw [le_div_iff₀ hp]
        have hd0 : (0 : ℝ) ≤ ((lLL C0 CE1 CE2 X a b x).deg q : ℝ) := Nat.cast_nonneg _
        nlinarith
    · rw [if_neg h, zero_mul]
      split_ifs <;> positivity
  calc _ ≤ ∑ q : Fin (2 * X.s + 1),
        ((if (q : ℕ) = 2 * (u : ℕ) then 5 / 2 * X.L.b' else 0) + 2 * X.L.a / X.p) :=
        Finset.sum_le_sum (fun q _ => key q)
    _ = 5 / 2 * X.L.b' + (2 * X.s + 1) * (2 * X.L.a / X.p) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Finset.sum_eq_single (⟨2 * (u : ℕ), by omega⟩ : Fin (2 * X.s + 1))]
        · simp
        · intro c _ hc
          rw [if_neg]
          intro hc'
          exact hc (Fin.ext hc')
        · intro hc
          exact absurd (Finset.mem_univ _) hc

end SI

end Formalism.MainNotions.G.SymmetricFormBlocks

end
