import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoLowerBoundLargeConductor
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.MeanDefs

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

/- English proof (translation)
The claim follows from `Real.sInf_nonneg fun _ h => h.1`.
-/
theorem kF_nonneg (X : Dat) (K : Cst) (R : RS X.p X.n') (al be : X.TT → ℕ) : 0 ≤ X.kF K R al be :=
  Real.sInf_nonneg fun _ h => h.1

open Classical in
/- English proof (translation)
Unfold `Dat.kText`. Establish `h1 : 0 ≤ (if X.Inside aa bb then X.kF K R (fun s => (aa s - X.ccl).toNat) (fun s => (bb s - X.ccl).toNat) else 1)` using `by split_ifs`. Conclude with `kF_nonneg _ _ _ _ _`. Conclude with `zero_le_one`. Establish `h2` using `kF_nonneg X K R (fun s => (aa s + X.ccl).toNat) (fun s => (bb s + X.ccl).toNat)`.

Establish `h3 : 0 ≤ 12 * (X.N : ℝ) * X.k * X.ccl / X.b'`. Unfold `Dat.k`. Check the signs of the components of the expression. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem kText_nonneg (X : Dat) (K : Cst) (R : RS X.p X.n') (hb : 0 < X.b') (aa bb : X.TT → ℤ) :
    0 ≤ X.kText K R aa bb := by
  unfold Dat.kText
  have h1 : 0 ≤ (if X.Inside aa bb then
      X.kF K R (fun s => (aa s - X.ccl).toNat) (fun s => (bb s - X.ccl).toNat) else 1) := by
    split_ifs
    · exact kF_nonneg _ _ _ _ _
    · exact zero_le_one
  have h2 := kF_nonneg X K R (fun s => (aa s + X.ccl).toNat) (fun s => (bb s + X.ccl).toNat)
  have h3 : 0 ≤ 12 * (X.N : ℝ) * X.k * X.ccl / X.b' := by
    unfold Dat.k
    positivity
  linarith

/- English proof (translation)
Introduce `hA`. Take `⟨T0, hT0, h0⟩` from `hA 4 (by norm_num)`. Use `⟨T0, hT0, fun C₀ hC₀ => ?_⟩` and prove the remaining obligations. Take `⟨T1, hT1, h1⟩` from `h0 C₀ hC₀`. Take `⟨T2, hT2, h2⟩` from `h1 T1 T1 T1 le_rfl le_rfl le_rfl`.

Take `⟨CA, Ckap, Ct, Cs, hCA, hCkap, hCt, hCs, hAdm⟩` from `h2 T2 le_rfl`. Set `K : Cst` to `⟨C₀, T2, CA, T1, T1, T1, Ckap, Ct, Cs⟩`. Establish `hK : K.Pos` using `⟨lt_of_lt_of_le hT0 hC₀, hT2, hCA, hT1, hT1, hT1, hCkap, hCt, hCs⟩`. Take `⟨Ta, Ca, hTa, hCa, hFa⟩` from `hN1 K hK`. Take `⟨Tb, Cb, hTb, hCb, hFb⟩` from `hN2 K hK`.

Use `⟨max Ta Tb, max (max Ca Cb) K.Cmean, lt_max_of_lt_left hTa, lt_max_of_lt_left (lt_max_of_lt_left hCa), fun CH hCH => ?_⟩` and prove the remaining obligations. Introduce `p n' m TT G' N₁ Y Yb a b' bl bu ccl Dp cStar hH`. Establish `hm : m ≠ 0`. Use `hH.2.2.2.2.2.2.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hY : 1 ≤ Y` using `hH.1`. Set `X : Dat` to `⟨p, n', m, hm, TT, G', N₁, Y, Yb, a, b', bl, bu, ccl, Dp, cStar⟩`. Establish `hX : X.Hyp K.C₀ CH` using `hH`. Establish `hLPf : FactsLP K (max (max Ca Cb) K.Cmean) X` using `hFa CH (le_trans (le_max_left _ _) hCH) _ (le_trans (le_max_left _ _) (le_max_left _ _)) X hX`. Establish `hMf : FM K X` using `hFb CH (le_trans (le_max_right _ _) hCH) (max (max Ca Cb) K.Cmean) (le_trans (le_max_right _ _) (le_max_left _ _)) X hX`.

Establish `hnn : 0 ≤ (TT.card : ℝ) * N₁ / Y` using `by positivity`. Distinguish the cases in `hne : Nonempty (RS p n')`. Take `⟨R₀⟩` from `hne`. Use `⟨X.kText K R₀, kText_nonneg X K R₀ hLPf.bpos, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `hMean K hK hAdm X hMf R₀`.

Establish `h' : K.Cmean * (TT.card : ℝ) * N₁ / Y ≤ max (max Ca Cb) K.Cmean * (TT.card : ℝ) * N₁ / Y`. Use `mul_le_mul_of_nonneg_right (le_max_right (max Ca Cb) K.Cmean) hnn` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_trans h h'`. Introduce `W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hstd aw bw lam0 hW t ht`.

Set `R : RS p n'` to `⟨W, Qq, O, Kf, ι, σ, j, w, hstd⟩`. Conclude with `hR p n' R₀ R m 1 lam0 t Dp _ cStar (hLP K _ X hLPf R₀ aw bw lam0 hW t ht)`. Use `⟨fun _ _ => 0, fun _ _ => le_rfl, ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : meanKap TT m Y a bl bu (fun _ _ => (0 : ℝ)) = 0` using `by simp [meanKap]`. Rewrite using `[h0]`.

Establish `hC : 0 ≤ max (max Ca Cb) K.Cmean` using `le_of_lt (lt_max_of_lt_left (lt_max_of_lt_left hCa))`. Use `mul_nonneg hC hnn` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Introduce `W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hstd`. Conclude with `absurd ⟨(⟨W, Qq, O, Kf, ι, σ, j, w, hstd⟩ : RS p n')⟩ hne`.
-/
theorem theorem_I_of_intermediate_bounds (D : Formalism.BasicNotions.D7) (FM : Cst → Dat → Prop) (hR : LPRingIndep) (hLP : ∀ K C, MidLP K C)
    (hMean : ∀ K : Cst, K.Pos → MidMean D K (FM K)) (hN1 : ∀ K : Cst, K.Pos → TransportedAlt K (FactsLP K))
    (hN2 : ∀ K : Cst, K.Pos → TransportedAlt K (fun _ => FM K)) : SecondPartClosed D := by
  intro hA
  obtain ⟨T0, hT0, h0⟩ := hA 4 (by norm_num)
  refine ⟨T0, hT0, fun C₀ hC₀ => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C₀ hC₀
  obtain ⟨T2, hT2, h2⟩ := h1 T1 T1 T1 le_rfl le_rfl le_rfl
  obtain ⟨CA, Ckap, Ct, Cs, hCA, hCkap, hCt, hCs, hAdm⟩ := h2 T2 le_rfl
  let K : Cst := ⟨C₀, T2, CA, T1, T1, T1, Ckap, Ct, Cs⟩
  have hK : K.Pos := ⟨lt_of_lt_of_le hT0 hC₀, hT2, hCA, hT1, hT1, hT1, hCkap, hCt, hCs⟩
  obtain ⟨Ta, Ca, hTa, hCa, hFa⟩ := hN1 K hK
  obtain ⟨Tb, Cb, hTb, hCb, hFb⟩ := hN2 K hK
  refine ⟨max Ta Tb, max (max Ca Cb) K.Cmean, lt_max_of_lt_left hTa,
    lt_max_of_lt_left (lt_max_of_lt_left hCa), fun CH hCH => ?_⟩
  intro p n' m TT G' N₁ Y Yb a b' bl bu ccl Dp cStar hH
  have hm : m ≠ 0 := by
    have := hH.2.2.2.2.2.2.1
    omega
  have hY : 1 ≤ Y := hH.1
  let X : Dat := ⟨p, n', m, hm, TT, G', N₁, Y, Yb, a, b', bl, bu, ccl, Dp, cStar⟩
  have hX : X.Hyp K.C₀ CH := hH
  have hLPf : FactsLP K (max (max Ca Cb) K.Cmean) X :=
    hFa CH (le_trans (le_max_left _ _) hCH) _ (le_trans (le_max_left _ _) (le_max_left _ _)) X hX
  have hMf : FM K X :=
    hFb CH (le_trans (le_max_right _ _) hCH) (max (max Ca Cb) K.Cmean)
      (le_trans (le_max_right _ _) (le_max_left _ _)) X hX
  have hnn : 0 ≤ (TT.card : ℝ) * N₁ / Y := by positivity
  by_cases hne : Nonempty (RS p n')
  · obtain ⟨R₀⟩ := hne
    refine ⟨X.kText K R₀, kText_nonneg X K R₀ hLPf.bpos, ?_, ?_⟩
    · have h := hMean K hK hAdm X hMf R₀
      have h' : K.Cmean * (TT.card : ℝ) * N₁ / Y ≤ max (max Ca Cb) K.Cmean * (TT.card : ℝ) * N₁ / Y := by
        have := mul_le_mul_of_nonneg_right (le_max_right (max Ca Cb) K.Cmean) hnn
        calc K.Cmean * (TT.card : ℝ) * N₁ / Y = K.Cmean * ((TT.card : ℝ) * N₁ / Y) := by ring
          _ ≤ max (max Ca Cb) K.Cmean * ((TT.card : ℝ) * N₁ / Y) := this
          _ = _ := by ring
      exact le_trans h h'
    · intro W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hstd aw bw lam0 hW t ht
      let R : RS p n' := ⟨W, Qq, O, Kf, ι, σ, j, w, hstd⟩
      exact hR p n' R₀ R m 1 lam0 t Dp _ cStar (hLP K _ X hLPf R₀ aw bw lam0 hW t ht)
  · refine ⟨fun _ _ => 0, fun _ _ => le_rfl, ?_, ?_⟩
    · have h0 : meanKap TT m Y a bl bu (fun _ _ => (0 : ℝ)) = 0 := by simp [meanKap]
      rw [h0]
      have hC : 0 ≤ max (max Ca Cb) K.Cmean := le_of_lt (lt_max_of_lt_left (lt_max_of_lt_left hCa))
      have := mul_nonneg hC hnn
      calc (0 : ℝ) ≤ max (max Ca Cb) K.Cmean * ((TT.card : ℝ) * N₁ / Y) := this
        _ = _ := by ring
    · intro W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hstd
      exact absurd ⟨(⟨W, Qq, O, Kf, ι, σ, j, w, hstd⟩ : RS p n')⟩ hne

end Formalism.MainNotions.flipOneThree.Pf

end
