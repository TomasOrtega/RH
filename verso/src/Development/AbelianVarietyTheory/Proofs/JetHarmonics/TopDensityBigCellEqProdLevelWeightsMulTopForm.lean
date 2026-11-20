import Mathlib
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory.TopDensity

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

/- English proof (translation)
Replace the relevant objects with their definitions. Use linear arithmetic over natural numbers and integers. Supply the required witnesses or components. Replace the relevant objects with their definitions. Rewrite the conclusion repeatedly using the stated equalities.

Supply the required witnesses or components. Supply the required witnesses or components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem RR_top_diag (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (γ : C.LPt) :
    ∃ x : ℝ, 0 ≤ x ∧ p.RR H (P.r + 1) w γ γ = (x : ℂ) := by
  unfold KB.Pl.RR D.RRplace
  split_ifs with h1 h2 h3 h4
  · omega
  · exact ⟨_, sq_nonneg _, Formalism.FourierDecayAlt.P.TBBx2.Tri.hsInner_self _⟩
  · unfold Top.topOf
    simp_rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.hsInner_self, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
    exact ⟨_, Finset.sum_nonneg fun e _ => Finset.sum_nonneg fun ρ _ =>
      mul_nonneg (mul_self_nonneg _) (sq_nonneg _), rfl⟩
  · exact ⟨0, le_rfl, by simp⟩
  · exact ⟨0, le_rfl, by simp⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem RR_top_zero (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (γ : C.LPt)
    (hv : ∀ F, p.V F γ = 0) : p.RR H (P.r + 1) w γ γ = 0 := by
  have hv' : ∀ F, D.vecV p.T.base p.ν' p.m₀ F γ = 0 := hv
  have h0 : B.hsInner (0 : Wq →L[ℂ] Wp) 0 = 0 := by
    unfold B.hsInner B.hsVec
    have : (WithLp.toLp 2 fun i : Fin (Module.finrank ℂ Wq) =>
        (0 : Wq →L[ℂ] Wp) (stdOrthonormalBasis ℂ Wq i)) = 0 := by
      simp; rfl
    rw [this, inner_zero_right]
  unfold KB.Pl.RR D.RRplace
  split_ifs with h1 h2 h3 h4
  · omega
  · rw [hv', h0]
  · unfold Top.topOf
    refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun ρ _ => ?_
    rw [hv', ContinuousLinearMap.comp_zero, h0, mul_zero]
  · rfl
  · rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem V_bigPt_zero (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ)
    (hζ : Complex.normSq (c (Fin.last P.r)) ≤ TBB.TTp p) : p.V F (TBB.bigPt P.r c) = 0 := by
  show D.vecV p.T.base p.ν' p.m₀ F (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = 0
  unfold D.vecV
  rw [dif_neg]
  rintro ⟨-, hG⟩
  have := Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG
  exact absurd this (not_lt.2 hζ)

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Substitute using the available equality. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem nPt_eq_prod (P : M.Par) (c : Fin (P.r + 1) → ℂ) (hζ : P.T * P.T' ≤ Complex.normSq (c (Fin.last P.r))) :
    TBB.nPt P.k P.r (P.T * P.T') (TBB.bigPt P.r c) = ∏ i : Fin (P.r + 1), KB.levW P ((i : ℕ) + 1) (c i) := by
  unfold TBB.nPt
  have e : D.ptGG (P.T * P.T') (TBB.bigPt P.r c) = Complex.normSq (c (Fin.last P.r)) - P.T * P.T' := by
    unfold D.ptGG
    rw [Formalism.FourierDecayAlt.P.CutBP.ptLast_bigPt]
  rw [e]
  unfold TBB.bigPt
  rw [Formalism.FourierDecayAlt.P.CutBP.level_product_of_constant_weights]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold KB.levW
  rw [add_comm 1 (i : ℕ)]
  split_ifs with h
  · have hi : i = Fin.last P.r := Fin.ext (by simp only [Fin.val_last]; omega)
    subst hi
    unfold B2.zWeight
    rw [if_pos hζ]
  · rfl

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem levW_nonneg (P : M.Par) (i : ℕ) (c : ℂ) : 0 ≤ KB.levW P i c := by
  unfold KB.levW B2.zWeight
  split_ifs with h1 h2
  · exact pow_nonneg (sub_nonneg.2 h2) _
  · exact le_rfl
  · exact zpow_nonneg (norm_nonneg _) _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem topDensity_eq : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ), (∀ a, c a ≠ 0) → TBB.Ew p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c) = (∏ i : Fin (P.r + 1), KB.levW P ((i : ℕ) + 1) (c i)) * (p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c)).re ∧ (p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c)).im = 0 ∧ 0 ≤ (p.RR H (P.r + 1) w (TBB.bigPt P.r c) (TBB.bigPt P.r c)).re := by
  intro Wp Wq _ _ _ _ _ _ P p H w c _
  obtain ⟨x, hx, hRR⟩ := RR_top_diag p H w (TBB.bigPt P.r c)
  refine ⟨?_, by rw [hRR, Complex.ofReal_im], by rw [hRR, Complex.ofReal_re]; exact hx⟩
  have hTT : TBB.TTp p = P.T * P.T' := by
    unfold TBB.TTp
    rw [p.hP.2.2.2.1, p.hP.2.2.2.2.1]
  by_cases hζ : P.T * P.T' ≤ Complex.normSq (c (Fin.last P.r))
  · have hn : TBB.normC (fun _ => 1) w = 1 := by
      unfold TBB.normC
      simp
    unfold TBB.Ew TBB.NP
    rw [hn, hTT, nPt_eq_prod P c hζ, div_one,
      Real.mul_self_sqrt (Finset.prod_nonneg fun i _ => levW_nonneg P _ _), Complex.re_ofReal_mul]
  · have h0 := RR_top_zero p H w (TBB.bigPt P.r c) fun F =>
      V_bigPt_zero p F c (by rw [hTT]; exact (not_le.1 hζ).le)
    unfold TBB.Ew TBB.NP
    rw [h0]
    simp

end GlobalTheory.TopDensity
