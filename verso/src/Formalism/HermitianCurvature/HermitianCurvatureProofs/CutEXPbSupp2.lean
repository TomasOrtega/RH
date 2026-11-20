import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbSuppOrbit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbSuppHyp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces

open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXPbSupp

/- English proof (translation)
Use extensionality with `i j`. Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Simplify using `only [Hpk, diagonal_apply, dS, Fin.ext_iff, Fin.val_last]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem hpk_zero (k : ℕ) : Hpk k 0 = diagonal (dS (2 * 0 + k)) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, diagonal_apply, dS, Fin.ext_iff, Fin.val_last]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Establish `e : ∀ w : ℂ, (starRingEnd ℂ w * w).re = ‖w‖ ^ 2`. Introduce `w`. Rewrite using `[Complex.conj_mul']`. Use `norm_cast`. Unfold `Tz herm`.

Rewrite using `[hpk_zero]`. Simplify using `only [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_castSucc, Pi.star_apply, Complex.star_def]`. Establish `h1 : ∀ i : Fin (2 * 0 + k), dS (2 * 0 + k) i.castSucc = 1` using `fun i => by`. Unfold `dS`. Rewrite using `[if_neg (Fin.castSucc_lt_last i).ne]`.

Establish `h2 : dS (2 * 0 + k) (Fin.last (2 * 0 + k)) = -1`. Unfold `dS`. Rewrite using `[if_pos rfl]`. Simplify using `only [h1, h2, one_mul, neg_one_mul, mul_neg, Complex.add_re, Complex.neg_re, Complex.re_sum, e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tz_sum (k : ℕ) (z : Fin (2 * 0 + k + 1) → ℂ) :
    ∑ i : Fin (2 * 0 + k), ‖z i.castSucc‖ ^ 2 = ‖z (Fin.last _)‖ ^ 2 - Tz k 0 z := by
  have e : ∀ w : ℂ, (starRingEnd ℂ w * w).re = ‖w‖ ^ 2 := by
    intro w
    rw [Complex.conj_mul']
    norm_cast
  unfold Tz herm
  rw [hpk_zero]
  simp only [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_castSucc, Pi.star_apply, Complex.star_def]
  have h1 : ∀ i : Fin (2 * 0 + k), dS (2 * 0 + k) i.castSucc = 1 := fun i => by
    unfold dS
    rw [if_neg (Fin.castSucc_lt_last i).ne]
  have h2 : dS (2 * 0 + k) (Fin.last (2 * 0 + k)) = -1 := by
    unfold dS
    rw [if_pos rfl]
  simp only [h1, h2, one_mul, neg_one_mul, mul_neg, Complex.add_re, Complex.neg_re, Complex.re_sum, e]
  ring

/- English proof (translation)
Substitute `hρ` using the available equality. Unfold `Gf Q.GGl Dmin`. Rewrite using `[Matrix.det_fin_zero, Matrix.det_fin_one]`. Simplify using `only [Complex.normSq_one, mul_one]`. Both sides reduce to the same expression.
-/
theorem gf_eq_GGl (k ρ : ℕ) (hρ : ρ = 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (g : B.Mat k ρ) :
    Gf k ρ z z' g = Q.GGl k ρ z z' g := by
  subst hρ
  unfold Gf Q.GGl Dmin
  rw [Matrix.det_fin_zero, Matrix.det_fin_one]
  simp only [Complex.normSq_one, mul_one]
  rfl

/- English proof (translation)
Substitute `hρ` using the available equality. Establish `hU : μᴴ * diagonal (dS (2 * 0 + k)) * μ = diagonal (dS (2 * 0 + k))`. Establish `h` using `hμ.1`. Rewrite `h` using `[hpk_zero]`. Conclude with `h`.

Establish `hζ : Q.zetaL k 0 z z' (Fin.last 0) μ = star z ⬝ᵥ (diagonal (dS (2 * 0 + k)) *ᵥ (μ *ᵥ z'))`. Unfold `Q.zetaL herm`. Rewrite using `[hpk_zero]`. Simplify using `[fvec]`. Rewrite using `[hζ]`.

Conclude with `entry_bound μ hU z z' _ _ hT hT' (tz_sum k z) (tz_sum k z') i j`.
-/
theorem mu_bound (k ρ : ℕ) (hρ : ρ = 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (hT : 0 < Tz k ρ z) (hT' : 0 < Tz k ρ z')
    (μ : B.Mat k ρ) (hμ : μ ∈ Q.Glev k ρ (Fin.last ρ)) (i j : Fin (2 * ρ + k + 1)) :
    ‖μ i j‖ * (Tz k ρ z * Tz k ρ z') ≤ 4 * ‖z ⟨2 * ρ + k, by omega⟩‖ * ‖z' ⟨2 * ρ + k, by omega⟩‖ *
      ‖Q.zetaL k ρ z z' (Fin.last ρ) μ‖ := by
  subst hρ
  have hU : μᴴ * diagonal (dS (2 * 0 + k)) * μ = diagonal (dS (2 * 0 + k)) := by
    have h := hμ.1
    rw [hpk_zero] at h
    exact h
  have hζ : Q.zetaL k 0 z z' (Fin.last 0) μ = star z ⬝ᵥ (diagonal (dS (2 * 0 + k)) *ᵥ (μ *ᵥ z')) := by
    unfold Q.zetaL herm
    rw [hpk_zero]
    simp [fvec]
  rw [hζ]
  exact entry_bound μ hU z z' _ _ hT hT' (tz_sum k z) (tz_sum k z') i j

end Formalism.FourierDecayAlt.P.CutEXPbSupp

namespace Formalism.FourierDecayAlt.P

open CutEX CutEXPbSupp

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P p G hG`. Take `⟨⟨_, ⟨R, hR⟩, ⟨ε, hε, hεG⟩⟩, K0, hK0c, h0K0, hK0⟩` from `hG`. Choose the witnesses or unpack the hypotheses as in `⟨δ, hδ, hδK⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ K0, δ ≤ ‖w‖ := by`. Take `⟨δ, hδ, hball⟩` from `Metric.isOpen_iff.mp hK0c.isClosed.isOpen_compl 0 h0K0`. Use `⟨δ, hδ, fun w hw => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Conclude with `hball (by simpa [Metric.mem_ball, dist_zero_right] using hlt) hw`. Take `⟨M1, hM1⟩` from `hK0c.isBounded.exists_norm_le`. Use `set M0 : ℝ := max M1 1 with hM0`.

Establish `hM0pos : 0 < M0` using `lt_of_lt_of_le one_pos (le_max_right _ _)`. Use `set SR : Set (B.Mat P.k P.r) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) R with hSRdef`. Establish `hSR : IsCompact SR` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _`. Take `⟨Cg, hCg⟩` from `hSR.exists_bound_of_continuousOn (f := fun g : B.Mat P.k P.r => Gf P.k P.r p.T.base.z p.T.base.z' g) (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf p.T.base.z p.T.base.z').continuous.continuousOn`. Use `set zr := (p.T.bs P.r).z with hzr`.

Use `set zr' := (p.T.bs P.r).z' with hzr'`. Establish `hT : 0 < Tz P.k (P.r - P.r) zr` using `(p.T.bs P.r).T_pos`. Establish `hT' : 0 < Tz P.k (P.r - P.r) zr'` using `(p.T.bs P.r).T'_pos`. Use `set TT : ℝ := Tz P.k (P.r - P.r) zr * Tz P.k (P.r - P.r) zr' with hTT`. Establish `hTTpos : 0 < TT` using `mul_pos hT hT'`.

Use `set Zb : ℝ := Real.sqrt (Cg / δ ^ 2 + TT) with hZb`. Use `set Bμ : ℝ := 4 * ‖zr ⟨2 * (P.r - P.r) + P.k, by omega⟩‖ * ‖zr' ⟨2 * (P.r - P.r) + P.k, by omega⟩‖ * Zb / TT with hBμ`. Use `set c : ℝ := ε / M0 ^ 2 with hc`. Establish `hcpos : 0 < c` using `div_pos hε (by positivity)`. Use `set Bset : Set (Mt P.k (P.r - P.r)) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) Bμ with hBset`.

Use `set Aset : Set (Fin P.r → Fin P.r → ℂ) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) R with hAset`. Establish `hA : IsCompact Aset` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _`. Establish `hB : IsCompact Bset` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _`. Use `⟨(Aset ×ˢ Bset) ∩ ((fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => (Matrix.of q.1).det) ⁻¹' K0) ∩ ((fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => (Matrix.of q.2 : B.Mat P.k (P.r - P.r))) ⁻¹' Q.Glev P.k (P.r - P.r) (Fin.last _)) ∩ {q | c ≤ Q.GGl P.k (P.r - P.r) …` and prove the remaining obligations. Use `(((hA.prod hB).inter_right ?_).inter_right ?_).inter_right ?_` and prove the remaining obligations.

Conclude with `hK0c.isClosed.preimage (Continuous.matrix_det continuous_fst)`. Conclude with `(Formalism.FourierDecayAlt.P.JCTx5.glev_closed _ _ _).preimage continuous_snd`. Conclude with `isClosed_le continuous_const ((Formalism.FourierDecayAlt.P.Qx8.GGl_cont _ _ _ _).comp continuous_snd)`. Introduce and unpack `q ⟨⟨⟨_, hq1⟩, _⟩, hq3⟩`. Use `⟨fun h0 => h0K0 ?_, lt_of_lt_of_le hcpos hq3⟩` and prove the remaining obligations.

Establish `: (Matrix.of q.1).det ∈ K0` using `hq1`. Rewrite `this` using `[h0]`. Then use the resulting hypothesis. Introduce `q hdet hμ hpb`. Take `⟨g, hg, hGg, u, hu, hb, hD, hGf⟩` from `CutEXPbSupp.orbit_point p G (Matrix.of q.1) (Matrix.of q.2) hdet hμ hpb`. Establish `hgR : B.gN g ≤ R` using `hR g hg hGg`.

Establish `hDK : (Matrix.of q.1).det ∈ K0` using `hD ▸ hK0 g hg hGg`. Establish `hdetδ : δ ≤ ‖(Matrix.of q.1).det‖` using `hδK _ hDK`. Establish `hdetM : ‖(Matrix.of q.1).det‖ ≤ M0` using `(hM1 _ hDK).trans (le_max_left _ _)`. Establish `hGε : ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' g` using `hεG g hg hGg`. Establish `hgSR : g ∈ SR`.

Rewrite using `[hSRdef]`. Conclude with `fun a _ b _ => by`. Rewrite using `[Metric.mem_closedBall, dist_zero_right]`. Conclude with `(CutEXPbSupp.norm_entry_le_gN g a b).trans hgR`. Establish `hGC : Gf P.k P.r p.T.base.z p.T.base.z' g ≤ Cg` using `(le_abs_self _).trans (hCg g hgSR)`.

Use `set Gr := Gf P.k (P.r - P.r) zr zr' (Matrix.of q.2) with hGr`. Establish `hns : Complex.normSq (Matrix.of q.1).det = ‖(Matrix.of q.1).det‖ ^ 2` using `Complex.normSq_eq_norm_sq _`. Establish `hGr_pos : 0 < Gr`. Assume the negation of the conclusion as `hle`. Use `push Not at hle`.

Establish `: Gf P.k P.r p.T.base.z p.T.base.z' g ≤ 0`. Rewrite using `[hGf]`. Conclude with `mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) hle`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hGGl : Q.GGl P.k (P.r - P.r) zr zr' (Matrix.of q.2) = Gr` using `(CutEXPbSupp.gf_eq_GGl P.k (P.r - P.r) (Nat.sub_self _) zr zr' _).symm`.

Establish `hδ2 : δ ^ 2 ≤ Complex.normSq (Matrix.of q.1).det`. Rewrite using `[hns]`. Conclude with `pow_le_pow_left₀ hδ.le hdetδ 2`. Establish `hM2 : Complex.normSq (Matrix.of q.1).det ≤ M0 ^ 2`. Rewrite using `[hns]`.

Conclude with `pow_le_pow_left₀ (norm_nonneg _) hdetM 2`. Establish `hGr_up : Gr ≤ Cg / δ ^ 2`. Rewrite using `[le_div_iff₀ (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Establish `hGr_lo : c ≤ Gr`.

Rewrite using `[hc, div_le_iff₀ (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Establish `hζ : ‖Q.zetaL P.k (P.r - P.r) zr zr' (Fin.last _) (Matrix.of q.2)‖ ≤ Zb`. Rewrite using `[Complex.norm_def, hZb]`. Use `Real.sqrt_le_sqrt ?_` and prove the remaining obligations.

Establish `e : Q.GGl P.k (P.r - P.r) zr zr' (Matrix.of q.2) = Complex.normSq (Q.zetaL P.k (P.r - P.r) zr zr' (Fin.last _) (Matrix.of q.2)) - TT` using `rfl`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨u, hu, ⟨⟨⟨?_, ?_⟩, hμ⟩, ?_⟩⟩` and prove the remaining obligations. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [hAset, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]`.

Conclude with `fun a b => (hb a b).trans hgR`. Simplify using `only [hBset, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]`. Introduce `a b`. Establish `hm` using `CutEXPbSupp.mu_bound P.k (P.r - P.r) (Nat.sub_self _) zr zr' hT hT' (Matrix.of q.2) hμ a b`. Rewrite using `[hBμ, le_div_iff₀ hTTpos]`.

Use `hm.trans ?_` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_left hζ (by positivity)`. Use `show (Matrix.of (Matrix.of.symm (Matrix.of q.1 * u))).det ∈ K0`. Rewrite using `[Equiv.apply_symm_apply, Matrix.det_mul, Formalism.DoubleCosetMeasures.isUpUni_det ℂ hu, mul_one]`. Conclude with `hDK`.

Use `show c ≤ Q.GGl P.k (P.r - P.r) zr zr' (Matrix.of q.2)`. Rewrite using `[hGGl]`. Conclude with `hGr_lo`.
-/
theorem pullback_support : CutEX.PbSupp := by
  intro Wp Wq _ _ _ _ _ _ P p G hG
  obtain ⟨⟨_, ⟨R, hR⟩, ⟨ε, hε, hεG⟩⟩, K0, hK0c, h0K0, hK0⟩ := hG

  obtain ⟨δ, hδ, hδK⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ K0, δ ≤ ‖w‖ := by
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hK0c.isClosed.isOpen_compl 0 h0K0
    refine ⟨δ, hδ, fun w hw => ?_⟩
    by_contra hlt
    push Not at hlt
    exact hball (by simpa [Metric.mem_ball, dist_zero_right] using hlt) hw

  obtain ⟨M1, hM1⟩ := hK0c.isBounded.exists_norm_le
  set M0 : ℝ := max M1 1 with hM0
  have hM0pos : 0 < M0 := lt_of_lt_of_le one_pos (le_max_right _ _)

  set SR : Set (B.Mat P.k P.r) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) R
    with hSRdef
  have hSR : IsCompact SR := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨Cg, hCg⟩ := hSR.exists_bound_of_continuousOn
    (f := fun g : B.Mat P.k P.r => Gf P.k P.r p.T.base.z p.T.base.z' g)
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf p.T.base.z p.T.base.z').continuous.continuousOn

  set zr := (p.T.bs P.r).z with hzr
  set zr' := (p.T.bs P.r).z' with hzr'
  have hT : 0 < Tz P.k (P.r - P.r) zr := (p.T.bs P.r).T_pos
  have hT' : 0 < Tz P.k (P.r - P.r) zr' := (p.T.bs P.r).T'_pos
  set TT : ℝ := Tz P.k (P.r - P.r) zr * Tz P.k (P.r - P.r) zr' with hTT
  have hTTpos : 0 < TT := mul_pos hT hT'
  set Zb : ℝ := Real.sqrt (Cg / δ ^ 2 + TT) with hZb
  set Bμ : ℝ := 4 * ‖zr ⟨2 * (P.r - P.r) + P.k, by omega⟩‖ * ‖zr' ⟨2 * (P.r - P.r) + P.k, by omega⟩‖ * Zb / TT
    with hBμ
  set c : ℝ := ε / M0 ^ 2 with hc
  have hcpos : 0 < c := div_pos hε (by positivity)
  set Bset : Set (Mt P.k (P.r - P.r)) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) Bμ with hBset
  set Aset : Set (Fin P.r → Fin P.r → ℂ) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) R with hAset
  have hA : IsCompact Aset := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hB : IsCompact Bset := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine ⟨(Aset ×ˢ Bset) ∩ ((fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => (Matrix.of q.1).det) ⁻¹' K0) ∩
      ((fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => (Matrix.of q.2 : B.Mat P.k (P.r - P.r))) ⁻¹'
        Q.Glev P.k (P.r - P.r) (Fin.last _)) ∩
      {q | c ≤ Q.GGl P.k (P.r - P.r) zr zr' (Matrix.of q.2)}, ?_, ?_, ?_⟩
  · refine (((hA.prod hB).inter_right ?_).inter_right ?_).inter_right ?_
    · exact hK0c.isClosed.preimage (Continuous.matrix_det continuous_fst)
    · exact (Formalism.FourierDecayAlt.P.JCTx5.glev_closed _ _ _).preimage continuous_snd
    · exact isClosed_le continuous_const ((Formalism.FourierDecayAlt.P.Qx8.GGl_cont _ _ _ _).comp continuous_snd)
  · rintro q ⟨⟨⟨_, hq1⟩, _⟩, hq3⟩
    refine ⟨fun h0 => h0K0 ?_, lt_of_lt_of_le hcpos hq3⟩
    have : (Matrix.of q.1).det ∈ K0 := hq1
    rwa [h0] at this
  · intro q hdet hμ hpb
    obtain ⟨g, hg, hGg, u, hu, hb, hD, hGf⟩ := CutEXPbSupp.orbit_point p G (Matrix.of q.1) (Matrix.of q.2) hdet hμ hpb
    have hgR : B.gN g ≤ R := hR g hg hGg
    have hDK : (Matrix.of q.1).det ∈ K0 := hD ▸ hK0 g hg hGg
    have hdetδ : δ ≤ ‖(Matrix.of q.1).det‖ := hδK _ hDK
    have hdetM : ‖(Matrix.of q.1).det‖ ≤ M0 := (hM1 _ hDK).trans (le_max_left _ _)
    have hGε : ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' g := hεG g hg hGg
    have hgSR : g ∈ SR := by
      rw [hSRdef]
      exact fun a _ b _ => by
        rw [Metric.mem_closedBall, dist_zero_right]; exact (CutEXPbSupp.norm_entry_le_gN g a b).trans hgR
    have hGC : Gf P.k P.r p.T.base.z p.T.base.z' g ≤ Cg := (le_abs_self _).trans (hCg g hgSR)
    set Gr := Gf P.k (P.r - P.r) zr zr' (Matrix.of q.2) with hGr
    have hns : Complex.normSq (Matrix.of q.1).det = ‖(Matrix.of q.1).det‖ ^ 2 := Complex.normSq_eq_norm_sq _
    have hGr_pos : 0 < Gr := by
      by_contra hle
      push Not at hle
      have : Gf P.k P.r p.T.base.z p.T.base.z' g ≤ 0 := by
        rw [hGf]; exact mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) hle
      linarith
    have hGGl : Q.GGl P.k (P.r - P.r) zr zr' (Matrix.of q.2) = Gr :=
      (CutEXPbSupp.gf_eq_GGl P.k (P.r - P.r) (Nat.sub_self _) zr zr' _).symm
    have hδ2 : δ ^ 2 ≤ Complex.normSq (Matrix.of q.1).det := by
      rw [hns]; exact pow_le_pow_left₀ hδ.le hdetδ 2
    have hM2 : Complex.normSq (Matrix.of q.1).det ≤ M0 ^ 2 := by
      rw [hns]; exact pow_le_pow_left₀ (norm_nonneg _) hdetM 2
    have hGr_up : Gr ≤ Cg / δ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      calc Gr * δ ^ 2 ≤ Gr * Complex.normSq (Matrix.of q.1).det := mul_le_mul_of_nonneg_left hδ2 hGr_pos.le
        _ = Gf P.k P.r p.T.base.z p.T.base.z' g := by rw [hGf, mul_comm]
        _ ≤ Cg := hGC
    have hGr_lo : c ≤ Gr := by
      rw [hc, div_le_iff₀ (by positivity)]
      calc ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' g := hGε
        _ = Complex.normSq (Matrix.of q.1).det * Gr := hGf
        _ ≤ M0 ^ 2 * Gr := mul_le_mul_of_nonneg_right hM2 hGr_pos.le
        _ = Gr * M0 ^ 2 := mul_comm _ _
    have hζ : ‖Q.zetaL P.k (P.r - P.r) zr zr' (Fin.last _) (Matrix.of q.2)‖ ≤ Zb := by
      rw [Complex.norm_def, hZb]
      refine Real.sqrt_le_sqrt ?_
      have e : Q.GGl P.k (P.r - P.r) zr zr' (Matrix.of q.2) =
          Complex.normSq (Q.zetaL P.k (P.r - P.r) zr zr' (Fin.last _) (Matrix.of q.2)) - TT := rfl
      linarith
    refine ⟨u, hu, ⟨⟨⟨?_, ?_⟩, hμ⟩, ?_⟩⟩
    · refine ⟨?_, ?_⟩
      · simp only [hAset, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
        exact fun a b => (hb a b).trans hgR
      · simp only [hBset, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
        intro a b
        have hm := CutEXPbSupp.mu_bound P.k (P.r - P.r) (Nat.sub_self _) zr zr' hT hT' (Matrix.of q.2) hμ a b
        rw [hBμ, le_div_iff₀ hTTpos]
        refine hm.trans ?_
        exact mul_le_mul_of_nonneg_left hζ (by positivity)
    · show (Matrix.of (Matrix.of.symm (Matrix.of q.1 * u))).det ∈ K0
      rw [Equiv.apply_symm_apply, Matrix.det_mul, Formalism.DoubleCosetMeasures.isUpUni_det ℂ hu, mul_one]
      exact hDK
    · show c ≤ Q.GGl P.k (P.r - P.r) zr zr' (Matrix.of q.2)
      rw [hGGl]; exact hGr_lo

end Formalism.FourierDecayAlt.P
