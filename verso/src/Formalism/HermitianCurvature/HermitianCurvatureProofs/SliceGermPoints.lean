import Formalism.HermitianCurvature.HermitianCurvatureProofs.YGSlice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableBlockIntegrand
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceOrbitalBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.G MeasureTheory

noncomputable section

section tr

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Substitute `hρ` using the available equality. Rewrite using `[Formalism.FourierDecayAlt.P.JCTx5.castM_rfl]`.
-/
theorem phiFun_tr {k p s ρ ρ' r : ℕ} (hρ : ρ = ρ') (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (e : r = p + s + ρ) (e' : r = p + s + ρ')
    (Z : G.Mat s) (γ : B.Mat k ρ) :
    U.PhiFun k ρ' σ d (D.castV e' z) (D.castV e' z') (D.castF e'.symm F) Z (D.castM hρ γ) =
      U.PhiFun k ρ σ d (D.castV e z) (D.castV e z') (D.castF e.symm F) Z γ := by
  subst hρ
  rw [Formalism.FourierDecayAlt.P.JCTx5.castM_rfl]

end tr

/- English proof (translation)
Establish `h1 : Module.finrank ℝ (UT (m + 1 + 1) → ℂ) = Fintype.card (UT (m + 1 + 1)) * 2`. Rewrite using `[Module.finrank_pi_fintype]`. Simplify using `[Complex.finrank_real_complex]`. Establish `h2` using `Formalism.FourierDecayAlt.P.Dx2.SL.card_UT (m + 1 + 1)`. Establish `h3 : ((Fintype.card (UT (m + 1 + 1)) * 2 : ℕ) : ℝ) = ((m : ℝ) + 2) * ((m : ℝ) + 1)`.

Establish `: Fintype.card (UT (m + 1 + 1)) * 2 = (m + 2) * (m + 1)`. Rewrite using `[mul_comm, h2, show m + 1 + 1 - 1 = m + 1 by omega]`. Rewrite using `[this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h1, h3]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem finrank_UT_lt (m : ℕ) (a : ℝ) (ha : ((m : ℝ) + 1) * ((m : ℝ) + 4) < a) :
    (Module.finrank ℝ (UT (m + 1 + 1) → ℂ) : ℝ) < a := by
  have h1 : Module.finrank ℝ (UT (m + 1 + 1) → ℂ) = Fintype.card (UT (m + 1 + 1)) * 2 := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
  have h2 := Formalism.FourierDecayAlt.P.Dx2.SL.card_UT (m + 1 + 1)
  have h3 : ((Fintype.card (UT (m + 1 + 1)) * 2 : ℕ) : ℝ) = ((m : ℝ) + 2) * ((m : ℝ) + 1) := by
    have : Fintype.card (UT (m + 1 + 1)) * 2 = (m + 2) * (m + 1) := by
      rw [mul_comm, h2, show m + 1 + 1 - 1 = m + 1 by omega]
    rw [this]; push_cast; ring
  rw [h1, h3]
  nlinarith

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.G MeasureTheory Formalism.FourierDecayAlt.P.FormNormSumIdentities

/- English proof (translation)
Introduce `k r E _ _ _ z z' F h' m ρ e1 V _ _ _ Φ L γ Kc K a hh' hKc ha hΦ hL q hq hint`. Establish `hW : (G.wMat (m + 1)).det ≠ 0` using `(Formalism.FourierDecayAlt.P.Ux3.wMat_det (m + 1)).ne_zero`. Break down `q with ⟨t, c⟩ | w0` into its components or cases. Take `⟨ht, hcK⟩` from `hq`. Establish `hc0 : c ≠ 0`.

Introduce and unpack `rfl`. Apply `hKc` to reduce the goal to its premises. Simplify using `using hcK`. Establish `hne : ∀ p, G.detM (G.orbM (m + 1) t c p) ≠ 0`. Introduce `p`.

Rewrite using `[Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_orbM]`. Conclude with `mul_ne_zero hW (fun h0 => hKc (h0 ▸ hcK))`. Establish `himg : ∀ p, G.detM (G.orbM (m + 1) t c p) ∈ (fun D => (G.wMat (m + 1)).det * D) '' Kc` using `fun p => ⟨c * t ^ (m + 1), hcK, (Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_orbM _ _ _ _).symm⟩`. Establish `hI` using `integrable_blockIntegrand U.betaU m Φ t c ht K a ha (fun p => (hΦ _ (hne p)).1) (fun p => (hΦ _ (hne p)).2)`. Use `show L (((kapB m : ℝ) : ℂ) • G.OmBlock U.betaU (m + 1) Φ t c) = _`.

Rewrite using `[L.map_smul, clm_omBlock L U.betaU (m + 1) Φ t c hI]`. Establish `hloc : D.IsLocPt (ptG h' m (Sum.inl (t, c))) (D.ptSize (ptG h' m (Sum.inl (t, c))))`. Use `⟨fun b hb => ?_, rfl⟩` and prove the remaining obligations. Simplify using `only [ptG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb`. Break down `hb with hb | hb | hb` into its components or cases.

Conclude with `hh'.1 b hb`. Substitute `hb; exact ⟨by omega, ht⟩` using the available equality. Substitute `hb` using the available equality. Conclude with `⟨le_rfl, hc0⟩`. Establish `hle : D.ptSize (ptG h' m (Sum.inl (t, c))) ≤ r` using `by rw [ptSize_ptG]; omega`.

Establish `hSB` using `Formalism.FourierDecayAlt.P.slice_orbital_block k r E z z' F h' (ptG h' m (Sum.inl (t, c))) m t c rfl hle (D.castM (by rw [ptSize_ptG]; omega) γ) hloc hint`. Rewrite using `[hSB]`. Use `congr 1`. Unfold `G.OmBlock`. Use `congr 1`.

Use function extensionality and compare the values at `p`. Simplify using `only [G.blockIntegrand]`. Use `congr 1`. Establish `hp` using `hL _ (hne p) (himg p)`. Simplify using `only [G.orbM] at hp`.

Rewrite using `[hp]`. Conclude with `(phiFun_tr (by rw [ptSize_ptG]; omega) _ _ z z' F _ _ _ γ).symm`. Take `⟨D0, hDK, hz⟩` from `hq`. Establish `hz0 : w0 ≠ 0`. Introduce and unpack `rfl`.

Apply `hKc` to reduce the goal to its premises. Establish `: (0 : ℂ) = (-1) ^ (m + 3) * D0` using `by simpa using hz`. Establish `h1 : D0 = 0`. Break down `mul_eq_zero.1 this.symm with h | h` into its components or cases. Conclude with `absurd h (pow_ne_zero _ (by norm_num))`.

Conclude with `h`. Conclude with `h1 ▸ hDK`. Establish `hne : ∀ v, G.detM (Formalism.FourierDecayAlt.P.JCTx6.Pos.Zv (m + 1) w0 v) ≠ 0`. Introduce `v`. Use `Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_longM m w0 D0 hz v` as an intermediate fact.

Use `show G.detM (Formalism.FourierDecayAlt.P.OrbitTailEstimates.longM (m + 1 + 1) w0 v) ≠ 0`. Rewrite using `[this]`. Conclude with `mul_ne_zero hW (fun h0 => hKc (h0 ▸ hDK))`. Establish `himg : ∀ v, G.detM (Formalism.FourierDecayAlt.P.JCTx6.Pos.Zv (m + 1) w0 v) ∈ (fun D => (G.wMat (m + 1)).det * D) '' Kc` using `fun v => ⟨D0, hDK, (Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_longM m w0 D0 hz v).symm⟩`. Establish `hI` using `integrable_longIntegrand (m + 1) Φ w0 hz0 K a (finrank_UT_lt m a ha) (fun v => (hΦ _ (hne v)).1) (fun v => (hΦ _ (hne v)).2)`.

Use `show L (((Real.pi ^ ((m + 2) * (m + 1) / 2) : ℝ) : ℂ) • G.OmLong U.betaU (m + 1) Φ w0) = _`. Rewrite using `[L.map_smul, clm_omLong L U.betaU (m + 1) Φ w0 hI]`. Establish `hloc : D.IsLocPt (ptG h' m (Sum.inr w0)) (D.ptSize (ptG h' m (Sum.inr w0)))`. Use `⟨fun b hb => ?_, rfl⟩` and prove the remaining obligations. Simplify using `only [ptG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb`.

Break down `hb with hb | hb` into its components or cases. Conclude with `hh'.1 b hb`. Substitute `hb; exact ⟨by omega, hz0⟩` using the available equality. Establish `hle : D.ptSize (ptG h' m (Sum.inr w0)) ≤ r` using `by rw [ptSize_ptG]; omega`. Establish `hSO` using `Formalism.FourierDecayAlt.P.slice_measure_identity k r E z z' F h' (ptG h' m (Sum.inr w0)) (m + 1) w0 rfl hle (D.castM (by rw [ptSize_ptG]; omega) γ) hloc hint`.

Rewrite using `[hSO]`. Use `congr 1`. Unfold `G.OmLong`. Use `congr 1`. Use function extensionality and compare the values at `v`.

Use `congr 1`. Establish `hp` using `hL _ (hne v) (himg v)`. Conclude with `hp.trans (phiFun_tr (by rw [ptSize_ptG]; omega) _ _ z z' F _ _ _ γ).symm`.
-/
theorem slice_germ_points : Formalism.FourierDecayAlt.P.FormNormSumIdentities.YGSlice := by
  intro k r E _ _ _ z z' F h' m ρ e1 V _ _ _ Φ L γ Kc K a hh' hKc ha hΦ hL q hq hint
  have hW : (G.wMat (m + 1)).det ≠ 0 := (Formalism.FourierDecayAlt.P.Ux3.wMat_det (m + 1)).ne_zero
  rcases q with ⟨t, c⟩ | w0
  · obtain ⟨ht, hcK⟩ := hq
    have hc0 : c ≠ 0 := by
      rintro rfl; apply hKc; simpa using hcK
    have hne : ∀ p, G.detM (G.orbM (m + 1) t c p) ≠ 0 := by
      intro p; rw [Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_orbM]
      exact mul_ne_zero hW (fun h0 => hKc (h0 ▸ hcK))
    have himg : ∀ p, G.detM (G.orbM (m + 1) t c p) ∈ (fun D => (G.wMat (m + 1)).det * D) '' Kc :=
      fun p => ⟨c * t ^ (m + 1), hcK, (Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_orbM _ _ _ _).symm⟩
    have hI := integrable_blockIntegrand U.betaU m Φ t c ht K a ha (fun p => (hΦ _ (hne p)).1)
      (fun p => (hΦ _ (hne p)).2)
    show L (((kapB m : ℝ) : ℂ) • G.OmBlock U.betaU (m + 1) Φ t c) = _
    rw [L.map_smul, clm_omBlock L U.betaU (m + 1) Φ t c hI]
    have hloc : D.IsLocPt (ptG h' m (Sum.inl (t, c))) (D.ptSize (ptG h' m (Sum.inl (t, c)))) := by
      refine ⟨fun b hb => ?_, rfl⟩
      simp only [ptG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with hb | hb | hb
      · exact hh'.1 b hb
      · subst hb; exact ⟨by omega, ht⟩
      · subst hb; exact ⟨le_rfl, hc0⟩
    have hle : D.ptSize (ptG h' m (Sum.inl (t, c))) ≤ r := by rw [ptSize_ptG]; omega
    have hSB := Formalism.FourierDecayAlt.P.slice_orbital_block k r E z z' F h' (ptG h' m (Sum.inl (t, c))) m t c rfl hle
      (D.castM (by rw [ptSize_ptG]; omega) γ) hloc hint
    rw [hSB]
    congr 1
    unfold G.OmBlock
    congr 1
    funext p
    simp only [G.blockIntegrand]
    congr 1
    have hp := hL _ (hne p) (himg p)
    simp only [G.orbM] at hp
    rw [hp]
    exact (phiFun_tr (by rw [ptSize_ptG]; omega) _ _ z z' F _ _ _ γ).symm
  · obtain ⟨D0, hDK, hz⟩ := hq
    have hz0 : w0 ≠ 0 := by
      rintro rfl
      apply hKc
      have : (0 : ℂ) = (-1) ^ (m + 3) * D0 := by simpa using hz
      have h1 : D0 = 0 := by
        rcases mul_eq_zero.1 this.symm with h | h
        · exact absurd h (pow_ne_zero _ (by norm_num))
        · exact h
      exact h1 ▸ hDK
    have hne : ∀ v, G.detM (Formalism.FourierDecayAlt.P.JCTx6.Pos.Zv (m + 1) w0 v) ≠ 0 := by
      intro v
      have := Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_longM m w0 D0 hz v
      show G.detM (Formalism.FourierDecayAlt.P.OrbitTailEstimates.longM (m + 1 + 1) w0 v) ≠ 0
      rw [this]
      exact mul_ne_zero hW (fun h0 => hKc (h0 ▸ hDK))
    have himg : ∀ v, G.detM (Formalism.FourierDecayAlt.P.JCTx6.Pos.Zv (m + 1) w0 v) ∈ (fun D => (G.wMat (m + 1)).det * D) '' Kc :=
      fun v => ⟨D0, hDK, (Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_longM m w0 D0 hz v).symm⟩
    have hI := integrable_longIntegrand (m + 1) Φ w0 hz0 K a (finrank_UT_lt m a ha)
      (fun v => (hΦ _ (hne v)).1) (fun v => (hΦ _ (hne v)).2)
    show L (((Real.pi ^ ((m + 2) * (m + 1) / 2) : ℝ) : ℂ) • G.OmLong U.betaU (m + 1) Φ w0) = _
    rw [L.map_smul, clm_omLong L U.betaU (m + 1) Φ w0 hI]
    have hloc : D.IsLocPt (ptG h' m (Sum.inr w0)) (D.ptSize (ptG h' m (Sum.inr w0))) := by
      refine ⟨fun b hb => ?_, rfl⟩
      simp only [ptG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with hb | hb
      · exact hh'.1 b hb
      · subst hb; exact ⟨by omega, hz0⟩
    have hle : D.ptSize (ptG h' m (Sum.inr w0)) ≤ r := by rw [ptSize_ptG]; omega
    have hSO := Formalism.FourierDecayAlt.P.slice_measure_identity k r E z z' F h' (ptG h' m (Sum.inr w0)) (m + 1) w0 rfl hle
      (D.castM (by rw [ptSize_ptG]; omega) γ) hloc hint
    rw [hSO]
    congr 1
    unfold G.OmLong
    congr 1
    funext v
    congr 1
    have hp := hL _ (hne v) (himg v)
    exact hp.trans (phiFun_tr (by rw [ptSize_ptG]; omega) _ _ z z' F _ _ _ γ).symm

end Formalism.FourierDecayAlt.P
