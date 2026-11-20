import Formalism.HermitianCurvature.HermitianCurvatureProofs.AsmCastVCastV

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨W0, F', hU, hgU, hF', hag⟩` from `hF g₀ hg₀`. Establish `hc : ContinuousAt F' g₀` using `(hF'.continuousOn).continuousAt (hU.mem_nhds hgU)`. Use `(hc.continuousWithinAt (s := B.GV k r)).congr_of_eventuallyEq ?_ (hag g₀ hgU hg₀)` and prove the remaining obligations. Use `filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with g hgU' hgG`.

Conclude with `hag g hgU' hgG`.
-/
theorem asm_contOn_of_ckOn {r : ℕ} {m : ℕ∞} {F : B.Mat k r → E} (hF : B.CkOn m (B.GV k r) F) :
    ContinuousOn F (B.GV k r) := by
  intro g₀ hg₀
  obtain ⟨W0, F', hU, hgU, hF', hag⟩ := hF g₀ hg₀
  have hc : ContinuousAt F' g₀ := (hF'.continuousOn).continuousAt (hU.mem_nhds hgU)
  refine (hc.continuousWithinAt (s := B.GV k r)).congr_of_eventuallyEq ?_ (hag g₀ hgU hg₀)
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with g hgU' hgG
  exact hag g hgU' hgG

/- English proof (translation)
Establish `hχc : Continuous χD` using `hχ.1.continuous`. Establish `hDc` using `Formalism.FourierDecayAlt.P.JCTx6.Pos.cont_DjU k j ρ`. Take `⟨Cχ, hCχ⟩` from `hχc.bounded_above_of_compact_support hχ.2.1`. Establish `hKc : IsCompact (B.GV k (j + ρ) ∩ {g : B.Mat k (j + ρ) | B.gN g ≤ R})` using `(Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k (j + ρ) R).inter_left (Formalism.FourierDecayAlt.P.unitary_group_closed k (j + ρ)).closed`. Take `⟨CF, hCF⟩` from `hKc.exists_bound_of_continuousOn ((asm_contOn_of_ckOn hFc).mono Set.inter_subset_left)`.

Use `⟨(max R 0) ^ A₁ * (max Cχ 0 * max CF 0), ⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `g₀ hg₀`. Take `⟨W0, F', hU, hgU, hF', hag⟩` from `hFc g₀ hg₀`. Use `⟨W0, fun g => χD (U.DjU k j ρ g) • F' g, hU, hgU, ?_, fun g hg hgG => by simp only [hag g hg hgG]⟩` and prove the remaining obligations. Conclude with `contDiffOn_zero.2 ((hχc.comp hDc).continuousOn.smul (hF'.continuousOn))`.

Introduce `g _ hne`. Use `⟨U.DjU k j ρ g, subset_tsupport _ (fun h0 => hne ?_), rfl⟩` and prove the remaining obligations. Simplify using `only [h0, zero_smul]`. Introduce `u v hu hv hl g hg`. Establish `hu0 : u = []` using `List.eq_nil_of_length_eq_zero (by omega)`.

Establish `hv0 : v = []` using `List.eq_nil_of_length_eq_zero (by omega)`. Substitute `hu0 hv0` using the available equality. Use `show B.gN g ^ A₁ * ‖χD (U.DjU k j ρ g) • F g‖ ≤ _`. Distinguish the cases in `h0 : F g = 0`. Rewrite using `[h0, smul_zero, norm_zero, mul_zero]`.

Conclude with `mul_nonneg (Real.rpow_nonneg (le_max_right _ _) _) (mul_nonneg (le_max_right _ _) (le_max_right _ _))`. Establish `hgR` using `hR g hg h0`. Establish `hg0 : 0 ≤ B.gN g` using `Real.sqrt_nonneg _`. Use `mul_le_mul (Real.rpow_le_rpow hg0 (hgR.trans (le_max_left _ _)) hA₁) ?_ (norm_nonneg _) (Real.rpow_nonneg (le_max_right _ _) _)` and prove the remaining obligations. Rewrite using `[norm_smul]`.

Conclude with `mul_le_mul ((hCχ _).trans (le_max_left _ _)) ((hCF g ⟨hg, hgR⟩).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)`.
-/
theorem asm_star_cpt (j ρ : ℕ) (F : B.Mat k (j + ρ) → E) (hFc : B.CkOn ⊤ (B.GV k (j + ρ)) F)
    (R : ℝ) (hR : ∀ g ∈ B.GV k (j + ρ), F g ≠ 0 → B.gN g ≤ R) (χD : ℂ → ℂ) (hχ : U.IsCutC χD) (A₁ : ℝ)
    (hA₁ : 0 ≤ A₁) :
    ∃ B₁, U.Star k j ρ (fun g => χD (U.DjU k j ρ g) • F g) A₁ 0 B₁ ((fun w : ℂ => ‖w‖) '' tsupport χD) := by
  have hχc : Continuous χD := hχ.1.continuous
  have hDc := Formalism.FourierDecayAlt.P.JCTx6.Pos.cont_DjU k j ρ
  obtain ⟨Cχ, hCχ⟩ := hχc.bounded_above_of_compact_support hχ.2.1
  have hKc : IsCompact (B.GV k (j + ρ) ∩ {g : B.Mat k (j + ρ) | B.gN g ≤ R}) :=
    (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k (j + ρ) R).inter_left (Formalism.FourierDecayAlt.P.unitary_group_closed k (j + ρ)).closed
  obtain ⟨CF, hCF⟩ := hKc.exists_bound_of_continuousOn ((asm_contOn_of_ckOn hFc).mono Set.inter_subset_left)
  refine ⟨(max R 0) ^ A₁ * (max Cχ 0 * max CF 0), ⟨?_, ?_, ?_⟩⟩
  · intro g₀ hg₀
    obtain ⟨W0, F', hU, hgU, hF', hag⟩ := hFc g₀ hg₀
    refine ⟨W0, fun g => χD (U.DjU k j ρ g) • F' g, hU, hgU, ?_, fun g hg hgG => by simp only [hag g hg hgG]⟩
    exact contDiffOn_zero.2 ((hχc.comp hDc).continuousOn.smul (hF'.continuousOn))
  · intro g _ hne
    refine ⟨U.DjU k j ρ g, subset_tsupport _ (fun h0 => hne ?_), rfl⟩
    simp only [h0, zero_smul]
  · intro u v hu hv hl g hg
    have hu0 : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hv0 : v = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hu0 hv0
    show B.gN g ^ A₁ * ‖χD (U.DjU k j ρ g) • F g‖ ≤ _
    by_cases h0 : F g = 0
    · rw [h0, smul_zero, norm_zero, mul_zero]
      exact mul_nonneg (Real.rpow_nonneg (le_max_right _ _) _) (mul_nonneg (le_max_right _ _) (le_max_right _ _))
    · have hgR := hR g hg h0
      have hg0 : 0 ≤ B.gN g := Real.sqrt_nonneg _
      refine mul_le_mul (Real.rpow_le_rpow hg0 (hgR.trans (le_max_left _ _)) hA₁) ?_ (norm_nonneg _)
        (Real.rpow_nonneg (le_max_right _ _) _)
      rw [norm_smul]
      exact mul_le_mul ((hCχ _).trans (le_max_left _ _)) ((hCF g ⟨hg, hgR⟩).trans (le_max_left _ _))
        (norm_nonneg _) (le_max_right _ _)

/- English proof (translation)
Establish `hw : (G.wMat (0 + 1)).det ≠ 0` using `Formalism.FourierDecayAlt.P.G2.det_wMat_ne_zero (0 + 1)`. Use `set c₀ : ℂ := (U.hMat σ d).det * (t ^ (0 + 1) * (G.wMat (0 + 1)).det) with hc₀def`. Establish `hc₀ : c₀ ≠ 0` using `mul_ne_zero (Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne σ d hd) (mul_ne_zero (pow_ne_zero _ ht) hw)`. Take `⟨χD, hχD, hχD1, hχDs⟩` from `Formalism.FourierDecayAlt.P.JCTx6.Pos.bump_exists hc₀`. Establish `hR0 : (0 : ℝ) ≤ ((ph + (0 + 1) + ρ : ℕ) : ℝ)` using `Nat.cast_nonneg _`.

Establish `hN0 : (0 : ℝ) ≤ ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Establish `hA₁ : (0 : ℝ) ≤ 8 * (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) + 1) * (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) + 1)` using `by positivity`. Take `⟨B₁, hStar⟩` from `asm_star_cpt (ph + (0 + 1)) ρ F hFc R hR χD hχD _ hA₁`. Establish `hK : IsCompact ((fun w : ℂ => ‖w‖) '' tsupport χD)` using `hχD.2.1.isCompact.image continuous_norm`. Establish `hK0 : (fun w : ℂ => ‖w‖) '' tsupport χD ⊆ Set.Ioi 0`.

Introduce and unpack `_ ⟨w, hw', rfl⟩`. Use `norm_pos_iff.mpr hc₀` as an intermediate fact. Conclude with `lt_of_lt_of_le (by positivity) (hχDs w hw').1`. Establish `hthr : 2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) < 8 * (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) + 1) * (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) + 1) / (8 * (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) + 1))`. Rewrite using `[mul_div_cancel_left₀ _ (by positivity)]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `Formalism.FourierDecayAlt.P.JCTx6.Int.intG k ph 0 ρ σ d t hd ht _ hK hK0 0 _ hthr z z' E _ B₁ hStar γ hγ`. Establish `e : Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d t z z' F γ = Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d t z z' (fun g => χD (U.DjU k (ph + (0 + 1)) ρ g) • F g) γ`. Use function extensionality and compare the values at `y`. Establish `hdet : G.detM (Matrix.of.symm (t • G.wMat (0 + 1) * G.upper y.2.2)) = t ^ (0 + 1) * (G.wMat (0 + 1)).det` using `Formalism.FourierDecayAlt.P.JCTx6.Pos.detM_Zv 0 t y.2.2`.

Establish `hD : U.DjU k (ph + (0 + 1)) ρ (U.gaXi (p` using `ph) (s := 0 + 1) k ρ σ d (y.1, y.2.1) (Matrix.of.symm (t • G.wMat (0 + 1) * G.upper y.2.2)) γ) = c₀ := by`. Rewrite using `[Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice, hdet]`. Simplify using `only [Formalism.FourierDecayAlt.P.JCTx6.gInt]`. Rewrite using `[hD, hχD1 c₀ (by rw [dist_self]; positivity), one_smul]`. Rewrite using `[e]`.

Conclude with `h1`.
-/
theorem asm_gInt_int (ph ρ : ℕ) (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (t : ℂ) (hd : ∀ i, d i ≠ 0) (ht : t ≠ 0)
    (z z' : Fin (2 * (ph + (0 + 1) + ρ) + k + 1) → ℂ) (F : B.Mat k (ph + (0 + 1) + ρ) → E)
    (hFc : B.CkOn ⊤ (B.GV k (ph + (0 + 1) + ρ)) F) (R : ℝ)
    (hR : ∀ g ∈ B.GV k (ph + (0 + 1) + ρ), F g ≠ 0 → B.gN g ≤ R) (γ : B.Mat k ρ) (hγ : γ ∈ B.GV k ρ) :
    Integrable (Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d t z z' F γ) (Formalism.FourierDecayAlt.P.JCTx6.muG k ph 0 ρ σ) := by
  have hw : (G.wMat (0 + 1)).det ≠ 0 := Formalism.FourierDecayAlt.P.G2.det_wMat_ne_zero (0 + 1)
  set c₀ : ℂ := (U.hMat σ d).det * (t ^ (0 + 1) * (G.wMat (0 + 1)).det) with hc₀def
  have hc₀ : c₀ ≠ 0 := mul_ne_zero (Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne σ d hd) (mul_ne_zero (pow_ne_zero _ ht) hw)
  obtain ⟨χD, hχD, hχD1, hχDs⟩ := Formalism.FourierDecayAlt.P.JCTx6.Pos.bump_exists hc₀
  have hR0 : (0 : ℝ) ≤ ((ph + (0 + 1) + ρ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hA₁ : (0 : ℝ) ≤ 8 * (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) + 1) *
      (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) + 1) := by positivity
  obtain ⟨B₁, hStar⟩ := asm_star_cpt (ph + (0 + 1)) ρ F hFc R hR χD hχD _ hA₁
  have hK : IsCompact ((fun w : ℂ => ‖w‖) '' tsupport χD) := hχD.2.1.isCompact.image continuous_norm
  have hK0 : (fun w : ℂ => ‖w‖) '' tsupport χD ⊆ Set.Ioi 0 := by
    rintro _ ⟨w, hw', rfl⟩
    have := norm_pos_iff.mpr hc₀
    exact lt_of_lt_of_le (by positivity) (hχDs w hw').1
  have hthr : 2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) <
      8 * (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) + 1) *
        (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) + 1) /
        (8 * (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) + 1)) := by
    rw [mul_div_cancel_left₀ _ (by positivity)]
    linarith
  have h1 := Formalism.FourierDecayAlt.P.JCTx6.Int.intG k ph 0 ρ σ d t hd ht _ hK hK0 0 _ hthr z z' E _ B₁ hStar γ hγ
  have e : Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d t z z' F γ =
      Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d t z z' (fun g => χD (U.DjU k (ph + (0 + 1)) ρ g) • F g) γ := by
    funext y
    have hdet : G.detM (Matrix.of.symm (t • G.wMat (0 + 1) * G.upper y.2.2)) = t ^ (0 + 1) * (G.wMat (0 + 1)).det :=
      Formalism.FourierDecayAlt.P.JCTx6.Pos.detM_Zv 0 t y.2.2
    have hD : U.DjU k (ph + (0 + 1)) ρ (U.gaXi (p := ph) (s := 0 + 1) k ρ σ d (y.1, y.2.1)
        (Matrix.of.symm (t • G.wMat (0 + 1) * G.upper y.2.2)) γ) = c₀ := by
      rw [Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice, hdet]
    simp only [Formalism.FourierDecayAlt.P.JCTx6.gInt]
    rw [hD, hχD1 c₀ (by rw [dist_self]; positivity), one_smul]
  rw [e]; exact h1

/- English proof (translation)
Establish `hE : IsEmpty (G.UT (0 + 1))` using `⟨fun q => by have h := q.2; rw [Fin.lt_def] at h; omega⟩`. Set `v₀ : G.UT (0 + 1) → ℂ` to `fun q => isEmptyElim q`. Establish `hvol : (volume : Measure (G.UT (0 + 1) → ℂ)) = Measure.dirac v₀`. Rewrite using `[volume_pi]`. Conclude with `Measure.pi_of_empty _ _`.

Establish `a1 : SigmaFinite (volume : Measure (Fin (0 + 1) → Fin ph → ℂ))` using `inferInstance`. Establish `a2 : SigmaFinite (volume : Measure (Fin ph → Fin (0 + 1) → ℂ))` using `inferInstance`. Establish `a3 : SigmaFinite (volume : Measure (U.LW σ → ℂ))` using `inferInstance`. Establish `a4 : SigmaFinite (volume : Measure (G.UT ph → ℂ))` using `inferInstance`. Establish `b1 : SigmaFinite (volume : Measure ((Fin (0 + 1) → Fin ph → ℂ) × (Fin ph → Fin (0 + 1) → ℂ)))`.

Rewrite using `[Measure.volume_eq_prod]`. Use `infer_instance`. Establish `b2 : SigmaFinite (volume : Measure ((U.LW σ → ℂ) × (G.UT ph → ℂ)))`. Rewrite using `[Measure.volume_eq_prod]`. Use `infer_instance`.

Establish `b3 : SigmaFinite (volume : Measure (U.XiH ph (0 + 1) σ))` using `by haveI := b1; haveI := b2`. Rewrite using `[Measure.volume_eq_prod]`. Use `infer_instance`. Establish `b4 : SigmaFinite (U.muXiH ph (0 + 1) σ)` using `by unfold U.muXiH; exact b3`. Establish `hg : MeasurePreserving (fun b : U.XiH ph (0 + 1) σ => (b, v₀)) volume ((volume : Measure (U.XiH ph (0 + 1) σ)).prod (volume : Measure (G.UT (0 + 1) → ℂ)))`.

Rewrite using `[hvol]`. Conclude with `⟨measurable_id.prodMk measurable_const, (Measure.prod_dirac _).symm⟩`. Use `Formalism.FourierDecayAlt.P.Dx2.SL.sigma_RC k (ph + (0 + 1)) ρ` as an intermediate fact. Establish `hφ : MeasurePreserving (Prod.map (id : U.RC k (ph + (0 + 1)) ρ × U.RC k (ph + (0 + 1)) ρ → _) (fun b : U.XiH ph (0 + 1) σ => (b, v₀))) (U.muXi k ph 1 ρ σ) (Formalism.FourierDecayAlt.P.JCTx6.muG k ph 0 ρ σ)` using `(MeasurePreserving.id _).prod hg`. Establish `h2` using `(hφ.integrable_comp h.aestronglyMeasurable).2 h`.

Use `h2.congr (ae_of_all _ fun ξ => ?_)` and prove the remaining obligations. Establish `hs : G.superSum (G.upper v₀) = 0` using `by simp [G.superSum]`. Establish `hZ : (Matrix.of.symm (c • G.wMat (0 + 1) * G.upper v₀) : G.Mat (0 + 1)) = fun _ _ => c`. Use function extensionality and compare the values at `i j`. Establish `hi : i = 0` using `Fin.ext (by have := i.isLt; simp)`.

Establish `hj : j = 0` using `Fin.ext (by have := j.isLt; simp)`. Substitute `hi hj` using the available equality. Simplify using `[G.wMat, G.upper, G.strictUpper, Matrix.mul_apply]`. Simplify using `only [Function.comp_apply, Prod.map, id, Formalism.FourierDecayAlt.P.JCTx6.gInt, hs, hZ]`. Simplify using `[G.psi]`.
-/
theorem integrable_unipotent_rank_one (ph ρ : ℕ) (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (c : ℂ)
    (z z' : Fin (2 * (ph + 1 + ρ) + k + 1) → ℂ) (F : B.Mat k (ph + 1 + ρ) → E) (γ : B.Mat k ρ)
    (h : Integrable (Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d c z z' F γ) (Formalism.FourierDecayAlt.P.JCTx6.muG k ph 0 ρ σ)) :
    Integrable (fun ξ : U.Xi k ph 1 ρ σ => U.psiStar k ρ σ z z' ξ • F (U.gaXi k ρ σ d ξ (fun _ _ => c) γ))
      (U.muXi k ph 1 ρ σ) := by
  have hE : IsEmpty (G.UT (0 + 1)) := ⟨fun q => by have h := q.2; rw [Fin.lt_def] at h; omega⟩
  let v₀ : G.UT (0 + 1) → ℂ := fun q => isEmptyElim q
  have hvol : (volume : Measure (G.UT (0 + 1) → ℂ)) = Measure.dirac v₀ := by
    rw [volume_pi]; exact Measure.pi_of_empty _ _
  have a1 : SigmaFinite (volume : Measure (Fin (0 + 1) → Fin ph → ℂ)) := inferInstance
  have a2 : SigmaFinite (volume : Measure (Fin ph → Fin (0 + 1) → ℂ)) := inferInstance
  have a3 : SigmaFinite (volume : Measure (U.LW σ → ℂ)) := inferInstance
  have a4 : SigmaFinite (volume : Measure (G.UT ph → ℂ)) := inferInstance
  have b1 : SigmaFinite (volume : Measure ((Fin (0 + 1) → Fin ph → ℂ) × (Fin ph → Fin (0 + 1) → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  have b2 : SigmaFinite (volume : Measure ((U.LW σ → ℂ) × (G.UT ph → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  have b3 : SigmaFinite (volume : Measure (U.XiH ph (0 + 1) σ)) := by
    haveI := b1; haveI := b2
    rw [Measure.volume_eq_prod]; infer_instance
  have b4 : SigmaFinite (U.muXiH ph (0 + 1) σ) := by unfold U.muXiH; exact b3
  have hg : MeasurePreserving (fun b : U.XiH ph (0 + 1) σ => (b, v₀)) volume
      ((volume : Measure (U.XiH ph (0 + 1) σ)).prod (volume : Measure (G.UT (0 + 1) → ℂ))) := by
    rw [hvol]
    exact ⟨measurable_id.prodMk measurable_const, (Measure.prod_dirac _).symm⟩
  have := Formalism.FourierDecayAlt.P.Dx2.SL.sigma_RC k (ph + (0 + 1)) ρ
  have hφ : MeasurePreserving (Prod.map (id : U.RC k (ph + (0 + 1)) ρ × U.RC k (ph + (0 + 1)) ρ → _)
      (fun b : U.XiH ph (0 + 1) σ => (b, v₀))) (U.muXi k ph 1 ρ σ) (Formalism.FourierDecayAlt.P.JCTx6.muG k ph 0 ρ σ) :=
    (MeasurePreserving.id _).prod hg
  have h2 := (hφ.integrable_comp h.aestronglyMeasurable).2 h
  refine h2.congr (ae_of_all _ fun ξ => ?_)
  have hs : G.superSum (G.upper v₀) = 0 := by simp [G.superSum]
  have hZ : (Matrix.of.symm (c • G.wMat (0 + 1) * G.upper v₀) : G.Mat (0 + 1)) = fun _ _ => c := by
    funext i j
    have hi : i = 0 := Fin.ext (by have := i.isLt; simp)
    have hj : j = 0 := Fin.ext (by have := j.isLt; simp)
    subst hi hj
    simp [G.wMat, G.upper, G.strictUpper, Matrix.mul_apply]
  simp only [Function.comp_apply, Prod.map, id, Formalism.FourierDecayAlt.P.JCTx6.gInt, hs, hZ]
  simp [G.psi]

end Formalism.FourierDecayAlt.P.PBH
