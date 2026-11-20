import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorConjIsThetaSomeLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockVanishingLevelUnitBlockMulInvStabStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalMatrixApproxTwoAdelicModuliStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilSkewIdealLatticeUnitVectorUnimodularEigenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergTranslateUnitVectorCongrUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerSkewConjMemThetaFunctionsStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall

/- English proof (translation)
Introduce `D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho j hj`. Establish `hn : D.host.conj • 𝔪 ≠ ⊥` using `GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm`. Establish `hF` using `GlobalTheory.T.latticeIntertwiner_skewConj_mem_thetaFunctions D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho`. Establish `hmove : ∀ g ∈ intG D a, ∀ g' ∈ intG D d, ∀ y y' : Matrix (Fin d) (Fin a) D.host.E, (∀ i l, (((g' : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * y.map (inc D) * (((g : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) - y'.map (inc D)) i l ∈ hatId …`. Introduce `g hg g' hg' y y' hy`.

Take `⟨m, hm0, hl⟩` from `W.lift g g' y _ hF`. Take `⟨z, hz1, hz2⟩` from `GlobalTheory.T.exists_global_matrix_approx_two_adelic_moduli D _ hn a d (((g' : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * y.map (inc D) * (((g : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) m hm0`. Rewrite using `[hl z hz1]`. Take `⟨c1, hc1, e1⟩` from `GlobalTheory.T.weil_skewIdealLatticeUnitVector_unimodular_eigen D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho g hg g' hg'`. Take `⟨c2, hc2, e2⟩` from `GlobalTheory.T.heisenbergTranslate_unitVector_congr_unimodular D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho z y' (fun i l => by`.

Use `sub_mem (hy i l) (hz2 i l)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `[Matrix.sub_apply, Matrix.map_apply, map_sub])`. Use `⟨c1 * c2, by rw [norm_mul, hc1, hc2, one_mul], ?_⟩` and prove the remaining obligations. Rewrite using `[e1]`.

Establish `: ∀ (x : VC D a d) (F : VC D a d → ℂ) (c : ℂ), Wd D (tor0 D ⊤ δ) x (c • F) = c • Wd D (tor0 D ⊤ δ) x F`. Introduce `x F c`. Use function extensionality and compare the values at `w`. Simplify using `only [Wd, U, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, e2, smul_smul]`. Take `⟨k, hk, hjk⟩` from `GlobalTheory.T.blockVanishingLevel_unitBlock_mul_inv_stab D 𝔪 hm hcop o a d ho j hj`. Take `⟨y', -, hy'⟩` from `GlobalTheory.T.exists_global_matrix_approx_two_adelic_moduli D _ hn a d ((unitBlock D o a d).map (inc D) * (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) 1 one_pos`. Establish `hjJ : j ∈ intG D d` using `GlobalTheory.BotPairSmall.blockJ_le D 𝔪 o d hj`. Take `⟨c1, hc1, e1⟩` from `hmove 1 (one_mem _) j hjJ (unitBlock D o a d) y' (fun i l => by`.

Use `add_mem (hjk i l) (hy' i l)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `[Matrix.sub_apply])`. Take `⟨c2, hc2, e2⟩` from `hmove k hk 1 (one_mem _) (unitBlock D o a d) y' (fun i l => by`. Use `hy' i l using 1` and compare the differences between its conclusion and the goal.

Simplify using `[Matrix.sub_apply])`. Establish `hwd : ∀ (x : VC D a d) (F : VC D a d → ℂ) (c : ℂ), Wd D (tor0 D ⊤ δ) x (c • F) = c • Wd D (tor0 D ⊤ δ) x F`. Introduce `x F c`. Use function extensionality and compare the values at `w`. Simplify using `only [Wd, U, Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Use `set s : ℂ := ((Real.sqrt ((Ideal.absNorm (D.host.conj • 𝔪) : ℝ) ^ (a * d)) : ℂ)) with hs_def`. Establish `hs : s ≠ 0`. Establish `h0 : (Ideal.absNorm (D.host.conj • 𝔪) : ℝ) ≠ 0`. Conclude with `(Ideal.absNorm_eq_zero_iff.not.2 hn)` after adjusting the coercions.

Establish `: 0 < Real.sqrt ((Ideal.absNorm (D.host.conj • 𝔪) : ℝ) ^ (a * d))` using `Real.sqrt_pos.2 (pow_pos (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h0)) _)`. Conclude with `Complex.ofReal_ne_zero.2 this.ne'`. Establish `hcv` using `GlobalTheory.T.cosetVector_conj_isTheta_some_level D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho`. Establish `hV : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d)) (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) = s • GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0`. Rewrite using `[GlobalTheory.BotPairSmall.cvec, smul_smul, mul_inv_cancel₀ hs, one_smul]`.

Establish `hVT : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d)) (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) ∈ TT D (tor0 D ⊤ δ) a d`. Rewrite using `[hV]`. Take `⟨h1, m, hm0, h2⟩` from `hcv`. Conclude with `⟨h1.const_smul s, m, hm0, fun x hx => by rw [hwd, h2 x hx]⟩`. Establish `hc2' : c2 ≠ 0` using `by intro h; rw [h, norm_zero] at hc2; exact zero_ne_one hc2`.

Use `⟨k, hk, c1 / c2, by rw [norm_div, hc1, hc2, div_one], ?_⟩` and prove the remaining obligations. Use `show W.Om 1 j (s⁻¹ • _) = (c1 / c2) • W.Om k 1 (s⁻¹ • _)`. Rewrite using `[W.smul _ _ _ _ hVT, W.smul _ _ _ _ hVT, e1, e2, smul_smul, smul_smul, smul_smul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
theorem cvec_eig : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ j ∈ GlobalTheory.BotPairSmall.blockJ D 𝔪 o d, ∃ k ∈ intG D a, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om 1 j (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0) = c • W.Om k 1 (GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0) := by
  intro D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho j hj
  have hn : D.host.conj • 𝔪 ≠ ⊥ := GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm
  have hF := GlobalTheory.T.latticeIntertwiner_skewConj_mem_thetaFunctions D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho
  have hmove : ∀ g ∈ intG D a, ∀ g' ∈ intG D d, ∀ y y' : Matrix (Fin d) (Fin a) D.host.E,
      (∀ i l, (((g' : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * y.map (inc D) *
        (((g : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) - y'.map (inc D)) i l ∈ hatId D (D.host.conj • 𝔪)) →
      ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om g g' (Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ y) (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0)) =
        c • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ y') (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) := by
    intro g hg g' hg' y y' hy
    obtain ⟨m, hm0, hl⟩ := W.lift g g' y _ hF
    obtain ⟨z, hz1, hz2⟩ := GlobalTheory.T.exists_global_matrix_approx_two_adelic_moduli D _ hn a d (((g' : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * y.map (inc D) *
        (((g : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) m hm0
    rw [hl z hz1]
    obtain ⟨c1, hc1, e1⟩ := GlobalTheory.T.weil_skewIdealLatticeUnitVector_unimodular_eigen D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho g hg g' hg'
    obtain ⟨c2, hc2, e2⟩ := GlobalTheory.T.heisenbergTranslate_unitVector_congr_unimodular D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho z y' (fun i l => by
      have := sub_mem (hy i l) (hz2 i l)
      convert this using 1
      simp [Matrix.sub_apply, Matrix.map_apply, map_sub])
    refine ⟨c1 * c2, by rw [norm_mul, hc1, hc2, one_mul], ?_⟩
    rw [e1]
    have : ∀ (x : VC D a d) (F : VC D a d → ℂ) (c : ℂ), Wd D (tor0 D ⊤ δ) x (c • F) = c • Wd D (tor0 D ⊤ δ) x F := by
      intro x F c; funext w; simp only [Wd, U, Pi.smul_apply, smul_eq_mul]; ring
    rw [this, e2, smul_smul]

  obtain ⟨k, hk, hjk⟩ := GlobalTheory.T.blockVanishingLevel_unitBlock_mul_inv_stab D 𝔪 hm hcop o a d ho j hj
  obtain ⟨y', -, hy'⟩ := GlobalTheory.T.exists_global_matrix_approx_two_adelic_moduli D _ hn a d ((unitBlock D o a d).map (inc D) *
    (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) 1 one_pos
  have hjJ : j ∈ intG D d := GlobalTheory.BotPairSmall.blockJ_le D 𝔪 o d hj
  obtain ⟨c1, hc1, e1⟩ := hmove 1 (one_mem _) j hjJ (unitBlock D o a d) y' (fun i l => by
    have := add_mem (hjk i l) (hy' i l)
    convert this using 1
    simp [Matrix.sub_apply])
  obtain ⟨c2, hc2, e2⟩ := hmove k hk 1 (one_mem _) (unitBlock D o a d) y' (fun i l => by
    convert hy' i l using 1
    simp [Matrix.sub_apply])
  have hwd : ∀ (x : VC D a d) (F : VC D a d → ℂ) (c : ℂ), Wd D (tor0 D ⊤ δ) x (c • F) = c • Wd D (tor0 D ⊤ δ) x F := by
    intro x F c; funext w; simp only [Wd, U, Pi.smul_apply, smul_eq_mul]; ring
  set s : ℂ := ((Real.sqrt ((Ideal.absNorm (D.host.conj • 𝔪) : ℝ) ^ (a * d)) : ℂ)) with hs_def
  have hs : s ≠ 0 := by
    have h0 : (Ideal.absNorm (D.host.conj • 𝔪) : ℝ) ≠ 0 := by
      exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hn)
    have : 0 < Real.sqrt ((Ideal.absNorm (D.host.conj • 𝔪) : ℝ) ^ (a * d)) :=
      Real.sqrt_pos.2 (pow_pos (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h0)) _)
    exact Complex.ofReal_ne_zero.2 this.ne'
  have hcv := GlobalTheory.T.cosetVector_conj_isTheta_some_level D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho
  have hV : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d)) (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) =
      s • GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0 := by
    rw [GlobalTheory.BotPairSmall.cvec, smul_smul, mul_inv_cancel₀ hs, one_smul]
  have hVT : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d)) (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) ∈ TT D (tor0 D ⊤ δ) a d := by
    rw [hV]
    obtain ⟨h1, m, hm0, h2⟩ := hcv
    exact ⟨h1.const_smul s, m, hm0, fun x hx => by rw [hwd, h2 x hx]⟩
  have hc2' : c2 ≠ 0 := by intro h; rw [h, norm_zero] at hc2; exact zero_ne_one hc2
  refine ⟨k, hk, c1 / c2, by rw [norm_div, hc1, hc2, div_one], ?_⟩
  show W.Om 1 j (s⁻¹ • _) = (c1 / c2) • W.Om k 1 (s⁻¹ • _)
  rw [W.smul _ _ _ _ hVT, W.smul _ _ _ _ hVT, e1, e2, smul_smul, smul_smul, smul_smul]
  congr 1
  field_simp

end GlobalTheory.BotPairSmall
