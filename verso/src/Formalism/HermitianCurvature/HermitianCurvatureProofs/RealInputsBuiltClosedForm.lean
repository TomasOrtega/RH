import Formalism.HermitianCurvature.StatementJCT
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroEstimateProduct
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConcreteBoundOfRecursion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondPolynomialClauses
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockEstimatesSumForm

open Finset NumberField MeasureTheory Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P

noncomputable section

/- English proof (translation)
Unfold `S6.rd`. Apply `Real.rpow_pos_of_pos` to reduce the goal to its premises. Conclude with `Int.cast_pos.mpr (abs_pos.mpr (NumberField.discr_ne_zero E))`.
-/
theorem jct_rd_pos (E : Type) [Field E] [NumberField E] : 0 < S6.rd E := by
  unfold S6.rd
  apply Real.rpow_pos_of_pos
  exact Int.cast_pos.mpr (abs_pos.mpr (NumberField.discr_ne_zero E))

/- English proof (translation)
Take `⟨hl1, hl2, hLA, hSl, htop, hGr, hW, hTW, hLB, hLT, hTL, hSF, -, -, -, hVt⟩` from `hIn`. Establish `hlen : ∀ v, ∀ w, D.AdmAt S v w → w.length ≤ S.Ntop`. Introduce and unpack `v w ⟨w', rfl⟩`. Conclude with `le_trans (Finset.le_sup (f := fun u => (w'.1 u).length) (Finset.mem_univ v)) w'.2.2`. Establish `hPos : C.ThmPPos S`.

Use `positivity_of_module E Wp Wq S T f χ ν' m₀ top A₀ hB (fun v => ?_) htop` and prove the remaining obligations. Take `⟨KK, hKK, hmem⟩` from `hMA hPA hRMF hPD hFS (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v) (S.l + 1) S.Ntop (D.AdmAt S v) (P5.Auser (D.parOf S v) S.Ntop + 1) (P5.mmUser (D.parOf S v) S.Ntop) (by omega) (by change S.l + 1 ≤ S.G.k; omega) (hlen v) le_rfl le_rfl (hLA v)`. Use `⟨KK, hKK, fun ε hε i hi w hw p hp a => ?_⟩` and prove the remaining obligations. Take `⟨ε', hε', hCk, hCC, hs⟩` from `hSl v ε hε i hi w hw p hp a`. Conclude with `hmem ⟨i, Nat.lt_succ_of_le hi⟩ _ ε' hε' hCC hCk hs`.

Establish `hInt : C.ThmPInt S`. Take `⟨dl, hdl, hpl⟩` from `hIBl`. Use `theorem_P_integral_of_places E Wp Wq S dl hPos hdl (fun i _ _ => ?_) hpl` and prove the remaining obligations. Establish `hg : 0 < S.g` using `Nat.mul_pos hg1 hg2`. Establish `hrd` using `jct_rd_pos E`.

Rewrite using `[unipotent_dual_lattice_covolume E hU S.g _ 1 hg]`. Check the signs of the components of the expression. Use `⟨hPos, hGr, hInt, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `plane_exponential_bound_of_places gram_positive_semidefinite words_pos_of_parts E Wp Wq S Lw hPos hGr hW hTW`. Conclude with `off_diagonal_lift_bound_of_places third_polynomial_prime_combine gram_positive_semidefinite words_pos_of_parts E Wp Wq S Ll Ll' hPos hGr hLB hLT hTL`.

Conclude with `corollary_T_of_sum_form blockEstimateOfCosetSum gram_positive_semidefinite words_pos_of_parts E Wp Wq S C₄ hPos hGr hSF`. Conclude with `gram_proposition_of_places E Wp Wq S (fun v => PiLp 2 (fun _ : Fin (Module.finrank ℂ (Wq (S.pl v))) => Wp (S.pl v))) (JC.vecPlace S T f ν' m₀) H Vt hVt (gram_at_built_place ptPerm_spec ptG_spec relevant_points_holds hMu orbital_integral_cutoff_scalar E Wp Wq S T f χ ν' m₀ top A₀ …`.
-/
theorem jct_parts_loc (hPA : P5.ThmPActual) (hRMF : JC.RadialModuleForm) (hPD : JC.PosDensityMM)
    (hFS : JC.FormLevSesqMM) (hMA : JC.ThmPModuleOfActualMM) (hMu : D.MuRHaar)
    (C₄ C₆ : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ)
    (L : ∀ v : Fin S.f, R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
    (j : ∀ v : Fin S.f, M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT)
    (lam : ∀ v : Fin S.f, Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ) (c : LE.Cut) (Cm σ : Fin S.f → ℝ)
    (Lw : ℕ → Fin S.f → ℝ) (Ll Ll' : ℕ → ℕ → Fin S.f → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : TB.Pt E → H)
    (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) (hU : S6.Unram E) (hB : D.IsBuilt S T f χ ν' m₀ top A₀)
    (hIBl : ∃ dl : ℕ → Fin S.f → ℝ,
      (∀ i, 1 ≤ i → i ≤ S.G.r + 1 →
        ∏ v, dl i v = ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1)) ∧
      ∀ v, JC.ThmPIntPlace S v fun i => dl i v)
    (hIn : JCT.BuiltInputs C₄ C₆ S T f χ ν' m₀ top L j lam c Cm σ Lw Ll Ll' Vt) :
    C.ThmPPos S ∧ C.GridsOK S ∧ C.ThmPInt S ∧ C.PlaneWaveBoundAllPlaces S ∧ C.OffDiagonalLiftBound S ∧ C.CorollaryT S C₄ ∧
      C.PropGram S Vt := by
  obtain ⟨hl1, hl2, hLA, hSl, htop, hGr, hW, hTW, hLB, hLT, hTL, hSF, -, -, -, hVt⟩ := hIn
  have hlen : ∀ v, ∀ w, D.AdmAt S v w → w.length ≤ S.Ntop := by
    rintro v w ⟨w', rfl⟩
    exact le_trans (Finset.le_sup (f := fun u => (w'.1 u).length) (Finset.mem_univ v)) w'.2.2
  have hPos : C.ThmPPos S := by
    refine positivity_of_module E Wp Wq S T f χ ν' m₀ top A₀ hB (fun v => ?_) htop
    obtain ⟨KK, hKK, hmem⟩ := hMA hPA hRMF hPD hFS (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v) (S.l + 1) S.Ntop
      (D.AdmAt S v) (P5.Auser (D.parOf S v) S.Ntop + 1) (P5.mmUser (D.parOf S v) S.Ntop) (by omega)
      (by change S.l + 1 ≤ S.G.k; omega) (hlen v) le_rfl
      le_rfl (hLA v)
    refine ⟨KK, hKK, fun ε hε i hi w hw p hp a => ?_⟩
    obtain ⟨ε', hε', hCk, hCC, hs⟩ := hSl v ε hε i hi w hw p hp a
    exact hmem ⟨i, Nat.lt_succ_of_le hi⟩ _ ε' hε' hCC hCk hs
  have hInt : C.ThmPInt S := by
    obtain ⟨dl, hdl, hpl⟩ := hIBl
    refine theorem_P_integral_of_places E Wp Wq S dl hPos hdl (fun i _ _ => ?_) hpl
    have hg : 0 < S.g := Nat.mul_pos hg1 hg2
    have hrd := jct_rd_pos E
    rw [unipotent_dual_lattice_covolume E hU S.g _ 1 hg]
    positivity
  refine ⟨hPos, hGr, hInt, ?_, ?_, ?_, ?_⟩
  · exact plane_exponential_bound_of_places gram_positive_semidefinite words_pos_of_parts E Wp Wq S Lw hPos hGr hW hTW
  · exact off_diagonal_lift_bound_of_places third_polynomial_prime_combine gram_positive_semidefinite words_pos_of_parts
      E Wp Wq S Ll Ll' hPos hGr hLB hLT hTL
  · exact corollary_T_of_sum_form blockEstimateOfCosetSum gram_positive_semidefinite words_pos_of_parts
      E Wp Wq S C₄ hPos hGr hSF
  · exact gram_proposition_of_places E Wp Wq S
      (fun v => PiLp 2 (fun _ : Fin (Module.finrank ℂ (Wq (S.pl v))) => Wp (S.pl v))) (JC.vecPlace S T f ν' m₀)
      H Vt hVt (gram_at_built_place ptPerm_spec ptG_spec relevant_points_holds hMu
        orbital_integral_cutoff_scalar E Wp Wq S T f χ ν' m₀ top A₀ hg1 hg2 hB)

/- English proof (translation)
The claim follows from `jct_parts_loc hPA hRMF hPD hFS hMA hMu C₄ C₆ E Wp Wq S T f χ ν' m₀ top A₀ L j lam c Cm σ Lw Ll Ll' H Vt hg1 hg2 hU hB (hIB E Wp Wq S T f χ ν' m₀ top A₀ hg1 hg2 hU hB) hIn`.
-/
theorem jct_parts (hPA : P5.ThmPActual) (hRMF : JC.RadialModuleForm) (hPD : JC.PosDensityMM)
    (hFS : JC.FormLevSesqMM) (hMA : JC.ThmPModuleOfActualMM) (hIB : JC.ThmPIntBuilt) (hMu : D.MuRHaar)
    (C₄ C₆ : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ)
    (L : ∀ v : Fin S.f, R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
    (j : ∀ v : Fin S.f, M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT)
    (lam : ∀ v : Fin S.f, Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ) (c : LE.Cut) (Cm σ : Fin S.f → ℝ)
    (Lw : ℕ → Fin S.f → ℝ) (Ll Ll' : ℕ → ℕ → Fin S.f → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : TB.Pt E → H)
    (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) (hU : S6.Unram E) (hB : D.IsBuilt S T f χ ν' m₀ top A₀)
    (hIn : JCT.BuiltInputs C₄ C₆ S T f χ ν' m₀ top L j lam c Cm σ Lw Ll Ll' Vt) :
    C.ThmPPos S ∧ C.GridsOK S ∧ C.ThmPInt S ∧ C.PlaneWaveBoundAllPlaces S ∧ C.OffDiagonalLiftBound S ∧ C.CorollaryT S C₄ ∧
      C.PropGram S Vt :=
  jct_parts_loc hPA hRMF hPD hFS hMA hMu C₄ C₆ E Wp Wq S T f χ ν' m₀ top A₀ L j lam c Cm σ Lw Ll Ll' H Vt hg1 hg2 hU hB
    (hIB E Wp Wq S T f χ ν' m₀ top A₀ hg1 hg2 hU hB) hIn

/- English proof (translation)
Introduce `hPA hRMF hPD hFS hMA hIB hMu hLEM`. Take `⟨C₆, hC₆, hLE⟩` from `lemma_E_of_model lemma_E_of_residue level_zero_holds good_of_admissible hLEM`. Use `⟨C₆, hC₆, ?_⟩` and prove the remaining obligations. Introduce `C₄ E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ L j lam c Cm σ Lw Ll Ll' H _ _ Vt hg1 hg2 hU hB hIn Kr hK0 Th e`. Take `⟨hPos, hGr, hInt, hP1, hP23, hT, hPG⟩` from `jct_parts hPA hRMF hPD hFS hMA hIB hMu C₄ C₆ E Wp Wq S T f χ ν' m₀ top A₀ L j lam c Cm σ Lw Ll Ll' H Vt hg1 hg2 hU hB hIn`.

Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, hsm, hcut, hmod, -⟩` from `hIn`. Establish `hE : C.LemmaE S (JCT.jvModel S j Cm)` using `hLE E Wp Wq S T f χ ν' m₀ top A₀ L j lam c Cm σ hB (fun v ε hε => cutoff_smooth _ _ _ _ (T v).base χ (f v) ε hB.1 (hsm v) hε) hcut hmod`. Conclude with `real_inputs_concrete_holds E Wp Wq S (JCT.jvModel S j Cm) H Vt C₄ hg1 hg2 hPos hGr hInt hP1 hP23 hT hE hPG Kr hK0 Th e`.
-/
theorem real_inputs_built : JCT.RealInputsBuilt := by
  intro hPA hRMF hPD hFS hMA hIB hMu hLEM
  obtain ⟨C₆, hC₆, hLE⟩ := lemma_E_of_model lemma_E_of_residue level_zero_holds good_of_admissible hLEM
  refine ⟨C₆, hC₆, ?_⟩
  intro C₄ E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ L j lam c Cm σ Lw Ll Ll' H _ _ Vt hg1 hg2 hU hB hIn
    Kr hK0 Th e
  obtain ⟨hPos, hGr, hInt, hP1, hP23, hT, hPG⟩ :=
    jct_parts hPA hRMF hPD hFS hMA hIB hMu C₄ C₆ E Wp Wq S T f χ ν' m₀ top A₀ L j lam c Cm σ Lw Ll Ll' H Vt
      hg1 hg2 hU hB hIn
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hsm, hcut, hmod, -⟩ := hIn
  have hE : C.LemmaE S (JCT.jvModel S j Cm) :=
    hLE E Wp Wq S T f χ ν' m₀ top A₀ L j lam c Cm σ hB
      (fun v ε hε => cutoff_smooth _ _ _ _ (T v).base χ (f v) ε hB.1 (hsm v) hε) hcut hmod
  exact real_inputs_concrete_holds E Wp Wq S (JCT.jvModel S j Cm) H Vt C₄ hg1 hg2 hPos hGr hInt hP1 hP23 hT hE
    hPG Kr hK0 Th e

/- English proof (translation)
Introduce `hPA hRMF hPD hFS hMA hIB hMu hLEM`. Take `⟨C₆, hC₆, hLE⟩` from `lemma_E_of_model lemma_E_of_residue level_zero_holds good_of_admissible hLEM`. Use `⟨C₆, hC₆, ?_⟩` and prove the remaining obligations. Introduce `C₁ C₄ h1 h4`. Take `⟨Cst, Cst', hA⟩` from `concrete_bound_holds C₁ C₄ h1 h4`.

Use `⟨Cst, Cst', ?_⟩` and prove the remaining obligations. Introduce `E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ L j lam c Cm σ Lw Ll Ll' cE Kr hK0 Th e Θ H _ _ _ Vt cr hf hg1 hg2 hU hB hIn hEL hΘ hCΘ hsmall hSz hKr hA2 hEB hDom hLS hA4 Rs`. Take `⟨hPos, hGr, hInt, hP1, hP23, hT, hPG⟩` from `jct_parts hPA hRMF hPD hFS hMA hIB hMu C₄ C₆ E Wp Wq S T f χ ν' m₀ top A₀ L j lam c Cm σ Lw Ll Ll' H Vt hg1 hg2 hU hB hIn`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, hsm, hcut, hmod, -⟩` from `hIn`. Establish `hE : C.LemmaE S (JCT.jvModel S j Cm)` using `hLE E Wp Wq S T f χ ν' m₀ top A₀ L j lam c Cm σ hB (fun v ε hε => cutoff_smooth _ _ _ _ (T v).base χ (f v) ε hB.1 (hsm v) hε) hcut hmod`.

Conclude with `hA E Wp Wq S (JCT.jvModel S j Cm) cE Kr hK0 Th e Θ H Vt cr hf hg1 hg2 hΘ hCΘ hsmall hSz hPos hGr hInt hP1 hP23 hT hE hEL hPG hKr hA2 hEB hDom hLS hA4 Rs`.
-/
theorem theorem_A_built : JCT.TheoremABuilt := by
  intro hPA hRMF hPD hFS hMA hIB hMu hLEM
  obtain ⟨C₆, hC₆, hLE⟩ := lemma_E_of_model lemma_E_of_residue level_zero_holds good_of_admissible hLEM
  refine ⟨C₆, hC₆, ?_⟩
  intro C₁ C₄ h1 h4
  obtain ⟨Cst, Cst', hA⟩ := concrete_bound_holds C₁ C₄ h1 h4
  refine ⟨Cst, Cst', ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ L j lam c Cm σ Lw Ll Ll' cE Kr hK0 Th e Θ H _ _ _ Vt cr
    hf hg1 hg2 hU hB hIn hEL hΘ hCΘ hsmall hSz hKr hA2 hEB hDom hLS hA4 Rs
  obtain ⟨hPos, hGr, hInt, hP1, hP23, hT, hPG⟩ :=
    jct_parts hPA hRMF hPD hFS hMA hIB hMu C₄ C₆ E Wp Wq S T f χ ν' m₀ top A₀ L j lam c Cm σ Lw Ll Ll' H Vt
      hg1 hg2 hU hB hIn
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hsm, hcut, hmod, -⟩ := hIn
  have hE : C.LemmaE S (JCT.jvModel S j Cm) :=
    hLE E Wp Wq S T f χ ν' m₀ top A₀ L j lam c Cm σ hB
      (fun v ε hε => cutoff_smooth _ _ _ _ (T v).base χ (f v) ε hB.1 (hsm v) hε) hcut hmod
  exact hA E Wp Wq S (JCT.jvModel S j Cm) cE Kr hK0 Th e Θ H Vt cr hf hg1 hg2 hΘ hCΘ hsmall hSz hPos hGr hInt hP1
    hP23 hT hE hEL hPG hKr hA2 hEB hDom hLS hA4 Rs

/- English proof (translation)
Unfold `JCT.IsBuiltPlace at h ⊢`. Take `⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩` from `h`. Use `⟨h1, h2, h3, h4, h5, h6, h7, ?_, le_trans hc h9, h10, h11, ?_, h13⟩` and prove the remaining obligations. Unfold `JCT.LongCut at h8 ⊢`. Introduce `v`.

Conclude with `le_trans (mul_le_mul_of_nonneg_right hc (by positivity)) (h8 v)`. Conclude with `le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)) h12`.
-/
theorem jct_isBuiltPlace_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ}
    {ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ} {m₀ : Fin S.f → B.Mat S.G.k S.G.r}
    {top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ}
    {A₀ Cc c : ℝ} (hc : c ≤ Cc) (h : JCT.IsBuiltPlace Cc S T f χ ν' m₀ top A₀) :
    JCT.IsBuiltPlace c S T f χ ν' m₀ top A₀ := by
  unfold JCT.IsBuiltPlace at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, le_trans hc h9, h10, h11, ?_, h13⟩
  · unfold JCT.LongCut at h8 ⊢
    intro v
    exact le_trans (mul_le_mul_of_nonneg_right hc (by positivity)) (h8 v)
  · exact le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)) h12

/- English proof (translation)
Introduce `hPA hRMF hPD hFS hMA hIB hMu hLEM hLA hSL hWv hLB hLT hSF hMP`. Take `⟨C₆, hC₆, hLE⟩` from `lemma_E_of_model lemma_E_of_residue level_zero_holds good_of_admissible hLEM`. Take `⟨c1, hLA⟩` from `hLA`. Take `⟨c2, hSL⟩` from `hSL`. Take `⟨c3, hWv⟩` from `hWv`.

Take `⟨c4, hLB⟩` from `hLB`. Take `⟨c5, hLT⟩` from `hLT`. Take `⟨c6, C₄, hC₄, hSF⟩` from `hSF`. Take `⟨c7, hMP⟩` from `hMP`. Use `⟨C₆, max c1 (max c2 (max c3 (max c4 (max c5 (max c6 c7))))), C₄, hC₆, hC₄, ?_⟩` and prove the remaining obligations.

Introduce `E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ c H _ _ Vt hBP hSB hc hcut htop hVt`. Establish `m1` using `jct_isBuiltPlace_mono (by simp) hBP (c := c1)`. Establish `m2` using `jct_isBuiltPlace_mono (by simp) hBP (c := c2)`. Establish `m3` using `jct_isBuiltPlace_mono (by simp) hBP (c := c3)`. Establish `m4` using `jct_isBuiltPlace_mono (by simp) hBP (c := c4)`.

Establish `m5` using `jct_isBuiltPlace_mono (by simp) hBP (c := c5)`. Establish `m6` using `jct_isBuiltPlace_mono (by simp) hBP (c := c6)`. Establish `m7` using `jct_isBuiltPlace_mono (by simp) hBP (c := c7)`. Take `⟨hg1, hg2, hU, hB, hl1, hl2, hGr, -, -, hsm, -, -, -⟩` from `hBP`. Use `choose L j lam Cm σ hmod using hMP E Wp Wq S T f χ ν' m₀ top A₀ m7 c hc`.

Take `⟨Lw, hW, hTW⟩` from `hWv E Wp Wq S T f χ ν' m₀ top A₀ m3`. Take `⟨Ll, hLB1, hTL1⟩` from `hLB E Wp Wq S T f χ ν' m₀ top A₀ m4`. Take `⟨Ll', hLT1, hTL2⟩` from `hLT E Wp Wq S T f χ ν' m₀ top A₀ m5`. Establish `hTL : JC.ThresholdsLift S Ll Ll'`. Unfold `JC.ThresholdsLift`.

Conclude with `⟨hTL1, hTL2⟩`. Establish `hIn : JCT.BuiltInputs C₄ C₆ S T f χ ν' m₀ top L j lam c Cm σ Lw Ll Ll' Vt`. Unfold `JCT.BuiltInputs`. Conclude with `⟨hl1, hl2, hLA E Wp Wq S T f χ ν' m₀ top A₀ m1, hSL E Wp Wq S T f χ ν' m₀ top A₀ m2 hSB, htop, hGr, hW, hTW, hLB1, hLT1, hTL, hSF E Wp Wq S T f χ ν' m₀ top A₀ m6, hsm, hcut, hmod, hVt⟩`. Use `⟨L, j, lam, Cm, σ, hmod, ?_⟩` and prove the remaining obligations.

Introduce `Kr hK0 Th e`. Take `⟨hPos, hGr', hInt, hP1, hP23, hT, hPG⟩` from `jct_parts hPA hRMF hPD hFS hMA hIB hMu C₄ C₆ E Wp Wq S T f χ ν' m₀ top A₀ L j lam c Cm σ Lw Ll Ll' H Vt hg1 hg2 hU hB hIn`. Establish `hE : C.LemmaE S (JCT.jvModel S j Cm)` using `hLE E Wp Wq S T f χ ν' m₀ top A₀ L j lam c Cm σ hB (fun v ε hε => cutoff_smooth _ _ _ _ (T v).base χ (f v) ε hB.1 (hsm v) hε) hcut hmod`. Conclude with `real_inputs_concrete_holds E Wp Wq S (JCT.jvModel S j Cm) H Vt C₄ hg1 hg2 hPos hGr' hInt hP1 hP23 hT hE hPG Kr hK0 Th e`.
-/
theorem real_inputs_built_closed_form : JCT.RealInputsBuiltClosed := by
  intro hPA hRMF hPD hFS hMA hIB hMu hLEM hLA hSL hWv hLB hLT hSF hMP
  obtain ⟨C₆, hC₆, hLE⟩ := lemma_E_of_model lemma_E_of_residue level_zero_holds good_of_admissible hLEM
  obtain ⟨c1, hLA⟩ := hLA
  obtain ⟨c2, hSL⟩ := hSL
  obtain ⟨c3, hWv⟩ := hWv
  obtain ⟨c4, hLB⟩ := hLB
  obtain ⟨c5, hLT⟩ := hLT
  obtain ⟨c6, C₄, hC₄, hSF⟩ := hSF
  obtain ⟨c7, hMP⟩ := hMP
  refine ⟨C₆, max c1 (max c2 (max c3 (max c4 (max c5 (max c6 c7))))), C₄, hC₆, hC₄, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ c H _ _ Vt hBP hSB hc hcut htop hVt
  have m1 := jct_isBuiltPlace_mono (by simp) hBP (c := c1)
  have m2 := jct_isBuiltPlace_mono (by simp) hBP (c := c2)
  have m3 := jct_isBuiltPlace_mono (by simp) hBP (c := c3)
  have m4 := jct_isBuiltPlace_mono (by simp) hBP (c := c4)
  have m5 := jct_isBuiltPlace_mono (by simp) hBP (c := c5)
  have m6 := jct_isBuiltPlace_mono (by simp) hBP (c := c6)
  have m7 := jct_isBuiltPlace_mono (by simp) hBP (c := c7)
  obtain ⟨hg1, hg2, hU, hB, hl1, hl2, hGr, -, -, hsm, -, -, -⟩ := hBP
  choose L j lam Cm σ hmod using hMP E Wp Wq S T f χ ν' m₀ top A₀ m7 c hc
  obtain ⟨Lw, hW, hTW⟩ := hWv E Wp Wq S T f χ ν' m₀ top A₀ m3
  obtain ⟨Ll, hLB1, hTL1⟩ := hLB E Wp Wq S T f χ ν' m₀ top A₀ m4
  obtain ⟨Ll', hLT1, hTL2⟩ := hLT E Wp Wq S T f χ ν' m₀ top A₀ m5
  have hTL : JC.ThresholdsLift S Ll Ll' := by
    unfold JC.ThresholdsLift
    exact ⟨hTL1, hTL2⟩
  have hIn : JCT.BuiltInputs C₄ C₆ S T f χ ν' m₀ top L j lam c Cm σ Lw Ll Ll' Vt := by
    unfold JCT.BuiltInputs
    exact ⟨hl1, hl2, hLA E Wp Wq S T f χ ν' m₀ top A₀ m1, hSL E Wp Wq S T f χ ν' m₀ top A₀ m2 hSB, htop, hGr, hW,
      hTW, hLB1, hLT1, hTL, hSF E Wp Wq S T f χ ν' m₀ top A₀ m6, hsm, hcut, hmod, hVt⟩
  refine ⟨L, j, lam, Cm, σ, hmod, ?_⟩
  intro Kr hK0 Th e
  obtain ⟨hPos, hGr', hInt, hP1, hP23, hT, hPG⟩ :=
    jct_parts hPA hRMF hPD hFS hMA hIB hMu C₄ C₆ E Wp Wq S T f χ ν' m₀ top A₀ L j lam c Cm σ Lw Ll Ll' H Vt
      hg1 hg2 hU hB hIn
  have hE : C.LemmaE S (JCT.jvModel S j Cm) :=
    hLE E Wp Wq S T f χ ν' m₀ top A₀ L j lam c Cm σ hB
      (fun v ε hε => cutoff_smooth _ _ _ _ (T v).base χ (f v) ε hB.1 (hsm v) hε) hcut hmod
  exact real_inputs_concrete_holds E Wp Wq S (JCT.jvModel S j Cm) H Vt C₄ hg1 hg2 hPos hGr' hInt hP1 hP23 hT hE
    hPG Kr hK0 Th e

/- English proof (translation)
Introduce `hBC`. Take `⟨Cc, hBC⟩` from `hBC`. Use `⟨Cc, ?_⟩` and prove the remaining obligations. Introduce `E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ jv hBP hL v`. Take `⟨-, -, -, hB, -, -, -, -, -, hsm, -, -, -⟩` from `id hBP`.

Establish `hpd` using `(hB.2 v).1`. Use `set Γ := D.GamLev S.G.k S.G.r (D.kapG S.g (S6.rd E)) (D.deG S.g (S6.rd E)) 0 with hΓ`. Take `⟨-, hlim⟩` from `hBC E Wp Wq S T f χ ν' m₀ top A₀ hBP v`. Establish `hemp : S.empW.1 v = []` using `rfl`. Establish `h1` using `hL S.empW v`.

Establish `h2 : Filter.Tendsto (fun ε => (S.pd v).RR ε 0 (S.empW.1 v) [] []) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((((1 / Γ : ℝ)) : ℂ) * (((B.normSq (T v).base (f v)).toReal : ℝ) : ℂ)))`. Use `(hlim.const_mul _).congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with ε hε`. Establish `hsm'` using `cutoff_smooth _ _ _ _ (T v).base χ (f v) ε hB.1 (hsm v) hε`. Rewrite using `[hpd]`.

Simplify using `only [D.componentFamilySetting_ofSetting, D.bSt, D.toStd, List.map_nil, List.prod_nil]`. Rewrite using `[level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hsm' (good_of_admissible _ _ _ S S.empW v)]`. Rewrite using `[hemp]`. Simplify using `only [C7.principalHermitianLattice, List.foldr_nil]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `h3` using `tendsto_nhds_unique h1 h2`. Rewrite `h3` using `[hemp]`. Establish `hsz : S.sizeAt v [] = 1` using `by simp [C.HidaSetting.sizeAt]`. Rewrite `h3` using `[hsz, one_mul]`.

Establish `h4 : jv v = 1 / Γ * (B.normSq (T v).base (f v)).toReal` using `by exact_mod_cast h3`. Rewrite using `[h4]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem energy_of_built_setting : JCT.EnergyOfLemmaE := by
  intro hBC
  obtain ⟨Cc, hBC⟩ := hBC
  refine ⟨Cc, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ jv hBP hL v
  obtain ⟨-, -, -, hB, -, -, -, -, -, hsm, -, -, -⟩ := id hBP
  have hpd := (hB.2 v).1
  set Γ := D.GamLev S.G.k S.G.r (D.kapG S.g (S6.rd E)) (D.deG S.g (S6.rd E)) 0 with hΓ
  obtain ⟨-, hlim⟩ := hBC E Wp Wq S T f χ ν' m₀ top A₀ hBP v
  have hemp : S.empW.1 v = [] := rfl
  have h1 := hL S.empW v
  have h2 : Filter.Tendsto (fun ε => (S.pd v).RR ε 0 (S.empW.1 v) [] []) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((((1 / Γ : ℝ)) : ℂ) * (((B.normSq (T v).base (f v)).toReal : ℝ) : ℂ))) := by
    refine (hlim.const_mul _).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hsm' := cutoff_smooth _ _ _ _ (T v).base χ (f v) ε hB.1 (hsm v) hε
    rw [hpd]
    simp only [D.componentFamilySetting_ofSetting, D.bSt, D.toStd, List.map_nil, List.prod_nil]
    rw [level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hsm' (good_of_admissible _ _ _ S S.empW v)]
    rw [hemp]
    simp only [C7.principalHermitianLattice, List.foldr_nil]
    push_cast
    ring
  have h3 := tendsto_nhds_unique h1 h2
  rw [hemp] at h3
  have hsz : S.sizeAt v [] = 1 := by simp [C.HidaSetting.sizeAt]
  rw [hsz, one_mul] at h3
  have h4 : jv v = 1 / Γ * (B.normSq (T v).base (f v)).toReal := by exact_mod_cast h3
  rw [h4]
  ring

end

end Formalism.FourierDecayAlt.P
