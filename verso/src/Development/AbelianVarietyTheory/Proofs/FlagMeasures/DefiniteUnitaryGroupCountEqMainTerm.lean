import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DefiniteFiniteCount
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsAutIdemElementary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentIsometryDefiniteEqOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConjPowOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrablePhStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientIntegrableMajorantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRadicalSpanPrimeOfNcardPrimesOverEqFinrankStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LogSingularValuesEuclidNormCartanPropertiesStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Dec

/- English proof (translation)
Take `⟨g, -, hinf, hfin⟩` from `hγ`. Establish `hdet : ∀ w, IsUnit (I.P w).det` using `fun w => (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit w)`. Use `set M : Matrix (Fin I.n) (Fin I.n) I.E := (g : Matrix (Fin I.n) (Fin I.n) I.E) with hM`. Establish `e1 : (I.P v)⁻¹ * M.map (I.φ v) * I.P v = 1` using `(hinf v).symm.trans h`. Establish `e2 : M.map (I.φ v) * I.P v = I.P v`.

Use `congrArg (I.P v * ·) e1` as an intermediate fact. Simplify `this` using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hdet v)]`. Establish `e3 : M.map (I.φ v) = 1`. Use `congrArg (· * (I.P v)⁻¹) e2` as an intermediate fact. Simplify `this` using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hdet v)]`.

Establish `hg : M = 1`. Apply `Matrix.map_injective (I.φ v).injective` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[e3, Matrix.map_one _ (map_zero _) (map_one _)]`. Use `Prod.ext (funext fun w => ?_) ?_` and prove the remaining obligations.

Establish `hw : uMat (γ.1 w) = 1`. Rewrite using `[hinf w, hg, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.nonsing_inv_mul _ (hdet w)]`. Conclude with `Subtype.ext (Units.ext (by simpa using hw))`. Establish `hf : I.fmat γ.2 = 1`. Rewrite using `[hfin, hg, Matrix.map_one _ (map_zero _) (map_one _)]`.

Conclude with `Subtype.ext (Units.ext (by simpa using hf))`.
-/
theorem GFset_eq_one_of_place (I : AutInst) (γ : I.GA) (hγ : γ ∈ I.GFset) (v : InfinitePlace I.F)
    (h : uMat (γ.1 v) = 1) : γ = 1 := by
  obtain ⟨g, -, hinf, hfin⟩ := hγ
  have hdet : ∀ w, IsUnit (I.P w).det := fun w => (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit w)
  set M : Matrix (Fin I.n) (Fin I.n) I.E := (g : Matrix (Fin I.n) (Fin I.n) I.E) with hM
  have e1 : (I.P v)⁻¹ * M.map (I.φ v) * I.P v = 1 := (hinf v).symm.trans h
  have e2 : M.map (I.φ v) * I.P v = I.P v := by
    have := congrArg (I.P v * ·) e1
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hdet v)] using this
  have e3 : M.map (I.φ v) = 1 := by
    have := congrArg (· * (I.P v)⁻¹) e2
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hdet v)] using this
  have hg : M = 1 := by
    apply Matrix.map_injective (I.φ v).injective
    dsimp only
    rw [e3, Matrix.map_one _ (map_zero _) (map_one _)]
  refine Prod.ext (funext fun w => ?_) ?_
  · have hw : uMat (γ.1 w) = 1 := by
      rw [hinf w, hg, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
        Matrix.nonsing_inv_mul _ (hdet w)]
    exact Subtype.ext (Units.ext (by simpa using hw))
  · have hf : I.fmat γ.2 = 1 := by
      rw [hfin, hg, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Subtype.ext (Units.ext (by simpa using hf))

/- English proof (translation)
Use `⟨1, Subgroup.one_mem _, fun v => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))]`. Both sides reduce to the same expression. Rewrite using `[Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]`. Both sides reduce to the same expression.
-/
theorem one_mem_GFset_def (I : AutInst) : (1 : I.GA) ∈ I.GFset := by
  refine ⟨1, Subgroup.one_mem _, fun v => ?_, ?_⟩
  · rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))]
    rfl
  · rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rfl

/- English proof (translation)
Introduce `B d p hH hfin`. Establish `hn : B.I.n = p` using `hH.rank_eq`. Take `⟨hDS, hSig, hp, -, hprime, hgt, hsplit⟩` from `hH`. Establish `hn1 : 1 ≤ B.I.n` using `hn ▸ hp`. Establish `hq : ∀ v, (univ.filter fun a => B.I.ε v a = false).card = 0` using `fun v => (hSig v).2`.

Establish `hrk : ∀ v, rkR (B.I.ε v) = 0` using `fun v => by`. Unfold `rkR`. Rewrite using `[hq v]`. Conclude with `Nat.min_zero _`. Establish `hpos : ∀ v a, B.I.ε v a = true` using `fun v a => by`.

Assume the negation of the conclusion as `hne`. Establish `ha : a ∈ univ.filter fun a => B.I.ε v a = false` using `by simpa using hne`. Rewrite `ha` using `[Finset.card_eq_zero.mp (hq v)]`. Conclude with `Finset.notMem_empty a ha`. Establish `hJ : ∀ v, Formalism.REAL.Jm (B.I.ε v) = 1` using `fun v => by`.

Unfold `Formalism.REAL.Jm`. Simplify using `[hpos v]`. Establish `hunit : ∀ v (g : Formalism.REAL.UJ (B.I.ε v)), (uMat g)ᴴ * uMat g = 1` using `fun v g => by`. Establish `h0 : (uMat g)ᴴ * Formalism.REAL.Jm (B.I.ε v) * uMat g = Formalism.REAL.Jm (B.I.ε v)` using `g.2`. Rewrite `h0` using `[hJ v, Matrix.mul_one]`. Then use the resulting hypothesis.

Establish `hdHS : ∀ v (g : Formalism.REAL.UJ (B.I.ε v)), dHS (uMat g) = 0` using `fun v g => (GlobalTheory.T.logSingularValuesEuclidNorm_cartan_properties B.I.n (B.I.ε v)).2.2.2 (hrk v) g`. Establish `hrad` using `GlobalTheory.T.isRadical_span_prime_of_ncard_primesOver_eq_finrank B.I.E B.g₀ hprime hsplit`. Establish `hNU` using `(GlobalTheory.NearElement.near_unipotent B d (1 / 10 ^ 5) (by norm_num) le_rfl hn1 hgt hrad _ _`. Use `rfl rfl).1`. Establish `hkey : ∀ x γ : B.I.GA, γ ∈ B.I.GFset → phe B d (x⁻¹ * γ * x) ≠ 0 → γ = 1`.

Introduce `x γ hγ hne`. Establish `hep : (0 : ℝ) ≤ 1 / 10 ^ 5 / ((B.I.n : ℝ) ^ 8 * (B.I.f : ℝ) ^ 2)` using `by positivity`. Take `⟨-, hu, -⟩` from `hNU x γ ⟨hγ, hne, fun v => by rw [hdHS]; exact hep⟩`. Take `⟨v⟩ : Nonempty (InfinitePlace B.I.F)` from `inferInstance`. Apply `GFset_eq_one_of_place B.I γ hγ v` to reduce the goal to its premises.

Apply `GlobalTheory.unipotent_isometry_definite_eq_one B.I.n B.I.n _ 1 one_ne_zero _ (hu v)` to reduce the goal to its premises. Simplify using `using hunit v (γ.1 v)`. Establish `hker : ∀ x, kern B.I (phe B d) x x = phe B d 1`. Introduce `x`. Unfold `kern`.

Rewrite using `[tsum_eq_single (⟨1, one_mem_GFset_def B.I⟩ : B.I.GFset)]`. Simplify using the standard rewrite rules. Introduce `γ hγ`. Assume the negation of the conclusion as `hne`. Conclude with `hγ (Subtype.ext (hkey x γ.1 γ.2 hne))`.

Establish `hph1 : ph B d 1 = ((∏ v, d v : ℝ) : ℂ)`. Unfold `ph`. Establish `hc : ∀ v, ⟪B.w v, B.σ v (uMat ((1 : B.I.Ginf) v)) (B.w v)⟫_ℂ = 1`. Introduce `v`. Establish `hs : B.σ v (uMat ((1 : B.I.Ginf) v)) = 1`.

Rewrite using `[show uMat ((1 : B.I.Ginf) v) = 1 from rfl]`. Conclude with `(hDS v).2.1.2.2.1.1.1`. Rewrite using `[hs, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, (hDS v).2.2.1.1]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.prod_congr rfl (fun v _ => hc v)]`.

Simplify using the standard rewrite rules. Establish `hloc : LocDec B 0`. Introduce `v g`. Establish `hd : decE (rkR (B.I.ε v)) 0 (dOp (uMat g)) = 1` using `by simp [decE]`. Rewrite using `[hd]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hbig : HBig B 32 0`. Introduce `v`. Rewrite using `[hrk v]`. Simplify using the standard rewrite rules.

Take `⟨hcont, hbd, hmaj⟩` from `GlobalTheory.T.discrete_series_coefficient_integrable_majorant B d 0 hDS hloc`. Establish `hm` using `hmaj 0 le_rfl (fun v => Or.inl (hrk v))`. Simplify using `only [zero_mul, Real.exp_zero, mul_one] at hm`. Establish `hint : Integrable (ph B d) (muInf B.I)` using `hm.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall hbd)`. Take `⟨T, hT⟩` from `(GlobalTheory.T.globalConvolutionOrthogonalProjector_proof B d hDS hint).2.2.1`.

Take `⟨-, -, -, -, -, -, -, hD, -⟩` from `GlobalTheory.T.kernelB' B d 0 hDS hn1 hloc hbig hfin T hT`. Rewrite `hD` using `[hker]`. Rewrite `hD` using `[setIntegral_const]`. Establish `hphe : phe B d 1 = ((∏ v, d v : ℝ) : ℂ) * B.e 1` using `by show ph B d (1 : B.I.GA).1 * B.e (1 : B.I.GA).2 = _`. Rewrite using `[Prod.fst_one, Prod.snd_one, hph1]`.

Rewrite `hD` using `[hphe]`. Establish `he1` using `(GlobalTheory.rowsAut_idem_elementary B).1`. Establish `hre` using `congrArg Complex.re hD`. Simplify using `only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, he1, mul_zero, sub_zero, zero_mul, Complex.natCast_re] at hre`. Unfold `mainTerm AutInst.Dstar AutInst.vol`.

Rewrite using `[← hre, measureReal_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem definite_count_of_finite : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p : ℕ),
    GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFiniteCount.DefiniteHyp B d p → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) →
      (B.D : ℝ) = mainTerm B d := by
  intro B d p hH hfin
  have hn : B.I.n = p := hH.rank_eq
  obtain ⟨hDS, hSig, hp, -, hprime, hgt, hsplit⟩ := hH
  have hn1 : 1 ≤ B.I.n := hn ▸ hp

  have hq : ∀ v, (univ.filter fun a => B.I.ε v a = false).card = 0 := fun v => (hSig v).2
  have hrk : ∀ v, rkR (B.I.ε v) = 0 := fun v => by
    unfold rkR
    rw [hq v]
    exact Nat.min_zero _
  have hpos : ∀ v a, B.I.ε v a = true := fun v a => by
    by_contra hne
    have ha : a ∈ univ.filter fun a => B.I.ε v a = false := by simpa using hne
    rw [Finset.card_eq_zero.mp (hq v)] at ha
    exact Finset.notMem_empty a ha
  have hJ : ∀ v, Formalism.REAL.Jm (B.I.ε v) = 1 := fun v => by
    unfold Formalism.REAL.Jm
    simp [hpos v]
  have hunit : ∀ v (g : Formalism.REAL.UJ (B.I.ε v)), (uMat g)ᴴ * uMat g = 1 := fun v g => by
    have h0 : (uMat g)ᴴ * Formalism.REAL.Jm (B.I.ε v) * uMat g = Formalism.REAL.Jm (B.I.ε v) := g.2
    rwa [hJ v, Matrix.mul_one] at h0
  have hdHS : ∀ v (g : Formalism.REAL.UJ (B.I.ε v)), dHS (uMat g) = 0 := fun v g =>
    (GlobalTheory.T.logSingularValuesEuclidNorm_cartan_properties B.I.n (B.I.ε v)).2.2.2 (hrk v) g

  have hrad := GlobalTheory.T.isRadical_span_prime_of_ncard_primesOver_eq_finrank B.I.E B.g₀ hprime hsplit
  have hNU := (GlobalTheory.NearElement.near_unipotent B d (1 / 10 ^ 5) (by norm_num) le_rfl hn1 hgt hrad _ _
    rfl rfl).1
  have hkey : ∀ x γ : B.I.GA, γ ∈ B.I.GFset → phe B d (x⁻¹ * γ * x) ≠ 0 → γ = 1 := by
    intro x γ hγ hne
    have hep : (0 : ℝ) ≤ 1 / 10 ^ 5 / ((B.I.n : ℝ) ^ 8 * (B.I.f : ℝ) ^ 2) := by positivity
    obtain ⟨-, hu, -⟩ := hNU x γ ⟨hγ, hne, fun v => by rw [hdHS]; exact hep⟩
    obtain ⟨v⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
    apply GFset_eq_one_of_place B.I γ hγ v
    apply GlobalTheory.unipotent_isometry_definite_eq_one B.I.n B.I.n _ 1 one_ne_zero _ (hu v)
    simpa using hunit v (γ.1 v)

  have hker : ∀ x, kern B.I (phe B d) x x = phe B d 1 := by
    intro x
    unfold kern
    rw [tsum_eq_single (⟨1, one_mem_GFset_def B.I⟩ : B.I.GFset)]
    · simp
    · intro γ hγ
      by_contra hne
      exact hγ (Subtype.ext (hkey x γ.1 γ.2 hne))
  have hph1 : ph B d 1 = ((∏ v, d v : ℝ) : ℂ) := by
    unfold ph
    have hc : ∀ v, ⟪B.w v, B.σ v (uMat ((1 : B.I.Ginf) v)) (B.w v)⟫_ℂ = 1 := by
      intro v
      have hs : B.σ v (uMat ((1 : B.I.Ginf) v)) = 1 := by
        rw [show uMat ((1 : B.I.Ginf) v) = 1 from rfl]
        exact (hDS v).2.1.2.2.1.1.1
      rw [hs, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, (hDS v).2.2.1.1]
      simp
    rw [Finset.prod_congr rfl (fun v _ => hc v)]
    simp

  have hloc : LocDec B 0 := by
    intro v g
    have hd : decE (rkR (B.I.ε v)) 0 (dOp (uMat g)) = 1 := by simp [decE]
    rw [hd]
    calc ‖⟪B.w v, B.σ v (uMat g) (B.w v)⟫_ℂ‖ ≤ ‖B.w v‖ * ‖B.σ v (uMat g) (B.w v)‖ :=
          norm_inner_le_norm _ _
      _ = 1 := by rw [(hDS v).2.1.2.2.1.2.1 _ g.2 _, (hDS v).2.2.1.1]; norm_num
  have hbig : HBig B 32 0 := by
    intro v
    rw [hrk v]
    simp
  obtain ⟨hcont, hbd, hmaj⟩ := GlobalTheory.T.discrete_series_coefficient_integrable_majorant B d 0 hDS hloc
  have hm := hmaj 0 le_rfl (fun v => Or.inl (hrk v))
  simp only [zero_mul, Real.exp_zero, mul_one] at hm
  have hint : Integrable (ph B d) (muInf B.I) :=
    hm.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  obtain ⟨T, hT⟩ := (GlobalTheory.T.globalConvolutionOrthogonalProjector_proof B d hDS hint).2.2.1
  obtain ⟨-, -, -, -, -, -, -, hD, -⟩ := GlobalTheory.T.kernelB' B d 0 hDS hn1 hloc hbig hfin T hT
  simp_rw [hker] at hD
  rw [setIntegral_const] at hD
  have hphe : phe B d 1 = ((∏ v, d v : ℝ) : ℂ) * B.e 1 := by
    show ph B d (1 : B.I.GA).1 * B.e (1 : B.I.GA).2 = _
    rw [Prod.fst_one, Prod.snd_one, hph1]
  rw [hphe] at hD
  have he1 := (GlobalTheory.rowsAut_idem_elementary B).1
  have hre := congrArg Complex.re hD
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, he1,
    mul_zero, sub_zero, zero_mul, Complex.natCast_re] at hre
  unfold mainTerm AutInst.Dstar AutInst.vol
  rw [← hre, measureReal_def]
  ring

end GlobalTheory.Dec
