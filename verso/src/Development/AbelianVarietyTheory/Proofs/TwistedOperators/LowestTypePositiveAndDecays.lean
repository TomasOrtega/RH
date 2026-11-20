import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiHolomorphicNearPositiveMatricesAtOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KTypeExtendsHolomorphicComplexifiedK
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedAdjoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TorusWeightVectorIffCartanWeightVector
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimKStableSubspaceKFiniteLie
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsKStableOnOfLieStableFiniteDim
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HighestWeightGeneratedWeightsBelow
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DiscreteSeriesCoverIrreducibleUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlWordJetRelationsEqZeroOfNilStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompressedWordsGlWordJetRelationsOfNoTypesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryFlowCoeffEqOfTaylorSeriesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlWordJetRelationsOfSchmidSystemJetsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedDerivInnerExpEqWordJetFormsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeFunctionEquivalenceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeRootArrayHighestVectorCoeffEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerKTypesPTensorStableUnderKStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FderivLeadingMinorPowerProductStrictUpperEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerFderivKAveragedMinorOperatorIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHolomorphicLowestKTypeComplexifiedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KAveragedMinorOperatorExpPosBoundAnalyticStatement

noncomputable section

namespace GlobalTheory.SphJet

section Linear

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] {E : Fin n → Fin n → Module.End ℂ V} {u : V} {j : W →ₗᵢ[ℂ] V}
  {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W}

/- English proof (translation)
Introduce `G hG`. Take `⟨hopen, hpos, -, -⟩` from `GlobalTheory.Dec.psBasic n ε lam W τ w hl hτ`. Establish `hopen' : IsOpen (U1 ε)` using `hopen`. Use `filter_upwards [hopen'.mem_nhds (hpos 1 Matrix.PosDef.one)] with z hz`. Use `ext_inner_left ℂ fun y => ?_` and prove the remaining obligations.

Establish `hd` using `fun p => GlobalTheory.T.inner_fderiv_kAveragedMinorOperator_integral n ε lam W τ w hl hτ z hz (z * thE ε p) y (G p)`. Rewrite using `[inner_sum, inner_zero_right]`. Simplify using `only [fun p => (hd p).2]`. Rewrite using `[← Finset.mul_sum, ← integral_finset_sum _ fun p _ => (hd p).1]`. Use `mul_eq_zero_of_right _ (integral_eq_zero_of_ae (Eventually.of_forall fun k => ?_))` and prove the remaining obligations.

Take `⟨G', hG', he⟩` from `GlobalTheory.T.lowerKTypes_pTensor_stable_under_K V W n ε E _ u j τ w hD hτ ht G hG (toMK k) k.2`. Establish `hk : toMK k * (toMK k)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (TauExt.mem_KC k.2).1)`. Establish `h0` using `GlobalTheory.T.fderiv_leadingMinorPowerProduct_strictUpper_eq_zero n lam ((toMK k)⁻¹ * z * toMK k) (∑ p, ⟪w, G' p⟫_ℂ • thE ε p) (hz _ k.2) (by`. Introduce `i i' hi`. Rewrite using `[Matrix.sum_apply]`.

Use `Finset.sum_eq_zero fun p _ => ?_` and prove the remaining obligations. Distinguish the cases in `hp : p = (i', i)`. Substitute `hp` using the available equality. Use `GlobalTheory.T.negativeRootArray_highestVector_coeff_eq_zero V n ε E _ u hD.1 hD.2.1 hD.2.2.1 _ hG' i' i hi` as an intermediate fact. Establish `e : ⟪w, G' (i', i)⟫_ℂ = 0` using `by rw [← j.inner_map_map, hw]; exact this`.

Rewrite using `[e, zero_smul, Matrix.zero_apply]`. Establish `: Matrix.single p.2 p.1 (1 : ℂ) i i' = 0` using `Matrix.single_apply_of_ne _ _ _ _ _ fun h => hp (Prod.ext h.2 h.1)`. Rewrite using `[thE, Matrix.smul_apply, Matrix.smul_apply, this, smul_zero, smul_zero])`. Rewrite `h0` using `[← he, Matrix.mul_sum, map_sum]`. Establish `e : ∀ p, (toMK k)⁻¹ * z * toMK k * (⟪τ (toMK k) w, G p⟫_ℂ • ((toMK k)⁻¹ * thE ε p * toMK k)) = ⟪τ (toMK k) w, G p⟫_ℂ • ((toMK k)⁻¹ * (z * thE ε p) * toMK k)` using `fun p => by`.

Rewrite using `[Matrix.mul_smul]`. Use `congr 1`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (toMK k), hk, Matrix.one_mul]`. Simplify using `only [e, map_smul, smul_eq_mul] at h0`.

Use `congrArg (fun c => ⟪y, τ (toMK k) w⟫_ℂ * c) h0` as an intermediate fact. Simplify using `only [Finset.mul_sum, mul_zero] at this`. Express the relevant statement in the definitionally equal form `∑ p, _ = (0 : ℂ)`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun p _ => by ring`.
-/
theorem funSchmid_ps (hl : IsHCParam lam) (hτ : IsTau ε (lowK ε lam) τ w) (hD : LowData ε E (lowK ε lam) u j)
    (hw : j w = u) (ht : TauTie ε E j τ) : FunSchmid ε E (lowK ε lam) u j (ps ε lam τ w) := by
  intro G hG
  obtain ⟨hopen, hpos, -, -⟩ := GlobalTheory.Dec.psBasic n ε lam W τ w hl hτ
  have hopen' : IsOpen (U1 ε) := hopen
  filter_upwards [hopen'.mem_nhds (hpos 1 Matrix.PosDef.one)] with z hz
  refine ext_inner_left ℂ fun y => ?_
  have hd := fun p => GlobalTheory.T.inner_fderiv_kAveragedMinorOperator_integral n ε lam W τ w hl hτ z hz (z * thE ε p) y (G p)
  rw [inner_sum, inner_zero_right]
  simp only [fun p => (hd p).2]
  rw [← Finset.mul_sum, ← integral_finset_sum _ fun p _ => (hd p).1]
  refine mul_eq_zero_of_right _ (integral_eq_zero_of_ae (Eventually.of_forall fun k => ?_))
  obtain ⟨G', hG', he⟩ := GlobalTheory.T.lowerKTypes_pTensor_stable_under_K V W n ε E _ u j τ w hD hτ ht G hG (toMK k) k.2
  have hk : toMK k * (toMK k)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (TauExt.mem_KC k.2).1)
  have h0 := GlobalTheory.T.fderiv_leadingMinorPowerProduct_strictUpper_eq_zero n lam ((toMK k)⁻¹ * z * toMK k) (∑ p, ⟪w, G' p⟫_ℂ • thE ε p) (hz _ k.2) (by
    intro i i' hi
    rw [Matrix.sum_apply]
    refine Finset.sum_eq_zero fun p _ => ?_
    by_cases hp : p = (i', i)
    · subst hp
      have := GlobalTheory.T.negativeRootArray_highestVector_coeff_eq_zero V n ε E _ u hD.1 hD.2.1 hD.2.2.1 _ hG' i' i hi
      have e : ⟪w, G' (i', i)⟫_ℂ = 0 := by rw [← j.inner_map_map, hw]; exact this
      rw [e, zero_smul, Matrix.zero_apply]
    · have : Matrix.single p.2 p.1 (1 : ℂ) i i' = 0 :=
        Matrix.single_apply_of_ne _ _ _ _ _ fun h => hp (Prod.ext h.2 h.1)
      rw [thE, Matrix.smul_apply, Matrix.smul_apply, this, smul_zero, smul_zero])
  rw [← he, Matrix.mul_sum, map_sum] at h0
  have e : ∀ p, (toMK k)⁻¹ * z * toMK k * (⟪τ (toMK k) w, G p⟫_ℂ • ((toMK k)⁻¹ * thE ε p * toMK k)) =
      ⟪τ (toMK k) w, G p⟫_ℂ • ((toMK k)⁻¹ * (z * thE ε p) * toMK k) := fun p => by
    rw [Matrix.mul_smul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (toMK k), hk, Matrix.one_mul]
  simp only [e, map_smul, smul_eq_mul] at h0
  have := congrArg (fun c => ⟪y, τ (toMK k) w⟫_ℂ * c) h0
  simp only [Finset.mul_sum, mul_zero] at this
  change ∑ p, _ = (0 : ℂ)
  rw [← this]
  exact Finset.sum_congr rfl fun p _ => by ring

/- English proof (translation)
Use `congrFun (congrFun hX.2 a) b` as an intermediate fact. Simplify using `only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply, h] at this`. Use `split_ifs at this`. Take the linear combination `(1 / 2 : ℂ) * this`. Take the linear combination `(-1 / 2 : ℂ) * this`.
-/
theorem apply_eq_zero_of_mem_noncompactPart {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) {a b : Fin n} (h : ε a = ε b) : X a b = 0 := by
  have := congrFun (congrFun hX.2 a) b
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply, h] at this
  split_ifs at this
  · linear_combination (1 / 2 : ℂ) * this
  · linear_combination (-1 / 2 : ℂ) * this

/- English proof (translation)
Use extensionality with `i i'`. Rewrite using `[thM, Matrix.sum_apply, Finset.sum_eq_single (i', i)]`. Distinguish the cases in `h : ε i' = ε i`. Simplify using `[apply_eq_zero_of_mem_noncompactPart hX h]`. Simplify using `[thE, sgn, h]`.

Introduce `p _ hp`. Establish `: Matrix.single p.2 p.1 (1 : ℂ) i i' = 0` using `Matrix.single_apply_of_ne _ _ _ _ _ fun h => hp (Prod.ext h.2 h.1)`. Rewrite using `[thE, Matrix.smul_apply, Matrix.smul_apply, this, smul_zero, smul_zero]`. Simplify using the standard rewrite rules.
-/
theorem thM_eq {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) : thM ε X = Xᵀ := by
  ext i i'
  rw [thM, Matrix.sum_apply, Finset.sum_eq_single (i', i)]
  · by_cases h : ε i' = ε i
    · simp [apply_eq_zero_of_mem_noncompactPart hX h]
    · simp [thE, sgn, h]
  · intro p _ hp
    have : Matrix.single p.2 p.1 (1 : ℂ) i i' = 0 :=
      Matrix.single_apply_of_ne _ _ _ _ _ fun h => hp (Prod.ext h.2 h.1)
    rw [thE, Matrix.smul_apply, Matrix.smul_apply, this, smul_zero, smul_zero]
  · simp

/- English proof (translation)
Take `⟨h1, h2⟩` from `(parabolic_character_holds n ε X).1.1 hX`. Use `(parabolic_character_holds n ε _).1.2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]`. Use `congr 1`. Conclude with `congrArg Matrix.transpose h1`.

Establish `h3` using `congrArg Matrix.transpose h2`. Establish `hJ : (Formalism.REAL.Jm ε)ᵀ = Formalism.REAL.Jm ε` using `Matrix.diagonal_transpose _`. Rewrite `h3` using `[Matrix.transpose_neg, Matrix.transpose_mul, Matrix.transpose_mul, hJ]`. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, h3, smul_neg, neg_neg]`.
-/
theorem smul_transpose_mem_noncompactPart {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (t : ℝ) : inP ε ((t : ℂ) • Xᵀ) := by
  obtain ⟨h1, h2⟩ := (parabolic_character_holds n ε X).1.1 hX
  refine (parabolic_character_holds n ε _).1.2 ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
    congr 1
    exact congrArg Matrix.transpose h1
  · have h3 := congrArg Matrix.transpose h2
    have hJ : (Formalism.REAL.Jm ε)ᵀ = Formalism.REAL.Jm ε := Matrix.diagonal_transpose _
    rw [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.transpose_mul, hJ] at h3
    rw [Matrix.smul_mul, Matrix.mul_smul, h3, smul_neg, neg_neg]

/- English proof (translation)
Use `haveI := hτ.1`. Use `haveI : CompleteSpace W := FiniteDimensional.complete ℂ W`. Establish `han : ∀ Y, inP ε Y → AnalyticAt ℂ (ps ε lam τ w) (NormedSpace.exp Y)` using `fun Y hY => (GlobalTheory.T.kAveragedMinorOperator_exp_pos_bound_analytic n ε lam W τ w hl hτ _ hg Y hY).2.2`. Establish `h1 : AnalyticAt ℂ (ps ε lam τ w) 1` using `by simpa using han _ (smul_transpose_mem_noncompactPart hX 0)`. Establish `r1` using `GlobalTheory.T.glWordJetRelations_of_schmidSystem_jets V W n ε E _ u j _ h1 (GlobalTheory.T.lowest_K_type_function_equivalence n ε lam W τ w hl hτ V E u j hD ht) (funSchmid_ps hl hτ hD hw ht)`.

Establish `r2` using `GlobalTheory.T.compressedWords_glWordJetRelations_of_no_types V W n ε E _ u j hD hlow`. Establish `r3` using `GlobalTheory.T.glWordJetRelations_eq_zero_of_nil V W n ε E lam u j _ hD (fun a b hab hne => by`. Use `hg a b hne` as an intermediate fact. Rewrite using `[abs_of_pos (sub_pos.2 (hl.1 hab))] at this) (r1.sub r2) (by` and apply the resulting hypothesis. Use extensionality with `y x`.

Establish `: ps ε lam τ w 1 = ContinuousLinearMap.id ℂ W` using `(GlobalTheory.Dec.psBasic n ε lam W τ w hl hτ).2.2.2`. Simplify using `[funJet_apply, modJet_apply, Rw, ew, this])`. Establish `r4` using `GlobalTheory.T.iteratedDeriv_inner_exp_eq_wordJetForms V W n ε E j _ h1 (fun l => sub_eq_zero.1 (r3 l)) X`. Rewrite `r4` using `[thM_eq hX]`. Establish `hφ : ∀ y x : W, AnalyticOnNhd ℝ (fun t : ℝ => ⟪y, ps ε lam τ w (NormedSpace.exp ((t : ℂ) • Xᵀ)) x⟫_ℂ) Set.univ`.

Introduce `y x t _`. Establish `a1 : AnalyticAt ℂ (fun s : ℂ => NormedSpace.exp (s • Xᵀ)) t` using `(Differentiable.analyticAt fun s => (hasDerivAt_exp_smul_const (𝕂 := ℂ) Xᵀ s).differentiableAt) _`. Establish `a2` using `(((innerSL ℂ y).comp (ContinuousLinearMap.apply ℂ W x)).analyticAt _).comp ((han _ (smul_transpose_mem_noncompactPart hX t)).comp (f := fun s : ℂ => NormedSpace.exp (s • Xᵀ)) a1)`. Conclude with `(a2.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t)`. Establish `hU : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε` using `exp_indefinite_unitary_holds n ε X hX.1`.

Establish `key` using `GlobalTheory.T.unitaryFlow_coeff_eq_of_taylor_series H (fun t => σ (NormedSpace.exp ((t : ℂ) • X))) (fun m => ι ((actM E X ^ m) (j x))) (ι (j y)) _ _ (by simpa using hσ.1.1) (fun s t => by`. Rewrite using `[Complex.ofReal_add, add_smul, Matrix.exp_add_of_commute _ _ ((Commute.refl X).smul_left _ |>.smul_right _)]`. Conclude with `hσ.1.2 _ (hU s) _ (hU t)) (fun t v => hσ.2.1 _ (hU t) v)`. Use the proof step `(fun m => by rw [pow_succ', Module.End.mul_apply]; exact hder X hX.1 _) (hφ y x) (hφ x x 0 trivial)`. Use the proof step `(fun m => by rw [r4, ι.inner_map_map]) (fun m => by rw [r4, ι.inner_map_map]; rfl) 1`.

Simplify using `using key.symm`.
-/
theorem compress_eq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ι : V →ₗᵢ[ℂ] H}
    (hl : IsHCParam lam) (hg : GapAtLeast ε lam (2 * n + 1)) (hσ : IsURepOn (UJset ε) σ) (hder : DerTie ε σ E ι)
    (hτ : IsTau ε (lowK ε lam) τ w) (hD : LowData ε E (lowK ε lam) u j) (hw : j w = u) (ht : TauTie ε E j τ)
    (hlow : ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ x : V, KHighest ε E (lowK ε lam - root a b) x → x = 0)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (y x : W) :
    ⟪ι (j y), σ (NormedSpace.exp X) (ι (j x))⟫_ℂ = ⟪y, ps ε lam τ w (NormedSpace.exp Xᵀ) x⟫_ℂ := by
  haveI := hτ.1
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have han : ∀ Y, inP ε Y → AnalyticAt ℂ (ps ε lam τ w) (NormedSpace.exp Y) := fun Y hY =>
    (GlobalTheory.T.kAveragedMinorOperator_exp_pos_bound_analytic n ε lam W τ w hl hτ _ hg Y hY).2.2
  have h1 : AnalyticAt ℂ (ps ε lam τ w) 1 := by simpa using han _ (smul_transpose_mem_noncompactPart hX 0)
  have r1 := GlobalTheory.T.glWordJetRelations_of_schmidSystem_jets V W n ε E _ u j _ h1 (GlobalTheory.T.lowest_K_type_function_equivalence n ε lam W τ w hl hτ V E u j hD ht)
    (funSchmid_ps hl hτ hD hw ht)
  have r2 := GlobalTheory.T.compressedWords_glWordJetRelations_of_no_types V W n ε E _ u j hD hlow
  have r3 := GlobalTheory.T.glWordJetRelations_eq_zero_of_nil V W n ε E lam u j _ hD (fun a b hab hne => by
    have := hg a b hne
    rwa [abs_of_pos (sub_pos.2 (hl.1 hab))] at this) (r1.sub r2) (by
    ext y x
    have : ps ε lam τ w 1 = ContinuousLinearMap.id ℂ W := (GlobalTheory.Dec.psBasic n ε lam W τ w hl hτ).2.2.2
    simp [funJet_apply, modJet_apply, Rw, ew, this])
  have r4 := GlobalTheory.T.iteratedDeriv_inner_exp_eq_wordJetForms V W n ε E j _ h1 (fun l => sub_eq_zero.1 (r3 l)) X
  rw [thM_eq hX] at r4
  have hφ : ∀ y x : W, AnalyticOnNhd ℝ
      (fun t : ℝ => ⟪y, ps ε lam τ w (NormedSpace.exp ((t : ℂ) • Xᵀ)) x⟫_ℂ) Set.univ := by
    intro y x t _
    have a1 : AnalyticAt ℂ (fun s : ℂ => NormedSpace.exp (s • Xᵀ)) t :=
      (Differentiable.analyticAt fun s => (hasDerivAt_exp_smul_const (𝕂 := ℂ) Xᵀ s).differentiableAt) _
    have a2 := (((innerSL ℂ y).comp (ContinuousLinearMap.apply ℂ W x)).analyticAt _).comp
      ((han _ (smul_transpose_mem_noncompactPart hX t)).comp (f := fun s : ℂ => NormedSpace.exp (s • Xᵀ)) a1)
    exact (a2.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t)
  have hU : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε := exp_indefinite_unitary_holds n ε X hX.1
  have key := GlobalTheory.T.unitaryFlow_coeff_eq_of_taylor_series H (fun t => σ (NormedSpace.exp ((t : ℂ) • X))) (fun m => ι ((actM E X ^ m) (j x)))
    (ι (j y)) _ _ (by simpa using hσ.1.1) (fun s t => by
      rw [Complex.ofReal_add, add_smul, Matrix.exp_add_of_commute _ _ ((Commute.refl X).smul_left _ |>.smul_right _)]
      exact hσ.1.2 _ (hU s) _ (hU t)) (fun t v => hσ.2.1 _ (hU t) v)
    (fun m => by rw [pow_succ', Module.End.mul_apply]; exact hder X hX.1 _) (hφ y x) (hφ x x 0 trivial)
    (fun m => by rw [r4, ι.inner_map_map]) (fun m => by rw [r4, ι.inner_map_map]; rfl) 1
  simpa using key.symm

/- English proof (translation)
Take `⟨W, _, _, τ, w, j, hτ, hw, hr, ht⟩` from `GlobalTheory.T.exists_holomorphic_lowestKType_complexified n ε _ H V σ E ι u hσ hder hu hK hwt`. Establish `e` using `compress_eq hl hg hσ hder hτ ⟨hE, hUn, hhi, hfin, hr⟩ hw ht hlow hX`. Establish `hXt : inP ε Xᵀ` using `by simpa using smul_transpose_mem_noncompactPart hX 1`. Take `⟨p1, p2, -⟩` from `GlobalTheory.T.kAveragedMinorOperator_exp_pos_bound_analytic n ε lam W τ w hl hτ h hh _ hXt`. Establish `hhs : hs Xᵀ = hs X` using `by unfold hs; exact Finset.sum_comm`.

Rewrite `hx`, the goal using `[← hr]`. Take `⟨_, ⟨x, rfl⟩, rfl⟩` from `hx`. Use `⟨(e x x).symm ▸ p1 x, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨y, rfl⟩, rfl⟩`. Use `(congrArg norm (e y x)).trans_le ((norm_inner_le_norm _ _).trans ?_)` and prove the remaining obligations.

Simplify using `only [LinearIsometry.coe_toLinearMap, LinearIsometry.norm_map]`. Rewrite using `[mul_comm, ← hhs]`. Conclude with `mul_le_mul_of_nonneg_right (((ps ε lam τ w _).le_opNorm x).trans (mul_le_mul_of_nonneg_right p2 (norm_nonneg _))) (norm_nonneg _)`.
-/
theorem core {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ι : V →ₗᵢ[ℂ] H} {h : ℝ}
    (hl : IsHCParam lam) (hh : GapAtLeast ε lam h) (hg : GapAtLeast ε lam (2 * n + 1))
    (hσ : IsURepOn (UJset ε) σ) (hder : DerTie ε σ E ι) (hE : GlRel E) (hUn : IsUnitary ε E) (hu : ‖u‖ = 1)
    (hhi : KHighest ε E (lowK ε lam) u) (hfin : FiniteDimensional ℂ (kSpan ε E u))
    (hK : IsKTypeOf ε σ (lowK ε lam) ((kSpan ε E u).map ι.toLinearMap))
    (hwt : IsWtOn (Kset ε) σ (lowK ε lam) (ι u))
    (hlow : ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ x : V, KHighest ε E (lowK ε lam - root a b) x → x = 0)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) {x : H} (hx : x ∈ (kSpan ε E u).map ι.toLinearMap) :
    0 ≤ ⟪x, σ (NormedSpace.exp X) x⟫_ℂ ∧ ∀ y ∈ (kSpan ε E u).map ι.toLinearMap,
      ‖⟪y, σ (NormedSpace.exp X) x⟫_ℂ‖ ≤ decHS h (rkR ε) (Real.sqrt (hs X)) * ‖x‖ * ‖y‖ := by
  obtain ⟨W, _, _, τ, w, j, hτ, hw, hr, ht⟩ := GlobalTheory.T.exists_holomorphic_lowestKType_complexified n ε _ H V σ E ι u hσ hder hu hK hwt
  have e := compress_eq hl hg hσ hder hτ ⟨hE, hUn, hhi, hfin, hr⟩ hw ht hlow hX
  have hXt : inP ε Xᵀ := by simpa using smul_transpose_mem_noncompactPart hX 1
  obtain ⟨p1, p2, -⟩ := GlobalTheory.T.kAveragedMinorOperator_exp_pos_bound_analytic n ε lam W τ w hl hτ h hh _ hXt
  have hhs : hs Xᵀ = hs X := by unfold hs; exact Finset.sum_comm
  rw [← hr] at hx ⊢
  obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := hx
  refine ⟨(e x x).symm ▸ p1 x, ?_⟩
  rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
  refine (congrArg norm (e y x)).trans_le ((norm_inner_le_norm _ _).trans ?_)
  simp only [LinearIsometry.coe_toLinearMap, LinearIsometry.norm_map]
  rw [mul_comm, ← hhs]
  exact mul_le_mul_of_nonneg_right (((ps ε lam τ w _).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right p2 (norm_nonneg _))) (norm_nonneg _)

end Linear

section Cover

open Matrix Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.MainNotions.S GlobalTheory.RealPar
open scoped InnerProductSpace ComplexOrder

variable {p q n : ℕ} {e : Ix p q ≃ Fin n} {ε : Fin n → Bool}

section Alg

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def unitOp (e : Ix p q ≃ Fin n) (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (a b : Fin n) : Module.End ℂ V :=
  act (Eab (e.symm a) (e.symm b))

/- English proof (translation)
Use `conv_lhs => rw [Matrix.matrix_eq_sum_single Z]`. Simplify using `only [map_sum, Eab, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]`.
-/
theorem act_eq_sum (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (Z : Mat p q) :
    act Z = ∑ a, ∑ b, Z a b • act (Eab a b) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  simp only [map_sum, Eab, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

/- English proof (translation)
Rewrite using `[act_eq_sum act Z, actM, ← e.sum_comp]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← e.sum_comp]`. Simplify using `[unitOp]`.
-/
theorem actM_unitOp (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (Z : Mat p q) :
    actM (unitOp e act) (Matrix.reindex e e Z) = act Z := by
  rw [act_eq_sum act Z, actM, ← e.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← e.sum_comp]
  simp [unitOp]

/- English proof (translation)
Introduce `a b c d`. Unfold `unitOp`. Rewrite using `[← h, map_sub]`. Use `congr 1`. Use `split_ifs with h1`.

Substitute `h1` using the available equality. Simplify using `[Eab]`. Rewrite using `[Eab, Eab, Matrix.single_mul_single_of_ne _ _ _ _ (e.symm.injective.ne h1), map_zero]`. Use `split_ifs with h1`. Substitute `h1` using the available equality.

Simplify using `[Eab]`. Rewrite using `[Eab, Eab, Matrix.single_mul_single_of_ne _ _ _ _ (e.symm.injective.ne h1), map_zero]`.
-/
theorem glRel_unitOp {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) : Formalism.REAL.GlRel (unitOp e act) := by
  intro a b c d
  unfold unitOp
  rw [← h, map_sub]
  congr 1
  · split_ifs with h1
    · subst h1; simp [Eab]
    · rw [Eab, Eab, Matrix.single_mul_single_of_ne _ _ _ _ (e.symm.injective.ne h1), map_zero]
  · split_ifs with h1
    · subst h1; simp [Eab]
    · rw [Eab, Eab, Matrix.single_mul_single_of_ne _ _ _ _ (e.symm.injective.ne h1), map_zero]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hW a b hab x hx`. Conclude with `hW _ (isKC_Eab ((h.sameBlock_iff _ _).2 (by simpa using hab))) x hx`. Introduce `hW Z hZ x hx`. Rewrite using `[act_eq_sum]`.

Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply]`. Use `W.sum_mem fun a _ => W.sum_mem fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hab : sameBlock a b`. Use `hW (e a) (e b) ((h.sameBlock_iff _ _).1 hab) x hx` as an intermediate fact. Simplify using `only [unitOp, Equiv.symm_apply_apply] at this`.

Conclude with `W.smul_mem _ this`. Rewrite using `[hZ a b hab, zero_smul]`. Conclude with `W.zero_mem`.
-/
theorem kStable_iff (h : BlockOrd e ε) (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (W : Submodule ℂ V) :
    KStable act W ↔ Formalism.REAL.KStable ε (unitOp e act) W := by
  constructor
  · intro hW a b hab x hx
    exact hW _ (isKC_Eab ((h.sameBlock_iff _ _).2 (by simpa using hab))) x hx
  · intro hW Z hZ x hx
    rw [act_eq_sum]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    refine W.sum_mem fun a _ => W.sum_mem fun b _ => ?_
    by_cases hab : sameBlock a b
    · have := hW (e a) (e b) ((h.sameBlock_iff _ _).1 hab) x hx
      simp only [unitOp, Equiv.symm_apply_apply] at this
      exact W.smul_mem _ this
    · rw [hZ a b hab, zero_smul]; exact W.zero_mem

/- English proof (translation)
Rewrite using `[mem_hwSub]`. Use `and_congr ?_ ?_` and prove the remaining obligations. Use `e.forall_congr_right.symm.trans (forall_congr' fun a => ?_)` and prove the remaining obligations. Simplify using `[unitOp, ← hμ]`. Use `e.forall_congr_right.symm.trans (forall_congr' fun a => ?_)` and prove the remaining obligations.

Use `e.forall_congr_right.symm.trans (forall_congr' fun b => ?_)` and prove the remaining obligations. Simplify using `[unitOp, h.posC_iff]`.
-/
theorem kHighest_iff (h : BlockOrd e ε) (act : Mat p q →ₗ[ℂ] Module.End ℂ V) {ν : Ix p q → ℚ} {μ : Fin n → ℝ}
    (hμ : ∀ a, (ν a : ℝ) = μ (e a)) (x : V) :
    Formalism.REAL.KHighest ε (unitOp e act) μ x ↔ x ∈ hwSub act ν := by
  rw [mem_hwSub]
  refine and_congr ?_ ?_
  · refine e.forall_congr_right.symm.trans (forall_congr' fun a => ?_)
    simp [unitOp, ← hμ]
  · refine e.forall_congr_right.symm.trans (forall_congr' fun a => ?_)
    refine e.forall_congr_right.symm.trans (forall_congr' fun b => ?_)
    simp [unitOp, h.posC_iff]

end Alg

/- English proof (translation)
Establish `e1 : Matrix.diagonal (fun a => Complex.exp (((Pi.single i (2 * Real.pi) : Fin n → ℝ) a : ℂ) * Complex.I)) = (1 : Matrix (Fin n) (Fin n) ℂ)`. Rewrite using `[← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Distinguish the cases in `ha : a = i`.

Substitute `ha` using the available equality. Simplify using the standard rewrite rules. Simplify using `[ha]`. Use `hw (Pi.single i (2 * Real.pi)) (by rw [e1]; exact ⟨one_mem _, by simp⟩)` as an intermediate fact. Rewrite `this` using `[e1, h1]`.

Establish `e2 : Complex.exp (((∑ a, μ a * (Pi.single i (2 * Real.pi) : Fin n → ℝ) a : ℝ) : ℂ) * Complex.I) = 1`. Use `smul_left_injective ℂ hv0 ?_` and prove the remaining obligations. Simplify using `using this.symm`. Take `⟨m, hm⟩` from `Complex.exp_eq_one_iff.1 e2`. Use `⟨m, ?_⟩` and prove the remaining obligations.

Simplify using `only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hm`. Establish `h3 : ((μ i : ℝ) : ℂ) = m`. Use `mul_right_cancel₀ Complex.two_pi_I_ne_zero ?_` and prove the remaining obligations. Rewrite using `[← hm]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `h3` after adjusting the coercions.
-/
theorem int_of_isWtOn {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h1 : σ 1 = 1) {μ : Fin n → ℝ} {v : H} (hv0 : v ≠ 0)
    (hw : IsWtOn (Formalism.REAL.Kset ε) σ μ v) (i : Fin n) : ∃ m : ℤ, μ i = m := by
  have e1 : Matrix.diagonal (fun a => Complex.exp (((Pi.single i (2 * Real.pi) : Fin n → ℝ) a : ℂ) * Complex.I)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← Matrix.diagonal_one]
    congr 1
    funext a
    by_cases ha : a = i
    · subst ha; simp
    · simp [ha]
  have := hw (Pi.single i (2 * Real.pi)) (by rw [e1]; exact ⟨one_mem _, by simp⟩)
  rw [e1, h1] at this
  have e2 : Complex.exp (((∑ a, μ a * (Pi.single i (2 * Real.pi) : Fin n → ℝ) a : ℝ) : ℂ) * Complex.I) = 1 := by
    refine smul_left_injective ℂ hv0 ?_
    simpa using this.symm
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 e2
  refine ⟨m, ?_⟩
  simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hm
  have h3 : ((μ i : ℝ) : ℂ) = m := by
    refine mul_right_cancel₀ Complex.two_pi_I_ne_zero ?_
    rw [← hm]; push_cast; ring
  exact_mod_cast h3

/- English proof (translation)
Use `open scoped Matrix.Norms.Operator in`. Conclude with `NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (LinearMap.continuous_of_finiteDimensional (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap) X`.
-/
theorem reindex_exp (e : Ix p q ≃ Fin n) (X : Mat p q) :
    Matrix.reindex e e (NormedSpace.exp X) = NormedSpace.exp (Matrix.reindex e e X) := by
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e)
    (LinearMap.continuous_of_finiteDimensional (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap) X

/- English proof (translation)
Unfold `Formalism.REAL.inG`. Rewrite using `[← h.reindex_Jm, Matrix.conjTranspose_reindex]`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]`. Conclude with `(Matrix.reindex e e).injective.eq_iff (a := Xᴴ * Jm p q + Jm p q * X) (b := 0)`.
-/
theorem inG_iff (h : BlockOrd e ε) (X : Mat p q) : Formalism.REAL.inG ε (Matrix.reindex e e X) ↔ X ∈ upq p q := by
  unfold Formalism.REAL.inG
  rw [← h.reindex_Jm, Matrix.conjTranspose_reindex]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  exact (Matrix.reindex e e).injective.eq_iff (a := Xᴴ * Jm p q + Jm p q * X) (b := 0)

/- English proof (translation)
Use `⟨(inG_iff h X).2 hX.1, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Take `⟨a, rfl⟩` from `e.surjective i`. Take `⟨b, rfl⟩` from `e.surjective j`. Simplify using `only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]`.

Distinguish the cases in `hab : sameBlock a b`. Simplify using `[hX.2 a b hab]`. Rewrite `hab` using `[h.sameBlock_iff]`. Apply the tactic sequence `cases h1 : ε (e a) <;> cases h2 : ε (e b) <;> simp_all`.
-/
theorem reindex_mem_noncompactPart (h : BlockOrd e ε) {X : Mat p q} (hX : X ∈ pR p q) : Formalism.REAL.inP ε (Matrix.reindex e e X) := by
  refine ⟨(inG_iff h X).2 hX.1, ?_⟩
  ext i j
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply]
  by_cases hab : sameBlock a b
  · simp [hX.2 a b hab]
  · rw [h.sameBlock_iff] at hab
    cases h1 : ε (e a) <;> cases h2 : ε (e b) <;> simp_all

/- English proof (translation)
Establish `key : (Finset.univ.filter fun b => ¬ sameBlock a b ∧ lam b < lam a).card + (Finset.univ.filter fun b => ¬ sameBlock a b ∧ lam a < lam b).card + (Finset.univ.filter fun b => sameBlock a b ∧ lam b < lam a).card + (Finset.univ.filter fun b => sameBlock a b ∧ lam a < lam b).card + 1 …`. Establish `h1 : (1 : ℕ) = ∑ b, if b = a then 1 else 0` using `by simp`. Establish `h2 : p + q = ∑ _b : Ix p q, 1` using `by simp`. Rewrite using `[h2]`. Simplify using `only [Finset.card_filter]`.

Use `nth_rewrite 5 [h1]`. Simplify using `only [← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality.

Simplify using the standard rewrite rules. Apply the tactic sequence `rcases lt_or_gt_of_ne (hl.ne hb) with h | h <;> by_cases hs : sameBlock a b <;> simp [hb, hs, h, h.not_gt]`. Use `⟨m - (Finset.univ.filter fun b => ¬ sameBlock a b ∧ lam b < lam a).card - (Finset.univ.filter fun b => sameBlock a b ∧ lam a < lam b).card, ?_⟩` and prove the remaining obligations. Unfold `blattner rhoNC at hm`. Rewrite using `[← key]`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sub_rho_int {lam : Ix p q → ℚ} (hl : Function.Injective lam) (a : Ix p q) {m : ℤ}
    (hm : blattner lam a = m) : ∃ k : ℤ, lam a - (((p + q : ℕ) : ℚ) - 1) / 2 = k := by
  classical
  have key : (Finset.univ.filter fun b => ¬ sameBlock a b ∧ lam b < lam a).card +
      (Finset.univ.filter fun b => ¬ sameBlock a b ∧ lam a < lam b).card +
      (Finset.univ.filter fun b => sameBlock a b ∧ lam b < lam a).card +
      (Finset.univ.filter fun b => sameBlock a b ∧ lam a < lam b).card + 1 = p + q := by
    have h1 : (1 : ℕ) = ∑ b, if b = a then 1 else 0 := by simp
    have h2 : p + q = ∑ _b : Ix p q, 1 := by simp
    rw [h2]
    simp only [Finset.card_filter]
    nth_rewrite 5 [h1]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b = a
    · subst hb; simp
    · rcases lt_or_gt_of_ne (hl.ne hb) with h | h <;> by_cases hs : sameBlock a b <;> simp [hb, hs, h, h.not_gt]
  refine ⟨m - (Finset.univ.filter fun b => ¬ sameBlock a b ∧ lam b < lam a).card -
    (Finset.univ.filter fun b => sameBlock a b ∧ lam a < lam b).card, ?_⟩
  unfold blattner rhoNC at hm
  rw [← key]
  push_cast
  linarith

variable {T : GrpData p q}

/- English proof (translation)
Use `⟨fun i => by simp, fun i => by simp, ?_⟩` and prove the remaining obligations. Introduce and unpack `(a | a) (b | b) hab`. Conclude with `hab`. Conclude with `hab.elim`. Conclude with `hab.elim`.

Conclude with `Nat.add_lt_add_left hab p`.
-/
theorem exists_blockOrd_std (p q : ℕ) :
    BlockOrd (finSumFinEquiv : Ix p q ≃ Fin (p + q)) fun i => (finSumFinEquiv.symm i).isLeft := by
  refine ⟨fun i => by simp, fun i => by simp, ?_⟩
  rintro (a | a) (b | b) hab
  · exact hab
  · exact hab.elim
  · exact hab.elim
  · exact Nat.add_lt_add_left hab p

/- English proof (translation)
Take `⟨v, hv, hs⟩` from `finrank_eq_one_iff'.1 h`. Conclude with `⟨v, ⟨fun h0 => hv (Subtype.ext h0), v.2⟩, fun x hx => (hs ⟨x, hx⟩).imp fun c hc => congrArg Subtype.val hc⟩`.
-/
theorem exists_isHW {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ}
    (h : Module.finrank ℂ (hwSub act μ) = 1) : ∃ v, IsHW act μ v ∧ ∀ x ∈ hwSub act μ, ∃ c : ℂ, c • v = x := by
  obtain ⟨v, hv, hs⟩ := finrank_eq_one_iff'.1 h
  exact ⟨v, ⟨fun h0 => hv (Subtype.ext h0), v.2⟩, fun x hx => (hs ⟨x, hx⟩).imp fun c hc => congrArg Subtype.val hc⟩

/- English proof (translation)
Introduce `h`. Establish `r : ∀ a b : Ix p q, ∑ c, lam c * ((if c = a then 1 else 0) - (if c = b then 1 else 0) : ℚ) = lam a - lam b`. Introduce `a b`. Simplify using `[mul_sub, Finset.sum_sub_distrib]`. Establish `h1 : -(lam a - lam b) = ∑ a, ∑ b, (m a b : ℚ) * (lam a - lam b)`.

Simplify using `only [← r, ← Finset.sum_neg_distrib, ← mul_neg, h, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring`.

Establish `h2 : 0 ≤ ∑ a, ∑ b, (m a b : ℚ) * (lam a - lam b)` using `Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by`. Distinguish the cases in `h0 : m a b = 0`. Simplify using `[h0]`. Conclude with `mul_nonneg (Nat.cast_nonneg _) (sub_pos.2 (hm a b h0)).le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem not_below {lam : Ix p q → ℚ} {a b : Ix p q} (hab : lam b < lam a) {m : Ix p q → Ix p q → ℕ}
    (hm : ∀ a b, m a b ≠ 0 → lam b < lam a) :
    ¬ ∀ c, -((if c = a then 1 else 0) - (if c = b then 1 else 0) : ℚ) =
      ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0)) := by
  intro h
  have r : ∀ a b : Ix p q, ∑ c, lam c * ((if c = a then 1 else 0) - (if c = b then 1 else 0) : ℚ) = lam a - lam b := by
    intro a b
    simp [mul_sub, Finset.sum_sub_distrib]
  have h1 : -(lam a - lam b) = ∑ a, ∑ b, (m a b : ℚ) * (lam a - lam b) := by
    simp only [← r, ← Finset.sum_neg_distrib, ← mul_neg, h, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
  have h2 : 0 ≤ ∑ a, ∑ b, (m a b : ℚ) * (lam a - lam b) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
      by_cases h0 : m a b = 0
      · simp [h0]
      · exact mul_nonneg (Nat.cast_nonneg _) (sub_pos.2 (hm a b h0)).le
  linarith

/- English proof (translation)
Take `⟨u₀, hu₀, hs₀⟩` from `exists_isHW h1`. Establish `inj : ∀ {v : R.HK.V}, v ≠ 0 → R.ι v ≠ 0` using `fun h h0 => h (R.ι_inj (by rw [h0, map_zero]))`. Establish `wint : ∀ {n : ℕ} {e : Ix p q ≃ Fin n} {ε : Fin n → Bool}, BlockOrd e ε → ∀ (μ : Fin n → ℝ) (v : R.HK.V), v ≠ 0 → (∀ a, R.HK.act (Eab a a) v = ((μ (e a) : ℝ) : ℂ) • v) → ∀ i, ∃ m : ℤ, μ i = m`. Introduce `n e ε hb μ v hv hw`. Take `⟨σ, hσ⟩` from `exists_factors R.U e hker`.

Conclude with `int_of_isWtOn (CoverURep.urep_irred p q n e ε T R σ hb hσ).1.1.1 (inj hv) ((TorusWt.isWtOn_iff p q n e ε T R σ hb hσ μ v).2 hw)`. Establish `hi : ∀ a, ∃ m : ℤ, lam a - (((p + q : ℕ) : ℚ) - 1) / 2 = m` using `fun a => by`. Take `⟨m, hm⟩` from `wint (exists_blockOrd_std p q) (fun i => (blattner lam (finSumFinEquiv.symm i) : ℝ)) u₀ hu₀.1 (fun a => by simpa using ((mem_hwSub _ _ _).1 hu₀.2).1 a) (finSumFinEquiv a)`. Rewrite `hm` using `[Equiv.symm_apply_apply]`. Conclude with `sub_rho_int hl.1 a (m := m) (by exact_mod_cast hm)`.

Take `⟨P, e, hsig, hb, hP⟩` from `exists_blockPar hl hi`. Establish `hle : ∀ a, (lam a : ℝ) = P.lam (e a)` using `fun a => by rw [hP]; exact ratEntry_cast P (e a)`. Establish `hΛ : ∀ a, (blattner lam a : ℝ) = Formalism.QuantumDeterminants.lowK P.sgn P.lam (e a)` using `blattner_eq P hb hle`. Take `⟨σ, hσ⟩` from `exists_factors R.U e hker`. Establish `hU` using `(CoverURep.urep_irred p q _ e _ T R σ hb hσ).1`.

Establish `gap : ∀ h : ℝ, GapGe lam h → Formalism.QuantumDeterminants.GapAtLeast P.sgn P.lam h` using `fun h hh i j hij => by`. Take `⟨a, rfl⟩` from `e.surjective i`. Take `⟨b, rfl⟩` from `e.surjective j`. Use `hh a b (by rwa [hb.sameBlock_iff])` as an intermediate fact. Rewrite `this` using `[Rat.cast_sub, hle, hle]`. Then use the resulting hypothesis.

Establish `hexp : ∀ X ∈ upq p q, R.U.π (T.expt X) = σ (NormedSpace.exp (Matrix.reindex e e X))` using `fun X hX => by`. Rewrite using `[hσ, T.expt_cov X hX, reindex_exp]`. Use `letI : NormedAddCommGroup R.HK.V := NormedAddCommGroup.induced _ _ R.ι R.ι_inj`. Use `letI : InnerProductSpace ℂ R.HK.V := InnerProductSpace.induced R.ι`. Set `ι : R.HK.V →ₗᵢ[ℂ] R.U.H` to `⟨R.ι, fun _ => rfl⟩`.

Use `set E := unitOp e R.HK.act with hE`. Establish `hder : DerTie P.sgn σ E ι`. Introduce `X hX v`. Take `⟨X, rfl⟩` from `(Matrix.reindex e e).surjective X`. Establish `hX'` using `(inG_iff hb X).1 hX`.

Rewrite using `[hE, actM_unitOp]`. Use `R.der X hX' v` as an intermediate fact. Simplify using `only [hexp _ (KStabLie.smul_mem_upq hX' _)] at this`. Conclude with `this`. Establish `hG : Formalism.REAL.GlRel E` using `glRel_unitOp R.HK.lie`.

Establish `hUn : Formalism.REAL.IsUnitary P.sgn E`. Introduce `i j x y`. Take `⟨a, rfl⟩` from `e.surjective i`. Take `⟨b, rfl⟩` from `e.surjective j`. Establish `h2` using `DerivedAdjoint.derived_adjoint p q T R.U R.HK R.ι R.der (Eab a b) x y`.

Establish `h3 : adjZ (Eab a b) = ((Formalism.REAL.sgn P.sgn (e a) (e b) : ℝ) : ℂ) • Eab b a`. Rewrite using `[adjZ, KStabLie.Jm_eq, Eab, Matrix.conjTranspose_single]`. Use extensionality with `c d`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`. Distinguish the cases in `hcd : b = c ∧ a = d`.

Take `⟨rfl, rfl⟩` from `hcd`. Apply the tactic sequence `cases a <;> cases b <;> simp [Formalism.REAL.sgn, hb.1, hb.2.1, Eab]`. Simplify using `[Eab, Matrix.single_apply, hcd]`. Rewrite `h2` using `[h3, map_smul, LinearMap.smul_apply, map_smul, inner_smul_right]`. Simplify using `only [hE, unitOp, Equiv.symm_apply_apply]`.

Conclude with `h2`. Use `set u : R.HK.V := ((‖u₀‖⁻¹ : ℝ) : ℂ) • u₀ with hu`. Establish `hn0 : ‖u₀‖ ≠ 0` using `norm_ne_zero_iff.2 hu₀.1`. Establish `hu1 : ‖u‖ = 1` using `by rw [hu, norm_smul]; simp [hn0]`. Establish `huw : IsHW R.HK.act (blattner lam) u` using `⟨fun h0 => by simp [h0] at hu1, Submodule.smul_mem _ _ hu₀.2⟩`.

Establish `hhi` using `(kHighest_iff hb R.HK.act hΛ u).2 huw.2`. Establish `hks` using `(kStable_iff hb R.HK.act _).2 (Formalism.REAL.compact_span_compact_stable P.sgn E u)`. Establish `hmin : ∀ W : Submodule ℂ R.HK.V, u ∈ W → KStable R.HK.act W → Formalism.REAL.kSpan P.sgn E u ≤ W` using `fun W a b => sInf_le ⟨a, (kStable_iff hb _ _).1 b⟩`. Establish `hfin : FiniteDimensional ℂ (Formalism.REAL.kSpan P.sgn E u)`. Take `⟨W, a, b, c⟩` from `R.HK.kfin u`.

Conclude with `Submodule.finiteDimensional_of_le (hmin W b c)`. Establish `kr` using `Formalism.REAL.glRel_kRel P.sgn E hG`. Establish `ku` using `Formalism.REAL.isUnitary_kUnit P.sgn E hUn`. Establish `hwt : IsWtOn (Formalism.REAL.Kset P.sgn) σ (Formalism.QuantumDeterminants.lowK P.sgn P.lam) (R.ι u)` using `(TorusWt.isWtOn_iff p q _ e _ T R σ hb hσ _ u).2 fun a => by`. Simplify `((mem_hwSub _ _ _).1 huw.2).1 a` using `[← hΛ]`.

Establish `hK : IsKTypeOf P.sgn σ (Formalism.QuantumDeterminants.lowK P.sgn P.lam) ((Formalism.REAL.kSpan P.sgn E u).map R.ι)`. Use `⟨inferInstance, isKStableOn_of_kStable p q _ e _ T R σ hb hσ _ hfin hks, fun S' a b => ?_, ⟨R.ι u, ⟨u, Formalism.REAL.mem_kSpan_self' _ _ _, rfl⟩, inj huw.1, hwt⟩, ?_⟩` and prove the remaining obligations. Take `⟨-, a1, a2⟩` from `comap_kstable R hb hσ (Submodule.finiteDimensional_of_le a) b`. Break down `Formalism.REAL.kIrr _ _ P.sgn E _ u hfin kr ku hhi (S'.comap R.ι) ((Submodule.comap_mono a).trans (Submodule.comap_map_eq_of_injective R.ι_inj _).le) ((kStable_iff hb _ _).1 a2) with h0 | h0` into its components or cases. Use `left`.

Rewrite using `[← a1, h0, Submodule.map_bot]`. Use `right`. Rewrite using `[← a1, h0]`. Take `⟨W0, c1, c2, -, c4⟩` from `HwGen.hw_generated p q R.HK.V R.HK.act R.HK.lie _ u huw`. Introduce and unpack `ν _ ⟨w, hw, rfl⟩ hw0 hwt`.

Take `⟨c, d1, d2⟩` from `c4 (fun a => ν (e a)) w (hmin W0 c1 c2 hw) (fun h0 => hw0 (by rw [h0, map_zero])) ((TorusWt.isWtOn_iff p q _ e _ T R σ hb hσ _ w).1 hwt)`. Use `⟨fun i j => c (e.symm i) (e.symm j), fun i j hij => by simpa using (hb.posC_iff _ _).1 (d1 _ _ hij), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Take `⟨x, rfl⟩` from `e.surjective i`. Simplify using `only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← hΛ, d2]`.

Rewrite using `[← e.sum_comp]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← e.sum_comp]`. Simplify using `only [Equiv.symm_apply_apply, root_apply]`. Establish `hlow : ∀ i j, i < j → P.sgn i ≠ P.sgn j → ∀ x, Formalism.REAL.KHighest P.sgn E (Formalism.QuantumDeterminants.lowK P.sgn P.lam - Formalism.REAL.root i j) x → x = 0`.

Introduce `i j hij _ x hx`. Take `⟨a, rfl⟩` from `e.surjective i`. Take `⟨b, rfl⟩` from `e.surjective j`. Assume the negation of the conclusion as `h0`. Take `⟨m, m1, m2⟩` from `hc (fun c => blattner lam c - ((if c = a then 1 else 0) - (if c = b then 1 else 0))) x ⟨h0, (kHighest_iff hb _ (fun c => by`.

Apply the tactic sequence `rw [Pi.sub_apply, root_apply, ← hΛ]; split_ifs <;> simp) x).1 hx⟩`. Use `not_below (a := a) (b := b) ?_ m1 fun c => by linarith [m2 c]` and prove the remaining obligations. Use `P.hc.1 hij` as an intermediate fact. Rewrite `this` using `[← hle, ← hle]`. Conclude with `this` after adjusting the coercions.

Establish `hiso : ∀ x ∈ isoVec R (blattner lam), x ∈ (Formalism.REAL.kSpan P.sgn E u).map R.ι`. Introduce and unpack `_ ⟨v, ⟨W, a, b, c, d⟩, rfl⟩`. Use `⟨v, ?_, rfl⟩` and prove the remaining obligations. Take `⟨m, x, μ, f1, -, f2⟩` from `Formalism.REAL.kDecomp _ _ P.sgn E W a kr ku ((kStable_iff hb _ _).1 c)`. Rewrite `b` using `[← f2]`.

Use `(iSup_le fun i => ?_ : _ ≤ Formalism.REAL.kSpan P.sgn E u) b` and prove the remaining obligations. Take `⟨g1, g2, g3⟩` from `f1 i`. Use `choose z hz using wint hb (μ i) (x i) g2 fun a => by simpa [hE, unitOp] using g3.1 (e a)`. Establish `g4` using `(kHighest_iff hb R.HK.act (ν := fun a => (z (e a) : ℚ)) (fun a => by simp [hz]) _).1 g3`. Rewrite `g4` using `[d _ _ g1 ⟨g2, g4⟩]`.

Take `⟨c, hc⟩` from `hs₀ _ g4`. Use `sInf_le ⟨?_, Formalism.REAL.compact_span_compact_stable P.sgn E u⟩` and prove the remaining obligations. Establish `: x i = (c * (‖u₀‖ : ℝ)) • u`. Rewrite using `[hu, smul_smul, mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hn0, ← hc]`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Formalism.REAL.mem_kSpan_self' _ _ _)`. Take `⟨r1, r2⟩` from `core (ι := ι) P.hc (gap h hh) (gap _ hg) hU hder hG hUn hu1 hhi hfin hK hwt hlow (reindex_mem_noncompactPart hb hY) (hiso x hx)`. Rewrite `r1`, `r2` using `[← hexp Y hY.1]`. Use `⟨r1, fun k hk y hy => ?_⟩` and prove the remaining obligations.

Establish `hk'` using `Formalism.REAL.Kset_star _ (KStabLie.mem_Kset hb T hk)`. Establish `hk2 : R.U.π k⁻¹ y ∈ (Formalism.REAL.kSpan P.sgn E u).map R.ι`. Establish `hki : k⁻¹ ∈ T.Kset`. Establish `h3 : Commute ((T.cov k : GL (Ix p q) ℂ) : Mat p q) (Jm p q)` using `(KStabLie.isKC_iff _).1 hk`. Express the relevant statement in the definitionally equal form `IsKC _`.

Rewrite using `[KStabLie.isKC_iff, map_inv]`. Conclude with `h3.units_inv_left`. Rewrite using `[hσ]`. Conclude with `hK.2.1 _ (KStabLie.mem_Kset hb T hki) y (hiso y hy)`. Establish `r3` using `r2 _ hk2`.

Rewrite `r3` using `[R.U.isom, ← DerivedAdjoint.inner_map T R.U k, ← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ← ContinuousLinearMap.mul_apply, ← map_mul, ContinuousLinearMap.one_apply]`. Establish `e1 : GlobalTheory.Count.rkR P.sgn = min p q` using `congrArg₂ min hsig.1 hsig.2`. Establish `e2 : Real.sqrt (Formalism.REAL.hs (Matrix.reindex e e Y)) = hsNorm Y`. Unfold `Formalism.REAL.hs hsNorm`. Use `congr 1`.

Rewrite using `[← e.sum_comp]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← e.sum_comp]`. Simplify using the standard rewrite rules. Rewrite `r3` using `[e1, e2]`. Then use the resulting hypothesis.
-/
theorem of_trivial (R : DSRep T) (hker : ∀ x, T.cov x = 1 → R.U.π x = 1) {lam : Ix p q → ℚ} (hl : IsParam lam)
    (h1 : Module.finrank ℂ (hwSub R.HK.act (blattner lam)) = 1)
    (hc : ∀ (μ : Ix p q → ℚ) v, IsHW R.HK.act μ v →
      ∃ m : Ix p q → Ix p q → ℕ, (∀ a b, m a b ≠ 0 → lam b < lam a) ∧
        ∀ c, μ c = blattner lam c +
          ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0)))
    {h : ℝ} (hh : GapGe lam h) (hg : GapGe lam (2 * (p + q : ℕ) + 1)) {Y : Mat p q} (hY : Y ∈ pR p q)
    {x : R.U.H} (hx : x ∈ isoVec R (blattner lam)) :
    0 ≤ ⟪x, R.U.π (T.expt Y) x⟫_ℂ ∧ ∀ k ∈ T.Kset, ∀ y ∈ isoVec R (blattner lam),
      ‖⟪y, R.U.π (k * T.expt Y) x⟫_ℂ‖ ≤
        Real.exp (-(h / 8) * min (hsNorm Y ^ 2) (hsNorm Y / Real.sqrt (2 * (min p q : ℕ)))) * ‖x‖ * ‖y‖ := by
  classical
  obtain ⟨u₀, hu₀, hs₀⟩ := exists_isHW h1
  have inj : ∀ {v : R.HK.V}, v ≠ 0 → R.ι v ≠ 0 := fun h h0 => h (R.ι_inj (by rw [h0, map_zero]))
  have wint : ∀ {n : ℕ} {e : Ix p q ≃ Fin n} {ε : Fin n → Bool}, BlockOrd e ε → ∀ (μ : Fin n → ℝ) (v : R.HK.V),
      v ≠ 0 → (∀ a, R.HK.act (Eab a a) v = ((μ (e a) : ℝ) : ℂ) • v) → ∀ i, ∃ m : ℤ, μ i = m := by
    intro n e ε hb μ v hv hw
    obtain ⟨σ, hσ⟩ := exists_factors R.U e hker
    exact int_of_isWtOn (CoverURep.urep_irred p q n e ε T R σ hb hσ).1.1.1 (inj hv)
      ((TorusWt.isWtOn_iff p q n e ε T R σ hb hσ μ v).2 hw)
  have hi : ∀ a, ∃ m : ℤ, lam a - (((p + q : ℕ) : ℚ) - 1) / 2 = m := fun a => by
    obtain ⟨m, hm⟩ := wint (exists_blockOrd_std p q) (fun i => (blattner lam (finSumFinEquiv.symm i) : ℝ)) u₀ hu₀.1
      (fun a => by simpa using ((mem_hwSub _ _ _).1 hu₀.2).1 a) (finSumFinEquiv a)
    rw [Equiv.symm_apply_apply] at hm
    exact sub_rho_int hl.1 a (m := m) (by exact_mod_cast hm)
  obtain ⟨P, e, hsig, hb, hP⟩ := exists_blockPar hl hi
  have hle : ∀ a, (lam a : ℝ) = P.lam (e a) := fun a => by rw [hP]; exact ratEntry_cast P (e a)
  have hΛ : ∀ a, (blattner lam a : ℝ) = Formalism.QuantumDeterminants.lowK P.sgn P.lam (e a) := blattner_eq P hb hle
  obtain ⟨σ, hσ⟩ := exists_factors R.U e hker
  have hU := (CoverURep.urep_irred p q _ e _ T R σ hb hσ).1
  have gap : ∀ h : ℝ, GapGe lam h → Formalism.QuantumDeterminants.GapAtLeast P.sgn P.lam h := fun h hh i j hij => by
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, rfl⟩ := e.surjective j
    have := hh a b (by rwa [hb.sameBlock_iff])
    rwa [Rat.cast_sub, hle, hle] at this
  have hexp : ∀ X ∈ upq p q, R.U.π (T.expt X) = σ (NormedSpace.exp (Matrix.reindex e e X)) := fun X hX => by
    rw [hσ, T.expt_cov X hX, reindex_exp]
  letI : NormedAddCommGroup R.HK.V := NormedAddCommGroup.induced _ _ R.ι R.ι_inj
  letI : InnerProductSpace ℂ R.HK.V := InnerProductSpace.induced R.ι
  let ι : R.HK.V →ₗᵢ[ℂ] R.U.H := ⟨R.ι, fun _ => rfl⟩
  set E := unitOp e R.HK.act with hE
  have hder : DerTie P.sgn σ E ι := by
    intro X hX v
    obtain ⟨X, rfl⟩ := (Matrix.reindex e e).surjective X
    have hX' := (inG_iff hb X).1 hX
    rw [hE, actM_unitOp]
    have := R.der X hX' v
    simp only [hexp _ (KStabLie.smul_mem_upq hX' _)] at this
    exact this
  have hG : Formalism.REAL.GlRel E := glRel_unitOp R.HK.lie
  have hUn : Formalism.REAL.IsUnitary P.sgn E := by
    intro i j x y
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, rfl⟩ := e.surjective j
    have h2 := DerivedAdjoint.derived_adjoint p q T R.U R.HK R.ι R.der (Eab a b) x y
    have h3 : adjZ (Eab a b) = ((Formalism.REAL.sgn P.sgn (e a) (e b) : ℝ) : ℂ) • Eab b a := by
      rw [adjZ, KStabLie.Jm_eq, Eab, Matrix.conjTranspose_single]
      ext c d
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases hcd : b = c ∧ a = d
      · obtain ⟨rfl, rfl⟩ := hcd
        cases a <;> cases b <;> simp [Formalism.REAL.sgn, hb.1, hb.2.1, Eab]
      · simp [Eab, Matrix.single_apply, hcd]
    rw [h3, map_smul, LinearMap.smul_apply, map_smul, inner_smul_right] at h2
    simp only [hE, unitOp, Equiv.symm_apply_apply]
    exact h2
  set u : R.HK.V := ((‖u₀‖⁻¹ : ℝ) : ℂ) • u₀ with hu
  have hn0 : ‖u₀‖ ≠ 0 := norm_ne_zero_iff.2 hu₀.1
  have hu1 : ‖u‖ = 1 := by rw [hu, norm_smul]; simp [hn0]
  have huw : IsHW R.HK.act (blattner lam) u :=
    ⟨fun h0 => by simp [h0] at hu1, Submodule.smul_mem _ _ hu₀.2⟩
  have hhi := (kHighest_iff hb R.HK.act hΛ u).2 huw.2
  have hks := (kStable_iff hb R.HK.act _).2 (Formalism.REAL.compact_span_compact_stable P.sgn E u)
  have hmin : ∀ W : Submodule ℂ R.HK.V, u ∈ W → KStable R.HK.act W → Formalism.REAL.kSpan P.sgn E u ≤ W :=
    fun W a b => sInf_le ⟨a, (kStable_iff hb _ _).1 b⟩
  have hfin : FiniteDimensional ℂ (Formalism.REAL.kSpan P.sgn E u) := by
    obtain ⟨W, a, b, c⟩ := R.HK.kfin u
    exact Submodule.finiteDimensional_of_le (hmin W b c)
  have kr := Formalism.REAL.glRel_kRel P.sgn E hG
  have ku := Formalism.REAL.isUnitary_kUnit P.sgn E hUn
  have hwt : IsWtOn (Formalism.REAL.Kset P.sgn) σ (Formalism.QuantumDeterminants.lowK P.sgn P.lam) (R.ι u) :=
    (TorusWt.isWtOn_iff p q _ e _ T R σ hb hσ _ u).2 fun a => by
      simpa [← hΛ] using ((mem_hwSub _ _ _).1 huw.2).1 a
  have hK : IsKTypeOf P.sgn σ (Formalism.QuantumDeterminants.lowK P.sgn P.lam) ((Formalism.REAL.kSpan P.sgn E u).map R.ι) := by
    refine ⟨inferInstance, isKStableOn_of_kStable p q _ e _ T R σ hb hσ _ hfin hks, fun S' a b => ?_,
      ⟨R.ι u, ⟨u, Formalism.REAL.mem_kSpan_self' _ _ _, rfl⟩, inj huw.1, hwt⟩, ?_⟩
    · obtain ⟨-, a1, a2⟩ := comap_kstable R hb hσ (Submodule.finiteDimensional_of_le a) b
      rcases Formalism.REAL.kIrr _ _ P.sgn E _ u hfin kr ku hhi (S'.comap R.ι)
        ((Submodule.comap_mono a).trans (Submodule.comap_map_eq_of_injective R.ι_inj _).le)
        ((kStable_iff hb _ _).1 a2) with h0 | h0
      · left; rw [← a1, h0, Submodule.map_bot]
      · right; rw [← a1, h0]
    · obtain ⟨W0, c1, c2, -, c4⟩ := HwGen.hw_generated p q R.HK.V R.HK.act R.HK.lie _ u huw
      rintro ν _ ⟨w, hw, rfl⟩ hw0 hwt
      obtain ⟨c, d1, d2⟩ := c4 (fun a => ν (e a)) w (hmin W0 c1 c2 hw) (fun h0 => hw0 (by rw [h0, map_zero]))
        ((TorusWt.isWtOn_iff p q _ e _ T R σ hb hσ _ w).1 hwt)
      refine ⟨fun i j => c (e.symm i) (e.symm j), fun i j hij => by simpa using (hb.posC_iff _ _).1 (d1 _ _ hij), ?_⟩
      funext i
      obtain ⟨x, rfl⟩ := e.surjective i
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← hΛ, d2]
      rw [← e.sum_comp]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← e.sum_comp]
      simp only [Equiv.symm_apply_apply, root_apply]
  have hlow : ∀ i j, i < j → P.sgn i ≠ P.sgn j → ∀ x, Formalism.REAL.KHighest P.sgn E
      (Formalism.QuantumDeterminants.lowK P.sgn P.lam - Formalism.REAL.root i j) x → x = 0 := by
    intro i j hij _ x hx
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, rfl⟩ := e.surjective j
    by_contra h0
    obtain ⟨m, m1, m2⟩ := hc (fun c => blattner lam c - ((if c = a then 1 else 0) - (if c = b then 1 else 0))) x
      ⟨h0, (kHighest_iff hb _ (fun c => by
        rw [Pi.sub_apply, root_apply, ← hΛ]; split_ifs <;> simp) x).1 hx⟩
    refine not_below (a := a) (b := b) ?_ m1 fun c => by linarith [m2 c]
    have := P.hc.1 hij
    rw [← hle, ← hle] at this
    exact_mod_cast this
  have hiso : ∀ x ∈ isoVec R (blattner lam), x ∈ (Formalism.REAL.kSpan P.sgn E u).map R.ι := by
    rintro _ ⟨v, ⟨W, a, b, c, d⟩, rfl⟩
    refine ⟨v, ?_, rfl⟩
    obtain ⟨m, x, μ, f1, -, f2⟩ := Formalism.REAL.kDecomp _ _ P.sgn E W a kr ku ((kStable_iff hb _ _).1 c)
    rw [← f2] at b
    refine (iSup_le fun i => ?_ : _ ≤ Formalism.REAL.kSpan P.sgn E u) b
    obtain ⟨g1, g2, g3⟩ := f1 i
    choose z hz using wint hb (μ i) (x i) g2 fun a => by simpa [hE, unitOp] using g3.1 (e a)
    have g4 := (kHighest_iff hb R.HK.act (ν := fun a => (z (e a) : ℚ)) (fun a => by simp [hz]) _).1 g3
    rw [d _ _ g1 ⟨g2, g4⟩] at g4
    obtain ⟨c, hc⟩ := hs₀ _ g4
    refine sInf_le ⟨?_, Formalism.REAL.compact_span_compact_stable P.sgn E u⟩
    have : x i = (c * (‖u₀‖ : ℝ)) • u := by
      rw [hu, smul_smul, mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hn0, ← hc]; simp
    rw [this]
    exact Submodule.smul_mem _ _ (Formalism.REAL.mem_kSpan_self' _ _ _)
  obtain ⟨r1, r2⟩ := core (ι := ι) P.hc (gap h hh) (gap _ hg) hU hder hG hUn hu1 hhi hfin hK hwt hlow
    (reindex_mem_noncompactPart hb hY) (hiso x hx)
  rw [← hexp Y hY.1] at r1 r2
  refine ⟨r1, fun k hk y hy => ?_⟩
  have hk' := Formalism.REAL.Kset_star _ (KStabLie.mem_Kset hb T hk)
  have hk2 : R.U.π k⁻¹ y ∈ (Formalism.REAL.kSpan P.sgn E u).map R.ι := by
    have hki : k⁻¹ ∈ T.Kset := by
      have h3 : Commute ((T.cov k : GL (Ix p q) ℂ) : Mat p q) (Jm p q) := (KStabLie.isKC_iff _).1 hk
      change IsKC _
      rw [KStabLie.isKC_iff, map_inv]
      exact h3.units_inv_left
    rw [hσ]
    exact hK.2.1 _ (KStabLie.mem_Kset hb T hki) y (hiso y hy)
  have r3 := r2 _ hk2
  rw [R.U.isom, ← DerivedAdjoint.inner_map T R.U k, ← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel,
    map_one, ← ContinuousLinearMap.mul_apply, ← map_mul, ContinuousLinearMap.one_apply] at r3
  have e1 : GlobalTheory.Count.rkR P.sgn = min p q := congrArg₂ min hsig.1 hsig.2
  have e2 : Real.sqrt (Formalism.REAL.hs (Matrix.reindex e e Y)) = hsNorm Y := by
    unfold Formalism.REAL.hs hsNorm
    congr 1
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← e.sum_comp]
    simp
  rwa [e1, e2] at r3

/- English proof (translation)
Establish `h1` using `T.expt_add Y hY.1 (1 / 2) (1 / 2)`. Rewrite `h1` using `[add_halves, one_smul]`. Establish `h2 : ((1 / 2 : ℝ) • Y).trace = 0` using `Finset.sum_eq_zero fun a _ => by`. Apply the tactic sequence `have : Y a a = 0 := hY.2 a a (by cases a <;> trivial)`. Simplify using `[this]`.

Rewrite using `[h1, map_mul, Units.val_mul, ← sq, T.sq_sq, T.expt_cov _ (KStabLie.smul_mem_upq hY.1 _), GlobalTheory.DetSqrtCover.det_exp, h2, Complex.exp_zero]`.
-/
theorem sq_expt {Y : Mat p q} (hY : Y ∈ pR p q) : ((T.sq (T.expt Y) : ℂˣ) : ℂ) = 1 := by
  have h1 := T.expt_add Y hY.1 (1 / 2) (1 / 2)
  rw [add_halves, one_smul] at h1
  have h2 : ((1 / 2 : ℝ) • Y).trace = 0 :=
    Finset.sum_eq_zero fun a _ => by
      have : Y a a = 0 := hY.2 a a (by cases a <;> trivial)
      simp [this]
  rw [h1, map_mul, Units.val_mul, ← sq, T.sq_sq, T.expt_cov _ (KStabLie.smul_mem_upq hY.1 _), GlobalTheory.DetSqrtCover.det_exp, h2,
    Complex.exp_zero]

/- English proof (translation)
Use extensionality with `v`. Distinguish the cases in `hv : v = 0`. Simplify using `[hv]`. Simplify `Cover.isHW_twAct act μ v` using `[IsHW, hv]`.
-/
theorem hwSub_twAct {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) :
    hwSub (Cover.twAct act) μ = hwSub act fun a => μ a + 1 / 2 := by
  ext v
  by_cases hv : v = 0
  · simp [hv]
  · simpa [IsHW, hv] using Cover.isHW_twAct act μ v

/- English proof (translation)
Take `⟨v, ⟨W, a, b, c, d⟩, rfl⟩` from `hx`. Use `⟨v, ⟨W, a, b, fun X hX w hw => ?_, fun ν w hw h => ?_⟩, rfl⟩` and prove the remaining obligations. Conclude with `(Cover.twAct_apply R.HK.act X w).symm ▸ W.sub_mem (c X hX w hw) (W.smul_mem (X.trace / 2) hw)`. Use `d _ w hw ((Cover.isHW_twAct R.HK.act ν w).1 h)` as an intermediate fact. Use function extensionality and compare the values at `a`.

Conclude with `add_right_cancel (congrFun this a)`.
-/
theorem isoVec_twist (R : DSRep T) {μ : Ix p q → ℚ} {x : R.U.H} (hx : x ∈ isoVec R fun a => μ a + 1 / 2) :
    x ∈ isoVec (Cover.twist R) μ := by
  obtain ⟨v, ⟨W, a, b, c, d⟩, rfl⟩ := hx
  refine ⟨v, ⟨W, a, b, fun X hX w hw => ?_, fun ν w hw h => ?_⟩, rfl⟩
  · exact (Cover.twAct_apply R.HK.act X w).symm ▸ W.sub_mem (c X hX w hw) (W.smul_mem (X.trace / 2) hw)
  · have := d _ w hw ((Cover.isHW_twAct R.HK.act ν w).1 h)
    funext a
    exact add_right_cancel (congrFun this a)

/- English proof (translation)
Break down `Cover.trivial_or_twist R with hker | hker` into its components or cases. Conclude with `of_trivial R hker hl h1 hc hh hg hY hx`. Use `set lam' : Ix p q → ℚ := fun a => lam a + -(1 / 2) with hlam`. Establish `hb : (fun a => blattner lam' a + 1 / 2) = blattner lam`. Rewrite using `[hlam, Cover.blattner_add]`.

Use function extensionality and compare the values at `a`. Expand and normalize the polynomial expressions, which then agree. Establish `hgap : ∀ h, GapGe lam h → GapGe lam' h` using `fun h hh a b hab => by simpa [hlam] using hh a b hab`. Establish `hl' : IsParam lam'`. Use `⟨fun a b hab => hl.1 (add_right_cancel hab), fun a b hab => by simpa [hlam] using hl.2.1 a b hab, fun a => ?_, fun a b => by simpa [hlam] using hl.2.2.2 a b⟩` and prove the remaining obligations.

Take `⟨k, hk⟩` from `hl.2.2.1 a`. Conclude with `⟨k - 1, by simp only [hlam]; push_cast; linarith⟩`. Take `⟨r1, r2⟩` from `of_trivial (Cover.twist R) hker hl' (by rw [← hb, ← hwSub_twAct] at h1; exact h1) (fun μ v hv => by`. Take `⟨m, m1, m2⟩` from `hc _ v ((Cover.isHW_twAct R.HK.act μ v).1 hv)`. Use `⟨m, fun a b hab => by simpa [hlam] using m1 a b hab, fun c => ?_⟩` and prove the remaining obligations.

Use `congrFun hb c` as an intermediate fact. Combine the linear relations using `[m2 c])`. Use the proof step `(hgap _ hh) (hgap _ hg) hY (isoVec_twist R (hb.symm ▸ hx))`. Use `⟨?_, fun k hk y hy => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `0 ≤ ⟪x, ((T.sq (T.expt Y) : ℂˣ) : ℂ)⁻¹ • R.U.π (T.expt Y) x⟫_ℂ at r1`.

Rewrite `r1` using `[sq_expt hY, inv_one, one_smul]`. Then use the resulting hypothesis. Establish `r3` using `r2 k hk y (isoVec_twist R (hb.symm ▸ hy))`. Express the relevant statement in the definitionally equal form `‖⟪y, ((T.sq (k * T.expt Y) : ℂˣ) : ℂ)⁻¹ • R.U.π (k * T.expt Y) x⟫_ℂ‖ ≤ _ at r3`. Rewrite `r3` using `[inner_smul_right, norm_mul, norm_inv, Cover.norm_sq, inv_one, one_mul]`. Then use the resulting hypothesis.
-/
theorem of_any (R : DSRep T) {lam : Ix p q → ℚ} (hl : IsParam lam)
    (h1 : Module.finrank ℂ (hwSub R.HK.act (blattner lam)) = 1)
    (hc : ∀ (μ : Ix p q → ℚ) v, IsHW R.HK.act μ v →
      ∃ m : Ix p q → Ix p q → ℕ, (∀ a b, m a b ≠ 0 → lam b < lam a) ∧
        ∀ c, μ c = blattner lam c +
          ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0)))
    {h : ℝ} (hh : GapGe lam h) (hg : GapGe lam (2 * (p + q : ℕ) + 1)) {Y : Mat p q} (hY : Y ∈ pR p q)
    {x : R.U.H} (hx : x ∈ isoVec R (blattner lam)) :
    0 ≤ ⟪x, R.U.π (T.expt Y) x⟫_ℂ ∧ ∀ k ∈ T.Kset, ∀ y ∈ isoVec R (blattner lam),
      ‖⟪y, R.U.π (k * T.expt Y) x⟫_ℂ‖ ≤
        Real.exp (-(h / 8) * min (hsNorm Y ^ 2) (hsNorm Y / Real.sqrt (2 * (min p q : ℕ)))) * ‖x‖ * ‖y‖ := by
  rcases Cover.trivial_or_twist R with hker | hker
  · exact of_trivial R hker hl h1 hc hh hg hY hx
  set lam' : Ix p q → ℚ := fun a => lam a + -(1 / 2) with hlam
  have hb : (fun a => blattner lam' a + 1 / 2) = blattner lam := by
    rw [hlam, Cover.blattner_add]
    funext a
    ring
  have hgap : ∀ h, GapGe lam h → GapGe lam' h := fun h hh a b hab => by simpa [hlam] using hh a b hab
  have hl' : IsParam lam' := by
    refine ⟨fun a b hab => hl.1 (add_right_cancel hab), fun a b hab => by simpa [hlam] using hl.2.1 a b hab,
      fun a => ?_, fun a b => by simpa [hlam] using hl.2.2.2 a b⟩
    obtain ⟨k, hk⟩ := hl.2.2.1 a
    exact ⟨k - 1, by simp only [hlam]; push_cast; linarith⟩
  obtain ⟨r1, r2⟩ := of_trivial (Cover.twist R) hker hl'
    (by rw [← hb, ← hwSub_twAct] at h1; exact h1)
    (fun μ v hv => by
      obtain ⟨m, m1, m2⟩ := hc _ v ((Cover.isHW_twAct R.HK.act μ v).1 hv)
      refine ⟨m, fun a b hab => by simpa [hlam] using m1 a b hab, fun c => ?_⟩
      have := congrFun hb c
      linarith [m2 c])
    (hgap _ hh) (hgap _ hg) hY (isoVec_twist R (hb.symm ▸ hx))
  refine ⟨?_, fun k hk y hy => ?_⟩
  · change 0 ≤ ⟪x, ((T.sq (T.expt Y) : ℂˣ) : ℂ)⁻¹ • R.U.π (T.expt Y) x⟫_ℂ at r1
    rwa [sq_expt hY, inv_one, one_smul] at r1
  · have r3 := r2 k hk y (isoVec_twist R (hb.symm ▸ hy))
    change ‖⟪y, ((T.sq (k * T.expt Y) : ℂˣ) : ℂ)⁻¹ • R.U.π (k * T.expt Y) x⟫_ℂ‖ ≤ _ at r3
    rwa [inner_smul_right, norm_mul, norm_inv, Cover.norm_sq, inv_one, one_mul] at r3

/- English proof (translation)
Introduce `X h1 _ _ _ p q lam hl h hh hr`. Take `⟨a, -, c⟩` from `h1 p q lam hl`. Establish `hg : GapGe lam (2 * (p + q : ℕ) + 1)`. Introduce `i j hij`. Use `le_trans (le_trans ?_ hr) (hh i j hij)` and prove the remaining obligations.

Establish `hpq : 1 ≤ p ∧ 1 ≤ q`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j`. Conclude with `(hij trivial).elim`. Conclude with `⟨i.pos, j.pos⟩`. Conclude with `⟨j.pos, i.pos⟩`.

Conclude with `(hij trivial).elim`. Establish `h2 : (1 : ℝ) ≤ ((min p q : ℕ) : ℝ) ^ ((3 : ℝ) / 2)` using `Real.one_le_rpow (by exact_mod_cast le_min hpq.1 hpq.2) (by norm_num)`. Establish `h3 : (1 : ℝ) ≤ ((p + q : ℕ) : ℝ)` using `by exact_mod_cast hpq.1.trans (Nat.le_add_right p q)`. Unfold `rangeOfSeventhSum`. Use the polynomial consequences of the given equalities and inequalities.

Establish `key` using `fun (Y : Mat p q) (hY : Y ∈ pR p q) x hx => of_any (X.ds p q lam) hl a (fun μ v hv => (c μ v hv).imp fun m hm => ⟨hm.1, congrFun hm.2⟩) hh hg hY (x := x) hx`. Use `⟨fun Y hY x hx => ?_, fun k hk Y hY x hx y hy => (key Y hY x hx).2 k hk y hy⟩` and prove the remaining obligations. Use `Complex.nonneg_iff.1 (key Y hY x hx).1` as an intermediate fact. Conclude with `⟨this.2.symm, this.1⟩`.
-/
theorem lowest_type_positive_and_decays : ∀ X : ProvA, DiscreteSeriesBlattner X → admQ5 X → admQ7 → admQ8 → DiscreteSeriesPositivity X := by
  intro X h1 _ _ _ p q lam hl h hh hr
  obtain ⟨a, -, c⟩ := h1 p q lam hl
  have hg : GapGe lam (2 * (p + q : ℕ) + 1) := by
    intro i j hij
    refine le_trans (le_trans ?_ hr) (hh i j hij)
    have hpq : 1 ≤ p ∧ 1 ≤ q := by
      rcases i with i | i <;> rcases j with j | j
      · exact (hij trivial).elim
      · exact ⟨i.pos, j.pos⟩
      · exact ⟨j.pos, i.pos⟩
      · exact (hij trivial).elim
    have h2 : (1 : ℝ) ≤ ((min p q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) :=
      Real.one_le_rpow (by exact_mod_cast le_min hpq.1 hpq.2) (by norm_num)
    have h3 : (1 : ℝ) ≤ ((p + q : ℕ) : ℝ) := by exact_mod_cast hpq.1.trans (Nat.le_add_right p q)
    unfold rangeOfSeventhSum
    nlinarith
  have key := fun (Y : Mat p q) (hY : Y ∈ pR p q) x hx => of_any (X.ds p q lam) hl a
    (fun μ v hv => (c μ v hv).imp fun m hm => ⟨hm.1, congrFun hm.2⟩) hh hg hY (x := x) hx
  refine ⟨fun Y hY x hx => ?_, fun k hk Y hY x hx y hy => (key Y hY x hx).2 k hk y hy⟩
  have := Complex.nonneg_iff.1 (key Y hY x hx).1
  exact ⟨this.2.symm, this.1⟩

end Cover

end GlobalTheory.SphJet
