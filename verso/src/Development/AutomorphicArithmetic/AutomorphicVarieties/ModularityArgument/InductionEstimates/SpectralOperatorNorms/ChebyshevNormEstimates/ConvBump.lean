import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.HeckeP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ActUniq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.IntegrableAeCpt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.CompLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.EqZeroOfSlices
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.FlatInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvSpec
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.Imports
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.AmpRep
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.RepOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CompBound
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CompCap
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CompShift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.BumpConvolutionOperators

/- English proof (translation)
Use `⟨fun x => ∫ t, κ t (w (x + t)), ?_, ?_, ?_, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ x, ∫ t, κ t (w (x + t)) = ∫ t in Set.Icc (-R) R, κ t (w (x + t))` using `fun x => by`. Use `(setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm` and prove the remaining obligations. Rewrite using `[hR t (lt_of_not_ge fun h => ht (abs_le.1 h)), ContinuousLinearMap.zero_apply]`. Simplify using `only [h1]`.

Conclude with `continuous_parametric_integral_of_continuous (f := fun x t => κ t (w (x + t))) ((hκ.1.comp continuous_snd).clm_apply (hw.comp (continuous_fst.add continuous_snd))) isCompact_Icc`. Take `⟨M, hM⟩` from `hc.isCompact.isBounded.subset_closedBall 0`. Use `HasCompactSupport.intro (isCompact_Icc (a := -(M + R)) (b := M + R)) fun x hx => ?_` and prove the remaining obligations. Establish `hx' : M + R < |x|` using `lt_of_not_ge fun h => hx (abs_le.1 h)`. Use `integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)` and prove the remaining obligations.

Distinguish the cases in `ht : R < |t|`. Simplify using `[hR t ht]`. Establish `: w (x + t) = 0`. Assume the negation of the conclusion as `h`. Establish `h2` using `hM (subset_tsupport _ h)`.

Rewrite `h2` using `[Metric.mem_closedBall, Real.dist_eq, sub_zero]`. Establish `h3` using `abs_sub (x + t) t`. Rewrite `h3` using `[add_sub_cancel_right]`. Combine the linear relations using `[not_lt.1 ht]`. Simplify using `[this]`.

Use `filter_upwards [(convSpec κ hκ U).1] with x hx`. Rewrite using `[hx]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [(measurePreserving_add_left volume x).quasiMeasurePreserving.ae hU] with t ht`. Rewrite using `[ht]`.

Establish `hi : Integrable (fun t : ℝ => Complex.exp ((0 : ℂ) * t) • κ t)`. Simplify using `using hκ.1.integrable_of_hasCompactSupport hκ.2`. Rewrite using `[symb, ContinuousLinearMap.integral_apply hi]`. Use `integral_congr_ae (Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Distinguish the cases in `ht : R < |t|`.

Simplify using `[hR t ht]`. Establish `: |x + t| ≤ R + 1` using `(abs_add_le x t).trans (by linarith [not_lt.1 ht])`. Simplify using `[he _ this]`.
-/
private theorem conv_bump {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]
    (κ : ℝ → V →L[ℂ] V) (hκ : Ker κ) (R : ℝ) (hR : ∀ t, R < |t| → κ t = 0) (w : ℝ → V) (hw : Continuous w) (hc : HasCompactSupport w)
    (e : V) (he : ∀ x, |x| ≤ R + 1 → w x = e) (U : L V) (hU : ∀ᵐ x : ℝ, U x = w x) :
    ∃ u : ℝ → V, Continuous u ∧ HasCompactSupport u ∧ (∀ᵐ x : ℝ, conv κ U x = u x) ∧ ∀ x, |x| ≤ 1 → u x = symb κ 0 e := by
  refine ⟨fun x => ∫ t, κ t (w (x + t)), ?_, ?_, ?_, fun x hx => ?_⟩
  · have h1 : ∀ x, ∫ t, κ t (w (x + t)) = ∫ t in Set.Icc (-R) R, κ t (w (x + t)) := fun x => by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm
      rw [hR t (lt_of_not_ge fun h => ht (abs_le.1 h)), ContinuousLinearMap.zero_apply]
    simp only [h1]
    exact continuous_parametric_integral_of_continuous (f := fun x t => κ t (w (x + t)))
      ((hκ.1.comp continuous_snd).clm_apply (hw.comp (continuous_fst.add continuous_snd))) isCompact_Icc
  · obtain ⟨M, hM⟩ := hc.isCompact.isBounded.subset_closedBall 0
    refine HasCompactSupport.intro (isCompact_Icc (a := -(M + R)) (b := M + R)) fun x hx => ?_
    have hx' : M + R < |x| := lt_of_not_ge fun h => hx (abs_le.1 h)
    refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : R < |t|
    · simp [hR t ht]
    · have : w (x + t) = 0 := by
        by_contra h
        have h2 := hM (subset_tsupport _ h)
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h2
        have h3 := abs_sub (x + t) t
        rw [add_sub_cancel_right] at h3
        linarith [not_lt.1 ht]
      simp [this]
  · filter_upwards [(convSpec κ hκ U).1] with x hx
    rw [hx]
    refine integral_congr_ae ?_
    filter_upwards [(measurePreserving_add_left volume x).quasiMeasurePreserving.ae hU] with t ht
    rw [ht]
  · have hi : Integrable (fun t : ℝ => Complex.exp ((0 : ℂ) * t) • κ t) := by
      simpa using hκ.1.integrable_of_hasCompactSupport hκ.2
    rw [symb, ContinuousLinearMap.integral_apply hi]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : R < |t|
    · simp [hR t ht]
    · have : |x + t| ≤ R + 1 := (abs_add_le x t).trans (by linarith [not_lt.1 ht])
      simp [he _ this]

/- English proof (translation)
Take `⟨M, hM⟩` from `hκ.2.isCompact.isBounded.subset_closedBall 0`. Use `⟨M, fun t ht => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Establish `h2` using `hM (subset_tsupport _ h)`. Rewrite `h2` using `[Metric.mem_closedBall, Real.dist_eq, sub_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem ker_bd {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (κ : ℝ → V →L[ℂ] V) (hκ : Ker κ) :
    ∃ R : ℝ, ∀ t, R < |t| → κ t = 0 := by
  obtain ⟨M, hM⟩ := hκ.2.isCompact.isBounded.subset_closedBall 0
  refine ⟨M, fun t ht => ?_⟩
  by_contra h
  have h2 := hM (subset_tsupport _ h)
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h2
  linarith

/- English proof (translation)
Set `w : ℝ → V` to `fun x => ((max 0 (min 1 (R + 1 - |x|)) : ℝ) : ℂ) • e`. Establish `hw : Continuous w` using `by fun_prop`. Establish `hc : HasCompactSupport w`. Use `HasCompactSupport.intro (isCompact_Icc (a := -(R + 1)) (b := R + 1)) fun x hx => ?_` and prove the remaining obligations. Establish `hx' : R + 1 < |x|` using `lt_of_not_ge fun h => hx (abs_le.1 h)`.

Establish `: max 0 (min 1 (R + 1 - |x|)) = 0` using `max_eq_left (min_le_of_right_le (by linarith))`. Simplify using `only [w, this, Complex.ofReal_zero, zero_smul]`. Use `⟨w, (hw.memLp_of_hasCompactSupport hc).toLp w, hw, hc, fun x hx => ?_, MemLp.coeFn_toLp _⟩` and prove the remaining obligations. Establish `: max 0 (min 1 (R + 1 - |x|)) = 1` using `by rw [min_eq_left (by linarith), max_eq_right zero_le_one]`. Simplify using `only [w, this, Complex.ofReal_one, one_smul]`.
-/
private theorem bump_ex {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (e : V) (R : ℝ) :
    ∃ (w : ℝ → V) (U : L V), Continuous w ∧ HasCompactSupport w ∧ (∀ x, |x| ≤ R → w x = e) ∧ ∀ᵐ x : ℝ, U x = w x := by
  let w : ℝ → V := fun x => ((max 0 (min 1 (R + 1 - |x|)) : ℝ) : ℂ) • e
  have hw : Continuous w := by fun_prop
  have hc : HasCompactSupport w := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -(R + 1)) (b := R + 1)) fun x hx => ?_
    have hx' : R + 1 < |x| := lt_of_not_ge fun h => hx (abs_le.1 h)
    have : max 0 (min 1 (R + 1 - |x|)) = 0 := max_eq_left (min_le_of_right_le (by linarith))
    simp only [w, this, Complex.ofReal_zero, zero_smul]
  refine ⟨w, (hw.memLp_of_hasCompactSupport hc).toLp w, hw, hc, fun x hx => ?_, MemLp.coeFn_toLp _⟩
  have : max 0 (min 1 (R + 1 - |x|)) = 1 := by rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  simp only [w, this, Complex.ofReal_one, one_smul]

/- English proof (translation)
Use `set ε : ℝ := ![1, -1] j with hε`. Apply the tactic sequence `have h1 : ∀ x : ℝ, (t + Pi.single j x : Fin 2 → ℝ) 0 - (t + Pi.single j x : Fin 2 → ℝ) 1 = t 0 - t 1 + ε * x := fun x => by fin_cases j <;> simp [hε] <;> ring`. Establish `h2 : ∀ᶠ x : ℝ in 𝓝 0, |t 0 - t 1 + ε * x| < 1`. Establish `: Continuous fun x : ℝ => |t 0 - t 1 + ε * x|` using `by fun_prop`. Conclude with `this.continuousAt.eventually_lt continuousAt_const (by simpa using ht)`.

Establish `h3 : HasDerivAt (fun x : ℝ => a * Complex.exp ((t 0 - t 1 + ε * x : ℝ) : ℂ)) (a * (Complex.exp ((t 0 - t 1 + ε * 0 : ℝ) : ℂ) * ((ε * 1 : ℝ) : ℂ))) 0` using `((((hasDerivAt_id (0 : ℝ)).const_mul ε).const_add (t 0 - t 1)).ofReal_comp.cexp).const_mul a`. Establish `h4` using `hG.unique (h3.congr_of_eventuallyEq (h2.mono fun x hx => by show F _ = _`. Rewrite using `[hF _ (by rwa [h1]), h1]))`. Rewrite using `[h4]`. Simplify using `only [mul_zero, add_zero, mul_one]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem der_loc (F : (Fin 2 → ℝ) → ℂ) (a : ℂ) (hF : ∀ t, |t 0 - t 1| < 1 → F t = a * Complex.exp ((t 0 - t 1 : ℝ) : ℂ))
    (j : Fin 2) (t : Fin 2 → ℝ) (ht : |t 0 - t 1| < 1) (G : ℂ) (hG : HasDerivAt (fun x : ℝ => F (t + Pi.single j x)) G 0) :
    G = (![1, -1] j : ℝ) * a * Complex.exp ((t 0 - t 1 : ℝ) : ℂ) := by
  set ε : ℝ := ![1, -1] j with hε
  have h1 : ∀ x : ℝ, (t + Pi.single j x : Fin 2 → ℝ) 0 - (t + Pi.single j x : Fin 2 → ℝ) 1 = t 0 - t 1 + ε * x := fun x => by
    fin_cases j <;> simp [hε] <;> ring
  have h2 : ∀ᶠ x : ℝ in 𝓝 0, |t 0 - t 1 + ε * x| < 1 := by
    have : Continuous fun x : ℝ => |t 0 - t 1 + ε * x| := by fun_prop
    exact this.continuousAt.eventually_lt continuousAt_const (by simpa using ht)
  have h3 : HasDerivAt (fun x : ℝ => a * Complex.exp ((t 0 - t 1 + ε * x : ℝ) : ℂ))
      (a * (Complex.exp ((t 0 - t 1 + ε * 0 : ℝ) : ℂ) * ((ε * 1 : ℝ) : ℂ))) 0 :=
    ((((hasDerivAt_id (0 : ℝ)).const_mul ε).const_add (t 0 - t 1)).ofReal_comp.cexp).const_mul a
  have h4 := hG.unique (h3.congr_of_eventuallyEq (h2.mono fun x hx => by
    show F _ = _
    rw [hF _ (by rwa [h1]), h1]))
  rw [h4]
  simp only [mul_zero, add_zero, mul_one]
  ring

/- English proof (translation)
Use `set p : Polynomial ℂ := (m.map fun r => Polynomial.X + Polynomial.C r).prod with hp`. Establish `hd : p.degree < (Finset.univ : Finset (Fin (n + 1))).card`. Establish `: p.natDegree = n`. Rewrite using `[hp, Polynomial.natDegree_multiset_prod_of_monic]`. Simplify using `[Multiset.map_map, hm]`.

Introduce `q hq`. Take `⟨r, -, rfl⟩` from `Multiset.mem_map.1 hq`. Conclude with `Polynomial.monic_X_add_C r`. Use `Polynomial.degree_le_natDegree.trans_lt ?_` and prove the remaining obligations. Rewrite using `[this, Finset.card_univ, Fintype.card_fin]`.

Conclude with `Nat.lt_succ_self n` after adjusting the coercions. Establish `hinj : Set.InjOn (fun j : Fin (n + 1) => ((j : ℕ) : ℂ)) (Finset.univ : Finset (Fin (n + 1)))` using `fun a _ b _ h => Fin.ext (Nat.cast_injective h)`. Establish `h1` using `congrArg (fun q : Polynomial ℂ => q.coeff (n - i)) (Lagrange.eq_interpolate hinj hd)`. Simplify using `only [Lagrange.interpolate_apply, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul] at h1`. Establish `h2 : p.coeff (n - i) = m.esymm i`.

Rewrite using `[hp, Multiset.prod_X_add_C_coeff m (by omega), hm, Nat.sub_sub_self hi]`. Rewrite using `[← h2, h1]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm, hp, Polynomial.eval_multiset_prod, Multiset.map_map]`. Simplify using the standard rewrite rules.
-/
private theorem coef (n i : ℕ) (hi : i ≤ n) (m : Multiset ℂ) (hm : m.card = n) :
    ∑ j : Fin (n + 1), (Lagrange.basis Finset.univ (fun j : Fin (n + 1) => ((j : ℕ) : ℂ)) j).coeff (n - i) *
      (m.map fun x => ((j : ℕ) : ℂ) + x).prod = m.esymm i := by
  set p : Polynomial ℂ := (m.map fun r => Polynomial.X + Polynomial.C r).prod with hp
  have hd : p.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
    have : p.natDegree = n := by
      rw [hp, Polynomial.natDegree_multiset_prod_of_monic]
      · simp [Multiset.map_map, hm]
      · intro q hq
        obtain ⟨r, -, rfl⟩ := Multiset.mem_map.1 hq
        exact Polynomial.monic_X_add_C r
    refine Polynomial.degree_le_natDegree.trans_lt ?_
    rw [this, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast Nat.lt_succ_self n
  have hinj : Set.InjOn (fun j : Fin (n + 1) => ((j : ℕ) : ℂ)) (Finset.univ : Finset (Fin (n + 1))) := fun a _ b _ h =>
    Fin.ext (Nat.cast_injective h)
  have h1 := congrArg (fun q : Polynomial ℂ => q.coeff (n - i)) (Lagrange.eq_interpolate hinj hd)
  simp only [Lagrange.interpolate_apply, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul] at h1
  have h2 : p.coeff (n - i) = m.esymm i := by
    rw [hp, Multiset.prod_X_add_C_coeff m (by omega), hm, Nat.sub_sub_self hi]
  rw [← h2, h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, hp, Polynomial.eval_multiset_prod, Multiset.map_map]
  simp

open GlobalTheory.CuspRep UpperTheory.V.Cm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {S : Set (Pl E)} (b b' : BW.Blo S 2)

private def Loc (ψ : Sm E (2 + 2)) (a : ℂ) : Prop :=
  BW.Umg ψ ∧ ∀ t : Fin 2 → ℝ, |t 0 - t 1| < 1 → (dat2 b b').comp ψ.1 t = a * Complex.exp ((t 0 - t 1 : ℝ) : ℂ)

variable {b b'}

/- English proof (translation)
Establish `hu` using `(BW.umgOps E (2 + 2)).2`. Use `⟨(hu _ ((hu _ h.1).2.2.1 c)).2.1 _ h'.1, fun t ht => ?_⟩` and prove the remaining obligations. Rewrite using `[(BW.compBound E S _ (dat2 b b')).2 ψ χ c h.1 h'.1 t, h.2 t ht, h'.2 t ht]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem Loc.lin {ψ χ : Sm E (2 + 2)} {a a' : ℂ} (h : Loc b b' ψ a) (h' : Loc b b' χ a') (c : ℂ) :
    Loc b b' (c • ψ + χ) (c * a + a') := by
  have hu := (BW.umgOps E (2 + 2)).2
  refine ⟨(hu _ ((hu _ h.1).2.2.1 c)).2.1 _ h'.1, fun t ht => ?_⟩
  rw [(BW.compBound E S _ (dat2 b b')).2 ψ χ c h.1 h'.1 t, h.2 t ht, h'.2 t ht]
  ring

/- English proof (translation)
Establish `h0` using `(BW.umgOps E (2 + 2)).1`. Use `⟨h0, fun t _ => ?_⟩` and prove the remaining obligations. Use `(BW.compBound E S _ (dat2 b b')).2 0 0 1 h0 h0 t` as an intermediate fact. Rewrite `this` using `[smul_zero, add_zero, one_mul]`. Rewrite using `[zero_mul]`.

Take the linear combination `-this`.
-/
private theorem Loc.zero : Loc b b' 0 0 := by
  have h0 := (BW.umgOps E (2 + 2)).1
  refine ⟨h0, fun t _ => ?_⟩
  have := (BW.compBound E S _ (dat2 b b')).2 0 0 1 h0 h0 t
  rw [smul_zero, add_zero, one_mul] at this
  rw [zero_mul]
  linear_combination -this

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using Loc.zero`. Consider the case `insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi]`. Conclude with `(h i).lin ih _`.
-/
private theorem Loc.sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (ψ : ι → Sm E (2 + 2)) (a : ι → ℂ) (h : ∀ i, Loc b b' (ψ i) (a i)) :
    Loc b b' (∑ i ∈ s, c i • ψ i) (∑ i ∈ s, c i * a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Loc.zero
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact (h i).lin ih _

/- English proof (translation)
Use `⟨?_, fun t ht => der_loc ((dat2 b b').comp ψ.1) a h.2 j t ht _ ((BW.compShift E S _ (dat2 b b') ψ t h.1).2 j)⟩` and prove the remaining obligations. Establish `: ∃ u, (dat2 b b').J j = uC E (2 + 2) u`. Simplify using `only [BW.Dat.J, ← uC_genC, ← map_sum, ← map_smul]`. Conclude with `⟨_, rfl⟩`. Take `⟨u, hu⟩` from `this`.

Rewrite using `[hu]`. Conclude with `((BW.umgOps E (2 + 2)).2 _ h.1).2.2.2.1 u`.
-/
private theorem Loc.der {ψ : Sm E (2 + 2)} {a : ℂ} (h : Loc b b' ψ a) (j : Fin 2) :
    Loc b b' ((dat2 b b').J j ψ) ((![1, -1] j : ℝ) * a) := by
  refine ⟨?_, fun t ht => der_loc ((dat2 b b').comp ψ.1) a h.2 j t ht _ ((BW.compShift E S _ (dat2 b b') ψ t h.1).2 j)⟩
  have : ∃ u, (dat2 b b').J j = uC E (2 + 2) u := by
    simp only [BW.Dat.J, ← uC_genC, ← map_sum, ← map_smul]
    exact ⟨_, rfl⟩
  obtain ⟨u, hu⟩ := this
  rw [hu]
  exact ((BW.umgOps E (2 + 2)).2 _ h.1).2.2.2.1 u

/- English proof (translation)
Establish `: (dat2 b b').idx = (![0, 0, 1, 1] : Fin 4 → Fin 2)`. Apply the tactic sequence `funext i; fin_cases i <;> rfl`. Unfold `BW.Dat.size`. Rewrite using `[this]`. Apply the tactic sequence `fin_cases j <;> rfl`.
-/
private theorem size_eq (j : Fin 2) : (dat2 b b').size j = 2 := by
  have : (dat2 b b').idx = (![0, 0, 1, 1] : Fin 4 → Fin 2) := by
    funext i; fin_cases i <;> rfl
  unfold BW.Dat.size
  rw [this]
  fin_cases j <;> rfl

/- English proof (translation)
Establish `h : (dat2 b b').rho j = ((∑ l ∈ Finset.Iio j, ((dat2 b b').size l : ℝ)) - ∑ l ∈ Finset.Ioi j, ((dat2 b b').size l : ℝ)) / 2` using `rfl`. Rewrite using `[h]`. Simplify using `only [size_eq]`. Apply the tactic sequence `fin_cases j <;> simp`.
-/
private theorem rho_eq (j : Fin 2) : (dat2 b b').rho j = -(![1, -1] j : ℝ) := by
  have h : (dat2 b b').rho j = ((∑ l ∈ Finset.Iio j, ((dat2 b b').size l : ℝ)) - ∑ l ∈ Finset.Ioi j, ((dat2 b b').size l : ℝ)) / 2 := rfl
  rw [h]
  simp only [size_eq]
  fin_cases j <;> simp

/- English proof (translation)
Use `h.lin (h.der j) (x + ((dat2 b b').rho j : ℂ))` as an intermediate fact. Rewrite using `[LinearMap.add_apply, Module.algebraMap_end_apply]`. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[rho_eq]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem Loc.fac {ψ : Sm E (2 + 2)} {a : ℂ} (h : Loc b b' ψ a) (j : Fin 2) (x : ℂ) :
    Loc b b' ((algebraMap ℂ (Module.End ℂ (Sm E (2 + 2))) (x + ((dat2 b b').rho j : ℂ)) + (dat2 b b').J j) ψ) (x * a) := by
  have := h.lin (h.der j) (x + ((dat2 b b').rho j : ℂ))
  rw [LinearMap.add_apply, Module.algebraMap_end_apply]
  convert this using 1
  rw [rho_eq]
  push_cast
  ring

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simpa using h`. Consider the case `cons i l ih`. Rewrite using `[List.map_cons, List.prod_cons, Module.End.mul_apply, List.map_cons, List.prod_cons, mul_assoc]`. Conclude with `ih.fac _ _`.
-/
private theorem Loc.prod {ψ : Sm E (2 + 2)} {a : ℂ} (h : Loc b b' ψ a) (x : Fin (2 + 2) → ℂ) (l : List (Fin (2 + 2))) :
    Loc b b' ((l.map fun i => algebraMap ℂ (Module.End ℂ (Sm E (2 + 2))) (x i + ((dat2 b b').rho ((dat2 b b').idx i) : ℂ)) +
      (dat2 b b').J ((dat2 b b').idx i)).prod ψ) ((l.map x).prod * a) := by
  induction l with
  | nil => simpa using h
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, List.map_cons, List.prod_cons, mul_assoc]
    exact ih.fac _ _

/- English proof (translation)
Use `⟨?_, fun t ht => ?_⟩` and prove the remaining obligations. Rewrite using `[← uC_capC]`. Conclude with `((BW.umgOps E (2 + 2)).2 _ h.1).2.2.2.1 _`. Rewrite using `[BW.compCap E S _ (dat2 b b') ψ τ u h.1, List.ofFn_eq_map, (h.prod (fun i => u + (dat2 b b').lam τ i) (List.finRange (2 + 2))).2 t ht, Multiset.map_map, ← List.ofFn_eq_map, List.prod_ofFn]`. Both sides reduce to the same expression.
-/
private theorem Loc.capelli {ψ : Sm E (2 + 2)} {a : ℂ} (h : Loc b b' ψ a) (τ : E →+* ℂ) (u : ℂ) :
    Loc b b' (cap τ u ψ) (((Finset.univ.val.map ((dat2 b b').lam τ)).map fun x => u + x).prod * a) := by
  refine ⟨?_, fun t ht => ?_⟩
  · rw [← uC_capC]
    exact ((BW.umgOps E (2 + 2)).2 _ h.1).2.2.2.1 _
  · rw [BW.compCap E S _ (dat2 b b') ψ τ u h.1, List.ofFn_eq_map,
      (h.prod (fun i => u + (dat2 b b').lam τ i) (List.finRange (2 + 2))).2 t ht, Multiset.map_map, ← List.ofFn_eq_map,
      List.prod_ofFn]
    rfl

/- English proof (translation)
Simplify using `only [BW.zop, BW.evZ, aeval_X, BW.zC, map_sum, map_smul, uC_capC]`.
-/
private theorem zop_X {n : ℕ} (y : Ix E n) : BW.zop (X y) = ∑ j : Fin (n + 1),
    (Lagrange.basis Finset.univ (fun j : Fin (n + 1) => ((j : ℕ) : ℂ)) j).coeff (n - (y.2 + 1)) •
      (cap y.1 ((j : ℕ) : ℂ) : Module.End ℂ (Sm E n)) := by
  simp only [BW.zop, BW.evZ, aeval_X, BW.zC, map_sum, map_smul, uC_capC]

/- English proof (translation)
Rewrite using `[zop_X, ← coef (2 + 2) (y.2 + 1) y.2.2 _ (by simp), Finset.sum_mul, LinearMap.sum_apply]`. Simplify using `only [LinearMap.smul_apply, mul_assoc]`. Conclude with `Loc.sum _ _ _ _ fun j => h.capelli _ _`.
-/
private theorem Loc.z {ψ : Sm E (2 + 2)} {a : ℂ} (h : Loc b b' ψ a) (y : Ix E (2 + 2)) :
    Loc b b' (BW.zop (X y) ψ) ((Finset.univ.val.map ((dat2 b b').lam y.1)).esymm (y.2 + 1) * a) := by
  rw [zop_X, ← coef (2 + 2) (y.2 + 1) y.2.2 _ (by simp), Finset.sum_mul, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, mul_assoc]
  exact Loc.sum _ _ _ _ fun j => h.capelli _ _

/- English proof (translation)
Establish `h : ∀ u : ℂ, Commute (cap y.1 u) (rt E n g)` using `fun u => by`. Rewrite using `[← infGL_mul_finGL g, map_mul]`. Conclude with `(GlobalTheory.CapAdInv.cap_commute_rt_infGL E n y.1 u _).mul_right (commute_cap_finRep y.1 u _)`. Establish `: Commute (BW.zop (X y)) (rt E n g)`. Rewrite using `[zop_X]`.

Conclude with `Commute.sum_left _ _ _ fun j _ => (h _).smul_left _`. Conclude with `(LinearMap.congr_fun this.eq ψ).symm`.
-/
private theorem rt_zop {n : ℕ} (y : Ix E n) (g : GA E n) (ψ : Sm E n) :
    rt E n g (BW.zop (X y) ψ) = BW.zop (X y) (rt E n g ψ) := by
  have h : ∀ u : ℂ, Commute (cap y.1 u) (rt E n g) := fun u => by
    rw [← infGL_mul_finGL g, map_mul]
    exact (GlobalTheory.CapAdInv.cap_commute_rt_infGL E n y.1 u _).mul_right (commute_cap_finRep y.1 u _)
  have : Commute (BW.zop (X y)) (rt E n g) := by
    rw [zop_X]
    exact Commute.sum_left _ _ _ fun j _ => (h _).smul_left _
  exact (LinearMap.congr_fun this.eq ψ).symm

/- English proof (translation)
Use `Eq.trans ?_ (add_comm _ _)` and prove the remaining obligations. Both sides reduce to the same expression.
-/
private theorem lam_eq (τ : E →+* ℂ) : Finset.univ.val.map ((dat2 b b').lam τ) =
    (Finset.univ.val.map fun i => b'.Λ τ i) + Finset.univ.val.map fun i => b.Λ τ i := by
  refine Eq.trans ?_ (add_comm _ _)
  rfl

/- English proof (translation)
Establish `l₂` using `h.z y`. Rewrite `l₂` using `[lam_eq, hm]`. Establish `l₃` using `(h.lin l₂ (-m.esymm (y.2 + 1))).2 0 (by simp)`. Rewrite using `[map_add, map_smul, rt_zop, l₃]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem Loc.kill {ψ : Sm E (2 + 2)} {a : ℂ} {g : GA E (2 + 2)} (h : Loc b b' (rt E (2 + 2) g ψ) a) (y : Ix E (2 + 2)) (m : Multiset ℂ)
    (hm : ((Finset.univ.val.map fun i => b'.Λ y.1 i) + Finset.univ.val.map fun i => b.Λ y.1 i) = m) :
    (dat2 b b').comp (rt E (2 + 2) g ((-m.esymm (y.2 + 1)) • ψ + BW.zop (X y) ψ)).1 (0 : Fin 2 → ℝ) = 0 := by
  have l₂ := h.z y
  rw [lam_eq, hm] at l₂
  have l₃ := (h.lin l₂ (-m.esymm (y.2 + 1))).2 0 (by simp)
  rw [map_add, map_smul, rt_zop, l₃]
  ring

/- English proof (translation)
Establish `h : HasCompactSupport (fun x => c • u x)` using `huc.comp_left (g := fun z => c • z) (smul_zero c)`. Use `⟨(hu.const_smul _).add hv, h.add hvc, ?_⟩` and prove the remaining obligations. Use `filter_upwards [Lp.coeFn_add (c • U) W, Lp.coeFn_smul c U, hua, hva] with x h1 h2 h3 h4`. Rewrite using `[h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4]`.
-/
private theorem comb {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (c : ℂ) {u v : ℝ → V} {U W : L V}
    (hu : Continuous u) (hv : Continuous v) (huc : HasCompactSupport u) (hvc : HasCompactSupport v)
    (hua : ∀ᵐ x : ℝ, U x = u x) (hva : ∀ᵐ x : ℝ, W x = v x) :
    Continuous (fun x => c • u x + v x) ∧ HasCompactSupport (fun x => c • u x + v x) ∧
      ∀ᵐ x : ℝ, (c • U + W : L V) x = c • u x + v x := by
  have h : HasCompactSupport (fun x => c • u x) := huc.comp_left (g := fun z => c • z) (smul_zero c)
  refine ⟨(hu.const_smul _).add hv, h.add hvc, ?_⟩
  filter_upwards [Lp.coeFn_add (c • U) W, Lp.coeFn_smul c U, hua, hva] with x h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4]

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.BumpConvolutionOperators

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.BumpConvolutionOperators in
/- English proof (translation)
Introduce `E _ _ _ μ _ θ 𝔢 𝔵 y`. Take `⟨f, hf, hZ⟩` from `genZk 𝔵 y`. Use `⟨?_, hZ ▸ (Hecke₃ E μ _ _ _ 𝔵.pair 𝔵.D _ _ 𝔵.A 𝔵.A' 𝔵.P 𝔵.isP).2 f hf⟩` and prove the remaining obligations. Take `⟨β, hβ, hc, -⟩` from `convR E μ _ _ _ ⟨𝔵.pair.irr₂, 𝔵.pair.irr₁, 𝔵.pair.orth.symm⟩ 𝔵.D _ _ 𝔵.A' 𝔵.A f hf`. Rewrite `hc` using `[hZ]`.

Use `⟨β, hβ, hc, ContinuousLinearMap.ext fun e => ?_⟩` and prove the remaining obligations. Take `⟨hα, ha, -⟩` from `𝔵.a_acts`. Rewrite `ha` using `[𝔢.a_op]`. Take `⟨R₁, h₁⟩` from `ker_bd β hβ`. Take `⟨R₂, h₂⟩` from `ker_bd _ hα`.

Take `⟨w, U, hw, hwc, hwe, hU⟩` from `bump_ex e (max R₁ R₂ + 1)`. Take `⟨u, hu, huc, hua, hu0⟩` from `conv_bump _ hα _ (fun t ht => h₂ t ((le_max_right R₁ R₂).trans_lt ht)) w hw hwc e hwe U hU`. Take `⟨v, hv, hvc, hva, hv0⟩` from `conv_bump _ hβ _ (fun t ht => h₁ t ((le_max_left R₁ R₂).trans_lt ht)) w hw hwc e hwe U hU`. Take `⟨ρ, N, Lm, hL, -, hLZ⟩` from `BW.ampRep E (2 + 2) μ 𝔢.toAmp (by norm_num)`. Establish `r₁` using `(hL (𝔵.A'.J U)).1`.

Establish `r₂` using `hLZ y (𝔵.A'.J U)`. Rewrite `r₁` using `[ha U _ (convSpec _ hα U).1]`. Rewrite `r₂` using `[hc U _ (convSpec _ hβ U).1]`. Use `set φ := Lm (𝔵.A'.J U)`. Use `set s := (𝔵.Λ y.1).esymm (y.2 + 1) with hs`.

Establish `r₃` using `(BW.repOps E (2 + 2) μ (by norm_num) _ _ r₁).2.1 _ _ (-s) r₂`. Rewrite `r₃` using `[← map_smul, ← map_add]`. Establish `key : (-s) • 𝔵.a₀ e + symb β 0 e = 0`. Use `bloEx 𝔵 _ fun b b' hb hb' k hk => ?_` and prove the remaining obligations. Take `⟨c, hc0, hcl⟩` from `compLine 𝔵 b b' hb hb'`.

Establish `l₁ : Loc b b' (GlobalTheory.CuspRep.rt E (2 + 2) (k : GlobalTheory.CuspRep.GA E (2 + 2)) φ) (c * ell b b' k (𝔵.A'.sec (𝔵.a₀ e)))`. Use `⟨((BW.umgOps E (2 + 2)).2 _ r₁.umg).2.2.2.2.1 _, fun t ht => ?_⟩` and prove the remaining obligations. Use `(hcl k hk u _ φ hu huc hua r₁ t).trans ?_` and prove the remaining obligations. Rewrite using `[hu0 _ (by rw [abs_div, abs_two]; linarith [abs_nonneg (t 0 - t 1)]), mul_right_comm]`. Both sides reduce to the same expression.

Establish `l₃` using `l₁.kill y (𝔵.Λ y.1) (by rw [hb.inf, hb'.inf]; rfl)`. Take `⟨c₁, c₂, c₃⟩` from `comb (-s) hu hv huc hvc hua hva`. Establish `l₅` using `(hcl k hk _ _ _ c₁ c₂ c₃ r₃ (0 : Fin 2 → ℝ)).symm.trans l₃`. Rewrite `l₅` using `[hu0 _ (by simp), hv0 _ (by simp)]`. Conclude with `(mul_eq_zero.1 l₅).resolve_left (mul_ne_zero hc0 (Complex.exp_ne_zero _))`.

Rewrite using `[ContinuousLinearMap.smul_apply]`. Rewrite `key` using `[neg_smul, neg_add_eq_zero]`. Conclude with `key.symm`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.genZ :
    ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {μ : Measure (normOneGL E (2 + 2))} [μ.IsHaarMeasure] {θ : Twist μ} {𝔢 : Side θ 2} (𝔵 : Fam 𝔢) (y : Ix E (2 + 2)),
      (∃ β, Ker β ∧ Conv 𝔵.A'.J 𝔵.A'.J (𝔢.toAmp.Z y) β ∧ symb β 0 = (𝔵.Λ y.1).esymm (y.2 + 1) • 𝔵.a₀) ∧
        𝔢.toAmp.Z y ∘L 𝔵.P = 𝔵.P ∘L 𝔢.toAmp.Z y := by
  intro E _ _ _ μ _ θ 𝔢 𝔵 y
  obtain ⟨f, hf, hZ⟩ := genZk 𝔵 y
  refine ⟨?_, hZ ▸ (Hecke₃ E μ _ _ _ 𝔵.pair 𝔵.D _ _ 𝔵.A 𝔵.A' 𝔵.P 𝔵.isP).2 f hf⟩
  obtain ⟨β, hβ, hc, -⟩ := convR E μ _ _ _ ⟨𝔵.pair.irr₂, 𝔵.pair.irr₁, 𝔵.pair.orth.symm⟩ 𝔵.D _ _ 𝔵.A' 𝔵.A f hf
  rw [hZ] at hc
  refine ⟨β, hβ, hc, ContinuousLinearMap.ext fun e => ?_⟩
  obtain ⟨hα, ha, -⟩ := 𝔵.a_acts
  rw [𝔢.a_op] at ha
  obtain ⟨R₁, h₁⟩ := ker_bd β hβ
  obtain ⟨R₂, h₂⟩ := ker_bd _ hα
  obtain ⟨w, U, hw, hwc, hwe, hU⟩ := bump_ex e (max R₁ R₂ + 1)
  obtain ⟨u, hu, huc, hua, hu0⟩ := conv_bump _ hα _ (fun t ht => h₂ t ((le_max_right R₁ R₂).trans_lt ht)) w hw hwc e hwe U hU
  obtain ⟨v, hv, hvc, hva, hv0⟩ := conv_bump _ hβ _ (fun t ht => h₁ t ((le_max_left R₁ R₂).trans_lt ht)) w hw hwc e hwe U hU
  obtain ⟨ρ, N, Lm, hL, -, hLZ⟩ := BW.ampRep E (2 + 2) μ 𝔢.toAmp (by norm_num)
  have r₁ := (hL (𝔵.A'.J U)).1
  have r₂ := hLZ y (𝔵.A'.J U)
  rw [ha U _ (convSpec _ hα U).1] at r₁
  rw [hc U _ (convSpec _ hβ U).1] at r₂
  set φ := Lm (𝔵.A'.J U)
  set s := (𝔵.Λ y.1).esymm (y.2 + 1) with hs
  have r₃ := (BW.repOps E (2 + 2) μ (by norm_num) _ _ r₁).2.1 _ _ (-s) r₂
  rw [← map_smul, ← map_add] at r₃
  have key : (-s) • 𝔵.a₀ e + symb β 0 e = 0 := by
    refine bloEx 𝔵 _ fun b b' hb hb' k hk => ?_
    obtain ⟨c, hc0, hcl⟩ := compLine 𝔵 b b' hb hb'
    have l₁ : Loc b b' (GlobalTheory.CuspRep.rt E (2 + 2) (k : GlobalTheory.CuspRep.GA E (2 + 2)) φ) (c * ell b b' k (𝔵.A'.sec (𝔵.a₀ e))) := by
      refine ⟨((BW.umgOps E (2 + 2)).2 _ r₁.umg).2.2.2.2.1 _, fun t ht => ?_⟩
      refine (hcl k hk u _ φ hu huc hua r₁ t).trans ?_
      rw [hu0 _ (by rw [abs_div, abs_two]; linarith [abs_nonneg (t 0 - t 1)]), mul_right_comm]
      rfl
    have l₃ := l₁.kill y (𝔵.Λ y.1) (by rw [hb.inf, hb'.inf]; rfl)
    obtain ⟨c₁, c₂, c₃⟩ := comb (-s) hu hv huc hvc hua hva
    have l₅ := (hcl k hk _ _ _ c₁ c₂ c₃ r₃ (0 : Fin 2 → ℝ)).symm.trans l₃
    rw [hu0 _ (by simp), hv0 _ (by simp)] at l₅
    exact (mul_eq_zero.1 l₅).resolve_left (mul_ne_zero hc0 (Complex.exp_ne_zero _))
  rw [ContinuousLinearMap.smul_apply]
  rw [neg_smul, neg_add_eq_zero] at key
  exact key.symm
