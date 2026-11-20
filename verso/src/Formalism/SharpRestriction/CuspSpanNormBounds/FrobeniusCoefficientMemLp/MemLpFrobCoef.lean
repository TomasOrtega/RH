import Formalism.SharpRestriction.CuspSpanNormBounds.HCFiniteKMultiplicityGapped
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalL1StatementOfProjectors
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.DecayHypothesisOfLargeConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FamilyDegreeRatioOfL2Uniqueness

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.S.Pv.DegI

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.BridgeLemma Formalism.MainNotions.PlaceDegreeData

/- English proof (translation)
Unfold `frob Formalism.REAL.hs`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.normSq_eq_norm_sq]`.
-/
theorem frob_eq_sqrt_hs {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : frob M = Real.sqrt (Formalism.REAL.hs M) := by
  unfold frob Formalism.REAL.hs
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_norm_sq]

/- English proof (translation)
Unfold `frob`. Conclude with `Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))`.
-/
theorem continuous_frob {n : ℕ} : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => frob M) := by
  unfold frob
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))

/- English proof (translation)
Introduce `a b hab`. Establish `h1` using `hG a b hab`. Establish `hco : ∀ j, |ν j - lam j| ≤ ρ` using `fun j => le_trans (Finset.single_le_sum (f := fun j => |ν j - lam j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)) hν`. Establish `h2` using `hco a`. Establish `h3` using `hco b`.

Establish `h4 : |lam a - lam b| ≤ |ν a - ν b| + |ν a - lam a| + |ν b - lam b|`. Establish `e : lam a - lam b = (ν a - ν b) - (ν a - lam a) + (ν b - lam b)` using `by ring`. Rewrite using `[e]`. Conclude with `le_trans (abs_add_le _ _) (by have := abs_sub (ν a - ν b) (ν a - lam a); linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gap_near {N : ℕ} {ε : Fin N → Bool} {lam ν : Fin N → ℝ} {G ρ : ℝ} (hG : GapAtLeast ε lam G)
    (hν : l1dist ν lam ≤ ρ) : GapAtLeast ε ν (G - 2 * ρ) := by
  intro a b hab
  have h1 := hG a b hab
  have hco : ∀ j, |ν j - lam j| ≤ ρ := fun j =>
    le_trans (Finset.single_le_sum (f := fun j => |ν j - lam j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)) hν
  have h2 := hco a
  have h3 := hco b
  have h4 : |lam a - lam b| ≤ |ν a - ν b| + |ν a - lam a| + |ν b - lam b| := by
    have e : lam a - lam b = (ν a - ν b) - (ν a - lam a) + (ν b - lam b) := by ring
    rw [e]
    exact le_trans (abs_add_le _ _) (by have := abs_sub (ν a - ν b) (ν a - lam a); linarith)
  linarith

section Rec

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

variable [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOneG] in

/- English proof (translation)
Take `⟨S, hS⟩` from `hσ.2.2.2.2.2.1`. Establish `hset : {S' | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S'} = {S}`. Use extensionality with `S'`. Prove the components needed by the constructor for the conclusion. Introduce `h'`.

Conclude with `BridgeDS3.lowest_K_type_mult_one_gapped n ε lam H σ hlam hσ h hgap hth S' S h' hS`. Introduce `h'`. Rewrite `h'` using `[Set.mem_singleton_iff]`. Rewrite using `[h']`. Conclude with `hS`.

Establish `e : lowKSub ε lam σ = S`. Unfold `lowKSub`. Rewrite using `[hset, sSup_singleton]`. Rewrite using `[e]`. Conclude with `hS.1`.
-/
theorem lowK_fd (hlam : IsHCParam lam) {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsDS ε lam σ) {h : ℝ}
    (hgap : GapAtLeast ε lam h) (hth : Formalism.MainNotions.GapDS.thrDS ε < h) : FiniteDimensional ℂ (lowKSub ε lam σ) := by
  obtain ⟨S, hS⟩ := hσ.2.2.2.2.2.1
  have hset : {S' | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S'} = {S} := by
    ext S'
    constructor
    · intro h'
      exact BridgeDS3.lowest_K_type_mult_one_gapped n ε lam H σ hlam hσ h hgap hth S' S h' hS
    · intro h'
      rw [Set.mem_singleton_iff] at h'
      rw [h']
      exact hS
  have e : lowKSub ε lam σ = S := by
    unfold lowKSub
    rw [hset, sSup_singleton]
  rw [e]
  exact hS.1

variable [Fact Formalism.MainNotions.BridgeCPX.HCMultDSG] [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOneG] in

/- English proof (translation)
Take `⟨s, hcs⟩` from `L1.exists_sign ε`. Use `set q0 : ℕ := min (pOf ε) (qOf ε) with hq0`. Establish `hqn : q0 ≤ n` using `hcs ▸ L1.card_SgIx_le ε s`. Establish `hn1 : 1 ≤ n` using `le_trans hpos hqn`. Establish `hnR : (1 : ℝ) ≤ n` using `by exact_mod_cast hn1`.

Establish `hqR : (1 : ℝ) ≤ q0` using `by exact_mod_cast hpos`. Establish `hqnR : (q0 : ℝ) ≤ n` using `by exact_mod_cast hqn`. Establish `hn3 : (1 : ℝ) ≤ (n : ℝ) ^ 3` using `one_le_pow₀ hnR`. Establish `hh0 : 0 ≤ h` using `le_trans (by positivity) hh`. Establish `hth : Formalism.MainNotions.GapDS.thrDS ε < h`.

Use `Formalism.MainNotions.GapDS.thrDS_le ε` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h120 : 120 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h`. Rewrite using `[← hq0]`. Establish `e1 : (q0 : ℝ) ^ ((3 : ℝ) / 2) ≤ (n : ℝ) ^ (2 : ℕ)`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Use `lowK_fd hlam hσ hgap hth` as an intermediate fact. Establish `hE : IsOrthProjOnto (lowKSub ε lam σ).starProjection (lowKSub ε lam σ)` using `⟨(lowKSub ε lam σ).isIdempotentElem_starProjection, fun x y => Submodule.inner_starProjection_left_eq_right _ x y, Submodule.range_starProjection _⟩`. Take `⟨w0, hw0⟩` from `exists_highest_weight_unit ε lam σ hσ`.

Establish `hlow : IsLowUnit ε lam σ w0` using `⟨hw0.1, hw0.2.1⟩`. Establish `hw00 : w0 ≠ 0`. Introduce `h0`. Use `hw0.1` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`.

Evaluate the numerical expressions using `at this`. Use `set A : ℝ := h / (8 * Real.sqrt (2 * (q0 : ℝ))) with hA`. Use `set C0 : ℝ := Real.sqrt n ^ A * Real.exp (A / Real.sqrt (2 * (q0 : ℝ))) with hC0`. Establish `hsq0 : 0 < Real.sqrt (2 * (q0 : ℝ))` using `Real.sqrt_pos.2 (by positivity)`. Establish `hA0 : 0 ≤ A` using `by rw [hA]; positivity`.

Establish `hC00 : 0 ≤ C0` using `by rw [hC0]; positivity`. Establish `hdec : ∀ g : Formalism.REAL.UJ ε, ‖⟪w0, σ (umat g) w0⟫_ℂ‖ ≤ C0 * Real.sqrt (Formalism.REAL.hs (umat g)) ^ (-A)`. Introduce `g`. Use `poly_decay_of_decay_statement D0 hDec n ε lam hlam H σ hσ _ hE h hgap h120 hpos w0 hlow (umat g) g.2` as an intermediate fact. Rewrite `this` using `[← hq0]`.

Conclude with `this`. Establish `hU` using `hσ.2.2.1`. Establish `hadm` using `BridgeCPX.HCAdmDSG_of_mult BridgeDS3.HC_finite_K_multiplicity_gapped n ε lam H σ hlam hσ h hgap hth`. Take `⟨Cf, hCf⟩` from `BridgeCPX.kfin_decay_UJ hU hσ.2.2.2.1 hadm hw00 hA0 hC00 hdec hv hw [] [] (by simp) (by simp)`. Establish `hbd : ∀ g : Formalism.REAL.UJ ε, ‖coefOn σ v w g‖ ≤ Cf * Real.sqrt (Formalism.REAL.hs (umat g)) ^ (-A)` using `fun g => hCf (umat g) g.2`.

Establish `hA1 : (n : ℝ) * q0 + 2 ≤ A`. Establish `hs2 : Real.sqrt (2 * (q0 : ℝ)) ≤ 2 * n`. Rewrite using `[Real.sqrt_le_left (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hA, le_div_iff₀ (by positivity)]`.

Establish `e1 : ((n : ℝ) * q0 + 2) * (8 * Real.sqrt (2 * (q0 : ℝ))) ≤ ((n : ℝ) * n + 2) * (8 * (2 * n))`. Apply `mul_le_mul (by nlinarith) (by linarith) (by positivity) (by positivity)` to reduce the goal to its premises. Establish `e2 : ((n : ℝ) * n + 2) * (8 * (2 * n)) ≤ 200 * (n : ℝ) ^ 3` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnq : 0 ≤ (n : ℝ) * q0` using `by positivity`.

Establish `hA1' : 1 ≤ A` using `by linarith`. Use `set F : Formalism.REAL.UJ ε → ℂ := fun g => (frob (umat g) : ℂ) * coefOn σ v w g with hF`. Establish `hFc : Continuous F`. Establish `h1 : Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) v` using `(hU.2.2 v).comp_continuous (Formalism.REAL.continuous_coeMatrix ε) (fun g => g.2)`. Establish `h2 : Continuous fun g : Formalism.REAL.UJ ε => coefOn σ v w g` using `continuous_const.inner h1`.

Conclude with `(Complex.continuous_ofReal.comp (continuous_frob.comp (Formalism.REAL.continuous_coeMatrix ε))).mul h2`. Establish `hs1 : ∀ g : Formalism.REAL.UJ ε, 1 ≤ Formalism.REAL.hs (umat g)` using `fun g => one_le_hilbert_schmidt_of_mem ε _ g.2 ⟨0, by omega⟩`. Establish `hFb : ∀ g : Formalism.REAL.UJ ε, ‖F g‖ ^ 2 ≤ Cf ^ 2 * Formalism.REAL.hs (umat g) ^ (1 - A)`. Introduce `g`. Use `set B : ℝ := Formalism.REAL.hs (umat g) with hB`.

Establish `hB1 : 1 ≤ B` using `hs1 g`. Establish `hB0 : 0 < B` using `by linarith`. Establish `hsB : 0 < Real.sqrt B` using `Real.sqrt_pos.2 hB0`. Establish `hc` using `hbd g`. Rewrite `hc` using `[← hB]`.

Establish `hc0 : 0 ≤ ‖coefOn σ v w g‖` using `norm_nonneg _`. Establish `hCf0 : 0 ≤ Cf * Real.sqrt B ^ (-A)` using `le_trans hc0 hc`. Establish `hnF : ‖F g‖ = Real.sqrt B * ‖coefOn σ v w g‖`. Simplify using `only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, frob_eq_sqrt_hs, ← hB, abs_of_nonneg (Real.sqrt_nonneg _)]`. Rewrite using `[hnF, mul_pow, Real.sq_sqrt hB0.le]`.

Establish `e1 : ‖coefOn σ v w g‖ ^ 2 ≤ (Cf * Real.sqrt B ^ (-A)) ^ 2` using `pow_le_pow_left₀ hc0 hc 2`. Establish `e2 : (Cf * Real.sqrt B ^ (-A)) ^ 2 = Cf ^ 2 * B ^ (-A)`. Rewrite using `[mul_pow, ← Real.rpow_natCast (Real.sqrt B ^ (-A)), ← Real.rpow_mul hsB.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hB0.le]`. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `e3 : B * (Cf ^ 2 * B ^ (-A)) = Cf ^ 2 * B ^ (1 - A)`. Rewrite using `[sub_eq_add_neg, Real.rpow_add hB0, Real.rpow_one]`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← e2]`. Conclude with `mul_le_mul_of_nonneg_left e1 hB0.le`. Use `_ = Cf ^ 2 * B ^ (1 - A) := e3`. Use `set M : ℝ := max (Cf ^ 2) 1 with hM`. Establish `hM1 : 1 ≤ M` using `le_max_right _ _`.

Establish `hM0 : 0 < M` using `by linarith`. Establish `hCM : Cf ^ 2 ≤ M` using `le_max_left _ _`. Use `set f : Formalism.REAL.UJ ε → ℂ := fun g => ((‖F g‖ ^ 2 / M : ℝ) : ℂ) with hf`. Establish `hfc : Continuous f` using `Complex.continuous_ofReal.comp ((hFc.norm.pow 2).div_const M)`. Establish `hfle : ∀ g, ‖F g‖ ^ 2 / M ≤ Formalism.REAL.hs (umat g) ^ (1 - A)`.

Introduce `g`. Rewrite using `[div_le_iff₀ hM0]`. Establish `hp : 0 ≤ Formalism.REAL.hs (umat g) ^ (1 - A)` using `Real.rpow_nonneg (by linarith [hs1 g]) _`. Combine the equalities or inequalities in the displayed calculation. Establish `hfn : ∀ g, ‖f g‖ = ‖F g‖ ^ 2 / M`.

Introduce `g`. Simplify using `only [hf, Complex.norm_real, Real.norm_eq_abs]`. Conclude with `abs_of_nonneg (by positivity)`. Establish `hone : ∀ g, ‖f g‖ ≤ 1`. Introduce `g`.

Rewrite using `[hfn]`. Conclude with `(hfle g).trans (Real.rpow_le_one_of_one_le_of_nonpos (hs1 g) (by linarith))`. Establish `hint : Integrable f (Formalism.REAL.muG ε)`. Use `L1.integrable_of_decay ε s f hfc hone (2 * (A - 1)) ?_ (fun g hg => ?_)` and prove the remaining obligations. Rewrite using `[hcs]`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hG0 : 0 < Formalism.REAL.hsG g` using `lt_trans (by positivity) hg`. Establish `hn0 : (0 : ℝ) < n` using `by linarith`. Establish `hx0 : 0 < Formalism.REAL.hsG g / n` using `div_pos hG0 hn0`.

Use `⟨Real.log (Formalism.REAL.hsG g / n) / 2, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[show 2 * (Real.log (Formalism.REAL.hsG g / n) / 2) = Real.log (Formalism.REAL.hsG g / n) by ring, Real.exp_log hx0]`. Rewrite using `[mul_div_cancel₀ _ hn0.ne']`. Establish `hgeq : Formalism.REAL.hsG g = Formalism.REAL.hs (umat g)` using `rfl`. Rewrite using `[hfn]`.

Use `(hfle g).trans ?_` and prove the remaining obligations. Use `set t : ℝ := Real.log (Formalism.REAL.hsG g / n) / 2 with ht`. Establish `e2 : (n : ℝ) ^ (1 - A) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hnR (by linarith)`. Establish `e3 : (Formalism.REAL.hsG g / n) ^ (1 - A) = Real.exp (-(2 * (A - 1) * t))`. Rewrite using `[Real.rpow_def_of_pos hx0, ht]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `e0 : Formalism.REAL.hs (umat g) = n * (Formalism.REAL.hsG g / n)`. Rewrite using `[← hgeq]`. Clear the denominators using the available nonvanishing facts.

Combine the equalities or inequalities in the displayed calculation. Establish `hsq : Integrable (fun g => ‖F g‖ ^ 2) (Formalism.REAL.muG ε)`. Establish `h1` using `(hint.re).const_mul M`. Use `h1.congr (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Establish `e : (f g).re = ‖F g‖ ^ 2 / M` using `by rw [hf]; exact Complex.ofReal_re _`.

Use `show M * (f g).re = ‖F g‖ ^ 2`. Rewrite using `[e]`. Clear the denominators using the available nonvanishing facts. Conclude with `(memLp_two_iff_integrable_sq_norm hFc.aestronglyMeasurable).2 hsq`.
-/
theorem memLp_frob_coef (D0 : Formalism.BasicNotions.D7) (hDec : DiscreteSeriesDecayBound D0) (hlam : IsHCParam lam)
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsDS ε lam σ) {h : ℝ} (hgap : GapAtLeast ε lam h)
    (hh : 200 * (n : ℝ) ^ 3 ≤ h) (hpos : 1 ≤ min (pOf ε) (qOf ε)) {v w : H} (hv : IsKFin ε σ v)
    (hw : IsKFin ε σ w) :
    MemLp (fun g : Formalism.REAL.UJ ε => (frob (umat g) : ℂ) * coefOn σ v w g) 2 (Formalism.REAL.muG ε) := by
  obtain ⟨s, hcs⟩ := L1.exists_sign ε
  set q0 : ℕ := min (pOf ε) (qOf ε) with hq0
  have hqn : q0 ≤ n := hcs ▸ L1.card_SgIx_le ε s
  have hn1 : 1 ≤ n := le_trans hpos hqn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hqR : (1 : ℝ) ≤ q0 := by exact_mod_cast hpos
  have hqnR : (q0 : ℝ) ≤ n := by exact_mod_cast hqn
  have hn3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hnR
  have hh0 : 0 ≤ h := le_trans (by positivity) hh

  have hth : Formalism.MainNotions.GapDS.thrDS ε < h := by
    have := Formalism.MainNotions.GapDS.thrDS_le ε
    linarith
  have h120 : 120 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h := by
    rw [← hq0]
    have e1 : (q0 : ℝ) ^ ((3 : ℝ) / 2) ≤ (n : ℝ) ^ (2 : ℕ) := by
      calc (q0 : ℝ) ^ ((3 : ℝ) / 2) ≤ (q0 : ℝ) ^ ((2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hqR (by norm_num)
        _ = (q0 : ℝ) ^ (2 : ℕ) := by rw [← Real.rpow_natCast]; norm_num
        _ ≤ (n : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ (by linarith) hqnR 2
    calc 120 * (n : ℝ) * (q0 : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (n : ℝ) * (n : ℝ) ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_left e1 (by positivity)
      _ = 120 * (n : ℝ) ^ 3 := by ring
      _ ≤ h := by linarith

  have := lowK_fd hlam hσ hgap hth
  have hE : IsOrthProjOnto (lowKSub ε lam σ).starProjection (lowKSub ε lam σ) :=
    ⟨(lowKSub ε lam σ).isIdempotentElem_starProjection,
      fun x y => Submodule.inner_starProjection_left_eq_right _ x y, Submodule.range_starProjection _⟩
  obtain ⟨w0, hw0⟩ := exists_highest_weight_unit ε lam σ hσ
  have hlow : IsLowUnit ε lam σ w0 := ⟨hw0.1, hw0.2.1⟩
  have hw00 : w0 ≠ 0 := by
    intro h0
    have := hw0.1
    rw [h0, norm_zero] at this
    norm_num at this

  set A : ℝ := h / (8 * Real.sqrt (2 * (q0 : ℝ))) with hA
  set C0 : ℝ := Real.sqrt n ^ A * Real.exp (A / Real.sqrt (2 * (q0 : ℝ))) with hC0
  have hsq0 : 0 < Real.sqrt (2 * (q0 : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hC00 : 0 ≤ C0 := by rw [hC0]; positivity
  have hdec : ∀ g : Formalism.REAL.UJ ε, ‖⟪w0, σ (umat g) w0⟫_ℂ‖ ≤ C0 * Real.sqrt (Formalism.REAL.hs (umat g)) ^ (-A) := by
    intro g
    have := poly_decay_of_decay_statement D0 hDec n ε lam hlam H σ hσ _ hE h hgap h120 hpos w0 hlow (umat g) g.2
    rw [← hq0] at this
    exact this

  have hU := hσ.2.2.1
  have hadm := BridgeCPX.HCAdmDSG_of_mult BridgeDS3.HC_finite_K_multiplicity_gapped n ε lam H σ hlam hσ h hgap hth
  obtain ⟨Cf, hCf⟩ := BridgeCPX.kfin_decay_UJ hU hσ.2.2.2.1 hadm hw00 hA0 hC00 hdec hv hw [] []
    (by simp) (by simp)
  have hbd : ∀ g : Formalism.REAL.UJ ε, ‖coefOn σ v w g‖ ≤ Cf * Real.sqrt (Formalism.REAL.hs (umat g)) ^ (-A) := fun g =>
    hCf (umat g) g.2

  have hA1 : (n : ℝ) * q0 + 2 ≤ A := by
    have hs2 : Real.sqrt (2 * (q0 : ℝ)) ≤ 2 * n := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    rw [hA, le_div_iff₀ (by positivity)]
    have e1 : ((n : ℝ) * q0 + 2) * (8 * Real.sqrt (2 * (q0 : ℝ))) ≤ ((n : ℝ) * n + 2) * (8 * (2 * n)) := by
      apply mul_le_mul (by nlinarith) (by linarith) (by positivity) (by positivity)
    have e2 : ((n : ℝ) * n + 2) * (8 * (2 * n)) ≤ 200 * (n : ℝ) ^ 3 := by nlinarith
    linarith
  have hnq : 0 ≤ (n : ℝ) * q0 := by positivity
  have hA1' : 1 ≤ A := by linarith

  set F : Formalism.REAL.UJ ε → ℂ := fun g => (frob (umat g) : ℂ) * coefOn σ v w g with hF
  have hFc : Continuous F := by
    have h1 : Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) v :=
      (hU.2.2 v).comp_continuous (Formalism.REAL.continuous_coeMatrix ε) (fun g => g.2)
    have h2 : Continuous fun g : Formalism.REAL.UJ ε => coefOn σ v w g := continuous_const.inner h1
    exact (Complex.continuous_ofReal.comp (continuous_frob.comp (Formalism.REAL.continuous_coeMatrix ε))).mul h2
  have hs1 : ∀ g : Formalism.REAL.UJ ε, 1 ≤ Formalism.REAL.hs (umat g) := fun g => one_le_hilbert_schmidt_of_mem ε _ g.2 ⟨0, by omega⟩

  have hFb : ∀ g : Formalism.REAL.UJ ε, ‖F g‖ ^ 2 ≤ Cf ^ 2 * Formalism.REAL.hs (umat g) ^ (1 - A) := by
    intro g
    set B : ℝ := Formalism.REAL.hs (umat g) with hB
    have hB1 : 1 ≤ B := hs1 g
    have hB0 : 0 < B := by linarith
    have hsB : 0 < Real.sqrt B := Real.sqrt_pos.2 hB0
    have hc := hbd g
    rw [← hB] at hc
    have hc0 : 0 ≤ ‖coefOn σ v w g‖ := norm_nonneg _
    have hCf0 : 0 ≤ Cf * Real.sqrt B ^ (-A) := le_trans hc0 hc
    have hnF : ‖F g‖ = Real.sqrt B * ‖coefOn σ v w g‖ := by
      simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, frob_eq_sqrt_hs, ← hB,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hnF, mul_pow, Real.sq_sqrt hB0.le]
    have e1 : ‖coefOn σ v w g‖ ^ 2 ≤ (Cf * Real.sqrt B ^ (-A)) ^ 2 := pow_le_pow_left₀ hc0 hc 2
    have e2 : (Cf * Real.sqrt B ^ (-A)) ^ 2 = Cf ^ 2 * B ^ (-A) := by
      rw [mul_pow, ← Real.rpow_natCast (Real.sqrt B ^ (-A)), ← Real.rpow_mul hsB.le, Real.sqrt_eq_rpow,
        ← Real.rpow_mul hB0.le]
      congr 2
      push_cast
      ring
    have e3 : B * (Cf ^ 2 * B ^ (-A)) = Cf ^ 2 * B ^ (1 - A) := by
      rw [sub_eq_add_neg, Real.rpow_add hB0, Real.rpow_one]
      ring
    calc B * ‖coefOn σ v w g‖ ^ 2 ≤ B * (Cf ^ 2 * B ^ (-A)) := by
          rw [← e2]; exact mul_le_mul_of_nonneg_left e1 hB0.le
      _ = Cf ^ 2 * B ^ (1 - A) := e3

  set M : ℝ := max (Cf ^ 2) 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM0 : 0 < M := by linarith
  have hCM : Cf ^ 2 ≤ M := le_max_left _ _
  set f : Formalism.REAL.UJ ε → ℂ := fun g => ((‖F g‖ ^ 2 / M : ℝ) : ℂ) with hf
  have hfc : Continuous f := Complex.continuous_ofReal.comp ((hFc.norm.pow 2).div_const M)
  have hfle : ∀ g, ‖F g‖ ^ 2 / M ≤ Formalism.REAL.hs (umat g) ^ (1 - A) := by
    intro g
    rw [div_le_iff₀ hM0]
    have hp : 0 ≤ Formalism.REAL.hs (umat g) ^ (1 - A) := Real.rpow_nonneg (by linarith [hs1 g]) _
    calc ‖F g‖ ^ 2 ≤ Cf ^ 2 * Formalism.REAL.hs (umat g) ^ (1 - A) := hFb g
      _ ≤ M * Formalism.REAL.hs (umat g) ^ (1 - A) := mul_le_mul_of_nonneg_right hCM hp
      _ = Formalism.REAL.hs (umat g) ^ (1 - A) * M := by ring
  have hfn : ∀ g, ‖f g‖ = ‖F g‖ ^ 2 / M := by
    intro g
    simp only [hf, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  have hone : ∀ g, ‖f g‖ ≤ 1 := by
    intro g
    rw [hfn]
    exact (hfle g).trans (Real.rpow_le_one_of_one_le_of_nonpos (hs1 g) (by linarith))
  have hint : Integrable f (Formalism.REAL.muG ε) := by
    refine L1.integrable_of_decay ε s f hfc hone (2 * (A - 1)) ?_ (fun g hg => ?_)
    · rw [hcs]
      push_cast
      linarith
    · have hG0 : 0 < Formalism.REAL.hsG g := lt_trans (by positivity) hg
      have hn0 : (0 : ℝ) < n := by linarith
      have hx0 : 0 < Formalism.REAL.hsG g / n := div_pos hG0 hn0
      refine ⟨Real.log (Formalism.REAL.hsG g / n) / 2, ?_, ?_⟩
      · rw [show 2 * (Real.log (Formalism.REAL.hsG g / n) / 2) = Real.log (Formalism.REAL.hsG g / n) by ring,
          Real.exp_log hx0]
        rw [mul_div_cancel₀ _ hn0.ne']
      · have hgeq : Formalism.REAL.hsG g = Formalism.REAL.hs (umat g) := rfl
        rw [hfn]
        refine (hfle g).trans ?_
        set t : ℝ := Real.log (Formalism.REAL.hsG g / n) / 2 with ht
        have e2 : (n : ℝ) ^ (1 - A) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hnR (by linarith)
        have e3 : (Formalism.REAL.hsG g / n) ^ (1 - A) = Real.exp (-(2 * (A - 1) * t)) := by
          rw [Real.rpow_def_of_pos hx0, ht]
          congr 1
          ring
        have e0 : Formalism.REAL.hs (umat g) = n * (Formalism.REAL.hsG g / n) := by
          rw [← hgeq]; field_simp
        calc Formalism.REAL.hs (umat g) ^ (1 - A) = (n * (Formalism.REAL.hsG g / n)) ^ (1 - A) := by rw [e0]
          _ = (n : ℝ) ^ (1 - A) * (Formalism.REAL.hsG g / n) ^ (1 - A) := Real.mul_rpow hn0.le hx0.le
          _ ≤ 1 * (Formalism.REAL.hsG g / n) ^ (1 - A) :=
              mul_le_mul_of_nonneg_right e2 (Real.rpow_nonneg hx0.le _)
          _ = Real.exp (-(2 * (A - 1) * t)) := by rw [one_mul, e3]
  have hsq : Integrable (fun g => ‖F g‖ ^ 2) (Formalism.REAL.muG ε) := by
    have h1 := (hint.re).const_mul M
    refine h1.congr (Filter.Eventually.of_forall fun g => ?_)
    have e : (f g).re = ‖F g‖ ^ 2 / M := by rw [hf]; exact Complex.ofReal_re _
    show M * (f g).re = ‖F g‖ ^ 2
    rw [e]
    field_simp
  exact (memLp_two_iff_integrable_sq_norm hFc.aestronglyMeasurable).2 hsq

end Rec

end Formalism.MainNotions.S.Pv.DegI

end
