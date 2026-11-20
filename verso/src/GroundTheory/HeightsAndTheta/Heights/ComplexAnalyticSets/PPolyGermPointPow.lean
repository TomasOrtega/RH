import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZariskiObjects
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPolyGermPointPow
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GradientAtPoint
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvalSmulOfIsHomogeneous
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter Asymptotics

noncomputable section

namespace PolyGermPointPow

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro d hd`. Conclude with `absurd hd (Nat.not_lt_zero _)`. Consider the case `succ k ih`. Establish `hn : (fun t : ℂ => ‖t‖) =O[𝓝 0] fun _ => (1 : ℝ)` using `(continuous_norm.tendsto (0 : ℂ)).isBigO_one ℝ`.

Establish `hk` using `ih (h.trans (by simpa [pow_succ] using (isBigO_refl (fun t : ℂ => ‖t‖ ^ k) _).mul hn))`. Take `⟨Q, hQ⟩` from `Polynomial.X_pow_dvd_iff.mpr hk`. Introduce `d hd`. Break down `Nat.lt_succ_iff_lt_or_eq.mp hd with hd | hd` into its components or cases. Conclude with `hk d hd`.

Rewrite using `[hd, hQ, Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, Polynomial.coeff_zero_eq_eval_zero]`. Take `⟨c, hc⟩` from `h.bound`. Establish `h1 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖Q.eval t‖ ≤ c * ‖t‖` using `by filter_upwards [nhdsWithin_le_nhds hc, self_mem_nhdsWithin] with t ht ht0`. Rewrite `ht` using `[hQ, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, norm_mul, norm_pow, norm_pow, norm_norm, pow_succ]`. Establish `hp : 0 < ‖t‖ ^ k` using `pow_pos (norm_pos_iff.mpr ht0) k`.

Conclude with `le_of_mul_le_mul_left (by linarith) hp`. Establish `h2 : Tendsto (fun t => ‖Q.eval t‖) (𝓝[≠] 0) (𝓝 ‖Q.eval 0‖)` using `((Q.continuous.tendsto 0).norm).mono_left nhdsWithin_le_nhds`. Establish `h3 : Tendsto (fun t : ℂ => c * ‖t‖) (𝓝[≠] 0) (𝓝 0)`. Simplify using `using ((continuous_norm.tendsto (0 : ℂ)).const_mul c).mono_left nhdsWithin_le_nhds`. Conclude with `norm_le_zero_iff.mp (le_of_tendsto_of_tendsto h2 h3 h1)`.
-/
theorem coeff_eq_zero_of_isBigO {P : Polynomial ℂ} {k : ℕ}
    (h : (fun t => P.eval t) =O[𝓝 0] fun t : ℂ => ‖t‖ ^ k) : ∀ d < k, P.coeff d = 0 := by
  induction k with
  | zero => intro d hd; exact absurd hd (Nat.not_lt_zero _)
  | succ k ih =>
    have hn : (fun t : ℂ => ‖t‖) =O[𝓝 0] fun _ => (1 : ℝ) := (continuous_norm.tendsto (0 : ℂ)).isBigO_one ℝ
    have hk := ih (h.trans (by simpa [pow_succ] using (isBigO_refl (fun t : ℂ => ‖t‖ ^ k) _).mul hn))
    obtain ⟨Q, hQ⟩ := Polynomial.X_pow_dvd_iff.mpr hk
    intro d hd
    rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd | hd
    · exact hk d hd
    rw [hd, hQ, Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, Polynomial.coeff_zero_eq_eval_zero]
    obtain ⟨c, hc⟩ := h.bound
    have h1 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖Q.eval t‖ ≤ c * ‖t‖ := by
      filter_upwards [nhdsWithin_le_nhds hc, self_mem_nhdsWithin] with t ht ht0
      rw [hQ, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, norm_mul, norm_pow, norm_pow,
        norm_norm, pow_succ] at ht
      have hp : 0 < ‖t‖ ^ k := pow_pos (norm_pos_iff.mpr ht0) k
      exact le_of_mul_le_mul_left (by linarith) hp
    have h2 : Tendsto (fun t => ‖Q.eval t‖) (𝓝[≠] 0) (𝓝 ‖Q.eval 0‖) :=
      ((Q.continuous.tendsto 0).norm).mono_left nhdsWithin_le_nhds
    have h3 : Tendsto (fun t : ℂ => c * ‖t‖) (𝓝[≠] 0) (𝓝 0) := by
      simpa using ((continuous_norm.tendsto (0 : ℂ)).const_mul c).mono_left nhdsWithin_le_nhds
    exact norm_le_zero_iff.mp (le_of_tendsto_of_tendsto h2 h3 h1)

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.HomogeneousEvalSmul.eval_smul_of_isHomogeneous hh t v`.
-/
theorem eval_smul_of_isHomogeneous {σ : Type} [Fintype σ] {h : MvPolynomial σ ℂ} {d : ℕ}
    (hh : h.IsHomogeneous d) (t : ℂ) (v : σ → ℂ) : eval (t • v) h = t ^ d * eval v h :=
  _root_.UpperTheory.Reformulated.B.HomogeneousEvalSmul.eval_smul_of_isHomogeneous hh t v

variable {σ : Type} [Fintype σ] (w : σ → ℂ)

def bigOIdeal (k : ℕ) : Ideal (holGerms w) where
  carrier := {φ | ∃ f : (σ → ℂ) → ℂ, (f : Germ (𝓝 w) ℂ) = (φ : Germ (𝓝 w) ℂ) ∧
    f =O[𝓝 w] fun z => ‖z - w‖ ^ k}
  add_mem' := by
    rintro φ ψ ⟨f, hf, hfO⟩ ⟨g, hg, hgO⟩
    exact ⟨f + g, by rw [Subring.coe_add, ← hf, ← hg]; rfl, hfO.add hgO⟩
  zero_mem' := ⟨0, rfl, isBigO_zero _ _⟩
  smul_mem' := by
    rintro c φ ⟨f, hf, hfO⟩
    obtain ⟨a, ha, hac⟩ := c.2
    refine ⟨a * f, ?_, ?_⟩
    · rw [smul_eq_mul, Subring.coe_mul, ← hf, ← hac]; rfl
    · show (fun z => a z * f z) =O[𝓝 w] fun z => ‖z - w‖ ^ k
      simpa using (ha.continuousAt.tendsto.isBigO_one ℝ).mul hfO

/- English proof (translation)
Use `eq_top_iff.mpr fun φ _ => ?_` and prove the remaining obligations. Take `⟨f, hf, hfφ⟩` from `φ.2`. Conclude with `⟨f, hfφ, by simpa using hf.continuousAt.tendsto.isBigO_one ℝ⟩`.
-/
theorem bigOIdeal_zero : bigOIdeal w 0 = ⊤ := by
  refine eq_top_iff.mpr fun φ _ => ?_
  obtain ⟨f, hf, hfφ⟩ := φ.2
  exact ⟨f, hfφ, by simpa using hf.continuousAt.tendsto.isBigO_one ℝ⟩

/- English proof (translation)
Introduce `φ hφ`. Take `⟨f, hf, hfφ⟩` from `φ.2`. Establish `h0 : f w = 0`. Establish `: (Germ.valueRingHom (x` using `w)) (f : Germ (𝓝 w) ℂ) = 0 := by rw [hfφ]; exact hφ`. Conclude with `this`.

Use `⟨f, hfφ, ?_⟩` and prove the remaining obligations. Use `hf.differentiableAt.hasFDerivAt.isBigO_sub` as an intermediate fact. Simplify using `only [h0, sub_zero] at this`. Simplify using `using this.norm_right`.
-/
theorem pointIdeal_le_bigOIdeal_one : holGermPointIdeal w ≤ bigOIdeal w 1 := by
  intro φ hφ
  obtain ⟨f, hf, hfφ⟩ := φ.2
  have h0 : f w = 0 := by
    have : (Germ.valueRingHom (x := w)) (f : Germ (𝓝 w) ℂ) = 0 := by rw [hfφ]; exact hφ
    exact this
  refine ⟨f, hfφ, ?_⟩
  have := hf.differentiableAt.hasFDerivAt.isBigO_sub
  simp only [h0, sub_zero] at this
  simpa using this.norm_right

/- English proof (translation)
Rewrite using `[Ideal.mul_le]`. Introduce and unpack `φ ⟨f, hf, hfO⟩ ψ ⟨g, hg, hgO⟩`. Use `⟨f * g, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Subring.coe_mul, ← hf, ← hg]`. Both sides reduce to the same expression.

Use `show (fun z => f z * g z) =O[𝓝 w] fun z => ‖z - w‖ ^ (a + b)`. Simplify `hfO.mul hgO` using `[pow_add]`.
-/
theorem bigOIdeal_mul_le (a b : ℕ) : bigOIdeal w a * bigOIdeal w b ≤ bigOIdeal w (a + b) := by
  rw [Ideal.mul_le]
  rintro φ ⟨f, hf, hfO⟩ ψ ⟨g, hg, hgO⟩
  refine ⟨f * g, ?_, ?_⟩
  · rw [Subring.coe_mul, ← hf, ← hg]; rfl
  · show (fun z => f z * g z) =O[𝓝 w] fun z => ‖z - w‖ ^ (a + b)
    simpa [pow_add] using hfO.mul hgO

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero, Ideal.one_eq_top, bigOIdeal_zero]`. Consider the case `succ k ih`. Rewrite using `[pow_succ]`. Conclude with `(Ideal.mul_mono ih (pointIdeal_le_bigOIdeal_one w)).trans (bigOIdeal_mul_le w k 1)`.
-/
theorem pointIdeal_pow_le (k : ℕ) : holGermPointIdeal w ^ k ≤ bigOIdeal w k := by
  induction k with
  | zero => rw [pow_zero, Ideal.one_eq_top, bigOIdeal_zero]
  | succ k ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih (pointIdeal_le_bigOIdeal_one w)).trans (bigOIdeal_mul_le w k 1)

/- English proof (translation)
Use `set q' := bind₁ (fun i => X i + C (w i)) q with hq'def`. Establish `hev : ∀ y, eval y q' = eval (y + w) q`. Introduce `y`. Rewrite using `[hq'def, show (eval y : MvPolynomial σ ℂ →+* ℂ) = eval₂Hom (RingHom.id ℂ) y from rfl, eval₂Hom_bind₁]`. Establish `hfun : (fun i => eval₂Hom (RingHom.id ℂ) y (X i + C (w i))) = y + w`.

Use extensionality with `i`. Simplify using `only [map_add, eval₂Hom_X', eval₂Hom_C, RingHom.id_apply, Pi.add_apply]`. Rewrite using `[hfun]`. Both sides reduce to the same expression. Establish `hcomp : ∀ d < k, homogeneousComponent d q' = 0`.

Introduce `d hd`. Distinguish the cases in `hdT : d ∈ Finset.range (q'.totalDegree + 1)`. Use `swap`. Conclude with `homogeneousComponent_eq_zero _ _ (by simpa [Nat.lt_succ_iff] using hdT)`. Use `MvPolynomial.funext fun v => ?_` and prove the remaining obligations.

Set `P : Polynomial ℂ` to `∑ e ∈ Finset.range (q'.totalDegree + 1), Polynomial.monomial e (eval v (homogeneousComponent e q'))`. Establish `hP : ∀ t, P.eval t = eval (t • v + w) q`. Introduce `t`. Rewrite using `[← hev]`. Use `conv_rhs => rw [← sum_homogeneousComponent q']`.

Simplify using `only [P, Polynomial.eval_finsetSum, Polynomial.eval_monomial, map_sum]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous e q'), mul_comm]`. Establish `hT : Tendsto (fun t : ℂ => t • v + w) (𝓝 0) (𝓝 w)`. Simplify using `using ((continuous_id.smul continuous_const).add continuous_const).tendsto (0 : ℂ) (f := fun t : ℂ => t • v + w)`.

Establish `hPO : (fun t => P.eval t) =O[𝓝 0] fun t : ℂ => ‖t‖ ^ k`. Repeatedly rewrite using `[hP]`. Use `(hq.comp_tendsto hT).trans (IsBigO.of_bound (‖v‖ ^ k) (Eventually.of_forall fun t => ?_))` and prove the remaining obligations. Simplify using `[norm_smul, mul_pow, mul_comm]`. Establish `hc` using `coeff_eq_zero_of_isBigO hPO d hd`.

Simplify using `only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq', if_pos hdT] at hc`. Simplify using `using hc`. Establish `hmem : q' ∈ idealOfVars σ ℂ ^ k`. Use `(mem_pow_idealOfVars_iff' k q').mpr fun x hx => ?_` and prove the remaining obligations. Use `congrArg (coeff x) (hcomp _ hx)` as an intermediate fact.

Rewrite `this` using `[coeff_homogeneousComponent, if_pos rfl, coeff_zero]`. Then use the resulting hypothesis. Establish `hback : bind₁ (fun i => X i - C (w i)) q' = q`. Rewrite using `[hq'def, bind₁_bind₁]`. Simplify using `[bind₁_X_right]`. Use `Ideal.mem_map_of_mem (bind₁ (fun i => (X i - C (w i) : MvPolynomial σ ℂ))) hmem` as an intermediate fact.

Rewrite `this` using `[Ideal.map_pow, idealOfVars, Ideal.map_span, ← Set.range_comp, hback]`. Rewrite using `[GroundTheory.Heights₂.Heights.GradientAtPoint.ker_eval_eq_span]`. Simplify `this` using `[Function.comp_def, bind₁_X_right]`.
-/
theorem mem_pow_ker_of_isBigO {k : ℕ} {q : MvPolynomial σ ℂ}
    (hq : (fun z => eval z q) =O[𝓝 w] fun z => ‖z - w‖ ^ k) :
    q ∈ RingHom.ker (MvPolynomial.eval w) ^ k := by
  set q' := bind₁ (fun i => X i + C (w i)) q with hq'def
  have hev : ∀ y, eval y q' = eval (y + w) q := by
    intro y
    rw [hq'def, show (eval y : MvPolynomial σ ℂ →+* ℂ) = eval₂Hom (RingHom.id ℂ) y from rfl, eval₂Hom_bind₁]
    have hfun : (fun i => eval₂Hom (RingHom.id ℂ) y (X i + C (w i))) = y + w := by
      ext i
      simp only [map_add, eval₂Hom_X', eval₂Hom_C, RingHom.id_apply, Pi.add_apply]
    rw [hfun]
    rfl

  have hcomp : ∀ d < k, homogeneousComponent d q' = 0 := by
    intro d hd
    by_cases hdT : d ∈ Finset.range (q'.totalDegree + 1)
    swap
    · exact homogeneousComponent_eq_zero _ _ (by simpa [Nat.lt_succ_iff] using hdT)
    refine MvPolynomial.funext fun v => ?_
    let P : Polynomial ℂ := ∑ e ∈ Finset.range (q'.totalDegree + 1),
      Polynomial.monomial e (eval v (homogeneousComponent e q'))
    have hP : ∀ t, P.eval t = eval (t • v + w) q := by
      intro t
      rw [← hev]
      conv_rhs => rw [← sum_homogeneousComponent q']
      simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_monomial, map_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous e q'), mul_comm]
    have hT : Tendsto (fun t : ℂ => t • v + w) (𝓝 0) (𝓝 w) := by
      simpa using ((continuous_id.smul continuous_const).add continuous_const).tendsto (0 : ℂ)
        (f := fun t : ℂ => t • v + w)
    have hPO : (fun t => P.eval t) =O[𝓝 0] fun t : ℂ => ‖t‖ ^ k := by
      simp_rw [hP]
      refine (hq.comp_tendsto hT).trans (IsBigO.of_bound (‖v‖ ^ k) (Eventually.of_forall fun t => ?_))
      simp [norm_smul, mul_pow, mul_comm]
    have hc := coeff_eq_zero_of_isBigO hPO d hd
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq', if_pos hdT] at hc
    simpa using hc
  have hmem : q' ∈ idealOfVars σ ℂ ^ k := by
    refine (mem_pow_idealOfVars_iff' k q').mpr fun x hx => ?_
    have := congrArg (coeff x) (hcomp _ hx)
    rwa [coeff_homogeneousComponent, if_pos rfl, coeff_zero] at this
  have hback : bind₁ (fun i => X i - C (w i)) q' = q := by
    rw [hq'def, bind₁_bind₁]
    simp [bind₁_X_right]
  have := Ideal.mem_map_of_mem (bind₁ (fun i => (X i - C (w i) : MvPolynomial σ ℂ))) hmem
  rw [Ideal.map_pow, idealOfVars, Ideal.map_span, ← Set.range_comp, hback] at this
  rw [GroundTheory.Heights₂.Heights.GradientAtPoint.ker_eval_eq_span]
  simpa [Function.comp_def, bind₁_X_right] using this

end PolyGermPointPow

/- English proof (translation)
Introduce `σ _ w k q hq`. Take `⟨f, hf, hfO⟩` from `PolyGermPointPow.pointIdeal_pow_le w k hq`. Establish `hf' : (f : Germ (𝓝 w) ℂ) = ((fun z => eval z q : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)` using `hf`. Conclude with `PolyGermPointPow.mem_pow_ker_of_isBigO w (hfO.congr' (Germ.coe_eq.mp hf') EventuallyEq.rfl)`.
-/
theorem PolyGermPointPow.proof : PolyGermPointPow.Statement := by
  intro σ _ w k q hq
  obtain ⟨f, hf, hfO⟩ := PolyGermPointPow.pointIdeal_pow_le w k hq
  have hf' : (f : Germ (𝓝 w) ℂ) = ((fun z => eval z q : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) := hf
  exact PolyGermPointPow.mem_pow_ker_of_isBigO w (hfO.congr' (Germ.coe_eq.mp hf') EventuallyEq.rfl)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
