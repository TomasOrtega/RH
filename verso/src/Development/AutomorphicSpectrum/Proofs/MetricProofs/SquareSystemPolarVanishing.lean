import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AlgebraicSquareBaseIntersectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PtsIntegralLogNormRatEqBaseStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationPotentialDegreeCompatibilityStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithmeticIntersectionMultilinearPolarStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralMultilinearExpansion
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSystemRegularityProperties
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsC2AtOfIsPotential
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.Intersections.PZeroSetNull
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsHomogeneousGrL

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.SqAt

section Polar

variable {σ : Type} [Fintype σ]

/- English proof (translation)
Unfold `polar`. Rewrite using `[Finset.sum_div]`. Conclude with `Finset.sum_congr rfl fun w _ => by ring`.
-/
theorem polar_div (n : ℕ) (a : (Fin n → σ) → ℝ) (c : Fin n → σ → ℝ) (b : ℝ) :
    polar n (fun w => a w / b) c = polar n a c / b := by
  unfold polar
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun w _ => by ring

/- English proof (translation)
Unfold `polar`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Simplify using `only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem polar_cons_sub {e : ℕ} (f : (Fin (e + 1) → σ) → ℝ) (x y : σ → ℝ) (W : Fin e → σ → ℝ) :
    polar (e + 1) f (Fin.cons (α := fun _ => σ → ℝ) (x - y) W) =
      polar (e + 1) f (Fin.cons (α := fun _ => σ → ℝ) x W) -
        polar (e + 1) f (Fin.cons (α := fun _ => σ → ℝ) y W) := by
  unfold polar
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.sub_apply]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [word]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem word_map {V W : Type} (f : V → W) (D k i : ℕ) (x y a : V) :
    word D k i (f x) (f y) (f a) = fun j => f (word D k i x y a j) := by
  funext j
  simp only [word]
  split_ifs <;> rfl

def i0 (c : σ → ℤ) : Option σ → ℤ := fun o => o.elim 0 c

open Classical in

def i1 (a₀ : σ) (c : σ → ℤ) : Option σ → ℤ :=
  fun o => o.elim (c a₀) fun a => if a = a₀ then 0 else c a

end Polar

section Lines

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {σ : Type} [Fintype σ]

/- English proof (translation)
Unfold `pullDeg`. Distinguish the cases in `h : ∃ k, κ k = k'`. Take `⟨k, rfl⟩` from `h`. Simplify using `only [hκ.extend_apply]`. Simplify using `only [Function.extend_apply' _ _ _ h, Pi.zero_apply, mul_zero, Finset.sum_const_zero]`.
-/
theorem pullDeg_sum {κ : K → K'} (hκ : Function.Injective κ) (n : σ → ℤ) (b : σ → K → ℤ) (k' : K') :
    pullDeg κ (fun k => ∑ x, n x * b x k) k' = ∑ x, n x * pullDeg κ (b x) k' := by
  unfold pullDeg
  by_cases h : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := h
    simp only [hκ.extend_apply]
  · simp only [Function.extend_apply' _ _ _ h, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use function extensionality and compare the values at `k' show ∑ x, i0 c x * (C x).a k' = pullDeg κ (fun k => ∑ x, c x * (B x).a k) k'`. Rewrite using `[pullDeg_sum hκ, Fintype.sum_option]`. Simplify using `only [i0, Option.elim, zero_mul, zero_add]`. Conclude with `Finset.sum_congr rfl fun a _ => by rw [(hB a).1]`.

Introduce `z show ∏ x, (C x).h z ^ i0 c x = ∏ x, (B x).h _ ^ c x`. Rewrite using `[Fintype.prod_option]`. Simplify using `only [i0, Option.elim, zpow_zero, one_mul]`. Conclude with `Finset.prod_congr rfl fun a _ => by rw [(hB a).2]`.
-/
theorem pull_comb0 {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hκ : Function.Injective κ)
    (B : σ → HermLine ι) (C : Option σ → HermLine ι') (c : σ → ℤ)
    (hB : ∀ a, IsPullHerm κ v (B a) (C (some a))) :
    IsPullHerm κ v (combLine B c) (combLine C (i0 c)) := by
  constructor
  · funext k'
    show ∑ x, i0 c x * (C x).a k' = pullDeg κ (fun k => ∑ x, c x * (B x).a k) k'
    rw [pullDeg_sum hκ, Fintype.sum_option]
    simp only [i0, Option.elim, zero_mul, zero_add]
    exact Finset.sum_congr rfl fun a _ => by rw [(hB a).1]
  · intro z
    show ∏ x, (C x).h z ^ i0 c x = ∏ x, (B x).h _ ^ c x
    rw [Fintype.prod_option]
    simp only [i0, Option.elim, zpow_zero, one_mul]
    exact Finset.prod_congr rfl fun a _ => by rw [(hB a).2]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `show ∑ x, n x * (B x).a k₀ = 0`. Use `Finset.sum_eq_zero fun x _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : x = a₀`. Rewrite using `[h, hn, zero_mul]`.

Rewrite using `[(hb x h).1, mul_zero]`. Introduce `z z' hz show ∏ x, (B x).h z ^ n x = ∏ x, (B x).h z' ^ n x`. Use `Finset.prod_congr rfl fun x _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : x = a₀`. Rewrite using `[h, hn, zpow_zero, zpow_zero]`.

Rewrite using `[(hb x h).2 z z' hz]`.
-/
theorem fromBase_comb {k₀ : K} (B : σ → HermLine ι) (a₀ : σ) (n : σ → ℤ) (hn : n a₀ = 0)
    (hb : ∀ a, a ≠ a₀ → FromBase k₀ (B a)) : FromBase k₀ (combLine B n) := by
  constructor
  · show ∑ x, n x * (B x).a k₀ = 0
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases h : x = a₀
    · rw [h, hn, zero_mul]
    · rw [(hb x h).1, mul_zero]
  · intro z z' hz
    show ∏ x, (B x).h z ^ n x = ∏ x, (B x).h z' ^ n x
    refine Finset.prod_congr rfl fun x _ => ?_
    by_cases h : x = a₀
    · rw [h, hn, zpow_zero, zpow_zero]
    · rw [(hb x h).2 z z' hz]

variable {P : Ideal (MRing ι)} {d : ℕ} {k₀ : K} {xi2 : K → ℤ}

/- English proof (translation)
Take `⟨i⟩` from `hne k`. Establish `h` using `Q.same ⟨k, i⟩ hk`. Establish `h0` using `(Q.block 0).2.2.1 ⟨k, i⟩`. Establish `h1` using `(Q.block 1).2.2.1 ⟨k, i⟩`. Rewrite `h0` using `[h]`.

Conclude with `h0.symm.trans h1`.
-/
theorem kappa_eq (Q : AlgSq P d k₀ xi2) (hne : ∀ k, Nonempty (ι k)) {k : K} (hk : k ≠ k₀) :
    Q.κ 0 k = Q.κ 1 k := by
  obtain ⟨i⟩ := hne k
  have h := Q.same ⟨k, i⟩ hk
  have h0 := (Q.block 0).2.2.1 ⟨k, i⟩
  have h1 := (Q.block 1).2.2.1 ⟨k, i⟩
  rw [h] at h0
  exact h0.symm.trans h1

/- English proof (translation)
Establish `i0'` using `(Q.block 0).1`. Establish `i1'` using `(Q.block 1).1`. Use function extensionality and compare the values at `k'`. Unfold `pullDeg`. Break down `Q.all k' with ⟨k, rfl⟩ | rfl` into its components or cases.

Rewrite using `[i0'.extend_apply]`. Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality. Rewrite using `[Function.extend_apply', ha]`. Both sides reduce to the same expression.

Introduce and unpack `⟨b, hb⟩`. Distinguish the cases in `hbk : b = k`. Substitute `hbk` using the available equality. Conclude with `Q.new ⟨b, hb.symm⟩`. Conclude with `hbk (i0' ((kappa_eq Q hne hbk).trans hb))`.

Rewrite using `[kappa_eq Q hne hk, i1'.extend_apply]`. Rewrite using `[i1'.extend_apply, ha, Function.extend_apply']`. Both sides reduce to the same expression. Introduce and unpack `⟨b, hb⟩`. Conclude with `Q.new ⟨b, hb⟩`.
-/
theorem pullDeg_base (Q : AlgSq P d k₀ xi2) (hne : ∀ k, Nonempty (ι k)) (a : K → ℤ) (ha : a k₀ = 0) :
    pullDeg (Q.κ 0) a = pullDeg (Q.κ 1) a := by
  have i0' := (Q.block 0).1
  have i1' := (Q.block 1).1
  funext k'
  unfold pullDeg
  rcases Q.all k' with ⟨k, rfl⟩ | rfl
  · rw [i0'.extend_apply]
    by_cases hk : k = k₀
    · subst hk
      rw [Function.extend_apply', ha]
      · rfl
      · rintro ⟨b, hb⟩
        by_cases hbk : b = k
        · subst hbk
          exact Q.new ⟨b, hb.symm⟩
        · exact hbk (i0' ((kappa_eq Q hne hbk).trans hb))
    · rw [kappa_eq Q hne hk, i1'.extend_apply]
  · rw [i1'.extend_apply, ha, Function.extend_apply']
    · rfl
    · rintro ⟨b, hb⟩
      exact Q.new ⟨b, hb⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use function extensionality and compare the values at `k' show ∑ x, i1 a₀ c x * (C x).a k' = pullDeg (Q.κ 1) (fun k => ∑ x, c x * (B x).a k) k'`. Rewrite using `[pullDeg_sum (Q.block 1).1, Fintype.sum_option]`. Establish `h : ∀ a, c a * pullDeg (Q.κ 1) (B a).a k' = (if a = a₀ then c a₀ * (C none).a k' else 0) + i1 a₀ c (some a) * (C (some a)).a k'`. Introduce `a`.

Distinguish the cases in `ha : a = a₀`. Substitute `ha` using the available equality. Simplify using `[i1, hN.1]`. Establish `e : (C (some a)).a = pullDeg (Q.κ 1) (B a).a`. Rewrite using `[(hB a).1, pullDeg_base Q hne _ (hb a ha).1]`.

Simplify using `[i1, ha, e]`. Rewrite using `[Finset.sum_congr rfl fun a _ => h a, Finset.sum_add_distrib, Finset.sum_ite_eq']`. Simplify using `[i1]`. Introduce `z show ∏ x, (C x).h z ^ i1 a₀ c x = ∏ x, (B x).h _ ^ c x`. Rewrite using `[Fintype.prod_option]`.

Establish `h : ∀ a, (B a).h (fun p => z (Q.v 1 p)) ^ c a = (if a = a₀ then (C none).h z ^ c a₀ else 1) * (C (some a)).h z ^ i1 a₀ c (some a)`. Introduce `a`. Distinguish the cases in `ha : a = a₀`. Substitute `ha` using the available equality. Simplify using `[i1, hN.2]`.

Establish `e : (C (some a)).h z = (B a).h (fun p => z (Q.v 1 p))`. Rewrite using `[(hB a).2]`. Use `(hb a ha).2 _ _ fun p hp => ?_` and prove the remaining obligations. Rewrite using `[Q.same p hp]`. Simplify using `[i1, ha, e]`.

Rewrite using `[Finset.prod_congr rfl fun a _ => h a, Finset.prod_mul_distrib, Finset.prod_ite_eq']`. Simplify using `[i1]`.
-/
theorem pull_comb1 (Q : AlgSq P d k₀ xi2) (hne : ∀ k, Nonempty (ι k)) (B : σ → HermLine ι)
    (C : Option σ → HermLine Q.ιW) (a₀ : σ) (c : σ → ℤ)
    (hB : ∀ a, IsPullHerm (Q.κ 0) (Q.v 0) (B a) (C (some a)))
    (hN : IsPullHerm (Q.κ 1) (Q.v 1) (B a₀) (C none))
    (hb : ∀ a, a ≠ a₀ → FromBase k₀ (B a)) :
    IsPullHerm (Q.κ 1) (Q.v 1) (combLine B c) (combLine C (i1 a₀ c)) := by
  classical
  constructor
  · funext k'
    show ∑ x, i1 a₀ c x * (C x).a k' = pullDeg (Q.κ 1) (fun k => ∑ x, c x * (B x).a k) k'
    rw [pullDeg_sum (Q.block 1).1, Fintype.sum_option]
    have h : ∀ a, c a * pullDeg (Q.κ 1) (B a).a k' =
        (if a = a₀ then c a₀ * (C none).a k' else 0) + i1 a₀ c (some a) * (C (some a)).a k' := by
      intro a
      by_cases ha : a = a₀
      · subst ha
        simp [i1, hN.1]
      · have e : (C (some a)).a = pullDeg (Q.κ 1) (B a).a := by
          rw [(hB a).1, pullDeg_base Q hne _ (hb a ha).1]
        simp [i1, ha, e]
    rw [Finset.sum_congr rfl fun a _ => h a, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp [i1]
  · intro z
    show ∏ x, (C x).h z ^ i1 a₀ c x = ∏ x, (B x).h _ ^ c x
    rw [Fintype.prod_option]
    have h : ∀ a, (B a).h (fun p => z (Q.v 1 p)) ^ c a =
        (if a = a₀ then (C none).h z ^ c a₀ else 1) * (C (some a)).h z ^ i1 a₀ c (some a) := by
      intro a
      by_cases ha : a = a₀
      · subst ha
        simp [i1, hN.2]
      · have e : (C (some a)).h z = (B a).h (fun p => z (Q.v 1 p)) := by
          rw [(hB a).2]
          refine (hb a ha).2 _ _ fun p hp => ?_
          rw [Q.same p hp]
        simp [i1, ha, e]
    rw [Finset.prod_congr rfl fun a _ => h a, Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp [i1]

end Lines

section Analytic

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x j show ContDiffOn ℝ _ (fun y => ∑ a, c a * (Pp a).φ x ((A.chart j).symm y)) _`. Use `ContDiffOn.sum fun a _ => contDiffOn_const.mul ?_` and prove the remaining obligations. Conclude with `((h a).1 x j).mono fun y hy => ⟨hy.1, Set.mem_iInter.1 hy.2 a⟩`. Introduce `x x' y hy`.

Establish `hya : ∀ a, y ∈ (Pp a).U x ∩ (Pp a).U x'` using `fun a => ⟨Set.mem_iInter.1 hy.1 a, Set.mem_iInter.1 hy.2 a⟩`. Use `choose W hW hyW G hG hE using fun a => (h a).2 x x' y (hya a)`. Use `⟨⋂ a, W a, isOpen_iInter_of_finite hW, Set.mem_iInter.2 hyW, fun z => ∑ a, (c a : ℂ) * G a z, ?_, ?_⟩` and prove the remaining obligations. Introduce `j z hz show AnalyticAt ℂ (fun w => ∑ a, (c a : ℂ) * G a ((A.chart j).symm w)) z`. Conclude with `Finset.analyticAt_fun_sum _ fun a _ => analyticAt_const.mul (hG a j z ⟨hz.1, Set.mem_iInter.1 hz.2 a⟩)`.

Introduce `z hz show ∑ a, c a * (Pp a).φ x z - ∑ a, c a * (Pp a).φ x' z = (∑ a, (c a : ℂ) * G a z).re`. Rewrite using `[← Finset.sum_sub_distrib, Complex.re_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `hE a z ⟨⟨Set.mem_iInter.1 hz.1.1 a, Set.mem_iInter.1 hz.1.2 a⟩, Set.mem_iInter.1 hz.2 a⟩` as an intermediate fact. Rewrite using `[Complex.re_ofReal_mul, ← this]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem isPotential_sumPot {e : ℕ} {X : Type} [TopologicalSpace X] {σ : Type} [Fintype σ]
    (A : FinHolAtlas e X) (c : σ → ℝ) (Pp : σ → LocPot X) (h : ∀ a, IsPotential A (Pp a)) :
    IsPotential A (sumPot c Pp) := by
  constructor
  · intro x j
    show ContDiffOn ℝ _ (fun y => ∑ a, c a * (Pp a).φ x ((A.chart j).symm y)) _
    refine ContDiffOn.sum fun a _ => contDiffOn_const.mul ?_
    exact ((h a).1 x j).mono fun y hy => ⟨hy.1, Set.mem_iInter.1 hy.2 a⟩
  · intro x x' y hy
    have hya : ∀ a, y ∈ (Pp a).U x ∩ (Pp a).U x' := fun a =>
      ⟨Set.mem_iInter.1 hy.1 a, Set.mem_iInter.1 hy.2 a⟩
    choose W hW hyW G hG hE using fun a => (h a).2 x x' y (hya a)
    refine ⟨⋂ a, W a, isOpen_iInter_of_finite hW, Set.mem_iInter.2 hyW,
      fun z => ∑ a, (c a : ℂ) * G a z, ?_, ?_⟩
    · intro j z hz
      show AnalyticAt ℂ (fun w => ∑ a, (c a : ℂ) * G a ((A.chart j).symm w)) z
      exact Finset.analyticAt_fun_sum _ fun a _ =>
        analyticAt_const.mul (hG a j z ⟨hz.1, Set.mem_iInter.1 hz.2 a⟩)
    · intro z hz
      show ∑ a, c a * (Pp a).φ x z - ∑ a, c a * (Pp a).φ x' z = (∑ a, (c a : ℂ) * G a z).re
      rw [← Finset.sum_sub_distrib, Complex.re_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have := hE a z ⟨⟨Set.mem_iInter.1 hz.1.1 a, Set.mem_iInter.1 hz.1.2 a⟩, Set.mem_iInter.1 hz.2 a⟩
      rw [Complex.re_ofReal_mul, ← this]
      ring

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {σ : Type} [Fintype σ]

/- English proof (translation)
Introduce `x _`. Use `choose V hV hxV G hG hE using fun a => h a x trivial`. Use `⟨R.U x ∩ ⋂ a, V a, (R.isOpen_U x).inter (isOpen_iInter_of_finite hV), ⟨R.mem_U x, Set.mem_iInter.2 hxV⟩, fun y => ∑ a, (c a : ℂ) * G a y, ?_, ?_⟩` and prove the remaining obligations. Introduce `j z hz show AnalyticAt ℂ (fun w => ∑ a, (c a : ℂ) * G a ((R.A.chart j).symm w)) z`. Conclude with `Finset.analyticAt_fun_sum _ fun a _ => analyticAt_const.mul (hG a j z ⟨hz.1, Set.mem_iInter.1 hz.2.2 a⟩)`.

Introduce `y hy`. Establish `hm` using `(R.mem x y hy.1).1`. Use `show Real.log (∏ a, (C a).h (R.lift x y) ^ c a) - ∑ a, (c a : ℝ) * (Pp a).φ (π x) (π y) = (∑ a, (c a : ℂ) * G a y).re`. Rewrite using `[Real.log_prod (fun a _ => (zpow_pos ((C a).pos _ hm) _).ne'), ← Finset.sum_sub_distrib, Complex.re_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Use `hE a y (Set.mem_iInter.1 hy.2 a)` as an intermediate fact. Establish `e : ((c a : ℂ) * G a y).re = (c a : ℝ) * (G a y).re`. Rewrite using `[show (c a : ℂ) = ((c a : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]`. Rewrite using `[e, ← this, Real.log_zpow]`. Use `show _ = (c a : ℝ) * (Real.log ((C a).h (R.lift x y)) - (Pp a).φ (π x) (π y))`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem samePot_comb {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) {X : Type} [TopologicalSpace X]
    (π : R.X → X) (hπ : Continuous π) (C : σ → HermLine ι) (Pp : σ → LocPot X) (c : σ → ℤ)
    (h : ∀ a, SamePot R.A Set.univ (potOf R (C a)) ((Pp a).pullback π hπ)) :
    SamePot R.A Set.univ (potOf R (combLine C c)) ((sumPot (fun a => (c a : ℝ)) Pp).pullback π hπ) := by
  intro x _
  choose V hV hxV G hG hE using fun a => h a x trivial
  refine ⟨R.U x ∩ ⋂ a, V a, (R.isOpen_U x).inter (isOpen_iInter_of_finite hV),
    ⟨R.mem_U x, Set.mem_iInter.2 hxV⟩, fun y => ∑ a, (c a : ℂ) * G a y, ?_, ?_⟩
  · intro j z hz
    show AnalyticAt ℂ (fun w => ∑ a, (c a : ℂ) * G a ((R.A.chart j).symm w)) z
    exact Finset.analyticAt_fun_sum _ fun a _ =>
      analyticAt_const.mul (hG a j z ⟨hz.1, Set.mem_iInter.1 hz.2.2 a⟩)
  · intro y hy
    have hm := (R.mem x y hy.1).1
    show Real.log (∏ a, (C a).h (R.lift x y) ^ c a) - ∑ a, (c a : ℝ) * (Pp a).φ (π x) (π y) =
      (∑ a, (c a : ℂ) * G a y).re
    rw [Real.log_prod (fun a _ => (zpow_pos ((C a).pos _ hm) _).ne'), ← Finset.sum_sub_distrib,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := hE a y (Set.mem_iInter.1 hy.2 a)
    have e : ((c a : ℂ) * G a y).re = (c a : ℝ) * (G a y).re := by
      rw [show (c a : ℂ) = ((c a : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
    rw [e, ← this, Real.log_zpow]
    show _ = (c a : ℝ) * (Real.log ((C a).h (R.lift x y)) - (Pp a).φ (π x) (π y))
    ring

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `x`. Take `⟨j, hj⟩` from `A.cover x`. Establish `hm : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ` using `⟨(A.chart j).map_source hj, trivial⟩`. Establish `hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ)`.

Simplify using `using (A.chart j).open_target`. Establish `h1 : ContinuousAt (u ∘ (A.chart j).symm) (A.chart j x)` using `(hu j).continuousOn.continuousAt (hopen.mem_nhds hm)`. Establish `h2` using `ContinuousAt.comp (f := A.chart j) (x := x) h1 ((A.chart j).continuousAt hj)`. Use `h2.congr ?_` and prove the remaining obligations. Use `filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy`.

Simplify using `[(A.chart j).left_inv hy]`.
-/
theorem continuous_of_smooth {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {u : X → ℝ}
    (hu : A.Smooth u) : Continuous u := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hj⟩ := A.cover x
  have hm : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ :=
    ⟨(A.chart j).map_source hj, trivial⟩
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ) := by
    simpa using (A.chart j).open_target
  have h1 : ContinuousAt (u ∘ (A.chart j).symm) (A.chart j x) :=
    (hu j).continuousOn.continuousAt (hopen.mem_nhds hm)
  have h2 := ContinuousAt.comp (f := A.chart j) (x := x) h1 ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

/- English proof (translation)
Establish `h1 : MIntegrable Q.SW.A Φ (logNormSec Q.L' Q.v)` using `logNormIntegrable Q.SW.A Q.L' Q.v _ _ Q.potL' Q.secv Q.sncv Φ hΦ`. Establish `hc : ∀ a, Continuous (SY.phT a t)` using `fun a => continuous_of_smooth SY.A (((SY.reg a).2.2 t ht ht').1)`. Establish `hcont : Continuous fun x => Q.cst + (1 / 2) * ∑ a, (ε a : ℝ) * (SY.phT a t (Q.q 0 x) + SY.phT a t (Q.q 1 x))` using `continuous_const.add (continuous_const.mul (continuous_finset_sum _ fun a _ => continuous_const.mul (((hc a).comp (Q.holo 0).1).add ((hc a).comp (Q.holo 1).1))))`. Establish `h2` using `mIntegrableCont Q.SW.A Φ hΦ _ hcont`. Introduce `j C hC hcpt`.

Use `((h1 j C hC hcpt).add (h2 j C hC hcpt)).congr_fun (fun y _ => ?_) hcpt.measurableSet` and prove the remaining obligations. Simplify using `only [AnSq.gT, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mIntegrable_gT {d : ℕ} {SY : AnSys (d + 1) σ} {a₀ : σ} {ε : σ → ℤ} (Q : AnSq SY a₀ ε) {t : ℝ}
    (ht : 0 < t) (ht' : t ≤ SY.t₀) (Φ : Fin (d + 2) → LocPot Q.SW.X)
    (hΦ : ∀ i, IsPotential Q.SW.A (Φ i)) : MIntegrable Q.SW.A Φ (Q.gT t) := by
  have h1 : MIntegrable Q.SW.A Φ (logNormSec Q.L' Q.v) :=
    logNormIntegrable Q.SW.A Q.L' Q.v _ _ Q.potL' Q.secv Q.sncv Φ hΦ
  have hc : ∀ a, Continuous (SY.phT a t) := fun a =>
    continuous_of_smooth SY.A (((SY.reg a).2.2 t ht ht').1)
  have hcont : Continuous fun x => Q.cst + (1 / 2) * ∑ a, (ε a : ℝ) *
      (SY.phT a t (Q.q 0 x) + SY.phT a t (Q.q 1 x)) :=
    continuous_const.add (continuous_const.mul (continuous_finset_sum _ fun a _ =>
      continuous_const.mul (((hc a).comp (Q.holo 0).1).add ((hc a).comp (Q.holo 1).1))))
  have h2 := mIntegrableCont Q.SW.A Φ hΦ _ hcont
  intro j C hC hcpt
  refine ((h1 j C hC hcpt).add (h2 j C hC hcpt)).congr_fun (fun y _ => ?_) hcpt.measurableSet
  simp only [AnSq.gT, Pi.add_apply]
  ring

end Analytic

section Main

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {d : ℕ} {σ : Type} [Fintype σ]
  {SY : AnSys (d + 1) σ} {P : Ideal (MRing ι)} {Re : Realis SY P} {a₀ : σ} {ε : σ → ℤ}

/- English proof (translation)
Establish `hgh : IsMultiHomog (Q.alg.g * Q.alg.h) (Q.alg.dg + Q.alg.dh)` using `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul Q.alg.g_deg Q.alg.h_deg`. Establish `hprime : Q.alg.PW.IsPrime` using `Q.alg.arithW.2.1.1`. Establish `hghP : Q.alg.g * Q.alg.h ∉ Q.alg.PW` using `fun hm => (hprime.mem_or_mem hm).elim Q.alg.g_nmem Q.alg.h_nmem`. Rewrite using `[GroundTheory.Heights₂.Heights.Inter.ZeroSetNull.proof Q.alg.KW Q.alg.ιW Q.alg.PW (d + 2) (Q.alg.g * Q.alg.h) _ _ _ (logNormRat Am Q.alg.g Q.alg.h) Q.alg.arithW hgh hghP (fun z hz hne => (hAm z hz hne).symm)]`. Take `⟨N, hN, hNe⟩` from `Q.norm_eq`.

Set `Z : Set Q.ReW.R.X` to `{x | eval (Q.ReW.R.lift x x) (map (Int.castRingHom ℂ) (Q.alg.g * Q.alg.h)) = 0}`. Establish `hZ : IsNull Q.ReW.R.A Z` using `fun j => GroundTheory.Heights₂.Heights.HilbertSamuel.AnResNullForm.full (d + 2) _ _ _ _ Q.ReW.R.toAnRes (Q.alg.g * Q.alg.h) _ Q.alg.arithW hgh hghP j`. Establish `hN' : IsNull Q.ReW.R.A (N ∪ Z)`. Introduce `j`. Rewrite using `[Set.preimage_union, Set.inter_union_distrib_left]`.

Conclude with `measure_union_null (hN j) (hZ j)`. Establish `hpotT : ∀ o, IsPotential Q.an.SW.A (Q.an.SW.potT o t)` using `fun o => (GlobalTheory.CompanionTheory.Ar.PB.anSys_open_basics _ _ Q.an.SW).2.2.2.1 o t ht ht'`. Set `Pt : Option σ → LocPot Q.an.SW.X` to `fun o => Q.an.SW.potT o t`. Set `Φ : Fin (d + 2) → LocPot Q.an.SW.X` to `fun j => sumPot (fun o => (c j o : ℝ)) Pt`. Establish `hΦ : ∀ j, IsPotential Q.an.SW.A (Φ j)` using `fun j => isPotential_sumPot _ _ _ hpotT`.

Establish `hre` using `GlobalTheory.T.realisation_potential_degree_compatibility hE _ _ (d + 2) _ Q.an.SW _ Q.ReW`. Establish `hSame : ∀ j, SamePot Q.ReW.R.A Set.univ (potOf Q.ReW.R (combLine (fun o => Q.ReW.line o t) (c j))) ((Φ j).pullback Q.ReW.π Q.ReW.holo.1)` using `fun j => samePot_comb Q.ReW.R _ _ _ Pt (c j) fun o => hre.1 o t ht ht'`. Establish `hsmooth : ∀ j, IsSmoothHerm (combLine (fun o => Q.ReW.line o t) (c j))` using `fun j => GlobalTheory.CompanionTheory.Ar.Cmp.isSmoothHerm_combLine (fun o => Q.ReW.line_smooth o t ht ht') _`. Establish `hw : ∀ w : Fin (d + 2) → Option σ, MIntegrable Q.an.SW.A (fun i => Pt (w i)) (Q.an.gT t)` using `fun w => mIntegrable_gT Q.an ht (ht'.trans Q.an.t₀_le) _ fun i => hpotT _`. Establish `hNull : IsNull Q.an.SW.A (Set.univ : Set Q.an.SW.X)ᶜ` using `fun j => by simp`.

Establish `hexp` using `GlobalTheory.CompanionTheory.Ar.PB.mInt_sumPot_expand (d + 2) Q.an.SW.X Q.an.SW.A (Option σ) Set.univ Pt (fun r o => (c r o : ℝ)) (Q.an.gT t) hNull (fun o x _ => GlobalTheory.CompanionTheory.Ar.Cmp.isC2At_of_isPotential _ (hpotT o) x) hw`. Establish `hEq : ∀ x ∉ N ∪ Z, logNormRat Am Q.alg.g Q.alg.h (Q.ReW.R.lift x x) = Q.an.gT t (Q.ReW.π x)`. Introduce `x hx`. Establish `hxN : x ∉ N` using `fun h => hx (Or.inl h)`. Establish `hxZ : x ∉ Z` using `fun h => hx (Or.inr h)`.

Rewrite using `[hAm _ (Q.ReW.R.mem x x (Q.ReW.R.mem_U x)) hxZ, hNe t ht ht' x hxN]`. Both sides reduce to the same expression. Establish `hbr` using `GlobalTheory.T.intersection_number_pullback_degree_alt hE _ _ Q.alg.PW Q.ReW.J (d + 2) Q.ReW.R Q.an.SW.X Q.an.SW.A Q.ReW.π Q.ReW.holo Q.ReW.deg Q.ReW.br Q.alg.arithW Q.ReW.degree (fun j => combLine (fun o => Q.ReW.line o t) (c j)) Φ hsmooth hΦ hSame Am Q.alg.g Q.alg.h (Q.an.gT t) …`. Rewrite using `[hbr, Q.deg_eq]`. Use `congr 1`.

Conclude with `hexp.2`.
-/
theorem pts_eq_polar (hE : ResExistsStatement) (Q : SqSys Re a₀ ε) {t : ℝ} (ht : 0 < t)
    (ht' : t ≤ Q.an.SW.t₀) (Am : HermLine Q.alg.ιW) (hAmS : IsSmoothHerm Am)
    (hRat : IsRatSectionOn Q.alg.PW Am Q.alg.g Q.alg.h)
    (hAm : ∀ z ∈ mcPts Q.alg.PW, eval z (map (Int.castRingHom ℂ) (Q.alg.g * Q.alg.h)) ≠ 0 →
      logNormRat Am Q.alg.g Q.alg.h z = Q.alg.logNormT (combLine (fun a => Re.line a t) ε) z)
    (c : Fin (d + 2) → Option σ → ℤ) :
    ptsIntegral Q.alg.PW (pot fun j => combLine (fun o => Q.ReW.line o t) (c j))
        (Q.alg.logNormT (combLine (fun a => Re.line a t) ε)) =
      (Re.deg : ℝ) * polar (d + 2)
        (fun w => mInt Q.an.SW.A (fun r => Q.an.SW.potT (w r) t) (Q.an.gT t)) (fun r o => (c r o : ℝ)) := by
  classical
  have hgh : IsMultiHomog (Q.alg.g * Q.alg.h) (Q.alg.dg + Q.alg.dh) :=
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul Q.alg.g_deg Q.alg.h_deg
  have hprime : Q.alg.PW.IsPrime := Q.alg.arithW.2.1.1
  have hghP : Q.alg.g * Q.alg.h ∉ Q.alg.PW := fun hm =>
    (hprime.mem_or_mem hm).elim Q.alg.g_nmem Q.alg.h_nmem
  rw [GroundTheory.Heights₂.Heights.Inter.ZeroSetNull.proof Q.alg.KW Q.alg.ιW Q.alg.PW (d + 2)
    (Q.alg.g * Q.alg.h) _ _ _ (logNormRat Am Q.alg.g Q.alg.h) Q.alg.arithW hgh hghP
    (fun z hz hne => (hAm z hz hne).symm)]
  obtain ⟨N, hN, hNe⟩ := Q.norm_eq
  let Z : Set Q.ReW.R.X :=
    {x | eval (Q.ReW.R.lift x x) (map (Int.castRingHom ℂ) (Q.alg.g * Q.alg.h)) = 0}
  have hZ : IsNull Q.ReW.R.A Z := fun j =>
    GroundTheory.Heights₂.Heights.HilbertSamuel.AnResNullForm.full (d + 2) _ _ _ _ Q.ReW.R.toAnRes
      (Q.alg.g * Q.alg.h) _ Q.alg.arithW hgh hghP j
  have hN' : IsNull Q.ReW.R.A (N ∪ Z) := by
    intro j
    rw [Set.preimage_union, Set.inter_union_distrib_left]
    exact measure_union_null (hN j) (hZ j)
  have hpotT : ∀ o, IsPotential Q.an.SW.A (Q.an.SW.potT o t) := fun o =>
    (GlobalTheory.CompanionTheory.Ar.PB.anSys_open_basics _ _ Q.an.SW).2.2.2.1 o t ht ht'
  let Pt : Option σ → LocPot Q.an.SW.X := fun o => Q.an.SW.potT o t
  let Φ : Fin (d + 2) → LocPot Q.an.SW.X := fun j => sumPot (fun o => (c j o : ℝ)) Pt
  have hΦ : ∀ j, IsPotential Q.an.SW.A (Φ j) := fun j => isPotential_sumPot _ _ _ hpotT
  have hre := GlobalTheory.T.realisation_potential_degree_compatibility hE _ _ (d + 2) _ Q.an.SW _ Q.ReW
  have hSame : ∀ j, SamePot Q.ReW.R.A Set.univ
      (potOf Q.ReW.R (combLine (fun o => Q.ReW.line o t) (c j)))
      ((Φ j).pullback Q.ReW.π Q.ReW.holo.1) := fun j =>
    samePot_comb Q.ReW.R _ _ _ Pt (c j) fun o => hre.1 o t ht ht'
  have hsmooth : ∀ j, IsSmoothHerm (combLine (fun o => Q.ReW.line o t) (c j)) := fun j =>
    GlobalTheory.CompanionTheory.Ar.Cmp.isSmoothHerm_combLine (fun o => Q.ReW.line_smooth o t ht ht') _
  have hw : ∀ w : Fin (d + 2) → Option σ,
      MIntegrable Q.an.SW.A (fun i => Pt (w i)) (Q.an.gT t) := fun w =>
    mIntegrable_gT Q.an ht (ht'.trans Q.an.t₀_le) _ fun i => hpotT _
  have hNull : IsNull Q.an.SW.A (Set.univ : Set Q.an.SW.X)ᶜ := fun j => by simp
  have hexp := GlobalTheory.CompanionTheory.Ar.PB.mInt_sumPot_expand (d + 2) Q.an.SW.X Q.an.SW.A (Option σ) Set.univ Pt
    (fun r o => (c r o : ℝ)) (Q.an.gT t) hNull
    (fun o x _ => GlobalTheory.CompanionTheory.Ar.Cmp.isC2At_of_isPotential _ (hpotT o) x) hw
  have hEq : ∀ x ∉ N ∪ Z, logNormRat Am Q.alg.g Q.alg.h (Q.ReW.R.lift x x) = Q.an.gT t (Q.ReW.π x) := by
    intro x hx
    have hxN : x ∉ N := fun h => hx (Or.inl h)
    have hxZ : x ∉ Z := fun h => hx (Or.inr h)
    rw [hAm _ (Q.ReW.R.mem x x (Q.ReW.R.mem_U x)) hxZ, hNe t ht ht' x hxN]
    rfl
  have hbr := GlobalTheory.T.intersection_number_pullback_degree_alt hE _ _ Q.alg.PW Q.ReW.J (d + 2) Q.ReW.R Q.an.SW.X Q.an.SW.A Q.ReW.π Q.ReW.holo
    Q.ReW.deg Q.ReW.br Q.alg.arithW Q.ReW.degree (fun j => combLine (fun o => Q.ReW.line o t) (c j)) Φ
    hsmooth hΦ hSame Am Q.alg.g Q.alg.h (Q.an.gT t) (N ∪ Z) hAmS hRat hN' hEq hexp.1
  rw [hbr, Q.deg_eq]
  congr 1
  exact hexp.2

end Main

end GlobalTheory.CompanionTheory.Ar.PB.SqAt

namespace GlobalTheory.CompanionTheory.Ar.PB

open GlobalTheory.CompanionTheory.Ar.PB.SqAt in

/- English proof (translation)
Introduce `hI II hII K _ ι _ d σ _ SY P Re a₀ ε Q n hn t ht ht'`. Establish `htY : t ≤ SY.t₀` using `ht'.trans Q.an.t₀_le`. Set `LY : σ → HermLine ι` to `fun a => Re.line a t`. Set `LW : Option σ → HermLine Q.alg.ιW` to `fun o => Q.ReW.line o t`. Establish `hsY : ∀ a, IsSmoothHerm (LY a)` using `fun a => Re.line_smooth a t ht htY`.

Establish `hsW : ∀ o, IsSmoothHerm (LW o)` using `fun o => Q.ReW.line_smooth o t ht ht'`. Establish `hne : ∀ k, Nonempty (ι k)`. Take `⟨z, hz, -⟩` from `GroundTheory.Heights₂.Heights.HilbertSamuel.exists_mcPts_not_mem_mcPts Re.arith Re.R.nondeg`. Introduce `k`. Take `⟨i, -⟩` from `hz.1 k`.

Conclude with `⟨i⟩`. Establish `hdegpos : (Re.deg : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 Re.deg_pos.ne'`. Establish `hpol : ∀ c : Fin (d + 2) → σ → ℤ, polar (d + 2) (Re.num II t) (fun r a => (c r a : ℝ)) = II K ι P (d + 2) (fun r => combLine LY (c r)) / Re.deg`. Introduce `c`. Rewrite using `[(GlobalTheory.T.arithmetic_intersection_multilinear_polar hI.metricLocal II hII K ι σ P (d + 2) LY c Re.arith hsY).2]`.

Conclude with `polar_div _ _ _ _`. Set `Xi : HermLine ι` to `combLine LY ε`. Set `A : HermLine ι` to `combLine LY n`. Set `X₀ : HermLine Q.alg.ιW` to `combLine LW (i0 ε)`. Set `X₁ : HermLine Q.alg.ιW` to `combLine LW (i1 a₀ ε)`.

Set `A₀ : HermLine Q.alg.ιW` to `combLine LW (i0 n)`. Establish `hXia : Xi.a = (combLine Re.ref ε).a`. Use function extensionality and compare the values at `k`. Use `show ∑ x, ε x * (Re.line x t).a k = ∑ x, ε x * (Re.ref x).a k`. Simplify using `only [Re.line_deg]`.

Establish `hsXi : IsSmoothHerm Xi` using `GlobalTheory.CompanionTheory.Ar.Cmp.isSmoothHerm_combLine hsY _`. Establish `hsA : IsSmoothHerm A` using `GlobalTheory.CompanionTheory.Ar.Cmp.isSmoothHerm_combLine hsY _`. Establish `hs0 : IsSmoothHerm X₀` using `GlobalTheory.CompanionTheory.Ar.Cmp.isSmoothHerm_combLine hsW _`. Establish `hs1 : IsSmoothHerm X₁` using `GlobalTheory.CompanionTheory.Ar.Cmp.isSmoothHerm_combLine hsW _`. Establish `hp0 : IsPullHerm (Q.alg.κ 0) (Q.alg.v 0) Xi X₀` using `pull_comb0 (Q.alg.block 0).1 LY LW ε fun a => Q.pull0 a t`.

Establish `hp1 : IsPullHerm (Q.alg.κ 1) (Q.alg.v 1) Xi X₁` using `pull_comb1 Q.alg hne LY LW a₀ ε (fun a => Q.pull0 a t) (Q.pull1 t) fun a h => Q.base a h t`. Establish `hpA : IsPullHerm (Q.alg.κ 0) (Q.alg.v 0) A A₀` using `pull_comb0 (Q.alg.block 0).1 LY LW n fun a => Q.pull0 a t`. Establish `hbase : FromBase Q.k₀ A` using `fromBase_comb LY a₀ n hn fun a h => Q.base a h t`. Establish `hF` using `GlobalTheory.T.algebraic_square_base_intersection hI II hII K ι P d Q.k₀ _ Q.alg Xi X₀ X₁ hXia hsXi hp0 hp1 A A₀ hsA hbase hpA`. Use `⟨?_, fun k hk hk2 => ?_⟩` and prove the remaining obligations.

Establish `h` using `hpol fun _ => n`. Rewrite using `[h, hF.1, zero_div]`. Establish `hc : ∀ k', 2 * ((Q.alg.dg k' : ℤ) - Q.alg.dh k') = -(X₀.a k' + X₁.a k')`. Introduce `k'`. Rewrite using `[Q.alg.deg_eq k', hp0.1, hp1.1, hXia]`.

Set `Am : HermLine Q.alg.ιW` to `GroundTheory.Heights₂.Heights.Inter.DiagRAux.halfInvLine X₀ X₁ (fun k' => (Q.alg.dg k' : ℤ) - Q.alg.dh k') hc`. Establish `hAmS : IsSmoothHerm Am` using `GroundTheory.Heights₂.Heights.Inter.DiagRAux.isSmoothHerm_halfInvLine hs0 hs1 _ hc`. Establish `hRat : IsRatSectionOn Q.alg.PW Am Q.alg.g Q.alg.h` using `⟨Q.alg.dg, Q.alg.dh, Q.alg.g_deg, Q.alg.h_deg, Q.alg.g_nmem, Q.alg.h_nmem, fun _ => rfl⟩`. Establish `hAm : ∀ z ∈ mcPts Q.alg.PW, eval z (map (Int.castRingHom ℂ) (Q.alg.g * Q.alg.h)) ≠ 0 → logNormRat Am Q.alg.g Q.alg.h z = Q.alg.logNormT Xi z`. Introduce `z hz hne'`.

Rewrite `hne'` using `[map_mul, eval_mul]`. Establish `hgz : ‖eval z (map (Int.castRingHom ℂ) Q.alg.g)‖ ≠ 0` using `norm_ne_zero_iff.2 (left_ne_zero_of_mul hne')`. Establish `hhz : ‖eval z (map (Int.castRingHom ℂ) Q.alg.h)‖ ≠ 0` using `norm_ne_zero_iff.2 (right_ne_zero_of_mul hne')`. Establish `h0` using `X₀.pos z hz.1`. Establish `h1` using `X₁.pos z hz.1`.

Establish `hAmz : Am.h z = (X₀.h z * X₁.h z) ^ (-(1 / 2 : ℝ))` using `GroundTheory.Heights₂.Heights.Inter.DiagRAux.halfInvLine_h_of_pos _ _ _ _ z hz.1`. Unfold `logNormRat AlgSq.logNormT`. Rewrite using `[hAmz, Real.log_div (div_ne_zero hgz hhz) (Real.rpow_pos_of_pos (mul_pos h0 h1) _).ne', Real.log_rpow (mul_pos h0 h1), Real.log_mul h0.ne' h1.ne', hp0.2 z, hp1.2 z]`. Expand and normalize the polynomial expressions, which then agree. Establish `hkey` using `fun c => SqAt.pts_eq_polar hI.resExists Q ht ht' Am hAmS hRat hAm c`.

Set `cst : (Option σ → ℤ) → Option σ → ℝ` to `fun f o => (f o : ℝ)`. Establish `hc0 : ∀ c : σ → ℤ, cst (i0 c) = Q.an.pull0 fun a => (c a : ℝ)`. Introduce `c`. Use function extensionality and compare the values at `o`. Apply the tactic sequence `cases o <;> simp [cst, i0, AnSq.pull0]`.

Establish `hc1 : cst (i1 a₀ ε) = Q.an.pull1 fun a => (ε a : ℝ)`. Use function extensionality and compare the values at `o`. Consider the cases of `o with`. Consider the case `none => simp [cst, i1, AnSq.pull1]`. Consider the case `some a`.

Apply the tactic sequence `by_cases h : a = a₀ <;> simp [cst, i1, AnSq.pull1, h]`. Set `Wd : ℕ → Fin (d + 1) → Option σ → ℤ` to `fun i => word (d + 1) k i (i0 ε) (i1 a₀ ε) (i0 n)`. Establish `hcons : ∀ (x : Option σ → ℤ) (i : ℕ), (Fin.cons (combLine LW x) (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.alg.ιW) = fun j => combLine LW ((Fin.cons (α` using `fun _ => Option σ → ℤ) x (Wd i) : Fin (d + 2) → Option σ → ℤ) j) := by`. Introduce `x i`. Establish `e : word (d + 1) k i X₀ X₁ A₀ = fun j => combLine LW (Wd i j)` using `word_map (combLine LW) (d + 1) k i (i0 ε) (i1 a₀ ε) (i0 n)`.

Rewrite using `[e]`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) j <;> simp`. Establish `hcast : ∀ (x : Option σ → ℤ) (i : ℕ), (fun r o => (((Fin.cons (α` using `fun _ => Option σ → ℤ) x (Wd i) : Fin (d + 2) → Option σ → ℤ) r o : ℤ) : ℝ)) = Fin.cons (α := fun _ => Option σ → ℝ) (cst x) (word (d + 1) k i (Q.an.pull0 fun a => (ε a : ℝ)) (Q.an.pull1 fun a => (ε a : ℝ)) (Q.an.pull0 fun a => (n a : ℝ))) := by`. Introduce `x i`.

Rewrite using `[← hc0 ε, ← hc1, ← hc0 n, word_map cst]`. Use function extensionality and compare the values at `r`. Use `Fin.cases ?_ (fun j => ?_) r` and prove the remaining obligations. Both sides reduce to the same expression. Both sides reduce to the same expression.

Establish `hs : ∀ i, ptsIntegral Q.alg.PW (pot (Fin.cons X₀ (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.alg.ιW)) (Q.alg.logNormT Xi) - ptsIntegral Q.alg.PW (pot (Fin.cons X₁ (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.alg.ιW)) (Q.alg.logNormT Xi) = (Re.deg : ℝ) * polar …`. Introduce `i`. Rewrite using `[hcons (i0 ε) i, hcons (i1 a₀ ε) i, hkey, hkey, hcast, hcast, ← mul_sub, hc0 ε, hc1]`. Unfold `AnSq.wcoef`. Rewrite using `[polar_cons_sub]`.

Establish `hmix : (mix (2 * k) (fun a => (ε a : ℝ)) fun a => (n a : ℝ) : Fin (d + 2) → σ → ℝ) = fun r a => ((mix (2 * k) ε n r : σ → ℤ) a : ℝ)`. Use function extensionality and compare the values at `r a`. Simplify using `only [mix]`. Apply the tactic sequence `split_ifs <;> rfl`. Establish `hmixL : (fun r => combLine LY ((mix (2 * k) ε n : Fin (d + 2) → σ → ℤ) r)) = mix (2 * k) Xi A`.

Use function extensionality and compare the values at `r`. Simplify using `only [mix]`. Apply the tactic sequence `split_ifs <;> rfl`. Rewrite using `[hmix, hpol, hmixL, hF.2 k hk hk2, Finset.sum_congr rfl fun i _ => hs i, ← Finset.mul_sum]`. Clear the denominators using the available nonvanishing facts.
-/
theorem first_half_at_scale : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (d : ℕ) (σ : Type) [Fintype σ]
    (SY : AnSys (d + 1) σ) (P : Ideal (MRing ι)) (Re : Realis SY P) (a₀ : σ) (ε : σ → ℤ)
    (Q : SqSys Re a₀ ε) (n : σ → ℤ), n a₀ = 0 → ∀ t, 0 < t → t ≤ Q.an.SW.t₀ →
    polar (d + 2) (Re.num II t) (fun _ a => (n a : ℝ)) = 0 ∧ ∀ k : ℕ, 1 ≤ k → 2 * k ≤ d + 2 →
      polar (d + 2) (Re.num II t) (mix (2 * k) (fun a => (ε a : ℝ)) fun a => (n a : ℝ)) =
        -∑ i ∈ Finset.range k, polar (d + 2)
          (fun w => mInt Q.an.SW.A (fun r => Q.an.SW.potT (w r) t) (Q.an.gT t))
          (Q.an.wcoef (fun a => (n a : ℝ)) k i) := by
  intro hI II hII K _ ι _ d σ _ SY P Re a₀ ε Q n hn t ht ht'
  classical
  have htY : t ≤ SY.t₀ := ht'.trans Q.an.t₀_le
  let LY : σ → HermLine ι := fun a => Re.line a t
  let LW : Option σ → HermLine Q.alg.ιW := fun o => Q.ReW.line o t
  have hsY : ∀ a, IsSmoothHerm (LY a) := fun a => Re.line_smooth a t ht htY
  have hsW : ∀ o, IsSmoothHerm (LW o) := fun o => Q.ReW.line_smooth o t ht ht'
  have hne : ∀ k, Nonempty (ι k) := by
    obtain ⟨z, hz, -⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.exists_mcPts_not_mem_mcPts Re.arith Re.R.nondeg
    intro k
    obtain ⟨i, -⟩ := hz.1 k
    exact ⟨i⟩
  have hdegpos : (Re.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Re.deg_pos.ne'
  have hpol : ∀ c : Fin (d + 2) → σ → ℤ, polar (d + 2) (Re.num II t) (fun r a => (c r a : ℝ)) =
      II K ι P (d + 2) (fun r => combLine LY (c r)) / Re.deg := by
    intro c
    rw [(GlobalTheory.T.arithmetic_intersection_multilinear_polar hI.metricLocal II hII K ι σ P (d + 2) LY c Re.arith hsY).2]
    exact polar_div _ _ _ _
  let Xi : HermLine ι := combLine LY ε
  let A : HermLine ι := combLine LY n
  let X₀ : HermLine Q.alg.ιW := combLine LW (i0 ε)
  let X₁ : HermLine Q.alg.ιW := combLine LW (i1 a₀ ε)
  let A₀ : HermLine Q.alg.ιW := combLine LW (i0 n)
  have hXia : Xi.a = (combLine Re.ref ε).a := by
    funext k
    show ∑ x, ε x * (Re.line x t).a k = ∑ x, ε x * (Re.ref x).a k
    simp only [Re.line_deg]
  have hsXi : IsSmoothHerm Xi := GlobalTheory.CompanionTheory.Ar.Cmp.isSmoothHerm_combLine hsY _
  have hsA : IsSmoothHerm A := GlobalTheory.CompanionTheory.Ar.Cmp.isSmoothHerm_combLine hsY _
  have hs0 : IsSmoothHerm X₀ := GlobalTheory.CompanionTheory.Ar.Cmp.isSmoothHerm_combLine hsW _
  have hs1 : IsSmoothHerm X₁ := GlobalTheory.CompanionTheory.Ar.Cmp.isSmoothHerm_combLine hsW _
  have hp0 : IsPullHerm (Q.alg.κ 0) (Q.alg.v 0) Xi X₀ :=
    pull_comb0 (Q.alg.block 0).1 LY LW ε fun a => Q.pull0 a t
  have hp1 : IsPullHerm (Q.alg.κ 1) (Q.alg.v 1) Xi X₁ :=
    pull_comb1 Q.alg hne LY LW a₀ ε (fun a => Q.pull0 a t) (Q.pull1 t) fun a h => Q.base a h t
  have hpA : IsPullHerm (Q.alg.κ 0) (Q.alg.v 0) A A₀ :=
    pull_comb0 (Q.alg.block 0).1 LY LW n fun a => Q.pull0 a t
  have hbase : FromBase Q.k₀ A := fromBase_comb LY a₀ n hn fun a h => Q.base a h t
  have hF := GlobalTheory.T.algebraic_square_base_intersection hI II hII K ι P d Q.k₀ _ Q.alg Xi X₀ X₁ hXia hsXi hp0 hp1 A A₀ hsA hbase hpA
  refine ⟨?_, fun k hk hk2 => ?_⟩
  · have h := hpol fun _ => n
    rw [h, hF.1, zero_div]

  have hc : ∀ k', 2 * ((Q.alg.dg k' : ℤ) - Q.alg.dh k') = -(X₀.a k' + X₁.a k') := by
    intro k'
    rw [Q.alg.deg_eq k', hp0.1, hp1.1, hXia]
  let Am : HermLine Q.alg.ιW :=
    GroundTheory.Heights₂.Heights.Inter.DiagRAux.halfInvLine X₀ X₁ (fun k' => (Q.alg.dg k' : ℤ) - Q.alg.dh k') hc
  have hAmS : IsSmoothHerm Am := GroundTheory.Heights₂.Heights.Inter.DiagRAux.isSmoothHerm_halfInvLine hs0 hs1 _ hc
  have hRat : IsRatSectionOn Q.alg.PW Am Q.alg.g Q.alg.h :=
    ⟨Q.alg.dg, Q.alg.dh, Q.alg.g_deg, Q.alg.h_deg, Q.alg.g_nmem, Q.alg.h_nmem, fun _ => rfl⟩
  have hAm : ∀ z ∈ mcPts Q.alg.PW, eval z (map (Int.castRingHom ℂ) (Q.alg.g * Q.alg.h)) ≠ 0 →
      logNormRat Am Q.alg.g Q.alg.h z = Q.alg.logNormT Xi z := by
    intro z hz hne'
    rw [map_mul, eval_mul] at hne'
    have hgz : ‖eval z (map (Int.castRingHom ℂ) Q.alg.g)‖ ≠ 0 :=
      norm_ne_zero_iff.2 (left_ne_zero_of_mul hne')
    have hhz : ‖eval z (map (Int.castRingHom ℂ) Q.alg.h)‖ ≠ 0 :=
      norm_ne_zero_iff.2 (right_ne_zero_of_mul hne')
    have h0 := X₀.pos z hz.1
    have h1 := X₁.pos z hz.1
    have hAmz : Am.h z = (X₀.h z * X₁.h z) ^ (-(1 / 2 : ℝ)) :=
      GroundTheory.Heights₂.Heights.Inter.DiagRAux.halfInvLine_h_of_pos _ _ _ _ z hz.1
    unfold logNormRat AlgSq.logNormT
    rw [hAmz, Real.log_div (div_ne_zero hgz hhz) (Real.rpow_pos_of_pos (mul_pos h0 h1) _).ne',
      Real.log_rpow (mul_pos h0 h1), Real.log_mul h0.ne' h1.ne', hp0.2 z, hp1.2 z]
    ring
  have hkey := fun c => SqAt.pts_eq_polar hI.resExists Q ht ht' Am hAmS hRat hAm c

  let cst : (Option σ → ℤ) → Option σ → ℝ := fun f o => (f o : ℝ)
  have hc0 : ∀ c : σ → ℤ, cst (i0 c) = Q.an.pull0 fun a => (c a : ℝ) := by
    intro c
    funext o
    cases o <;> simp [cst, i0, AnSq.pull0]
  have hc1 : cst (i1 a₀ ε) = Q.an.pull1 fun a => (ε a : ℝ) := by
    funext o
    cases o with
    | none => simp [cst, i1, AnSq.pull1]
    | some a =>
      by_cases h : a = a₀ <;> simp [cst, i1, AnSq.pull1, h]
  let Wd : ℕ → Fin (d + 1) → Option σ → ℤ := fun i => word (d + 1) k i (i0 ε) (i1 a₀ ε) (i0 n)
  have hcons : ∀ (x : Option σ → ℤ) (i : ℕ),
      (Fin.cons (combLine LW x) (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.alg.ιW) =
        fun j => combLine LW ((Fin.cons (α := fun _ => Option σ → ℤ) x (Wd i) : Fin (d + 2) → Option σ → ℤ) j) := by
    intro x i
    have e : word (d + 1) k i X₀ X₁ A₀ = fun j => combLine LW (Wd i j) :=
      word_map (combLine LW) (d + 1) k i (i0 ε) (i1 a₀ ε) (i0 n)
    rw [e]
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp
  have hcast : ∀ (x : Option σ → ℤ) (i : ℕ),
      (fun r o => (((Fin.cons (α := fun _ => Option σ → ℤ) x (Wd i) : Fin (d + 2) → Option σ → ℤ) r o : ℤ) : ℝ)) =
        Fin.cons (α := fun _ => Option σ → ℝ) (cst x)
          (word (d + 1) k i (Q.an.pull0 fun a => (ε a : ℝ)) (Q.an.pull1 fun a => (ε a : ℝ))
            (Q.an.pull0 fun a => (n a : ℝ))) := by
    intro x i
    rw [← hc0 ε, ← hc1, ← hc0 n, word_map cst]
    funext r
    refine Fin.cases ?_ (fun j => ?_) r
    · rfl
    · rfl
  have hs : ∀ i, ptsIntegral Q.alg.PW (pot (Fin.cons X₀ (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.alg.ιW))
        (Q.alg.logNormT Xi) -
      ptsIntegral Q.alg.PW (pot (Fin.cons X₁ (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.alg.ιW))
        (Q.alg.logNormT Xi) =
      (Re.deg : ℝ) * polar (d + 2) (fun w => mInt Q.an.SW.A (fun r => Q.an.SW.potT (w r) t) (Q.an.gT t))
        (Q.an.wcoef (fun a => (n a : ℝ)) k i) := by
    intro i
    rw [hcons (i0 ε) i, hcons (i1 a₀ ε) i, hkey, hkey, hcast, hcast, ← mul_sub, hc0 ε, hc1]
    unfold AnSq.wcoef
    rw [polar_cons_sub]
  have hmix : (mix (2 * k) (fun a => (ε a : ℝ)) fun a => (n a : ℝ) : Fin (d + 2) → σ → ℝ) =
      fun r a => ((mix (2 * k) ε n r : σ → ℤ) a : ℝ) := by
    funext r a
    simp only [mix]
    split_ifs <;> rfl
  have hmixL : (fun r => combLine LY ((mix (2 * k) ε n : Fin (d + 2) → σ → ℤ) r)) = mix (2 * k) Xi A := by
    funext r
    simp only [mix]
    split_ifs <;> rfl
  rw [hmix, hpol, hmixL, hF.2 k hk hk2, Finset.sum_congr rfl fun i _ => hs i, ← Finset.mul_sum]
  field_simp

end GlobalTheory.CompanionTheory.Ar.PB
