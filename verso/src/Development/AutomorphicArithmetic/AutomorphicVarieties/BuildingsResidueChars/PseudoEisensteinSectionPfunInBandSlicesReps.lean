import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecCrit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BfFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ThBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.DenseCc

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

/- English proof (translation)
Use `filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_smul c v), h] with y e1 e2`. Rewrite using `[e1, Pi.smul_apply, e2, smul_eq_mul]`.
-/
private theorem reps_const {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    {v : L2 μ} {φ : G1 K n → ℂ} (c : ℂ) (h : Reps μ v φ) : Reps μ (c • v) (fun y => c * φ y) := by
  filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_smul c v), h] with y e1 e2
  rw [e1, Pi.smul_apply, e2, smul_eq_mul]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_zero ℂ 2 (quotientMeasure (Gam K n) μ))] with y e`. Simplify using `using e`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi]`.

Use `filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_add (v i) (∑ j ∈ s, v j)), ih, h i] with y e1 e2 e3`. Rewrite using `[e1, Pi.add_apply, e2, e3, Finset.sum_insert hi]`.
-/
private theorem reps_finsum {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    {ι : Type} (s : Finset ι) (v : ι → L2 μ) (φ : ι → G1 K n → ℂ) (h : ∀ i, Reps μ (v i) (φ i)) :
    Reps μ (∑ i ∈ s, v i) (fun y => ∑ i ∈ s, φ i y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_zero ℂ 2 (quotientMeasure (Gam K n) μ))] with y e
    simpa using e
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_add (v i) (∑ j ∈ s, v j)), ih, h i] with y e1 e2 e3
    rw [e1, Pi.add_apply, e2, e3, Finset.sum_insert hi]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => filter_upwards [Lp.coeFn_zero (Eu d) 2 (volume : Measure ℝ)] with x e`. Simplify using `using e`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi]`.

Use `filter_upwards [Lp.coeFn_add (W i) (∑ j ∈ s, W j), ih] with x e1 e2`. Rewrite using `[e1, Pi.add_apply, e2, Finset.sum_insert hi]`.
-/
private theorem coe_lsum {d : ℕ} {ι : Type} (s : Finset ι) (W : ι → L (Eu d)) :
    ∀ᵐ x : ℝ, (∑ i ∈ s, W i : L (Eu d)) x = ∑ i ∈ s, W i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero (Eu d) 2 (volume : Measure ℝ)] with x e
    simpa using e
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (W i) (∑ j ∈ s, W j), ih] with x e1 e2
    rw [e1, Pi.add_apply, e2, Finset.sum_insert hi]

/- English proof (translation)
Introduce `K _ _ _ μ _ μ₂ _ τ₁ τ₂ D d A h₁ h₂ u F hu hcs hF`. Establish `hsec : ∀ v, IsSec τ₁ τ₂ (A.sec v) ∧ D.Fix (A.sec v)` using `fun v => (A.onto _).1 ⟨v, rfl⟩`. Establish `hS : ∀ v, SFun (A.sec v)` using `fun v => secFun μ₂ τ₁ τ₂ D h₁ h₂ _ (hsec v).1 (hsec v).2`. Take `⟨h1, -, h3, -, -⟩` from `hpSpec (K := K)`. Take `⟨-, -, hl, -⟩` from `blkLaws (K := K)`.

Establish `hn : ∀ (X : AutomorphicForm.UPos (2 + 2) 2 → _) (g : G1 K (2 + 2)), HH (nn X * g) = HH g` using `fun X g => by`. Use `h1 X 1 1 0 g` as an intermediate fact. Rewrite `this` using `[hl, mul_one, zero_add]`. Then use the resulting hypothesis. Establish `hm : ∀ (m₁ m₂ : G1 K 2) (g : G1 K (2 + 2)), HH (lv m₁ m₂ 0 * g) = HH g` using `fun m₁ m₂ g => by`. Use `h1 0 m₁ m₂ 0 g` as an intermediate fact.

Rewrite `this` using `[mul_assoc, hn, zero_add]`. Then use the resulting hypothesis. Take `⟨e, he⟩ : ∃ e : Fin d → Eu d, e = fun i => EuclideanSpace.single i 1` from `⟨_, rfl⟩`. Take `⟨β, hβ⟩ : ∃ β : Fin d → ℝ → ℂ, β = fun i x => u x i` from `⟨_, rfl⟩`. Establish `hβc : ∀ i, Continuous (β i)` using `fun i => by`. Rewrite using `[hβ]`.

Conclude with `(EuclideanSpace.proj i : Eu d →L[ℂ] ℂ).continuous.comp hu`. Establish `hβs : ∀ i, HasCompactSupport (β i)` using `fun i => by`. Rewrite using `[hβ]`. Conclude with `hcs.comp_left (g := fun w : Eu d => w i) rfl`. Establish `hexp : ∀ x, u x = ∑ i, β i x • e i` using `fun x => by`.

Use extensionality with `j`. Simplify using `[hβ, he, Finset.sum_apply, Pi.single_apply]`. Establish `hFs : ∀ g, F g = ∑ i, bf (β i) (A.sec (e i)) g` using `fun g => by`. Rewrite using `[hF, hexp (HH g), map_sum, Finset.sum_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, Pi.smul_apply, smul_eq_mul, bf]`. Establish `: ((((2 + 2 : ℕ) : ℝ) / 2 * HP 2 2 g : ℝ) : ℂ) = 2 * (HH g : ℂ)`. Use `push_cast`. Evaluate the numerical expressions. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hB` using `fun i => bfFun (A.sec (e i)) (β i) (hS _) (hβc i) (hβs i)`. Use `⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[show F = fun g => ∑ i, bf (β i) (A.sec (e i)) g from funext hFs]`. Conclude with `continuous_finset_sum _ fun i _ => (hB i).1.cont`.

Use `choose C hC using fun i => (hB i).1.bdd`. Use `⟨∑ i, C i, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[hFs]`. Conclude with `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hC i g)`. Introduce `X g`.

Rewrite using `[hF, hF, hn, (hS _).unip]`. Introduce `γ hγ g`. Rewrite using `[hF, hF, h3 γ hγ, (hS _).rat γ hγ]`. Introduce `g`. Repeatedly rewrite using `[hF, hm]`.

Rewrite using `[integral_const_mul, (hS _).cusp₁ g, mul_zero]`. Introduce `g`. Repeatedly rewrite using `[hF, hm]`. Rewrite using `[integral_const_mul, (hS _).cusp₂ g, mul_zero]`. Take `⟨R, hR⟩` from `hcs.isCompact.isBounded.exists_norm_le`.

Use `⟨R, fun g hg => ?_⟩` and prove the remaining obligations. Establish `hne : u (HH g) ≠ 0` using `fun h0 => hg (by rw [hF, h0, map_zero]; simp)`. Conclude with `hR _ (subset_tsupport u hne)`. Introduce `g`. Establish `hsl` using `fun v => (secCrit μ₂ τ₁ τ₂ D h₁ h₂ (A.sec v) (hsec v).2).1 (hsec v).1`.

Establish `hv : ∀ m₁ m₂, F (lv m₁ m₂ 0 * g) = Complex.exp (2 * (HH g : ℂ)) * A.sec (u (HH g)) (lv m₁ m₂ 0 * g)` using `fun m₁ m₂ => by`. Rewrite using `[hF, hm]`. Take `⟨-, -, -, -, hs⟩` from `hsl (u (HH g))`. Use `⟨fun m₂ => ?_, fun m₁ => ?_⟩` and prove the remaining obligations. Take `⟨v, hvτ, hr⟩` from `(hs g).1 m₂`.

Conclude with `⟨_, τ₁.smul_mem (Complex.exp (2 * (HH g : ℂ))) hvτ, by simpa only [hv] using reps_const μ₂ _ hr⟩`. Take `⟨v, hvτ, hr⟩` from `(hs g).2 m₁`. Conclude with `⟨_, τ₂.smul_mem (Complex.exp (2 * (HH g : ℂ))) hvτ, by simpa only [hv] using reps_const μ₂ _ hr⟩`. Introduce `U hU choose W hW using fun i => (denseCc d).2.1 (β i) (e i) (hβc i) (hβs i)`. Establish `hUW : U = ∑ i, W i`.

Use `Lp.ext ?_` and prove the remaining obligations. Establish `hall : ∀ᵐ x : ℝ, ∀ i, W i x = β i x • e i` using `ae_all_iff.2 hW`. Use `filter_upwards [hU, coe_lsum Finset.univ W, hall] with x a1 a2 a3`. Rewrite using `[a1, a2, hexp x]`. Conclude with `Finset.sum_congr rfl fun i _ => (a3 i).symm`.

Establish `hth : th F = fun y => ∑ i, theta (β i) (A.sec (e i)) y`. Use function extensionality and compare the values at `y`. Rewrite using `[th]`. Repeatedly rewrite using `[hFs, theta_eq, th]`. Use `finsum_sum_comm _ _ fun i _ => ?_` and prove the remaining obligations.

Establish `hfin` using `(thBasic μ _ (hB i).1.cont (hB i).1.rat (hB i).2.1).1 {y} isCompact_singleton`. Conclude with `hfin.subset fun q hq => ⟨y, rfl, hq⟩`. Rewrite using `[hUW, map_sum, hth]`. Conclude with `reps_finsum μ _ _ _ fun i => A.spec (β i) (e i) (W i) (hβc i) (hβs i) (hW i)`.
-/
theorem UpperTheory.pseudoEisenstein_section_pfun_inBand_slices_reps :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (D : TypeDat K (2 + 2)) {d : ℕ} (A : Line μ τ₁ τ₂ D d), CuspIrr μ₂ τ₁ → CuspIrr μ₂ τ₂ →
          ∀ (u : ℝ → Eu d) (F : G1 K (2 + 2) → ℂ), Continuous u → HasCompactSupport u → (∀ g, F g = Complex.exp (2 * (HH g : ℂ)) * A.sec (u (HH g)) g) →
            PFun F ∧ InBand F ∧ Slices τ₁ τ₂ F ∧ ∀ U : L (Eu d), (∀ᵐ x : ℝ, U x = u x) → Reps μ (A.J U) (th F) := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ D d A h₁ h₂ u F hu hcs hF
  have hsec : ∀ v, IsSec τ₁ τ₂ (A.sec v) ∧ D.Fix (A.sec v) := fun v => (A.onto _).1 ⟨v, rfl⟩
  have hS : ∀ v, SFun (A.sec v) := fun v => secFun μ₂ τ₁ τ₂ D h₁ h₂ _ (hsec v).1 (hsec v).2
  obtain ⟨h1, -, h3, -, -⟩ := hpSpec (K := K)
  obtain ⟨-, -, hl, -⟩ := blkLaws (K := K)
  have hn : ∀ (X : AutomorphicForm.UPos (2 + 2) 2 → _) (g : G1 K (2 + 2)), HH (nn X * g) = HH g := fun X g => by
    have := h1 X 1 1 0 g
    rwa [hl, mul_one, zero_add] at this
  have hm : ∀ (m₁ m₂ : G1 K 2) (g : G1 K (2 + 2)), HH (lv m₁ m₂ 0 * g) = HH g := fun m₁ m₂ g => by
    have := h1 0 m₁ m₂ 0 g
    rwa [mul_assoc, hn, zero_add] at this

  obtain ⟨e, he⟩ : ∃ e : Fin d → Eu d, e = fun i => EuclideanSpace.single i 1 := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : Fin d → ℝ → ℂ, β = fun i x => u x i := ⟨_, rfl⟩
  have hβc : ∀ i, Continuous (β i) := fun i => by
    rw [hβ]
    exact (EuclideanSpace.proj i : Eu d →L[ℂ] ℂ).continuous.comp hu
  have hβs : ∀ i, HasCompactSupport (β i) := fun i => by
    rw [hβ]
    exact hcs.comp_left (g := fun w : Eu d => w i) rfl
  have hexp : ∀ x, u x = ∑ i, β i x • e i := fun x => by
    ext j
    simp [hβ, he, Finset.sum_apply, Pi.single_apply]
  have hFs : ∀ g, F g = ∑ i, bf (β i) (A.sec (e i)) g := fun g => by
    rw [hF, hexp (HH g), map_sum, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, bf]
    have : ((((2 + 2 : ℕ) : ℝ) / 2 * HP 2 2 g : ℝ) : ℂ) = 2 * (HH g : ℂ) := by
      push_cast
      norm_num
    rw [this]
    ring
  have hB := fun i => bfFun (A.sec (e i)) (β i) (hS _) (hβc i) (hβs i)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [show F = fun g => ∑ i, bf (β i) (A.sec (e i)) g from funext hFs]
    exact continuous_finset_sum _ fun i _ => (hB i).1.cont
  · choose C hC using fun i => (hB i).1.bdd
    refine ⟨∑ i, C i, fun g => ?_⟩
    rw [hFs]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hC i g)
  · intro X g
    rw [hF, hF, hn, (hS _).unip]
  · intro γ hγ g
    rw [hF, hF, h3 γ hγ, (hS _).rat γ hγ]
  · intro g
    simp_rw [hF, hm]
    rw [integral_const_mul, (hS _).cusp₁ g, mul_zero]
  · intro g
    simp_rw [hF, hm]
    rw [integral_const_mul, (hS _).cusp₂ g, mul_zero]
  · obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.exists_norm_le
    refine ⟨R, fun g hg => ?_⟩
    have hne : u (HH g) ≠ 0 := fun h0 => hg (by rw [hF, h0, map_zero]; simp)
    exact hR _ (subset_tsupport u hne)
  · intro g
    have hsl := fun v => (secCrit μ₂ τ₁ τ₂ D h₁ h₂ (A.sec v) (hsec v).2).1 (hsec v).1
    have hv : ∀ m₁ m₂, F (lv m₁ m₂ 0 * g) = Complex.exp (2 * (HH g : ℂ)) * A.sec (u (HH g)) (lv m₁ m₂ 0 * g) := fun m₁ m₂ => by
      rw [hF, hm]
    obtain ⟨-, -, -, -, hs⟩ := hsl (u (HH g))
    refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨v, hvτ, hr⟩ := (hs g).1 m₂
      exact ⟨_, τ₁.smul_mem (Complex.exp (2 * (HH g : ℂ))) hvτ, by simpa only [hv] using reps_const μ₂ _ hr⟩
    · obtain ⟨v, hvτ, hr⟩ := (hs g).2 m₁
      exact ⟨_, τ₂.smul_mem (Complex.exp (2 * (HH g : ℂ))) hvτ, by simpa only [hv] using reps_const μ₂ _ hr⟩
  · intro U hU
    choose W hW using fun i => (denseCc d).2.1 (β i) (e i) (hβc i) (hβs i)
    have hUW : U = ∑ i, W i := by
      refine Lp.ext ?_
      have hall : ∀ᵐ x : ℝ, ∀ i, W i x = β i x • e i := ae_all_iff.2 hW
      filter_upwards [hU, coe_lsum Finset.univ W, hall] with x a1 a2 a3
      rw [a1, a2, hexp x]
      exact Finset.sum_congr rfl fun i _ => (a3 i).symm
    have hth : th F = fun y => ∑ i, theta (β i) (A.sec (e i)) y := by
      funext y
      rw [th]
      simp_rw [hFs, theta_eq, th]
      refine finsum_sum_comm _ _ fun i _ => ?_
      have hfin := (thBasic μ _ (hB i).1.cont (hB i).1.rat (hB i).2.1).1 {y} isCompact_singleton
      exact hfin.subset fun q hq => ⟨y, rfl, hq⟩
    rw [hUW, map_sum, hth]
    exact reps_finsum μ _ _ _ fun i => A.spec (β i) (e i) (W i) (hβc i) (hβs i) (hW i)
