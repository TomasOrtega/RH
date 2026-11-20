import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

/- English proof (translation)
Take `⟨A, hA, h1, h2⟩` from `rowInt X φ hφ`. Establish `hm : Measurable (Function.uncurry (ker X.Γ φ))` using `(kerBasic X φ hφ).2.1.measurable`. Establish `hν : SFinite X.ν` using `by unfold Ctx.ν; infer_instance`. Establish `hP` using `schurInt X.G X.ν (ker X.Γ φ) A hm hA h1 h2 g f hg hf`. Establish `e1 : ∀ y, ∫ z, g z * ker X.Γ φ z y * f y ∂X.ν = (∫ z, g z * ker X.Γ φ z y ∂X.ν) * f y` using `fun y => integral_mul_const _ _`.

Establish `e2 : ∀ z, ∫ y, g z * ker X.Γ φ z y * f y ∂X.ν = g z * ∫ y, ker X.Γ φ z y * f y ∂X.ν` using `fun z => by`. Repeatedly rewrite using `[mul_assoc]`. Conclude with `integral_const_mul _ _`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Simplify `hP.integral_prod_right` using `only [e1]`.

Simplify `hP.integral_prod_left` using `only [e2]`. Repeatedly rewrite using `[← e1, ← e2]`. Conclude with `(integral_integral_swap (f := fun z y => g z * ker X.Γ φ z y * f y) hP).symm`.
-/
private theorem ctx_fub (X : Ctx) (φ : X.G → ℂ) (hφ : Tst φ) (g f : X.G → ℂ) (hg : MemLp g 2 X.ν) (hf : MemLp f 2 X.ν) :
    Integrable (fun y => (∫ z, g z * ker X.Γ φ z y ∂X.ν) * f y) X.ν ∧
      Integrable (fun z => g z * ∫ y, ker X.Γ φ z y * f y ∂X.ν) X.ν ∧
      ∫ y, (∫ z, g z * ker X.Γ φ z y ∂X.ν) * f y ∂X.ν = ∫ z, g z * ∫ y, ker X.Γ φ z y * f y ∂X.ν ∂X.ν := by
  obtain ⟨A, hA, h1, h2⟩ := rowInt X φ hφ
  have hm : Measurable (Function.uncurry (ker X.Γ φ)) := (kerBasic X φ hφ).2.1.measurable
  have hν : SFinite X.ν := by unfold Ctx.ν; infer_instance
  have hP := schurInt X.G X.ν (ker X.Γ φ) A hm hA h1 h2 g f hg hf
  have e1 : ∀ y, ∫ z, g z * ker X.Γ φ z y * f y ∂X.ν = (∫ z, g z * ker X.Γ φ z y ∂X.ν) * f y :=
    fun y => integral_mul_const _ _
  have e2 : ∀ z, ∫ y, g z * ker X.Γ φ z y * f y ∂X.ν = g z * ∫ y, ker X.Γ φ z y * f y ∂X.ν := fun z => by
    simp_rw [mul_assoc]; exact integral_const_mul _ _
  refine ⟨?_, ?_, ?_⟩
  · simpa only [e1] using hP.integral_prod_right
  · simpa only [e2] using hP.integral_prod_left
  · simp_rw [← e1, ← e2]
    exact (integral_integral_swap (f := fun z y => g z * ker X.Γ φ z y * f y) hP).symm

/- English proof (translation)
Introduce `E _ _ _ n ι _ s v u i`. Establish `hth : ∀ y : H E n 0, th (th y) = y` using `fun y => Prod.ext (GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol _) (GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol _)`. Set `c : ι → ℂ` to `fun l => s.M l i`. Set `g : ι → H E n 0 → ℂ` to `fun j z => starRingEnd ℂ ((u j : H E n 0 → ℂ) z)`. Establish `hg : ∀ j, MemLp (g j) 2 s.D.ν` using `fun j => (Lp.memLp (u j)).star`.

Establish `F : ∀ j l, Integrable (fun y => (∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y) s.D.ν ∧ Integrable (fun z => g j z * ∫ y, kerH (s.Φ₂ j l) z y * (v : H E n 0 → ℂ) y ∂s.D.ν) s.D.ν ∧ ∫ y, (∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y ∂s.D.ν = ∫ z, …` using `fun j l => ctx_fub (ctx ratProper_holds s.D) (s.Φ₂ j l) (s.t₂ j l) (g j) v (hg j) (Lp.memLp v)`. Establish `hrep : ∀ y, (v : H E n 0 → ℂ) y * inner ℂ u (s.k₂ (th y) i) = ∑ j, ∑ l, c l * ((∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y)`. Introduce `y`. Rewrite using `[s.vecs.rep₂ (th y) i u, hth, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[integral_mul_const]`. Expand and normalize the polynomial expressions, which then agree. Establish `hv : ∀ (l : ι) (φ : H E n 0 → ℂ), ∫ y, φ y * ((vecM v c l : Lp ℂ 2 s.D.ν) : H E n 0 → ℂ) y ∂s.D.ν = c l * ∫ y, φ y * (v : H E n 0 → ℂ) y ∂s.D.ν`.

Introduce `l φ`. Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Establish `e : (vecM v c l : Lp ℂ 2 s.D.ν) = c l • v` using `rfl`. Use `filter_upwards [Lp.coeFn_smul (c l) v] with y hy`.

Rewrite using `[e, hy, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hR : inner ℂ u (s.T₂ (vecM v c)) = ∑ j, ∑ l, c l * ∫ z, g j z * ∫ y, kerH (s.Φ₂ j l) z y * (v : H E n 0 → ℂ) y ∂s.D.ν ∂s.D.ν`. Rewrite using `[PiLp.inner_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[L2.inner_def]`. Establish `h : (fun z => inner ℂ ((u j : Lp ℂ 2 s.D.ν) z) ((s.T₂ (vecM v c) j : Lp ℂ 2 s.D.ν) z)) =ᵐ[s.D.ν] fun z => ∑ l, c l * (g j z * ∫ y, kerH (s.Φ₂ j l) z y * (v : H E n 0 → ℂ) y ∂s.D.ν)` using `by filter_upwards [s.o₂ (vecM v c) j] with z hz`. Rewrite using `[hz, RCLike.inner_apply, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[hv]`.

Simplify using `only [g]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[integral_congr_ae h, integral_finset_sum _ fun l _ => (F j l).2.1.const_mul _]`. Conclude with `Finset.sum_congr rfl fun l _ => integral_const_mul _ _`. Establish `hint : Integrable (fun y => ∑ j, ∑ l, c l * ((∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y)) s.D.ν` using `integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun l _ => (F j l).1.const_mul _`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify `hint` using `only [hrep]`. Simplify using `only [hrep]`. Express the relevant statement in the definitionally equal form `_ = inner ℂ u (s.T₂ (vecM v c))`. Rewrite using `[hR, integral_finset_sum _ fun j _ => integrable_finset_sum _ fun l _ => (F j l).1.const_mul _]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[integral_finset_sum _ fun l _ => (F j l).1.const_mul _]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[integral_const_mul, (F j l).2.2]`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.weak_pf :
    Weak := by
  intro E _ _ _ n ι _ s v u i
  have hth : ∀ y : H E n 0, th (th y) = y := fun y =>
    Prod.ext (GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol _) (GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol _)
  let c : ι → ℂ := fun l => s.M l i
  let g : ι → H E n 0 → ℂ := fun j z => starRingEnd ℂ ((u j : H E n 0 → ℂ) z)
  have hg : ∀ j, MemLp (g j) 2 s.D.ν := fun j => (Lp.memLp (u j)).star
  have F : ∀ j l, Integrable (fun y => (∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y) s.D.ν ∧
      Integrable (fun z => g j z * ∫ y, kerH (s.Φ₂ j l) z y * (v : H E n 0 → ℂ) y ∂s.D.ν) s.D.ν ∧
      ∫ y, (∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y ∂s.D.ν =
        ∫ z, g j z * ∫ y, kerH (s.Φ₂ j l) z y * (v : H E n 0 → ℂ) y ∂s.D.ν ∂s.D.ν := fun j l =>
    ctx_fub (ctx ratProper_holds s.D) (s.Φ₂ j l) (s.t₂ j l) (g j) v (hg j) (Lp.memLp v)
  have hrep : ∀ y, (v : H E n 0 → ℂ) y * inner ℂ u (s.k₂ (th y) i) =
      ∑ j, ∑ l, c l * ((∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y) := by
    intro y
    rw [s.vecs.rep₂ (th y) i u, hth, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_mul_const]
    ring
  have hv : ∀ (l : ι) (φ : H E n 0 → ℂ), ∫ y, φ y * ((vecM v c l : Lp ℂ 2 s.D.ν) : H E n 0 → ℂ) y ∂s.D.ν =
      c l * ∫ y, φ y * (v : H E n 0 → ℂ) y ∂s.D.ν := by
    intro l φ
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    have e : (vecM v c l : Lp ℂ 2 s.D.ν) = c l • v := rfl
    filter_upwards [Lp.coeFn_smul (c l) v] with y hy
    rw [e, hy, Pi.smul_apply, smul_eq_mul]
    ring
  have hR : inner ℂ u (s.T₂ (vecM v c)) =
      ∑ j, ∑ l, c l * ∫ z, g j z * ∫ y, kerH (s.Φ₂ j l) z y * (v : H E n 0 → ℂ) y ∂s.D.ν ∂s.D.ν := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [L2.inner_def]
    have h : (fun z => inner ℂ ((u j : Lp ℂ 2 s.D.ν) z) ((s.T₂ (vecM v c) j : Lp ℂ 2 s.D.ν) z)) =ᵐ[s.D.ν]
        fun z => ∑ l, c l * (g j z * ∫ y, kerH (s.Φ₂ j l) z y * (v : H E n 0 → ℂ) y ∂s.D.ν) := by
      filter_upwards [s.o₂ (vecM v c) j] with z hz
      rw [hz, RCLike.inner_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hv]
      simp only [g]
      ring
    rw [integral_congr_ae h, integral_finset_sum _ fun l _ => (F j l).2.1.const_mul _]
    exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _
  have hint : Integrable (fun y => ∑ j, ∑ l, c l *
      ((∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y)) s.D.ν :=
    integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun l _ => (F j l).1.const_mul _
  refine ⟨?_, ?_⟩
  · simpa only [hrep] using hint
  · simp only [hrep]
    change _ = inner ℂ u (s.T₂ (vecM v c))
    rw [hR, integral_finset_sum _ fun j _ => integrable_finset_sum _ fun l _ => (F j l).1.const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finset_sum _ fun l _ => (F j l).1.const_mul _]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, (F j l).2.2]

end
