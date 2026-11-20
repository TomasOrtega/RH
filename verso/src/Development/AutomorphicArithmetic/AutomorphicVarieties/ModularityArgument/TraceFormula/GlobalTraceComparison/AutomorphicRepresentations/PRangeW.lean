import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

/- English proof (translation)
Unfold `ac`. Rewrite using `[zero_div, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_zero]`. Both sides reduce to the same expression.
-/
private theorem ac_zero (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : ac E n 0 = 1 := by
  unfold ac
  rw [zero_div, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_zero]
  rfl

/- English proof (translation)
Establish `e : trM Φ M = ∑ i, ∑ j, fun y => Φ i j y * M j i`. Use function extensionality and compare the values at `y`. Simplify using `[trM, Finset.sum_apply]`. Prove the components needed by the constructor for the conclusion. Conclude with `continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => (hΦ i j).1.mul continuous_const`.

Rewrite using `[e]`. Conclude with `HasCompactSupport.finset_sum fun i _ => HasCompactSupport.finset_sum fun j _ => (hΦ i j).2.mul_right`.
-/
private theorem test_trM {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]
    {Φ : Matrix ι ι (H E n 0 → ℂ)} (hΦ : IsTestM Φ) (M : Matrix ι ι ℂ) :
    Continuous (trM Φ M) ∧ HasCompactSupport (trM Φ M) := by
  have e : trM Φ M = ∑ i, ∑ j, fun y => Φ i j y * M j i := by
    funext y
    simp [trM, Finset.sum_apply]
  constructor
  · exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => (hΦ i j).1.mul continuous_const
  · rw [e]
    exact HasCompactSupport.finset_sum fun i _ => HasCompactSupport.finset_sum fun j _ => (hΦ i j).2.mul_right

/- English proof (translation)
Take `⟨R, hR⟩` from `(hc.isCompact.image (continuous_abs.comp (continuous_ldet (E := E) (n := n)))).bddAbove`. Take `⟨N, hN⟩` from `exists_nat_ge R`. Conclude with `⟨N, fun z hz => (hR ⟨z, subset_tsupport _ hz, rfl⟩).trans hN⟩`.
-/
private theorem ldet_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {φ : H E n 0 → ℂ}
    (hc : HasCompactSupport φ) : ∃ N : ℕ, ∀ z, φ z ≠ 0 → |ldet z| ≤ N := by
  obtain ⟨R, hR⟩ := (hc.isCompact.image (continuous_abs.comp (continuous_ldet (E := E) (n := n)))).bddAbove
  obtain ⟨N, hN⟩ := exists_nat_ge R
  exact ⟨N, fun z hz => (hR ⟨z, subset_tsupport _ hz, rfl⟩).trans hN⟩

/- English proof (translation)
The claim follows from `Complex.continuous_ofReal.comp (Dcy.continuous_chi N)`.
-/
private theorem cut_cont (N : ℕ) : Continuous fun t : ℝ => ((Dcy.chi N t : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp (Dcy.continuous_chi N)

/- English proof (translation)
The claim follows from `HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) ((N : ℝ) + 1)) fun t ht => by rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at ht rw [Dcy.chi_eq_zero ht.le, Complex.ofReal_zero]`.
-/
private theorem cut_supp (N : ℕ) : HasCompactSupport fun t : ℝ => ((Dcy.chi N t : ℝ) : ℂ) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) ((N : ℝ) + 1)) fun t ht => by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at ht
    rw [Dcy.chi_eq_zero ht.le, Complex.ofReal_zero]

/- English proof (translation)
Introduce `hR E _ _ _ n ι _ s p hF m ψ hψ x₀ h₀`. Take `⟨N, hN⟩` from `ldet_bound (test_trM m.t s.M).2`. Use `set u : ℝ → ℂ := fun t => ((Dcy.chi N t : ℝ) : ℂ) with hu`. Establish `rep` using `fun y => hR E n ι s m ψ hψ u (cut_cont N) (cut_supp N) y`. Establish `key : ∀ y : H E n 0, ldet y = 0 → ∫ x, ψ.1 x.1 * m.G y x * u (ldet x) ∂s.D.ν = ∫ z, m.φ z * ψ.1 (thetaA E n (y.1 * z.1)) ∂s.D.μ`.

Introduce `y hy`. Rewrite using `[(rep y).2]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Distinguish the cases in `hz : m.φ z = 0`. Simplify using `[hz]`.

Establish `h1 : |(-(ldet y + ldet z))| ≤ N`. Rewrite using `[hy, zero_add, abs_neg]`. Conclude with `hN z hz`. Simplify using `only [hu, Dcy.chi_eq_one h1, Complex.ofReal_one, mul_one]`. Rewrite using `[← key x₀ h₀]`.

Establish `hG : ∀ x, ψ.1 x.1 * m.G x₀ x * u (ldet x) = ∑ b, (p.w b).1 x₀.1 * (ψ.1 x.1 * m.G (p.x b) x * u (ldet x))`. Introduce `x`. Rewrite using `[hF m x₀ x, h₀, ac_zero, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[one_mul]`.

Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[hG]`. Rewrite using `[integral_finset_sum _ fun b _ => ((rep (p.x b)).1).const_mul _]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[integral_const_mul, key (p.x b) (p.zero b)]`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.rangeW_pf :
    Rep → RangeW := by
  intro hR E _ _ _ n ι _ s p hF m ψ hψ x₀ h₀
  obtain ⟨N, hN⟩ := ldet_bound (test_trM m.t s.M).2
  set u : ℝ → ℂ := fun t => ((Dcy.chi N t : ℝ) : ℂ) with hu
  have rep := fun y => hR E n ι s m ψ hψ u (cut_cont N) (cut_supp N) y
  have key : ∀ y : H E n 0, ldet y = 0 →
      ∫ x, ψ.1 x.1 * m.G y x * u (ldet x) ∂s.D.ν = ∫ z, m.φ z * ψ.1 (thetaA E n (y.1 * z.1)) ∂s.D.μ := by
    intro y hy
    rw [(rep y).2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : m.φ z = 0
    · simp [hz]
    · have h1 : |(-(ldet y + ldet z))| ≤ N := by
        rw [hy, zero_add, abs_neg]
        exact hN z hz
      simp only [hu, Dcy.chi_eq_one h1, Complex.ofReal_one, mul_one]
  rw [← key x₀ h₀]
  have hG : ∀ x, ψ.1 x.1 * m.G x₀ x * u (ldet x) =
      ∑ b, (p.w b).1 x₀.1 * (ψ.1 x.1 * m.G (p.x b) x * u (ldet x)) := by
    intro x
    rw [hF m x₀ x, h₀, ac_zero, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [one_mul]
    ring
  simp_rw [hG]
  rw [integral_finset_sum _ fun b _ => ((rep (p.x b)).1).const_mul _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, key (p.x b) (p.zero b)]

end
