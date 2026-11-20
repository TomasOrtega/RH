import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.CutRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.ContinuousLeviUnipotentPath
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.UnipMemIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PairFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LocFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TruncEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.HeckeP

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

/- English proof (translation)
Establish `a : ∀ u, P (J u) = J u` using `fun u => by`. Establish `k : P (J u - P (J u)) = 0`. Rewrite using `[map_sub, sub_eq_zero]`. Conclude with `(DFunLike.congr_fun h2 (J u)).symm`. Establish `e : ⟪J u - P (J u), J u - P (J u)⟫_ℂ = 0`.

Rewrite using `[inner_sub_left, h3 _ k, h1.isSymmetric.apply_clm, k, inner_zero_right, sub_zero]`. Conclude with `(sub_eq_zero.1 (inner_self_eq_zero.1 e)).symm`. Use `⟨a, fun h => ext_inner_left ℂ fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right, ← h1.isSymmetric.apply_clm, a]`.
-/
private theorem fix_of {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (J : V →L[ℂ] H) (P : H →L[ℂ] H)
    (h1 : IsSelfAdjoint P) (h2 : P ∘L P = P) (h3 : ∀ h, P h = 0 → ∀ u, ⟪J u, h⟫_ℂ = 0) :
    (∀ u, P (J u) = J u) ∧ ∀ h, ContinuousLinearMap.adjoint J (P h) = ContinuousLinearMap.adjoint J h := by
  have a : ∀ u, P (J u) = J u := fun u => by
    have k : P (J u - P (J u)) = 0 := by
      rw [map_sub, sub_eq_zero]; exact (DFunLike.congr_fun h2 (J u)).symm
    have e : ⟪J u - P (J u), J u - P (J u)⟫_ℂ = 0 := by
      rw [inner_sub_left, h3 _ k, h1.isSymmetric.apply_clm, k, inner_zero_right, sub_zero]
    exact (sub_eq_zero.1 (inner_self_eq_zero.1 e)).symm
  refine ⟨a, fun h => ext_inner_left ℂ fun u => ?_⟩
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
    ← h1.isSymmetric.apply_clm, a]

/- English proof (translation)
Establish `c` using `cutLaws (V := V) (Ioi T) (Ioi T) measurableSet_Ioi measurableSet_Ioi`. Establish `e : cut V (Ioi T) (cut V (Ioi T) u) = cut V (Ioi T) u`. Use `DFunLike.congr_fun c.1 u` as an intermediate fact. Rewrite `this` using `[inter_self]`. Then use the resulting hypothesis. Use `filter_upwards [(c.2.2.2.2.2.2.2.1 _).1 e] with x hx h`.

Conclude with `hx (not_lt.2 h)`.
-/
private theorem cut_van {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]
    (T : ℝ) (u : L V) : ∀ᵐ x : ℝ, x ≤ T → cut V (Ioi T) u x = 0 := by
  have c := cutLaws (V := V) (Ioi T) (Ioi T) measurableSet_Ioi measurableSet_Ioi
  have e : cut V (Ioi T) (cut V (Ioi T) u) = cut V (Ioi T) u := by
    have := DFunLike.congr_fun c.1 u
    rwa [inter_self] at this
  filter_upwards [(c.2.2.2.2.2.2.2.1 _).1 e] with x hx h
  exact hx (not_lt.2 h)

/- English proof (translation)
Establish `fin : ∀ G : G1 K (2 + 2) → ℂ, (Function.support fun q : Cos K => hi T G ((q.out : G1 K (2 + 2)) * x)).Finite` using `fun G => by`. Use `(locFin {x} T isCompact_singleton).subset fun q hq => ⟨x, rfl, ?_⟩` and prove the remaining obligations. Establish `h1 : ((q.out : G1 K (2 + 2)) * x) ∈ {z : G1 K (2 + 2) | T < HH z}` using `Set.mem_of_indicator_ne_zero (f := G) hq`. Conclude with `le_of_lt h1`. Unfold `th`.

Rewrite using `[← finsum_add_distrib (fin F₁) (fin F₂)]`. Use `finsum_congr fun q => ?_` and prove the remaining obligations. Establish `: F = F₁ + F₂` using `funext h`. Substitute `this` using the available equality. Unfold `hi`.

Rewrite using `[Set.indicator_add']`. Both sides reduce to the same expression.
-/
private theorem th_hi_add {K : Type} [Field K] [NumberField K] (T : ℝ) (F F₁ F₂ : G1 K (2 + 2) → ℂ)
    (h : ∀ z, F z = F₁ z + F₂ z) (x : G1 K (2 + 2)) : th (hi T F) x = th (hi T F₁) x + th (hi T F₂) x := by
  have fin : ∀ G : G1 K (2 + 2) → ℂ,
      (Function.support fun q : Cos K => hi T G ((q.out : G1 K (2 + 2)) * x)).Finite := fun G => by
    refine (locFin {x} T isCompact_singleton).subset fun q hq => ⟨x, rfl, ?_⟩
    have h1 : ((q.out : G1 K (2 + 2)) * x) ∈ {z : G1 K (2 + 2) | T < HH z} :=
      Set.mem_of_indicator_ne_zero (f := G) hq
    exact le_of_lt h1
  unfold th
  rw [← finsum_add_distrib (fin F₁) (fin F₂)]
  refine finsum_congr fun q => ?_
  have : F = F₁ + F₂ := funext h
  subst this
  unfold hi
  rw [Set.indicator_add']
  rfl

/- English proof (translation)
Introduce `K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' P Λ T hP hT hΛ`. Establish `hp' : Pair μ₂ τ₂ τ₁` using `⟨hp.irr₂, hp.irr₁, hp.orth.symm⟩`. Establish `hc` using `(pairFacts K μ μ₂ τ₁ τ₂ hp D d d' A A').2`. Establish `ho : ∀ u v, ⟪A.J (cut (Eu d) (Ioi T) u), A'.J (cut (Eu d') (Ioi T) v)⟫_ℂ = 0` using `fun u v => by`. Use `hc T _ _ (cut_van T u) ?_` and prove the remaining obligations.

Use `filter_upwards [cut_van T v] with x hx h`. Conclude with `hx (by linarith)`. Establish `hL` using `(truncEq A.J A'.J T Λ ho).1 hΛ`. Establish `hv : ∀ w, Λ w = w - A.J (cut (Eu d) (Ioi T) (Jd A.J w)) - A'.J (cut (Eu d') (Ioi T) (Jd A'.J w))` using `fun w => by`. Rewrite using `[hL]`.

Both sides reduce to the same expression. Establish `hae : ∀ w : L2 μ, ∀ᵐ y ∂μ, (Λ w : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y) = (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y) - (A.J (cut (Eu d) (Ioi T) (Jd A.J w)) : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y) - (A'.J (cut (Eu d …` using `fun w => by`. Rewrite using `[hv w]`. Use `filter_upwards [(quasiMeasurePreserving_mk (Gam K (2 + 2)) μ).ae (Lp.coeFn_sub (w - A.J (cut (Eu d) (Ioi T) (Jd A.J w))) (A'.J (cut (Eu d') (Ioi T) (Jd A'.J w)))), (quasiMeasurePreserving_mk (Gam K (2 + 2)) μ).ae (Lp.coeFn_sub w (A.J (cut (Eu d) (Ioi T) (Jd A.J w))))] with y e1 e …`. Rewrite using `[e1, Pi.sub_apply, e2, Pi.sub_apply]`.

Take `⟨f1, g1⟩` from `fix_of A.J.toContinuousLinearMap P hP.1 hP.2.1 fun h hh => ((hP.2.2 h).1 hh).1`. Take `⟨f2, g2⟩` from `fix_of A'.J.toContinuousLinearMap P hP.1 hP.2.1 fun h hh => ((hP.2.2 h).1 hh).2`. Establish `c1` using `cutRep K μ μ₂ τ₁ τ₂ hp D d d' A A' T`. Establish `c2` using `cutRep K μ μ₂ τ₂ τ₁ hp' D d' d A' A T`. Use `⟨ContinuousLinearMap.ext fun h => ?_, fun w => ?_, fun a ha φ hφ => ?_⟩` and prove the remaining obligations.

Rewrite using `[ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hv, hv, map_sub, map_sub]`. Establish `a1` using `f1 (cut (Eu d) (Ioi T) (Jd A.J h))`. Establish `a2` using `f2 (cut (Eu d') (Ioi T) (Jd A'.J h))`. Establish `b1 : Jd A.J (P h) = Jd A.J h` using `g1 h`. Establish `b2 : Jd A'.J (P h) = Jd A'.J h` using `g2 h`.

Rewrite `a1`, `a2` using `[LinearIsometry.coe_toContinuousLinearMap]`. Rewrite using `[a1, a2, b1, b2]`. Use `filter_upwards [hae w, (c1 (Jd A.J w)).1, (c2 (Jd A'.J w)).1] with y e e1 e2 hy`. Rewrite using `[e, e1 hy, e2 hy, sub_zero, sub_zero]`. Take `⟨C, hC⟩` from `ctRep K μ μ₂ τ₁ τ₂ hp D d d' A A' a P hP ha`.

Take `⟨U, U', hU, hU', -, r1, r2, hct⟩` from `hC φ hφ`. Use `filter_upwards [hae (Rop μ a φ), (c1 _).2 U hU r1, (c2 _).2 U' hU' r2, ((ctKv μ a).2 φ).2.1] with y e e1 e2 e3`. Rewrite using `[e, e1, e2, e3, lam, th_hi_add T _ _ _ hct, sub_sub]`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.lamRep :
    ForAllC fun K _ _ μ _ _ _ _ _ D _ _ A A' => ∀ (P Λ : L2 μ →L[ℂ] L2 μ) (T : ℝ), IsOrthogonalProjectionTwoLines A.J A'.J P → 0 ≤ T → IsTrunc A.J A'.J T Λ →
      Λ ∘L P = P ∘L Λ ∧ (∀ w : L2 μ, ∀ᵐ y ∂μ, Om T y → (Λ w : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y) =
        (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y)) ∧
      ∀ a : CC K (2 + 2), D.Hecke a → ∀ φ, P φ = φ → Reps μ (Λ (Rop μ a φ)) (lam T (rc μ a φ)) := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' P Λ T hP hT hΛ
  have hp' : Pair μ₂ τ₂ τ₁ := ⟨hp.irr₂, hp.irr₁, hp.orth.symm⟩
  have hc := (pairFacts K μ μ₂ τ₁ τ₂ hp D d d' A A').2
  have ho : ∀ u v, ⟪A.J (cut (Eu d) (Ioi T) u), A'.J (cut (Eu d') (Ioi T) v)⟫_ℂ = 0 := fun u v => by
    refine hc T _ _ (cut_van T u) ?_
    filter_upwards [cut_van T v] with x hx h
    exact hx (by linarith)
  have hL := (truncEq A.J A'.J T Λ ho).1 hΛ
  have hv : ∀ w, Λ w = w - A.J (cut (Eu d) (Ioi T) (Jd A.J w)) - A'.J (cut (Eu d') (Ioi T) (Jd A'.J w)) := fun w => by
    rw [hL]; rfl
  have hae : ∀ w : L2 μ, ∀ᵐ y ∂μ, (Λ w : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y) =
      (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y) -
      (A.J (cut (Eu d) (Ioi T) (Jd A.J w)) : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y) -
      (A'.J (cut (Eu d') (Ioi T) (Jd A'.J w)) : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y) := fun w => by
    rw [hv w]
    filter_upwards [(quasiMeasurePreserving_mk (Gam K (2 + 2)) μ).ae (Lp.coeFn_sub
        (w - A.J (cut (Eu d) (Ioi T) (Jd A.J w))) (A'.J (cut (Eu d') (Ioi T) (Jd A'.J w)))),
      (quasiMeasurePreserving_mk (Gam K (2 + 2)) μ).ae (Lp.coeFn_sub w (A.J (cut (Eu d) (Ioi T) (Jd A.J w))))] with y e1 e2
    rw [e1, Pi.sub_apply, e2, Pi.sub_apply]
  obtain ⟨f1, g1⟩ := fix_of A.J.toContinuousLinearMap P hP.1 hP.2.1 fun h hh => ((hP.2.2 h).1 hh).1
  obtain ⟨f2, g2⟩ := fix_of A'.J.toContinuousLinearMap P hP.1 hP.2.1 fun h hh => ((hP.2.2 h).1 hh).2
  have c1 := cutRep K μ μ₂ τ₁ τ₂ hp D d d' A A' T
  have c2 := cutRep K μ μ₂ τ₂ τ₁ hp' D d' d A' A T
  refine ⟨ContinuousLinearMap.ext fun h => ?_, fun w => ?_, fun a ha φ hφ => ?_⟩
  · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hv, hv, map_sub, map_sub]
    have a1 := f1 (cut (Eu d) (Ioi T) (Jd A.J h))
    have a2 := f2 (cut (Eu d') (Ioi T) (Jd A'.J h))
    have b1 : Jd A.J (P h) = Jd A.J h := g1 h
    have b2 : Jd A'.J (P h) = Jd A'.J h := g2 h
    rw [LinearIsometry.coe_toContinuousLinearMap] at a1 a2
    rw [a1, a2, b1, b2]
  · filter_upwards [hae w, (c1 (Jd A.J w)).1, (c2 (Jd A'.J w)).1] with y e e1 e2 hy
    rw [e, e1 hy, e2 hy, sub_zero, sub_zero]
  · obtain ⟨C, hC⟩ := ctRep K μ μ₂ τ₁ τ₂ hp D d d' A A' a P hP ha
    obtain ⟨U, U', hU, hU', -, r1, r2, hct⟩ := hC φ hφ
    filter_upwards [hae (Rop μ a φ), (c1 _).2 U hU r1, (c2 _).2 U' hU' r2, ((ctKv μ a).2 φ).2.1] with y e e1 e2 e3
    rw [e, e1, e2, e3, lam, th_hi_add T _ _ _ hct, sub_sub]
