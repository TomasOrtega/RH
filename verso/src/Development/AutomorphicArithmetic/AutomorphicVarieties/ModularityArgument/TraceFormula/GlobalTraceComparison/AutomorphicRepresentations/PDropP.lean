import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

/- English proof (translation)
Introduce `hZ hK hB hW hR hC E _ _ _ n ι _ s m x y`. Take `⟨-, -, -, -, -, -, -, hthth, hthmul, hrat, -, hthc⟩` from `hB E n s.pos`. Use `set S := piSp s.D s.π ι with hS`. Use `set P := S.starProjection with hP`. Establish `hmem : ∀ f, P f ∈ S` using `fun f => Submodule.starProjection_apply_mem S f`.

Establish `hPP : ∀ f, P (P f) = P f` using `fun f => (Submodule.starProjection_eq_self_iff).2 (hmem f)`. Establish `hUπ : ∀ f, m.Uπ f = m.U (P f)` using `fun f => by`. Establish `h2 : f - P f ∈ Sᗮ` using `Submodule.sub_starProjection_mem_orthogonal f`. Establish `hdec : P f + (f - P f) = f` using `by abel`. Combine the equalities or inequalities in the displayed calculation.

Establish `C₁ : ∀ f, P (s.T₁ f) = s.T₁ (P f)` using `hC E n s.pos s.D s.π s.fix ι s.Φ₁ s.T₁ s.t₁ s.o₁`. Establish `C₂ : ∀ f, P (s.T₂ f) = s.T₂ (P f)` using `hC E n s.pos s.D s.π s.fix ι s.Φ₂ s.T₂ s.t₂ s.o₂`. Establish `C₃ : ∀ f, P ((s.T₁ * m.U * s.T₂) f) = (s.T₁ * m.U * s.T₂) (P f)` using `hC E n s.pos s.D s.π s.fix ι m.Φ (s.T₁ * m.U * s.T₂) m.t m.o`. Use `set Q : Hs (ι := ι) s.D →L[ℂ] Hs (ι := ι) s.D := (ContinuousLinearMap.id ℂ _ - P) ∘L m.Uπ with hQ`. Establish `hQa : ∀ f, Q f = m.Uπ f - P (m.Uπ f)` using `fun f => rfl`.

Establish `key : ∀ g, s.T₁ (Q (s.T₂ g)) = 0` using `fun g => by`. Establish `e : s.T₁ (m.U (s.T₂ (P g))) = (s.T₁ * m.U * s.T₂) (P g)` using `rfl`. Rewrite using `[hQa, map_sub, ← C₁, hUπ, C₂, e, ← C₃, hPP, sub_self]`. Establish `hz : ∀ g i, inner ℂ (s.k₁ x i) (Q (s.T₂ g)) = 0` using `fun g i => by`. Establish `h0` using `hR E n ι s s.Φ₁ s.T₁ s.t₁ s.o₁ (Q (s.T₂ g)) 0 (by rw [map_zero]; exact key g) x i`.

Rewrite using `[h0]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Establish `hj : (((0 : Hs (ι` using `ι) s.D) j : Lp ℂ 2 s.D.ν) : H E n 0 → ℂ) =ᵐ[s.D.ν] 0 := Lp.coeFn_zero _ _ _`. Rewrite using `[integral_congr_ae (g := fun _ => (0 : ℂ)) (hj.mono fun z hz => by rw [hz]; simp)]`. Simplify using the standard rewrite rules.

Use `set f : H E n 0 → ℂ := fun z => ∑ i, inner ℂ (s.k₁ x i) (Q (s.k₂ (th z) i)) with hf`. Establish `hfc : Continuous f` using `continuous_finset_sum _ fun i _ => continuous_const.inner (Q.continuous.comp ((s.vecs.cont i).2.comp hthc))`. Establish `hfi : Inv f` using `fun γ z => by`. Establish `h` using `(hK E n ι s).2 ⟨th (γ : H E n 0), (hrat γ).2⟩ (th z)`. Simplify using `only [hf, hthmul]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[show s.k₂ (th (γ : H E n 0) * th z) = s.k₂ (th z) from h]`. Establish `hf0` using `hZ E n s.D f Set.univ hfc hfi isOpen_univ (fun v _ => by`. Establish `hw` using `fun i => hW E n ι s v (ContinuousLinearMap.adjoint Q (s.k₁ x i)) i`. Establish `hpt : ∀ z, (v : H E n 0 → ℂ) z * f z = ∑ i, (v : H E n 0 → ℂ) z * inner ℂ (ContinuousLinearMap.adjoint Q (s.k₁ x i)) (s.k₂ (th z) i)` using `fun z => by`.

Simplify using `only [hf, Finset.mul_sum, ContinuousLinearMap.adjoint_inner_left]`. Simplify using `only [hpt]`. Rewrite using `[integral_finset_sum _ fun i _ => (hw i).1]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[(hw i).2, ContinuousLinearMap.adjoint_inner_left]`.

Conclude with `hz _ i)`. Establish `h1` using `hf0 (th y) (Set.mem_univ _)`. Simplify using `only [hf, hthth, hQa, inner_sub_right, Finset.sum_sub_distrib] at h1`. Conclude with `sub_eq_zero.1 h1`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.dropP_pf :
    Zero → KInv → Basic → Weak → PointRep → PComm → DropP := by
  intro hZ hK hB hW hR hC E _ _ _ n ι _ s m x y
  classical
  obtain ⟨-, -, -, -, -, -, -, hthth, hthmul, hrat, -, hthc⟩ := hB E n s.pos
  set S := piSp s.D s.π ι with hS
  set P := S.starProjection with hP
  have hmem : ∀ f, P f ∈ S := fun f => Submodule.starProjection_apply_mem S f
  have hPP : ∀ f, P (P f) = P f := fun f => (Submodule.starProjection_eq_self_iff).2 (hmem f)
  have hUπ : ∀ f, m.Uπ f = m.U (P f) := fun f => by
    have h2 : f - P f ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal f
    have hdec : P f + (f - P f) = f := by abel
    calc m.Uπ f = m.Uπ (P f + (f - P f)) := by rw [hdec]
      _ = m.U (P f) := by rw [map_add, m.pp.1 _ (hmem f), m.pp.2 _ h2, add_zero]
  have C₁ : ∀ f, P (s.T₁ f) = s.T₁ (P f) := hC E n s.pos s.D s.π s.fix ι s.Φ₁ s.T₁ s.t₁ s.o₁
  have C₂ : ∀ f, P (s.T₂ f) = s.T₂ (P f) := hC E n s.pos s.D s.π s.fix ι s.Φ₂ s.T₂ s.t₂ s.o₂
  have C₃ : ∀ f, P ((s.T₁ * m.U * s.T₂) f) = (s.T₁ * m.U * s.T₂) (P f) := hC E n s.pos s.D s.π s.fix ι m.Φ (s.T₁ * m.U * s.T₂) m.t m.o
  set Q : Hs (ι := ι) s.D →L[ℂ] Hs (ι := ι) s.D := (ContinuousLinearMap.id ℂ _ - P) ∘L m.Uπ with hQ
  have hQa : ∀ f, Q f = m.Uπ f - P (m.Uπ f) := fun f => rfl
  have key : ∀ g, s.T₁ (Q (s.T₂ g)) = 0 := fun g => by
    have e : s.T₁ (m.U (s.T₂ (P g))) = (s.T₁ * m.U * s.T₂) (P g) := rfl
    rw [hQa, map_sub, ← C₁, hUπ, C₂, e, ← C₃, hPP, sub_self]
  have hz : ∀ g i, inner ℂ (s.k₁ x i) (Q (s.T₂ g)) = 0 := fun g i => by
    have h0 := hR E n ι s s.Φ₁ s.T₁ s.t₁ s.o₁ (Q (s.T₂ g)) 0 (by rw [map_zero]; exact key g) x i
    rw [h0]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hj : (((0 : Hs (ι := ι) s.D) j : Lp ℂ 2 s.D.ν) : H E n 0 → ℂ) =ᵐ[s.D.ν] 0 := Lp.coeFn_zero _ _ _
    rw [integral_congr_ae (g := fun _ => (0 : ℂ)) (hj.mono fun z hz => by rw [hz]; simp)]
    simp
  set f : H E n 0 → ℂ := fun z => ∑ i, inner ℂ (s.k₁ x i) (Q (s.k₂ (th z) i)) with hf
  have hfc : Continuous f := continuous_finset_sum _ fun i _ =>
    continuous_const.inner (Q.continuous.comp ((s.vecs.cont i).2.comp hthc))
  have hfi : Inv f := fun γ z => by
    have h := (hK E n ι s).2 ⟨th (γ : H E n 0), (hrat γ).2⟩ (th z)
    simp only [hf, hthmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show s.k₂ (th (γ : H E n 0) * th z) = s.k₂ (th z) from h]
  have hf0 := hZ E n s.D f Set.univ hfc hfi isOpen_univ (fun v _ => by
    have hw := fun i => hW E n ι s v (ContinuousLinearMap.adjoint Q (s.k₁ x i)) i
    have hpt : ∀ z, (v : H E n 0 → ℂ) z * f z =
        ∑ i, (v : H E n 0 → ℂ) z * inner ℂ (ContinuousLinearMap.adjoint Q (s.k₁ x i)) (s.k₂ (th z) i) := fun z => by
      simp only [hf, Finset.mul_sum, ContinuousLinearMap.adjoint_inner_left]
    simp only [hpt]
    rw [integral_finset_sum _ fun i _ => (hw i).1]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [(hw i).2, ContinuousLinearMap.adjoint_inner_left]
    exact hz _ i)
  have h1 := hf0 (th y) (Set.mem_univ _)
  simp only [hf, hthth, hQa, inner_sub_right, Finset.sum_sub_distrib] at h1
  exact sub_eq_zero.1 h1
