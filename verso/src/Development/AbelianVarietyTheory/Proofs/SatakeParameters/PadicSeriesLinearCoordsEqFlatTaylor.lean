import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.KerJet
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoLatticesFormTaylorCorrespond
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.FlatTaylorBridge

open MvPowerSeries

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. A detailed English derivation is pending.
-/
theorem coeff_taylorMv_flatV (D : D7) (X : Fields) (s : Seam D X) (N N' : ℕ) (G : TaylorLogMetric.VC D N N' → ℂ)
    (hG : AnalyticOnNhd ℂ G Set.univ) (m : DVar X.Tau N N' →₀ ℕ) :
    coeff m (taylorMv fun z => G (s.flatV N N' z)) =
      TaylorLogMetric.taylor D G (m.mapDomain fun v => (s.iT v.1, v.2)) := by
  have hc : ∀ k : ℕ, ContDiff ℂ k G := fun k => hG.contDiff
  let G' : VCx X.Tau N N' → ℂ := fun w => G fun τ => w (s.iT.symm τ)
  let L : VCx X.Tau N N' →L[ℂ] TaylorLogMetric.VC D N N' :=
    ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (s.iT.symm τ)
  have hG' : AnalyticOnNhd ℂ G' Set.univ := by
    have : G' = G ∘ L := rfl
    rw [this]
    exact hG.comp (L.analyticOnNhd _) (fun _ _ => trivial)
  have h1 := Formalism.L2.AlgTh.taylor_jet_expansion X.Tau N N' G' hG' m
  have h2 := GlobalTheory.SeamTransport.deriv_transport s.iT G hc m
  rw [GlobalTheory.SeamTransport.taylor_eq] at h2
  have hfl : (fun z => G (s.flatV N N' z)) = fun z => G' (Formalism.L2.AlgTh.flat X.Tau N N' z) := rfl
  have hne : ((m.mapDomain fun v => (s.iT v.1, v.2)).prod fun _ n => (n.factorial : ℂ)) ≠ 0 := by
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hpr : ((m.mapDomain fun v => (s.iT v.1, v.2)).prod fun _ n => (n.factorial : ℂ)) =
      ((Formalism.DworkPowerSeriesWeights.mfact m : ℕ) : ℂ) := by
    rw [Finsupp.prod_mapDomain_index_inj]
    · simp [Formalism.DworkPowerSeriesWeights.mfact, Finsupp.prod]
    · intro v w h
      exact Prod.ext (s.iT.injective (Prod.ext_iff.1 h).1) (Prod.ext_iff.1 h).2
  apply mul_left_cancel₀ hne
  rw [← h2, hpr, hfl]
  convert h1 using 3

end GlobalTheory.FlatTaylorBridge

namespace GlobalTheory.FlatTaylorBridge
open MvPowerSeries

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem subst_rename_lin {σ τ γ : Type} [Finite σ] [Finite τ] {R : Type} [CommRing R] (f : σ → τ)
    (a : τ → MvPowerSeries γ R) (ha : ∀ t, constantCoeff (a t) = 0) (Φ : MvPowerSeries σ R) :
    subst a (rename f Φ) = subst (fun s => a (f s)) Φ := by
  have hs := hasSubst_of_constantCoeff_zero ha
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp f) hs Φ]
  congr 1
  funext x
  exact subst_X hs (f x)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem bridge : ∀ (D : D7) (X : Fields) (s : Seam D X) (N N' : ℕ) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), Formalism.L2.KerInert.IotaExt lm ι → ∀ G : TaylorLogMetric.VC D N N' → ℂ, AnalyticOnNhd ℂ G Set.univ → TaylorLogMetric.CoefIn D G TaylorLogMetric.Qbar → ∀ (ν : Type) [Fintype ν] (M : D.what₂.Tau × Fin N' × Fin N → ν → ℂ_[p]), TaylorLogMetric.atLin M (fun j => MvPowerSeries.X j) (TaylorLogMetric.pSer D lm G) = Formalism.L2.Th1.G.linSub (fun (i : DVar X.Tau N N') x => M (s.iT i.1, i.2) x) (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv fun z => G (s.flatV N N' z))) := by
  intro D X s N N' p _ lm ι hι G hG hC ν _ M
  let eE : DVar X.Tau N N' ≃ D.what₂.Tau × Fin N' × Fin N := s.iT.prodCongr (Equiv.refl _)
  have hP : TaylorLogMetric.pSer D lm G =
      rename (eE : DVar X.Tau N N' → D.what₂.Tau × Fin N' × Fin N)
        (map (ι : ℂ →+* ℂ_[p]) (taylorMv fun z => G (s.flatV N N' z))) := by
    ext α
    obtain ⟨m, rfl⟩ := Finsupp.mapDomain_surjective eE.surjective α
    have h := coeff_embDomain_rename eE.toEmbedding
      (map (ι : ℂ →+* ℂ_[p]) (taylorMv fun z => G (s.flatV N N' z))) m
    rw [Finsupp.embDomain_eq_mapDomain] at h
    refine Eq.trans ?_ h.symm
    rw [coeff_map, coeff_taylorMv_flatV D X s N N' G hG m]
    change TaylorLogMetric.lamC lm (TaylorLogMetric.taylor D G _) = _
    unfold TaylorLogMetric.lamC
    rw [dif_pos (hC _)]
    exact (hι ⟨_, hC _⟩).symm
  rw [hP]
  unfold TaylorLogMetric.atLin Formalism.L2.Th1.G.linSub
  rw [subst_rename_lin]
  · congr 1
  · intro t
    rw [map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_mul, constantCoeff_X, mul_zero]

end GlobalTheory.FlatTaylorBridge
