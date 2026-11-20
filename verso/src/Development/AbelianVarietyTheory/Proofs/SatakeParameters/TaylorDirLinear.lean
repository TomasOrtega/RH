import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.IntegralJetsPairing
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeries
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts

open Filter Topology

namespace GlobalTheory.PSerLin

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem map_subst_linear {σ κ R S : Type*} [Finite σ] [Fintype κ] [CommRing R] [CommRing S]
    (h : R →+* S) (c : σ → κ → R) (F : MvPowerSeries σ R) :
    MvPowerSeries.map h (MvPowerSeries.subst
      (fun k => ∑ x, MvPowerSeries.C (c k x) * (MvPowerSeries.X x : MvPowerSeries κ R)) F) =
    MvPowerSeries.subst
      (fun k => ∑ x, MvPowerSeries.C (h (c k x)) * (MvPowerSeries.X x : MvPowerSeries κ S))
      (MvPowerSeries.map h F) := by
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp)]
  simp

open Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetsPairing

open Classical in

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument.

Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem taylorDir_linear (D : D7) {N N' : ℕ} (G : VC D N N' → ℂ)
    (c : D.what₂.Tau × Fin N' × Fin N → D.what₂.Tau × Fin N' × Fin N → ℂ)
    (hG : Differentiable ℂ G) :
    taylorDir (Formalism.MainNotions.TaylorLogMetric.coordV D) (fun z : VC D N N' => G (fun τ i j =>
      ∑ x : D.what₂.Tau × Fin N' × Fin N, c (τ, i, j) x * z x.1 x.2.1 x.2.2)) =
    MvPowerSeries.subst (fun k => ∑ x, MvPowerSeries.C (c k x) *
      (MvPowerSeries.X x : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ))
      (taylorDir (Formalism.MainNotions.TaylorLogMetric.coordV D) G) := by
  let L : (D.what₂.Tau × Fin N' × Fin N → ℂ) →L[ℂ] VC D N N' :=
    ContinuousLinearMap.pi fun τ => ContinuousLinearMap.pi fun a => ContinuousLinearMap.pi fun b =>
      ContinuousLinearMap.proj (τ, a, b)
  have hL : ∀ z τ a b, L z τ a b = z (τ, a, b) := fun _ _ _ _ => rfl
  have hc : Formalism.MainNotions.TaylorLogMetric.coordV D = fun k => L (Pi.single k 1) := by
    funext ⟨k1, k2, k3⟩ τ a b
    simp [hL, Formalism.MainNotions.TaylorLogMetric.coordV, Pi.single_apply]
  have han : AnalyticAt ℂ G 0 :=
    SCV.analyticAt_iff_eventually_differentiableAt.2 (Eventually.of_forall hG)
  have han' : AnalyticAt ℂ (fun z => G (L z)) 0 :=
    han.comp_of_eq (L.analyticAt 0) (map_zero L)
  let ev : (D.what₂.Tau × Fin N' × Fin N) → (VC D N N' →L[ℂ] ℂ) := fun x =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) x.2.2).comp
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N' => Fin N → ℂ) x.2.1).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : D.what₂.Tau => Fin N' → Fin N → ℂ) x.1))
  let ℓ : (D.what₂.Tau × Fin N' × Fin N) → (VC D N N' →L[ℂ] ℂ) := fun k => ∑ x, c k x • ev x
  have hℓ : ∀ k z, ℓ k z = ∑ x, c k x * z x.1 x.2.1 x.2.2 := fun k z => by
    simp [ℓ, ev]
  have h := taylorDir_comp (Formalism.MainNotions.TaylorLogMetric.coordV D) (φ := fun z k => ℓ k z)
    (analyticAt_pi_iff.2 fun k => (ℓ k).analyticAt 0) (funext fun k => map_zero (ℓ k)) han'
  rw [taylor_comp_clm L han, ← hc] at h
  convert h using 2
  · funext z
    refine congrArg G ?_
    funext τ i j
    exact (hℓ (τ, i, j) z).symm
  · funext k
    rw [show (fun z => ℓ k z) = ⇑(ℓ k) from rfl, taylorDir_clm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MvPowerSeries.smul_eq_C_mul, hℓ, hc]
    simp [hL, Pi.single_apply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem pSer_linear : ∀ (D : D7) (N N' p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (G : VC D N N' → ℂ) (c : D.what₂.Tau × Fin N' × Fin N → D.what₂.Tau × Fin N' × Fin N → ℂ), Differentiable ℂ G → CoefIn D G Qbar → (∀ k x, c k x ∈ Qbar) → pSer D lam (fun z : VC D N N' => G (fun τ i j => ∑ x : D.what₂.Tau × Fin N' × Fin N, c (τ, i, j) x * z x.1 x.2.1 x.2.2)) = linAt (fun k x => lamC lam (c k x)) (pSer D lam G) := by
  intro D N N' p _ lam G c hG hco hc
  let F₀ : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) Qbar := fun α => ⟨_, hco α⟩
  let c₀ : D.what₂.Tau × Fin N' × Fin N → D.what₂.Tau × Fin N' × Fin N → Qbar :=
    fun k x => ⟨_, hc k x⟩
  have hl : ∀ x : Qbar, lamC lam x = lam x := fun x => by simp [lamC]
  have h1 : MvPowerSeries.map (algebraMap Qbar ℂ) F₀ = taylorDir (Formalism.MainNotions.TaylorLogMetric.coordV D) G := by
    ext α
    rw [MvPowerSeries.coeff_map, ← ConjSeries.taylor_eq_coeff]
    rfl
  have h2 : MvPowerSeries.map lam F₀ = pSer D lam G := by
    ext α
    rw [MvPowerSeries.coeff_map, ← hl]
    rfl
  have h3 := map_subst_linear (algebraMap Qbar ℂ) c₀ F₀
  have h4 := map_subst_linear lam c₀ F₀
  rw [h1] at h3
  rw [h2] at h4
  have h5 := h3.trans (taylorDir_linear D G c hG).symm
  simp only [← hl] at h4
  refine Eq.trans ?_ h4
  ext α
  rw [MvPowerSeries.coeff_map, ← hl]
  change lamC lam (Formalism.MainNotions.TaylorLogMetric.taylor D _ α) = _
  rw [ConjSeries.taylor_eq_coeff, ← h5, MvPowerSeries.coeff_map]
  rfl

end GlobalTheory.PSerLin
