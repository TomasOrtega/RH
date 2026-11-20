import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFiniteDimFinitePartsWeilOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorArchimedeanSliceSchwartzSeminormBounStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformTransportedWeilContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSummableMajorantAdelicSchwartzLocallyUnifoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtCharSeriesCoefZeroStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.WeilCont

/- English proof (translation)
Introduce `D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ _ co hco ω hω om htr Φ hΦ z`. Establish `hth` using `GlobalTheory.T.thetaTransform_transportedWeil_continuous D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr Φ hΦ`. Use `continuous_iff_continuousAt.2 fun p0 => ?_` and prove the remaining obligations. Take `⟨N, hN, m, g, y, hg, hy, hf⟩` from `GlobalTheory.T.exists_local_finiteDim_finiteParts_weilOperators D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr Φ hΦ p0`. Set `f : _ → Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ` to `fun p => if h : p ∈ N then Classical.choose (hf p h) else 0`.

Establish `hfe : ∀ p ∈ N, om p Φ = ∑ i, GlobalTheory.WeilM.pureA D.host.F (f p i) (g i)` using `fun p hp => by`. Simplify using `only [f, dif_pos hp]`. Conclude with `Classical.choose_spec (hf p hp)`. Establish `hslice : ∀ p ∈ N, ∀ i v, f p i v = om p Φ (GlobalTheory.WeilCont.adeleJoin D.host.F v (y i))`. Introduce `p hp i v`.

Rewrite using `[hfe p hp, Finset.sum_apply, Finset.sum_eq_single i]`. Rewrite using `[GlobalTheory.WeilCont.pureA_adeleJoin, hy, if_pos rfl, mul_one]`. Introduce `j _ hji`. Rewrite using `[GlobalTheory.WeilCont.pureA_adeleJoin, hy, if_neg hji, mul_zero]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ i) h`. Establish `hbd : ∀ k : ℕ, ∃ C : ℝ, ∀ᶠ p in nhds p0, ∀ i v, ‖v‖ ^ k * ‖f p i v‖ ≤ C`. Introduce `k`. Use `choose C hC using fun i => GlobalTheory.T.weilOperator_archimedeanSlice_schwartzSeminorm_bounded D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr Φ hΦ (y i) p0 k 0`. Use `⟨∑ i, |C i|, ?_⟩` and prove the remaining obligations.

Use `filter_upwards [Filter.eventually_all.2 hC, hN] with p hp hpN i v`. Establish `h1` using `hp i v`. Rewrite `h1` using `[norm_iteratedFDeriv_zero]`. Rewrite using `[hslice p hpN i v]`. Conclude with `h1.trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)))`.

Take `⟨M, hM, hMb⟩` from `GlobalTheory.T.exists_summableMajorant_adelicSchwartz_locallyUniform D.host.F κ (fun p => om p Φ) p0 m g f hg (Filter.eventually_of_mem hN fun p hp => hfe p hp) hbd z`. Set `e : (κ → D.host.F) → AddChar (κ → AF D.host.F) ℂ` to `fun a => ψ.compAddMonoidHom (AddMonoidHom.mk' (fun y => (fun i => algebraMap D.host.F (AF D.host.F) (a i)) ⬝ᵥ y) (fun y y' => dotProduct_add _ y y'))`. Establish `he : ∀ a y, e a y = ψ ((fun i => algebraMap D.host.F (AF D.host.F) (a i)) ⬝ᵥ y)` using `fun a y => rfl`. Establish `hform : ∀ p y', GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (om p Φ) (co.e.symm (z, y')) = ψ (⅟(2 : AF D.host.F) * (z ⬝ᵥ y')) * ∑' a, e a y' * om p Φ (fun j => algebraMap D.host.F (AF D.host.F) (a j) + z j)`. Introduce `p y'`.

Simplify using `only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, LinearEquiv.apply_symm_apply, he]`. Rewrite using `[← tsum_mul_left]`. Use `tsum_congr fun a => ?_` and prove the remaining obligations. Simplify using `only [AddChar.map_add_eq_mul, Pi.add_def]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h0 : ∀ y, e 0 y = 1` using `fun y => by`. Rewrite using `[he]`. Simplify using the standard rewrite rules. Establish `hne : ∀ a : κ → D.host.F, a ≠ 0 → ∃ y, e a y ≠ 1`. Introduce `a ha`.

Take `⟨i, hi⟩` from `Function.ne_iff.1 ha`. Take `⟨x0, hx0⟩` from `hψ.1.2.2.2`. Use `⟨Pi.single i (algebraMap D.host.F (AF D.host.F) (a i)⁻¹ * x0), ?_⟩` and prove the remaining obligations. Rewrite using `[he, dotProduct_single, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]`. Conclude with `hx0`.

Establish `hψinv : ∀ t : AF D.host.F, ψ (-t) * ψ t = 1` using `fun t => by`. Simplify using `using (AddChar.map_add_eq_mul ψ (-t) t).symm`. Establish `hc : ∀ y', ContinuousAt (fun p => ∑' a, e a y' * om p Φ (fun j => algebraMap D.host.F (AF D.host.F) (a j) + z j)) p0`. Introduce `y'`. Establish `h2 : ∀ p, ψ (-(⅟(2 : AF D.host.F) * (z ⬝ᵥ y'))) * GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (om p Φ) (co.e.symm (z, y')) = ∑' a, e a y' * om p Φ (fun j => algebraMap D.host.F (AF D.host.F) (a j) + z j)`.

Introduce `p`. Simplify using `only [hform, ← mul_assoc, hψinv, one_mul]`. Conclude with `((continuous_const.mul (hth _)).continuousAt).congr (Filter.Eventually.of_forall h2)`. Establish `hL` using `GlobalTheory.T.continuousAt_coeff_zero_of_continuousAt_char_series e (fun a y => hψ.1.2.1 _) h0 hne _ p0 M hM hMb hc`. Simplify using `using hL`.
-/
theorem continuous_transport_apply : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
  ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ z : κ → AF D.host.F, Continuous fun p => om p Φ z := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ _ co hco ω hω om htr Φ hΦ z
  have hth := GlobalTheory.T.thetaTransform_transportedWeil_continuous D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr Φ hΦ
  refine continuous_iff_continuousAt.2 fun p0 => ?_
  obtain ⟨N, hN, m, g, y, hg, hy, hf⟩ :=
    GlobalTheory.T.exists_local_finiteDim_finiteParts_weilOperators D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr Φ hΦ p0
  let f : _ → Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ :=
    fun p => if h : p ∈ N then Classical.choose (hf p h) else 0
  have hfe : ∀ p ∈ N, om p Φ = ∑ i, GlobalTheory.WeilM.pureA D.host.F (f p i) (g i) := fun p hp => by
    simp only [f, dif_pos hp]
    exact Classical.choose_spec (hf p hp)
  have hslice : ∀ p ∈ N, ∀ i v, f p i v = om p Φ (GlobalTheory.WeilCont.adeleJoin D.host.F v (y i)) := by
    intro p hp i v
    rw [hfe p hp, Finset.sum_apply, Finset.sum_eq_single i]
    · rw [GlobalTheory.WeilCont.pureA_adeleJoin, hy, if_pos rfl, mul_one]
    · intro j _ hji
      rw [GlobalTheory.WeilCont.pureA_adeleJoin, hy, if_neg hji, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hbd : ∀ k : ℕ, ∃ C : ℝ, ∀ᶠ p in nhds p0, ∀ i v, ‖v‖ ^ k * ‖f p i v‖ ≤ C := by
    intro k
    choose C hC using fun i =>
      GlobalTheory.T.weilOperator_archimedeanSlice_schwartzSeminorm_bounded D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr Φ hΦ (y i) p0 k 0
    refine ⟨∑ i, |C i|, ?_⟩
    filter_upwards [Filter.eventually_all.2 hC, hN] with p hp hpN i v
    have h1 := hp i v
    rw [norm_iteratedFDeriv_zero] at h1
    rw [hslice p hpN i v]
    exact h1.trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)))
  obtain ⟨M, hM, hMb⟩ := GlobalTheory.T.exists_summableMajorant_adelicSchwartz_locallyUniform D.host.F κ (fun p => om p Φ) p0 m g f hg
    (Filter.eventually_of_mem hN fun p hp => hfe p hp) hbd z
  let e : (κ → D.host.F) → AddChar (κ → AF D.host.F) ℂ := fun a =>
    ψ.compAddMonoidHom (AddMonoidHom.mk' (fun y => (fun i => algebraMap D.host.F (AF D.host.F) (a i)) ⬝ᵥ y)
      (fun y y' => dotProduct_add _ y y'))
  have he : ∀ a y, e a y = ψ ((fun i => algebraMap D.host.F (AF D.host.F) (a i)) ⬝ᵥ y) := fun a y => rfl
  have hform : ∀ p y', GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (om p Φ) (co.e.symm (z, y')) =
      ψ (⅟(2 : AF D.host.F) * (z ⬝ᵥ y')) * ∑' a, e a y' * om p Φ (fun j => algebraMap D.host.F (AF D.host.F) (a j) + z j) := by
    intro p y'
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr,
      LinearEquiv.apply_symm_apply, he]
    rw [← tsum_mul_left]
    refine tsum_congr fun a => ?_
    simp only [AddChar.map_add_eq_mul, Pi.add_def]
    ring
  have h0 : ∀ y, e 0 y = 1 := fun y => by
    rw [he]
    simp
  have hne : ∀ a : κ → D.host.F, a ≠ 0 → ∃ y, e a y ≠ 1 := by
    intro a ha
    obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
    obtain ⟨x0, hx0⟩ := hψ.1.2.2.2
    refine ⟨Pi.single i (algebraMap D.host.F (AF D.host.F) (a i)⁻¹ * x0), ?_⟩
    rw [he, dotProduct_single, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
    exact hx0
  have hψinv : ∀ t : AF D.host.F, ψ (-t) * ψ t = 1 := fun t => by
    simpa using (AddChar.map_add_eq_mul ψ (-t) t).symm
  have hc : ∀ y', ContinuousAt (fun p => ∑' a, e a y' * om p Φ (fun j => algebraMap D.host.F (AF D.host.F) (a j) + z j)) p0 := by
    intro y'
    have h2 : ∀ p, ψ (-(⅟(2 : AF D.host.F) * (z ⬝ᵥ y'))) *
          GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (om p Φ) (co.e.symm (z, y')) =
        ∑' a, e a y' * om p Φ (fun j => algebraMap D.host.F (AF D.host.F) (a j) + z j) := by
      intro p
      simp only [hform, ← mul_assoc, hψinv, one_mul]
    exact ((continuous_const.mul (hth _)).continuousAt).congr (Filter.Eventually.of_forall h2)
  have hL := GlobalTheory.T.continuousAt_coeff_zero_of_continuousAt_char_series e (fun a y => hψ.1.2.1 _) h0 hne _ p0 M hM hMb hc
  simpa using hL

end GlobalTheory.WeilCont
