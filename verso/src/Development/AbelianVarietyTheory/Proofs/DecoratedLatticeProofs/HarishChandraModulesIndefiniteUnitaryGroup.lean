import Mathlib
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.SubquotientNontrivial
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.CommutatorAdjointHolds
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.GrowthOfBasic
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.KSpanFinB
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.BoundedOperators
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.PCDesc
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.LogNormEstimates
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.CasScalar
import CompanionTheory.AutomorphicTheory.HarishChandraMultiplicity.HCMult
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.SopNegComm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DenseKFiniteVectorsUnitaryGroupRepStatement

noncomputable section

/- English proof (translation)
The claim follows from `GlobalTheory.T.dense_kFinite_vectors_unitaryGroupRep n ε H σ hσ`.
-/
theorem GlobalTheory.HcPort.kfinDense_UJC {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) : Dense {v : H | Formalism.MainNotions.S.IsKFin ε σ v} :=
  GlobalTheory.T.dense_kFinite_vectors_unitaryGroupRep n ε H σ hσ

section

open Matrix Topology Filter
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.HcPort
open CompanionTheory.D.gk.HC

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

/- English proof (translation)
Take `⟨a, ha, hK⟩` from `Metric.dense_iff.1 (kfinDense_UJC hσ) w δ hδ`. Conclude with `⟨a, hK, by rwa [Metric.mem_ball, dist_eq_norm] at ha⟩`.
-/
theorem exists_kfin_near_A [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {w : H}
    (_hw : w ∈ smD ε σ) {δ : ℝ} (hδ : 0 < δ) : ∃ a : H, Formalism.MainNotions.S.IsKFin ε σ a ∧ ‖a - w‖ < δ := by
  obtain ⟨a, ha, hK⟩ := Metric.dense_iff.1 (kfinDense_UJC hσ) w δ hδ
  exact ⟨a, hK, by rwa [Metric.mem_ball, dist_eq_norm] at ha⟩

/- English proof (translation)
Use `norm_eq_zero.1 (le_antisymm (le_of_forall_pos_le_add fun δ hδ => ?_) (norm_nonneg _))` and prove the remaining obligations. Rewrite using `[zero_add]`. Take `⟨a, ha, hlt⟩` from `exists_kfin_near_A hσ hw hδ`. Establish `h1 : ‖w‖ ^ 2 = RCLike.re ⟪w - a, w⟫_ℂ`. Rewrite using `[inner_sub_left, map_sub, h a ha, map_zero, sub_zero, inner_self_eq_norm_sq]`.

Establish `h2 : RCLike.re ⟪w - a, w⟫_ℂ ≤ ‖w - a‖ * ‖w‖` using `(RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)`. Rewrite `h2` using `[norm_sub_rev]`. Distinguish the cases in `h0 : ‖w‖ = 0`. Rewrite using `[h0]`. Conclude with `hδ.le`.

Establish `hpos : 0 < ‖w‖` using `lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem eq_zero_of_perp_A [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {w : H}
    (hw : w ∈ smD ε σ) (h : ∀ a : H, Formalism.MainNotions.S.IsKFin ε σ a → ⟪a, w⟫_ℂ = 0) : w = 0 := by
  refine norm_eq_zero.1 (le_antisymm (le_of_forall_pos_le_add fun δ hδ => ?_) (norm_nonneg _))
  rw [zero_add]
  obtain ⟨a, ha, hlt⟩ := exists_kfin_near_A hσ hw hδ
  have h1 : ‖w‖ ^ 2 = RCLike.re ⟪w - a, w⟫_ℂ := by
    rw [inner_sub_left, map_sub, h a ha, map_zero, sub_zero, inner_self_eq_norm_sq]
  have h2 : RCLike.re ⟪w - a, w⟫_ℂ ≤ ‖w - a‖ * ‖w‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  rw [norm_sub_rev] at h2
  by_cases h0 : ‖w‖ = 0
  · rw [h0]; exact hδ.le
  · have hpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

/- English proof (translation)
Establish `hU` using `isInfUnitary_of_isDerivedOn hσ (isDerivedOn_smE hσ)`. Simplify using `only [casimir, LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[hU, hU, ← mul_assoc]`. Establish `: adjSign ε a b * adjSign ε b a = 1`.

Unfold `adjSign`. Distinguish the cases in `h : ε a = ε b`. Simplify using `[h]`. Simplify using `[h, Ne.symm h]`. Rewrite using `[this, one_mul]`.
-/
theorem casimir_symm_A (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (x y : smD ε σ) :
    ⟪casimir (smE ε σ) x, y⟫_ℂ = ⟪x, casimir (smE ε σ) y⟫_ℂ := by
  have hU := isInfUnitary_of_isDerivedOn hσ (isDerivedOn_smE hσ)
  simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hU, hU, ← mul_assoc]
  have : adjSign ε a b * adjSign ε b a = 1 := by
    unfold adjSign
    by_cases h : ε a = ε b
    · simp [h]
    · simp [h, Ne.symm h]
  rw [this, one_mul]

end GlobalTheory.HcPort

end

section

open Matrix
open scoped InnerProductSpace

namespace GlobalTheory.HcPort
open CompanionTheory.D.gk.HC

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

/- English proof (translation)
Unfold `Formalism.L2.SG.Pf.admitted.gen casGen casSg Formalism.L2.SG.Pf.admitted.sg`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem gen_eq_A (p : Fin n × Fin n) : Formalism.L2.SG.Pf.admitted.gen ε p = casGen ε p := by
  unfold Formalism.L2.SG.Pf.admitted.gen casGen casSg Formalism.L2.SG.Pf.admitted.sg
  split_ifs <;> simp

/- English proof (translation)
Unfold `Formalism.L2.SG.Pf.admitted.wt Formalism.L2.SG.Pf.admitted.sg casWt casSg`. Apply the tactic sequence `split_ifs <;> push_cast <;> ring`.
-/
theorem coef_eq_A (p : Fin n × Fin n) :
    (((Formalism.L2.SG.Pf.admitted.wt p * Formalism.L2.SG.Pf.admitted.sg ε p : ℝ)) : ℂ) = casWt p * casSg ε p := by
  unfold Formalism.L2.SG.Pf.admitted.wt Formalism.L2.SG.Pf.admitted.sg casWt casSg
  split_ifs <;> push_cast <;> ring

/- English proof (translation)
Rewrite using `[← casU_eq_casimir (isDerivedOn_smE hσ) v]`. Unfold `Formalism.L2.SG.Pf.admitted.Cas casU`. Use `congr 1`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[coef_eq_A, gen_eq_A]`.

Both sides reduce to the same expression.
-/
theorem cas_eq_A (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (v : smD ε σ) :
    Formalism.L2.SG.Pf.admitted.Cas ε σ v = ((casimir (smE ε σ) v : smD ε σ) : H) := by
  rw [← casU_eq_casimir (isDerivedOn_smE hσ) v]
  unfold Formalism.L2.SG.Pf.admitted.Cas casU
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [coef_eq_A, gen_eq_A]
  rfl

/- English proof (translation)
The claim follows from `Formalism.MainNotions.BridgeCPX.HCAdm_of_mult (fun n ε H _ _ _ σ h1 h2 S h3 h4 => CompanionTheory.HCMult.harish_chandra_multiplicity n ε H σ h1 h2 S h3 h4) n ε H σ hσ hirr`.
-/
theorem admissibleProjection_of_irreducible_indefUnitary [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) : Formalism.MainNotions.BridgeCPX.AdmProjAt ε σ :=
  Formalism.MainNotions.BridgeCPX.HCAdm_of_mult (fun n ε H _ _ _ σ h1 h2 S h3 h4 => CompanionTheory.HCMult.harish_chandra_multiplicity n ε H σ h1 h2 S h3 h4)
    n ε H σ hσ hirr

/- English proof (translation)
Introduce `n ε H _ _ _ σ hσ hirr`. Distinguish the cases in `hex : ∃ w : H, Formalism.MainNotions.S.IsKFin ε σ w ∧ w ≠ 0`. Take `⟨w, hwK, hw⟩` from `hex`. Take `⟨c, hc⟩` from `Formalism.L2.SG.Pf.admitted.casScalar n ε H σ hσ hirr w hw`. Establish `hK : ∀ (x : smD ε σ), Formalism.MainNotions.S.IsKFin ε σ (x : H) → casimir (smE ε σ) x = (c : ℂ) • x` using `fun x hx => by`.

Establish `h1` using `hc x (Formalism.MainNotions.BridgeCPX.kfin_mem_Vsub hσ hirr (admissibleProjection_of_irreducible_indefUnitary hσ hirr) hw hx)`. Rewrite `h1` using `[cas_eq_A hσ]`. Conclude with `Subtype.ext (by rw [h1]; rfl)`. Use `⟨c, fun v => ?_⟩` and prove the remaining obligations. Establish `hy : ((casimir (smE ε σ) v - (c : ℂ) • v : smD ε σ) : H) = 0`.

Use `eq_zero_of_perp_A hσ (Submodule.coe_mem _) fun a ha => ?_` and prove the remaining obligations. Establish `haS` using `mem_smD_of_isKFin hσ hirr ha`. Establish `h1` using `casimir_symm_A hσ ⟨a, haS⟩ v`. Rewrite `h1` using `[hK ⟨a, haS⟩ ha, inner_smul_left, Complex.conj_ofReal]`. Rewrite using `[Submodule.coe_sub, Submodule.coe_smul, inner_sub_right, inner_smul_right]`.

Establish `h2 : ⟪a, ((casimir (smE ε σ) v : smD ε σ) : H)⟫_ℂ = (c : ℂ) * ⟪a, (v : H)⟫_ℂ`. Use `h1.symm` as an intermediate fact. Simplify using `using this`. Rewrite using `[h2, sub_self]`. Conclude with `Subtype.ext (sub_eq_zero.1 (by simpa using hy))`.

Use `push Not at hex`. Use `⟨0, fun v => ?_⟩` and prove the remaining obligations. Establish `h0 : (v : H) = 0` using `eq_zero_of_perp_A hσ v.2 fun a ha => by`. Rewrite using `[show a = 0 by by_contra h; exact h (hex a ha) |>.elim]`. Simplify using the standard rewrite rules.

Establish `hv : v = 0` using `Subtype.ext h0`. Rewrite using `[hv, map_zero, smul_zero]`.
-/
theorem casimirActsByScalar_indefUnitary : CasScal := by
  intro n ε H _ _ _ σ hσ hirr
  by_cases hex : ∃ w : H, Formalism.MainNotions.S.IsKFin ε σ w ∧ w ≠ 0
  · obtain ⟨w, hwK, hw⟩ := hex
    obtain ⟨c, hc⟩ := Formalism.L2.SG.Pf.admitted.casScalar n ε H σ hσ hirr w hw
    have hK : ∀ (x : smD ε σ), Formalism.MainNotions.S.IsKFin ε σ (x : H) →
        casimir (smE ε σ) x = (c : ℂ) • x := fun x hx => by
      have h1 := hc x (Formalism.MainNotions.BridgeCPX.kfin_mem_Vsub hσ hirr (admissibleProjection_of_irreducible_indefUnitary hσ hirr) hw hx)
      rw [cas_eq_A hσ] at h1
      exact Subtype.ext (by rw [h1]; rfl)
    refine ⟨c, fun v => ?_⟩
    have hy : ((casimir (smE ε σ) v - (c : ℂ) • v : smD ε σ) : H) = 0 := by
      refine eq_zero_of_perp_A hσ (Submodule.coe_mem _) fun a ha => ?_
      have haS := mem_smD_of_isKFin hσ hirr ha
      have h1 := casimir_symm_A hσ ⟨a, haS⟩ v
      rw [hK ⟨a, haS⟩ ha, inner_smul_left, Complex.conj_ofReal] at h1
      rw [Submodule.coe_sub, Submodule.coe_smul, inner_sub_right, inner_smul_right]
      have h2 : ⟪a, ((casimir (smE ε σ) v : smD ε σ) : H)⟫_ℂ = (c : ℂ) * ⟪a, (v : H)⟫_ℂ := by
        have := h1.symm
        simpa using this
      rw [h2, sub_self]
    exact Subtype.ext (sub_eq_zero.1 (by simpa using hy))
  · push Not at hex
    refine ⟨0, fun v => ?_⟩
    have h0 : (v : H) = 0 := eq_zero_of_perp_A hσ v.2 fun a ha => by
      rw [show a = 0 by by_contra h; exact h (hex a ha) |>.elim]
      simp
    have hv : v = 0 := Subtype.ext h0
    rw [hv, map_zero, smul_zero]

end GlobalTheory.HcPort

end

section
namespace GlobalTheory.HcPort
open CompanionTheory.D.gk.HC

/- English proof (translation)
The claim follows from `wordBd_of casimirActsByScalar_indefUnitary`.
-/
theorem kFiniteWordBound_indefUnitary : WordBd := wordBd_of casimirActsByScalar_indefUnitary

/- English proof (translation)
The claim follows from `kFiniteAnalytic_of K_finite_smooth_vectors kFiniteWordBound_indefUnitary`.
-/
theorem kFiniteVectors_analytic_indefiniteUnitary : GlobalTheory.Published.KFiniteAnalyticUJ := kFiniteAnalytic_of K_finite_smooth_vectors kFiniteWordBound_indefUnitary

end GlobalTheory.HcPort

end

section
namespace GlobalTheory.HcPort
open CompanionTheory.D.gk.HC

/- English proof (translation)
The claim follows from `harish_chandra_first_clause (fun _ _ _ _ _ _ _ hσ _ => kfinDense_UJC hσ) hS hW hI hA harish_chandra_descent`.
-/
theorem clause1_of (hS : KFSm) (hW : IntWts) (hI : UIrr) (hA : UAdm) : Clause1 :=
  harish_chandra_first_clause (fun _ _ _ _ _ _ _ hσ _ => kfinDense_UJC hσ) hS hW hI hA harish_chandra_descent

/- English proof (translation)
The claim follows from `harish_chandra_third_clause fun _ _ _ πU => kfinDense_coverC (fun _ _ _ _ _ _ _ hσ => kfinDense_UJC hσ) πU`.
-/
theorem harishChandraThird_indefiniteUnitary : Clause3 :=
  harish_chandra_third_clause fun _ _ _ πU => kfinDense_coverC (fun _ _ _ _ _ _ _ hσ => kfinDense_UJC hσ) πU

end GlobalTheory.HcPort

end

section

open Matrix WithLp
open scoped InnerProductSpace

namespace GlobalTheory.HcPort
open CompanionTheory.D.gk.HC

open ReciprocityTheory.ChartRestriction.DS
open Formalism.BasicNotions.TH (GrpData URep GKMod Mat upq IsKC Eab wtSub hwSub posC KFin sameBlock)
open Formalism.MainNotions.SchurIrreducible (IsHCMod IrrU)

section Graph

open USum

variable {n : ℕ} {ε : Fin n → Bool} {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}
  {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {E₂ : Fin n → Fin n → Module.End ℂ D₂}

/- English proof (translation)
Set `κ : N →ₗ[ℂ] sD D₁ D₂` to `ofP ∘ₗ κ₁.prod κ₂`. Establish `hκ : ∀ a b w, sE E₁ E₂ a b (κ w) = κ (F a b w)` using `fun a b w => by show ofP (E₁ a b (κ₁ w), E₂ a b (κ₂ w)) = ofP (κ₁ (F a b w), κ₂ (F a b w))`. Rewrite using `[e₁, e₂]`. Establish `c₁ : ∀ w, casimir E₁ (κ₁ w) = κ₁ (casimir F w)` using `fun w => by`. Simplify using `only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum, e₁]`.

Establish `cF : ∀ w, casimir F w = (c : ℂ) • w` using `fun w => hi (by rw [← c₁, hc, map_smul])`. Establish `cκ : ∀ w, casimir (sE E₁ E₂) (κ w) = (c : ℂ) • κ w` using `fun w => by`. Rewrite using `[← map_smul, ← cF]`. Simplify using `only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum, hκ]`. Set `Γ : Submodule ℂ (WithLp 2 (H₁ × H₂))` to `{ carrier := {x | U (ofLp x).1 = (ofLp x).2} add_mem' := fun {a b} ha hb => by show U ((ofLp a).1 + (ofLp b).1) = (ofLp a).2 + (ofLp b).2`.

Rewrite using `[map_add, show U (ofLp a).1 = (ofLp a).2 from ha, show U (ofLp b).1 = (ofLp b).2 from hb]`. Use the proof step `zero_mem' := map_zero U`. Use the proof step `smul_mem' := fun r a ha => by show U (r • (ofLp a).1) = r • (ofLp a).2`. Rewrite using `[map_smul, show U (ofLp a).1 = (ofLp a).2 from ha] }`. Establish `hL : Continuous (ofLp : WithLp 2 (H₁ × H₂) → H₁ × H₂)` using `(WithLp.prodContinuousLinearEquiv 2 ℂ H₁ H₂).continuous`.

Establish `hΓ : IsClosed (Γ : Set (WithLp 2 (H₁ × H₂)))` using `isClosed_eq (U.continuous.comp (continuous_fst.comp hL)) (continuous_snd.comp hL)`. Establish `hle : genSub (sE E₁ E₂) (W.map κ) ≤ LinearMap.range κ` using `sInf_le ⟨LinearMap.map_le_range, by rintro a b _ ⟨u, rfl⟩; exact ⟨_, (hκ a b u).symm⟩⟩`. Establish `hle' : ((genSub (sE E₁ E₂) (W.map κ)).map (sD D₁ D₂).subtype).topologicalClosure ≤ Γ`. Use `Submodule.topologicalClosure_minimal _ ?_ hΓ` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Take `⟨u, rfl⟩` from `hle hx`. Conclude with `hU u`. Use `closure_genSub_stable (isURepOn_sσ h₁ h₂) (isDerivedOn_sσ hD₁ hD₂) (V := W.map κ) (c := c) inferInstance (by rintro a b hab _ ⟨u, hu, rfl⟩; exact ⟨_, hWK a b hab u hu, (hκ a b u).symm⟩) (by rintro _ ⟨u, -, rfl⟩; exact cκ u) g hg (κ w : WithLp 2 (H₁ × H₂)) (Submodule.le_topologica …` as an intermediate fact. Conclude with `hle' this`.
-/
theorem graphD [CompleteSpace H₁] [CompleteSpace H₂] (h₁ : IsURepOn (UJset ε) σ₁) (h₂ : IsURepOn (UJset ε) σ₂)
    (hD₁ : IsDerivedOn ε σ₁ D₁ E₁) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂) {N : Type} [AddCommGroup N] [Module ℂ N]
    (F : Fin n → Fin n → Module.End ℂ N) (κ₁ : N →ₗ[ℂ] D₁) (κ₂ : N →ₗ[ℂ] D₂) (hi : Function.Injective κ₁)
    (e₁ : ∀ a b w, E₁ a b (κ₁ w) = κ₁ (F a b w)) (e₂ : ∀ a b w, E₂ a b (κ₂ w) = κ₂ (F a b w))
    {c : ℝ} (hc : ∀ v, casimir E₁ v = (c : ℂ) • v) (U : H₁ →L[ℂ] H₂) (hU : ∀ w, U (κ₁ w) = κ₂ w)
    {W : Submodule ℂ N} (hW : FiniteDimensional ℂ W) (hWK : IsKStableSub ε F W) {w : N} (hw : w ∈ W)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : U (σ₁ g (κ₁ w)) = σ₂ g (κ₂ w) := by
  let κ : N →ₗ[ℂ] sD D₁ D₂ := ofP ∘ₗ κ₁.prod κ₂
  have hκ : ∀ a b w, sE E₁ E₂ a b (κ w) = κ (F a b w) := fun a b w => by
    show ofP (E₁ a b (κ₁ w), E₂ a b (κ₂ w)) = ofP (κ₁ (F a b w), κ₂ (F a b w))
    rw [e₁, e₂]
  have c₁ : ∀ w, casimir E₁ (κ₁ w) = κ₁ (casimir F w) := fun w => by
    simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum, e₁]
  have cF : ∀ w, casimir F w = (c : ℂ) • w := fun w => hi (by rw [← c₁, hc, map_smul])
  have cκ : ∀ w, casimir (sE E₁ E₂) (κ w) = (c : ℂ) • κ w := fun w => by
    rw [← map_smul, ← cF]
    simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum, hκ]
  let Γ : Submodule ℂ (WithLp 2 (H₁ × H₂)) :=
    { carrier := {x | U (ofLp x).1 = (ofLp x).2}
      add_mem' := fun {a b} ha hb => by
        show U ((ofLp a).1 + (ofLp b).1) = (ofLp a).2 + (ofLp b).2
        rw [map_add, show U (ofLp a).1 = (ofLp a).2 from ha, show U (ofLp b).1 = (ofLp b).2 from hb]
      zero_mem' := map_zero U
      smul_mem' := fun r a ha => by
        show U (r • (ofLp a).1) = r • (ofLp a).2
        rw [map_smul, show U (ofLp a).1 = (ofLp a).2 from ha] }
  have hL : Continuous (ofLp : WithLp 2 (H₁ × H₂) → H₁ × H₂) :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ H₁ H₂).continuous
  have hΓ : IsClosed (Γ : Set (WithLp 2 (H₁ × H₂))) :=
    isClosed_eq (U.continuous.comp (continuous_fst.comp hL)) (continuous_snd.comp hL)
  have hle : genSub (sE E₁ E₂) (W.map κ) ≤ LinearMap.range κ :=
    sInf_le ⟨LinearMap.map_le_range, by rintro a b _ ⟨u, rfl⟩; exact ⟨_, (hκ a b u).symm⟩⟩
  have hle' : ((genSub (sE E₁ E₂) (W.map κ)).map (sD D₁ D₂).subtype).topologicalClosure ≤ Γ := by
    refine Submodule.topologicalClosure_minimal _ ?_ hΓ
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, rfl⟩ := hle hx
    exact hU u
  have := closure_genSub_stable (isURepOn_sσ h₁ h₂) (isDerivedOn_sσ hD₁ hD₂) (V := W.map κ) (c := c) inferInstance
    (by rintro a b hab _ ⟨u, hu, rfl⟩; exact ⟨_, hWK a b hab u hu, (hκ a b u).symm⟩)
    (by rintro _ ⟨u, -, rfl⟩; exact cκ u) g hg (κ w : WithLp 2 (H₁ × H₂))
    (Submodule.le_topologicalClosure _ ⟨κ w, (le_sInf fun _ hT => hT.1 : W.map κ ≤ genSub (sE E₁ E₂) (W.map κ))
      ⟨w, hw, rfl⟩, rfl⟩)
  exact hle' this

end Graph

section Twist

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

/- English proof (translation)
Establish `hm : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε` using `hg`. Establish `hd` using `congrArg (fun A => ‖Matrix.det A‖) hm`. Establish `hJ : ‖(Formalism.REAL.Jm ε).det‖ ≠ 0` using `norm_ne_zero_iff.2 ((Matrix.isUnit_iff_isUnit_det _).1 (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε))).ne_zero`. Simplify using `only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star] at hd`. Establish `h2 : ‖g.det‖ ^ 2 = 1` using `mul_right_cancel₀ hJ (by nlinarith)`.

Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h2`.
-/
theorem norm_detD {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.MainNotions.S.UJset ε) : ‖g.det‖ = 1 := by
  have hm : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have hd := congrArg (fun A => ‖Matrix.det A‖) hm
  have hJ : ‖(Formalism.REAL.Jm ε).det‖ ≠ 0 := norm_ne_zero_iff.2
    ((Matrix.isUnit_iff_isUnit_det _).1 (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε))).ne_zero
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star] at hd
  have h2 : ‖g.det‖ ^ 2 = 1 := mul_right_cancel₀ hJ (by nlinarith)
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h2

def twD (m : ℕ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H) :=
  fun g => g.det ^ m • σ g

/- English proof (translation)
Use `⟨⟨by simp [twD, h.1.1], fun a ha b hb => ?_⟩, fun g hg v => ?_, fun v => ?_⟩` and prove the remaining obligations. Simplify using `only [twD]`. Rewrite using `[h.1.2 a ha b hb, det_mul, mul_pow, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]`. Simplify using `only [twD, ContinuousLinearMap.smul_apply, norm_smul, norm_pow, norm_detD hg, one_pow, one_mul, h.2.1 g hg]`. Conclude with `((continuous_id.matrix_det).pow m).continuousOn.smul (h.2.2 v)`.
-/
theorem twD_rep (m : ℕ) (h : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) :
    Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) (twD m σ) := by
  refine ⟨⟨by simp [twD, h.1.1], fun a ha b hb => ?_⟩, fun g hg v => ?_, fun v => ?_⟩
  · simp only [twD]
    rw [h.1.2 a ha b hb, det_mul, mul_pow, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]
  · simp only [twD, ContinuousLinearMap.smul_apply, norm_smul, norm_pow, norm_detD hg, one_pow, one_mul, h.2.1 g hg]
  · exact ((continuous_id.matrix_det).pow m).continuousOn.smul (h.2.2 v)

/- English proof (translation)
Introduce `S hS hinv` and use `h S hS fun g hg v hv => by have h0 : g.det ^ m ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [norm_detD hg]; exact one_ne_zero)) exact (S.smul_mem_iff h0).1 (hinv g hg v hv)`.
-/
theorem twD_irr (m : ℕ) (h : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) :
    Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (twD m σ) := fun S hS hinv => h S hS fun g hg v hv => by
  have h0 : g.det ^ m ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [norm_detD hg]; exact one_ne_zero))
  exact (S.smul_mem_iff h0).1 (hinv g hg v hv)

/- English proof (translation)
Take `⟨S, h1, h2, h3⟩` from `h`. Conclude with `⟨S, h1, h2, fun g hg u hu => S.smul_mem _ (h3 g hg u hu)⟩`.
-/
theorem twD_kfin (m : ℕ) {v : H} (h : Formalism.MainNotions.S.IsKFin ε σ v) : Formalism.MainNotions.S.IsKFin ε (twD m σ) v := by
  obtain ⟨S, h1, h2, h3⟩ := h
  exact ⟨S, h1, h2, fun g hg u hu => S.smul_mem _ (h3 g hg u hu)⟩

end Twist

section Cover

variable {p q : ℕ} {T : GrpData p q} {πU : URep T} {M : GKMod p q} {io : M.V →ₗ[ℂ] πU.H}

/- English proof (translation)
Introduce `Y hY v w` and use `by have h1 := (h.2.2 Y hY v).inner ℂ (h.2.2 Y hY w) simp only [inner_piC, zero_smul, T.expt_zero, map_one, ContinuousLinearMap.one_apply] at h1 have h2 := h1.unique (hasDerivAt_const _ _) linear_combination h2`.
-/
theorem skewD (h : IsHCMod πU M io) : SkewD M io := fun Y hY v w => by
  have h1 := (h.2.2 Y hY v).inner ℂ (h.2.2 Y hY w)
  simp only [inner_piC, zero_smul, T.expt_zero, map_one, ContinuousLinearMap.one_apply] at h1
  have h2 := h1.unique (hasDerivAt_const _ _)
  linear_combination h2

/- English proof (translation)
Establish `hd : ∀ s : ℝ, HasDerivAt (fun r : ℝ => πU.π (T.expt (r • X)) (io v)) (c • πU.π (T.expt (s • X)) (io v)) s`. Introduce `s`. Establish `h0 : HasDerivAt (fun r : ℝ => πU.π (T.expt (r • X)) (io v)) (io (M.act X v)) (s - s)`. Rewrite using `[sub_self]`. Conclude with `h.2.2 X hX v`.

Establish `h1` using `((πU.π (T.expt (s • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (h0.comp_sub_const s s)`. Rewrite `h1` using `[hv, map_smul]`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `r show _ = πU.π (T.expt (s • X)) (πU.π (T.expt ((r - s) • X)) (io v))`. Rewrite using `[← pi_mulC, ← T.expt_add X hX, add_sub_cancel]`.

Conclude with `(map_smul _ _ _).symm`. Establish `hg : ∀ s : ℝ, HasDerivAt (fun r : ℝ => Complex.exp (-(c * r)) • πU.π (T.expt (r • X)) (io v)) 0 s`. Introduce `s`. Establish `h1` using `(((hasDerivAt_id s).ofReal_comp.const_mul c).fun_neg.cexp).fun_smul (hd s)`. Use `h1.congr_deriv ?_` and prove the remaining obligations.

Rewrite using `[smul_smul, ← add_smul, Complex.ofReal_one, show ∀ x : ℂ, x * c + x * -(c * 1) = 0 from fun x => by ring, zero_smul]`. Establish `h2` using `is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv) t 0`. Simplify using `only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, zero_smul, T.expt_zero, map_one, ContinuousLinearMap.one_apply, one_smul] at h2`. Use `conv_rhs => rw [← h2]`. Rewrite using `[smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]`.
-/
theorem eigD (h : IsHCMod πU M io) {X : Mat p q} (hX : X ∈ upq p q) {v : M.V} {c : ℂ} (hv : M.act X v = c • v)
    (t : ℝ) : πU.π (T.expt (t • X)) (io v) = Complex.exp (c * t) • io v := by
  have hd : ∀ s : ℝ, HasDerivAt (fun r : ℝ => πU.π (T.expt (r • X)) (io v)) (c • πU.π (T.expt (s • X)) (io v)) s := by
    intro s
    have h0 : HasDerivAt (fun r : ℝ => πU.π (T.expt (r • X)) (io v)) (io (M.act X v)) (s - s) := by
      rw [sub_self]; exact h.2.2 X hX v
    have h1 := ((πU.π (T.expt (s • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (h0.comp_sub_const s s)
    rw [hv, map_smul] at h1
    convert h1 using 1
    · funext r
      show _ = πU.π (T.expt (s • X)) (πU.π (T.expt ((r - s) • X)) (io v))
      rw [← pi_mulC, ← T.expt_add X hX, add_sub_cancel]
    · exact (map_smul _ _ _).symm
  have hg : ∀ s : ℝ, HasDerivAt (fun r : ℝ => Complex.exp (-(c * r)) • πU.π (T.expt (r • X)) (io v)) 0 s := by
    intro s
    have h1 := (((hasDerivAt_id s).ofReal_comp.const_mul c).fun_neg.cexp).fun_smul (hd s)
    refine h1.congr_deriv ?_
    rw [smul_smul, ← add_smul, Complex.ofReal_one, show ∀ x : ℂ, x * c + x * -(c * 1) = 0 from fun x => by ring,
      zero_smul]
  have h2 := is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv) t 0
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, zero_smul, T.expt_zero, map_one,
    ContinuousLinearMap.one_apply, one_smul] at h2
  conv_rhs => rw [← h2]
  rw [smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]

/- English proof (translation)
The claim follows from `mem_upq_of_adjZD (by rw [adjZ_smulD, adjZ_singleD a a (sameBlock_reflD a), show star Complex.I = -Complex.I from Complex.conj_I, neg_smul])`.
-/
theorem iE_memD (a : Formalism.BasicNotions.TH.Ix p q) : Complex.I • Eab a a ∈ upq p q :=
  mem_upq_of_adjZD (by
    rw [adjZ_smulD, adjZ_singleD a a (sameBlock_reflD a), show star Complex.I = -Complex.I from Complex.conj_I, neg_smul])

/- English proof (translation)
Establish `e : ((2 * Real.pi : ℝ) : ℂ) • rx (Complex.I • Eab a a) = diagonal fun i => if i = finSumFinEquiv a then 2 * Real.pi * Complex.I else 0`. Use extensionality with `i k`. Take `⟨b, rfl⟩` from `finSumFinEquiv.surjective i`. Take `⟨d, rfl⟩` from `finSumFinEquiv.surjective k`. Simplify using `only [rx, Eab, Matrix.smul_apply, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Matrix.single_apply, diagonal_apply, Equiv.apply_eq_iff_eq, smul_eq_mul]`.

Distinguish the cases in `h1 : b = d`. Substitute `h1` using the available equality. Distinguish the cases in `h2 : b = a`. Substitute `h2` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h2, Ne.symm h2]`. Rewrite using `[if_neg h1, if_neg (fun h => h1 (h.1.symm.trans h.2))]`. Simplify using the standard rewrite rules. Rewrite using `[e, Matrix.exp_diagonal, ← diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Rewrite using `[Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]`. Use `split_ifs`. Conclude with `Complex.exp_two_pi_mul_I`. Conclude with `Complex.exp_zero`.
-/
theorem exp_twoPiD (a : Formalism.BasicNotions.TH.Ix p q) :
    NormedSpace.exp (((2 * Real.pi : ℝ) : ℂ) • rx (Complex.I • Eab a a)) = 1 := by
  have e : ((2 * Real.pi : ℝ) : ℂ) • rx (Complex.I • Eab a a) =
      diagonal fun i => if i = finSumFinEquiv a then 2 * Real.pi * Complex.I else 0 := by
    ext i k
    obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨d, rfl⟩ := finSumFinEquiv.surjective k
    simp only [rx, Eab, Matrix.smul_apply, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Matrix.single_apply,
      diagonal_apply, Equiv.apply_eq_iff_eq, smul_eq_mul]
    by_cases h1 : b = d
    · subst h1
      by_cases h2 : b = a
      · subst h2; simp
      · simp [h2, Ne.symm h2]
    · rw [if_neg h1, if_neg (fun h => h1 (h.1.symm.trans h.2))]; simp
  rw [e, Matrix.exp_diagonal, ← diagonal_one]
  congr 1
  funext i
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  split_ifs
  · exact Complex.exp_two_pi_mul_I
  · exact Complex.exp_zero

/- English proof (translation)
Establish `e` using `eigD h (iE_memD a) (v := v) (c := Complex.I * c) (by rw [map_smul, LinearMap.smul_apply, hv, smul_smul]) (2 * Real.pi)`. Rewrite `e` using `[(hex _ (iE_memD a)).2, exp_twoPiD, h1, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]`. Establish `hne : io v ≠ 0` using `fun h0 => hv0 (h.1 (h0.trans (map_zero io).symm))`. Rewrite using `[← smul_left_injective ℂ hne e, ← Complex.exp_pi_mul_I, ← Complex.exp_nat_mul, trace_smul, Eab, trace_single_eq_same]`. Use `congr 1`.

Use `push_cast`. Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem signD (h : IsHCMod πU M io) {j : ℕ} {σ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ → (πU.H →L[ℂ] πU.H)}
    (h1 : σ 1 = 1) (hex : ∀ X ∈ upq p q, inG (epq p q) (rx X) ∧ ∀ t : ℝ,
      πU.π (T.expt (t • X)) = Complex.exp ((j : ℂ) * (t * X.trace / 2)) • σ (NormedSpace.exp ((t : ℂ) • rx X)))
    (a : Formalism.BasicNotions.TH.Ix p q) {v : M.V} (hv0 : v ≠ 0) {c : ℂ} (hv : M.act (Eab a a) v = c • v) :
    Complex.exp (Complex.I * c * (2 * Real.pi : ℝ)) = (-1) ^ j := by
  have e := eigD h (iE_memD a) (v := v) (c := Complex.I * c)
    (by rw [map_smul, LinearMap.smul_apply, hv, smul_smul]) (2 * Real.pi)
  rw [(hex _ (iE_memD a)).2, exp_twoPiD, h1, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] at e
  have hne : io v ≠ 0 := fun h0 => hv0 (h.1 (h0.trans (map_zero io).symm))
  rw [← smul_left_injective ℂ hne e, ← Complex.exp_pi_mul_I, ← Complex.exp_nat_mul, trace_smul, Eab,
    trace_single_eq_same]
  congr 1
  push_cast
  simp only [smul_eq_mul]
  ring

/- English proof (translation)
Establish `hτ` using `twD_rep m hσ`. Take `⟨hsm, -⟩` from `hS _ _ _ (twD m σ) hτ (twD_irr m hσi)`. Establish `hder` using `isDerivedOn_smE (ε := epq p q) (σ := twD m σ) hτ`. Set `κ : M.V →ₗ[ℂ] smD (epq p q) (twD m σ)` to `io.codRestrict _ fun v => hsm _ (twD_kfin m ((hkf _).1 ((h.2.1 _).1 ⟨v, rfl⟩)))`. Use `⟨κ, fun _ => rfl, ?_⟩` and prove the remaining obligations.

Establish `key : ∀ Y ∈ upq p q, ∀ v, actLC (smE (epq p q) (twD m σ)) (rx Y) (κ v) = κ (M.act Y v + (((m : ℂ) - j / 2) * Y.trace) • v)`. Introduce `Y hY v`. Use `Subtype.ext ((hder.deriv _ (hex Y hY).1 (κ v)).unique ?_)` and prove the remaining obligations. Apply the tactic sequence `have d1 : HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • rx Y)).det) (rx Y).trace 0 := PI.UnitaryCorollaryDerivatives.DjC.hasDerivAt_det_of_one _ _ (by simp) fun a b => PI.UnitaryCorollaryDerivatives.DjC.hasDerivAt_exp_entry (rx Y) a b`. Establish `d2` using `((((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Y.trace).div_const 2).const_mul (j : ℂ)).fun_neg.cexp`.

Establish `d3` using `((d1.fun_pow m).fun_mul d2).fun_smul (h.2.2 Y hY v)`. Use `d3 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `t`. Rewrite using `[(hex Y hY).2, ContinuousLinearMap.smul_apply, smul_smul, mul_assoc, ← Complex.exp_add]`. Simplify using `only [id, neg_add_cancel, Complex.exp_zero, mul_one, twD, ContinuousLinearMap.smul_apply, Complex.coe_smul]`.

Both sides reduce to the same expression. Use `show io _ = _`. Simplify using `only [map_add, map_smul, id, zero_smul, NormedSpace.exp_zero, det_one, one_pow, Complex.ofReal_zero, zero_mul, zero_div, mul_zero, neg_zero, Complex.exp_zero, mul_one, one_mul, one_smul, T.expt_zero, map_one, ContinuousLinearMap.one_apply, trace_rxC, Complex.ofReal_one]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.

Introduce `Z v`. Take `⟨Y₁, h₁, Y₂, h₂, e, -⟩` from `upq_decC Z`. Use `show actLC _ (rx Z) (κ v) = _`. Rewrite using `[e, show rx (Y₁ + Complex.I • Y₂) = rx Y₁ + Complex.I • rx Y₂ from rfl]`. Simplify using `only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, key Y₁ h₁, key Y₂ h₂, trace_add, trace_smul, smul_eq_mul]`.

Use `module`.
-/
theorem dictD (hS : KFSm) (h : IsHCMod πU M io) {j : ℕ} (m : ℕ)
    {σ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ → (πU.H →L[ℂ] πU.H)}
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (epq p q)) σ) (hσi : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset (epq p q)) σ)
    (hkf : ∀ x, KFin T πU.π x ↔ Formalism.MainNotions.S.IsKFin (epq p q) σ x)
    (hex : ∀ X ∈ upq p q, inG (epq p q) (rx X) ∧ ∀ t : ℝ,
      πU.π (T.expt (t • X)) = Complex.exp ((j : ℂ) * (t * X.trace / 2)) • σ (NormedSpace.exp ((t : ℂ) • rx X))) :
    ∃ κ : M.V →ₗ[ℂ] smD (epq p q) (twD m σ), (∀ v, (κ v : πU.H) = io v) ∧ ∀ Z v,
      actM (smE (epq p q) (twD m σ)) (rx Z) (κ v) = κ (M.act Z v + (((m : ℂ) - j / 2) * Z.trace) • v) := by
  have hτ := twD_rep m hσ
  obtain ⟨hsm, -⟩ := hS _ _ _ (twD m σ) hτ (twD_irr m hσi)
  have hder := isDerivedOn_smE (ε := epq p q) (σ := twD m σ) hτ
  let κ : M.V →ₗ[ℂ] smD (epq p q) (twD m σ) :=
    io.codRestrict _ fun v => hsm _ (twD_kfin m ((hkf _).1 ((h.2.1 _).1 ⟨v, rfl⟩)))
  refine ⟨κ, fun _ => rfl, ?_⟩
  have key : ∀ Y ∈ upq p q, ∀ v, actLC (smE (epq p q) (twD m σ)) (rx Y) (κ v) =
      κ (M.act Y v + (((m : ℂ) - j / 2) * Y.trace) • v) := by
    intro Y hY v
    refine Subtype.ext ((hder.deriv _ (hex Y hY).1 (κ v)).unique ?_)
    have d1 : HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • rx Y)).det) (rx Y).trace 0 :=
      PI.UnitaryCorollaryDerivatives.DjC.hasDerivAt_det_of_one _ _ (by simp) fun a b => PI.UnitaryCorollaryDerivatives.DjC.hasDerivAt_exp_entry (rx Y) a b
    have d2 := ((((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Y.trace).div_const 2).const_mul (j : ℂ)).fun_neg.cexp
    have d3 := ((d1.fun_pow m).fun_mul d2).fun_smul (h.2.2 Y hY v)
    convert d3 using 1
    · funext t
      rw [(hex Y hY).2, ContinuousLinearMap.smul_apply, smul_smul, mul_assoc, ← Complex.exp_add]
      simp only [id, neg_add_cancel, Complex.exp_zero, mul_one, twD, ContinuousLinearMap.smul_apply, Complex.coe_smul]
      rfl
    · show io _ = _
      simp only [map_add, map_smul, id, zero_smul, NormedSpace.exp_zero, det_one, one_pow, Complex.ofReal_zero, zero_mul,
        zero_div, mul_zero, neg_zero, Complex.exp_zero, mul_one, one_mul, one_smul, T.expt_zero, map_one,
        ContinuousLinearMap.one_apply, trace_rxC, Complex.ofReal_one]
      congr 2
      ring
  intro Z v
  obtain ⟨Y₁, h₁, Y₂, h₂, e, -⟩ := upq_decC Z
  show actLC _ (rx Z) (κ v) = _
  rw [e, show rx (Y₁ + Complex.I • Y₂) = rx Y₁ + Complex.I • rx Y₂ from rfl]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, key Y₁ h₁, key Y₂ h₂, trace_add, trace_smul,
    smul_eq_mul]
  module

end Cover

/- English proof (translation)
Introduce `p q hpq T π₁ π₂ i₁ i₂ M₁ M₂ io₁ io₂ m₁ m₂ e he`. Take `⟨hA, hI⟩` from `(h1 p q hpq T π₁ i₁).2.2 M₁ io₁ m₁`. Take `⟨c, hc, hB⟩` from `form_propD io₁ (io₂ ∘ₗ e.toLinearMap) m₁.1 (m₂.1.comp e.injective) (skewD m₁) (fun Y hY v w => by show ⟪io₂ (e (M₁.act Y v)), io₂ (e w)⟫_ℂ = -⟪io₂ (e v), io₂ (e (M₁.act Y w))⟫_ℂ`. Rewrite using `[he, he]`. Conclude with `skewD m₂ Y hY _ _) hI hA`.

Establish `hs : 0 < √c` using `Real.sqrt_pos.2 hc`. Take `⟨r, hr⟩ : ∃ r : ℂ, r = (((√c)⁻¹ : ℝ) : ℂ)` from `⟨_, rfl⟩`. Establish `hr0 : r ≠ 0` using `by rw [hr]; exact Complex.ofReal_ne_zero.2 (inv_pos.2 hs).ne'`. Establish `dense : ∀ (π : URep T) (M : GKMod p q) (io : M.V →ₗ[ℂ] π.H), IsHCMod π M io → DenseRange io` using `fun π M io m => (kfinDense_coverC (fun _ _ _ _ _ _ _ hσ => kfinDense_UJC hσ) π).mono fun x hx => (m.2.1 x).2 hx`. Establish `d₁` using `dense π₁ M₁ io₁ m₁`.

Establish `d₂ : DenseRange (r • io₂)` using `(dense π₂ M₂ io₂ m₂).mono (by`. Introduce and unpack `_ ⟨v, rfl⟩`. Conclude with `⟨r⁻¹ • v, by rw [LinearMap.smul_apply, map_smul, smul_smul, mul_inv_cancel₀ hr0, one_smul]⟩)`. Establish `hn : ∀ v, ‖(r • io₂) (e v)‖ = ‖io₁ v‖` using `fun v => by`. Establish `h2 : ‖io₂ (e v)‖ ^ 2 = c * ‖io₁ v‖ ^ 2`.

Use `congrArg Complex.re (hB v v)` as an intermediate fact. Rewrite `this` using `[Complex.re_ofReal_mul]`. Rewrite using `[← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]`. Conclude with `this`. Establish `h3 : ‖io₂ (e v)‖ = √c * ‖io₁ v‖`.

Rewrite using `[← Real.sqrt_sq (norm_nonneg (io₂ (e v))), h2, Real.sqrt_mul hc.le, Real.sqrt_sq (norm_nonneg _)]`. Rewrite using `[LinearMap.smul_apply, norm_smul, hr, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hs).le, h3, inv_mul_cancel_left₀ hs.ne']`. Apply the tactic sequence `let U := e.extendOfIsometry io₁ (r • io₂) d₁ d₂ hn`. Establish `hU : ∀ v, U (io₁ v) = r • io₂ (e v)` using `LinearEquiv.extendOfIsometry_eq e io₁ (r • io₂) d₁ d₂ hn`. Take `⟨j₁, σ₁, ⟨hσ₁, hπ₁⟩, hi₁, hk₁, hx₁⟩` from `hDe p q T π₁ i₁`.

Take `⟨j₂, σ₂, ⟨hσ₂, hπ₂⟩, hi₂, hk₂, hx₂⟩` from `hDe p q T π₂ i₂`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : Even (j₁ + j₂) := by`. Take `⟨μ, v, hv, hv0⟩` from `exists_hwD hI.1`. Establish `a : Formalism.BasicNotions.TH.Ix p q` using `finSumFinEquiv.symm ⟨0, hpq⟩`. Establish `hw` using `mem_wtSubD.1 (Submodule.mem_inf.1 hv).1 a`.

Establish `s₁` using `signD m₁ hσ₁.1.1 hx₁ a hv0 hw`. Establish `s₂` using `signD m₂ hσ₂.1.1 hx₂ a (v := e v) (e.map_ne_zero_iff.2 hv0) (by rw [← he, hw, map_smul])`. Use `(neg_one_pow_eq_one_iff_even (R := ℂ) (by norm_num)).1 ?_` and prove the remaining obligations. Rewrite using `[pow_add, ← s₁, s₂, ← pow_add, ← two_mul, pow_mul]`. Evaluate the numerical expressions.

Take `⟨κ₁, hκ₁, a₁⟩` from `dictD hS m₁ m hσ₁ hi₁ hk₁ hx₁`. Take `⟨κ₂, hκ₂, a₂⟩` from `dictD hS m₂ j₂ hσ₂ hi₂ hk₂ hx₂`. Establish `hmj : (m : ℂ) - j₁ / 2 = j₂ / 2`. Establish `: (j₁ : ℂ) + j₂ = m + m` using `by exact_mod_cast hm`. Take the linear combination `(-1 / 2 : ℂ) * this`.

Set `F : Fin (p + q) → Fin (p + q) → Module.End ℂ M₁.V` to `fun a b => M₁.act (ixC (single a b 1)) + ((j₂ / 2 : ℂ) * (ixC (single a b (1 : ℂ))).trace) • 1`. Take `⟨cs, hcs⟩` from `hC _ _ _ (twD m σ₁) (twD_rep m hσ₁) (twD_irr m hi₁)`. Establish `hone : ∀ {N : Type} [AddCommGroup N] [Module ℂ N] (E : Fin (p + q) → Fin (p + q) → Module.End ℂ N) a b, E a b = actM E (rx (ixC (single a b 1)))` using `fun E a b => by`. Rewrite using `[rx_ixC]`. Conclude with `((actLC_single E a b 1).trans (one_smul _ _)).symm`.

Establish `main : ∀ g ∈ Formalism.MainNotions.S.UJset (epq p q), ∀ w, U (twD m σ₁ g (io₁ w)) = twD j₂ σ₂ g (U (io₁ w))`. Introduce `g hg w`. Take `⟨W, hWf, hw, hWs⟩` from `M₁.kfin w`. Use `graphD (ε := epq p q) (twD_rep m hσ₁) (twD_rep j₂ hσ₂) (isDerivedOn_smE (twD_rep m hσ₁)) (isDerivedOn_smE (twD_rep j₂ hσ₂)) F κ₁ (r • (κ₂ ∘ₗ e.toLinearMap)) (fun a b h => m₁.1 (by rw [← hκ₁, ← hκ₁, h])) (fun a b w => by rw [hone (smE _ _) a b, a₁, hmj]; rfl) (fun a b w => by show …` as an intermediate fact. Rewrite using `[map_smul, hone (smE _ _) a b, a₂, map_add e, map_smul e, he, show (j₂ : ℂ) - j₂ / 2 = j₂ / 2 by ring])`.

Use `hcs U.toContinuousLinearEquiv.toContinuousLinearMap`. Use the proof step `(fun w => by show U (κ₁ w) = r • (κ₂ (e w) : π₂.H)`. Rewrite using `[hκ₁, hκ₂, hU])`. Use `hWf (fun a b hab u hu => add_mem (hWs _ (fun c d hcd => ?_) u hu) (W.smul_mem _ hu)) hw hg`. Establish `e2 : ((r • (κ₂ ∘ₗ e.toLinearMap)) w : π₂.H) = U (io₁ w)`.

Rewrite using `[hU, ← hκ₂]`. Both sides reduce to the same expression. Rewrite `this` using `[e2, hκ₁]`. Conclude with `this`. Use `show single a b (1 : ℂ) (finSumFinEquiv c) (finSumFinEquiv d) = 0`.

Rewrite using `[Matrix.single_apply, if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`. Simplify using `only [epq, Equiv.symm_apply_apply] at hab`. Apply the tactic sequence `rcases c with c | c <;> rcases d with d | d <;> simp_all [sameBlock]`. Use `⟨U, fun x => ?_⟩` and prove the remaining obligations.

Use `d₁.induction ?_ (isClosed_eq (U.continuous.comp (π₁.π x).continuous) ((π₂.π x).continuous.comp U.continuous))` and prove the remaining obligations. Introduce and unpack `_ ⟨w, rfl⟩`. Establish `h0 : ((T.sq x : ℂˣ) : ℂ) ^ j₂ ≠ 0` using `pow_ne_zero _ (Units.ne_zero _)`. Establish `h` using `main _ (mem_UJC T x) w`. Simplify using `only [twD, ContinuousLinearMap.smul_apply, det_rxC, ← sq_sqC, ← pow_mul] at h`.

Use `smul_right_injective _ h0 ?_` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[← map_smul U, hπ₁, hπ₂]`. Simplify using `only [ContinuousLinearMap.smul_apply, smul_smul, ← pow_add]`. Rewrite using `[show j₂ + j₁ = 2 * m by omega, show j₂ + j₂ = 2 * j₂ by omega]`.

Conclude with `h`.
-/
theorem clause2_of (h1 : Clause1) (hS : KFSm) (hC : CasScal) (hDe : Descend) : Clause2 := by
  intro p q hpq T π₁ π₂ i₁ i₂ M₁ M₂ io₁ io₂ m₁ m₂ e he
  obtain ⟨hA, hI⟩ := (h1 p q hpq T π₁ i₁).2.2 M₁ io₁ m₁
  obtain ⟨c, hc, hB⟩ := form_propD io₁ (io₂ ∘ₗ e.toLinearMap) m₁.1 (m₂.1.comp e.injective) (skewD m₁)
    (fun Y hY v w => by
      show ⟪io₂ (e (M₁.act Y v)), io₂ (e w)⟫_ℂ = -⟪io₂ (e v), io₂ (e (M₁.act Y w))⟫_ℂ
      rw [he, he]; exact skewD m₂ Y hY _ _) hI hA
  have hs : 0 < √c := Real.sqrt_pos.2 hc
  obtain ⟨r, hr⟩ : ∃ r : ℂ, r = (((√c)⁻¹ : ℝ) : ℂ) := ⟨_, rfl⟩
  have hr0 : r ≠ 0 := by rw [hr]; exact Complex.ofReal_ne_zero.2 (inv_pos.2 hs).ne'
  have dense : ∀ (π : URep T) (M : GKMod p q) (io : M.V →ₗ[ℂ] π.H), IsHCMod π M io → DenseRange io :=
    fun π M io m => (kfinDense_coverC (fun _ _ _ _ _ _ _ hσ => kfinDense_UJC hσ) π).mono fun x hx => (m.2.1 x).2 hx
  have d₁ := dense π₁ M₁ io₁ m₁
  have d₂ : DenseRange (r • io₂) := (dense π₂ M₂ io₂ m₂).mono (by
    rintro _ ⟨v, rfl⟩
    exact ⟨r⁻¹ • v, by rw [LinearMap.smul_apply, map_smul, smul_smul, mul_inv_cancel₀ hr0, one_smul]⟩)
  have hn : ∀ v, ‖(r • io₂) (e v)‖ = ‖io₁ v‖ := fun v => by
    have h2 : ‖io₂ (e v)‖ ^ 2 = c * ‖io₁ v‖ ^ 2 := by
      have := congrArg Complex.re (hB v v)
      rw [Complex.re_ofReal_mul] at this
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
      exact this
    have h3 : ‖io₂ (e v)‖ = √c * ‖io₁ v‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (io₂ (e v))), h2, Real.sqrt_mul hc.le, Real.sqrt_sq (norm_nonneg _)]
    rw [LinearMap.smul_apply, norm_smul, hr, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hs).le, h3,
      inv_mul_cancel_left₀ hs.ne']
  let U := e.extendOfIsometry io₁ (r • io₂) d₁ d₂ hn
  have hU : ∀ v, U (io₁ v) = r • io₂ (e v) := LinearEquiv.extendOfIsometry_eq e io₁ (r • io₂) d₁ d₂ hn
  obtain ⟨j₁, σ₁, ⟨hσ₁, hπ₁⟩, hi₁, hk₁, hx₁⟩ := hDe p q T π₁ i₁
  obtain ⟨j₂, σ₂, ⟨hσ₂, hπ₂⟩, hi₂, hk₂, hx₂⟩ := hDe p q T π₂ i₂
  obtain ⟨m, hm⟩ : Even (j₁ + j₂) := by
    obtain ⟨μ, v, hv, hv0⟩ := exists_hwD hI.1
    have a : Formalism.BasicNotions.TH.Ix p q := finSumFinEquiv.symm ⟨0, hpq⟩
    have hw := mem_wtSubD.1 (Submodule.mem_inf.1 hv).1 a
    have s₁ := signD m₁ hσ₁.1.1 hx₁ a hv0 hw
    have s₂ := signD m₂ hσ₂.1.1 hx₂ a (v := e v) (e.map_ne_zero_iff.2 hv0) (by rw [← he, hw, map_smul])
    refine (neg_one_pow_eq_one_iff_even (R := ℂ) (by norm_num)).1 ?_
    rw [pow_add, ← s₁, s₂, ← pow_add, ← two_mul, pow_mul]
    norm_num
  obtain ⟨κ₁, hκ₁, a₁⟩ := dictD hS m₁ m hσ₁ hi₁ hk₁ hx₁
  obtain ⟨κ₂, hκ₂, a₂⟩ := dictD hS m₂ j₂ hσ₂ hi₂ hk₂ hx₂
  have hmj : (m : ℂ) - j₁ / 2 = j₂ / 2 := by
    have : (j₁ : ℂ) + j₂ = m + m := by exact_mod_cast hm
    linear_combination (-1 / 2 : ℂ) * this
  let F : Fin (p + q) → Fin (p + q) → Module.End ℂ M₁.V := fun a b =>
    M₁.act (ixC (single a b 1)) + ((j₂ / 2 : ℂ) * (ixC (single a b (1 : ℂ))).trace) • 1
  obtain ⟨cs, hcs⟩ := hC _ _ _ (twD m σ₁) (twD_rep m hσ₁) (twD_irr m hi₁)
  have hone : ∀ {N : Type} [AddCommGroup N] [Module ℂ N] (E : Fin (p + q) → Fin (p + q) → Module.End ℂ N) a b,
      E a b = actM E (rx (ixC (single a b 1))) := fun E a b => by
    rw [rx_ixC]; exact ((actLC_single E a b 1).trans (one_smul _ _)).symm
  have main : ∀ g ∈ Formalism.MainNotions.S.UJset (epq p q), ∀ w, U (twD m σ₁ g (io₁ w)) = twD j₂ σ₂ g (U (io₁ w)) := by
    intro g hg w
    obtain ⟨W, hWf, hw, hWs⟩ := M₁.kfin w
    have := graphD (ε := epq p q) (twD_rep m hσ₁) (twD_rep j₂ hσ₂) (isDerivedOn_smE (twD_rep m hσ₁))
      (isDerivedOn_smE (twD_rep j₂ hσ₂)) F κ₁ (r • (κ₂ ∘ₗ e.toLinearMap))
      (fun a b h => m₁.1 (by rw [← hκ₁, ← hκ₁, h]))
      (fun a b w => by rw [hone (smE _ _) a b, a₁, hmj]; rfl)
      (fun a b w => by
        show smE _ _ a b (r • κ₂ (e w)) = r • κ₂ (e (M₁.act (ixC (single a b 1)) w + ((j₂ / 2 : ℂ) * (ixC (single a b (1 : ℂ))).trace) • w))
        rw [map_smul, hone (smE _ _) a b, a₂, map_add e, map_smul e, he,
          show (j₂ : ℂ) - j₂ / 2 = j₂ / 2 by ring])
      hcs U.toContinuousLinearEquiv.toContinuousLinearMap
      (fun w => by
        show U (κ₁ w) = r • (κ₂ (e w) : π₂.H)
        rw [hκ₁, hκ₂, hU])
      hWf (fun a b hab u hu => add_mem (hWs _ (fun c d hcd => ?_) u hu) (W.smul_mem _ hu)) hw hg
    · have e2 : ((r • (κ₂ ∘ₗ e.toLinearMap)) w : π₂.H) = U (io₁ w) := by
        rw [hU, ← hκ₂]; rfl
      rw [e2, hκ₁] at this
      exact this
    · show single a b (1 : ℂ) (finSumFinEquiv c) (finSumFinEquiv d) = 0
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      simp only [epq, Equiv.symm_apply_apply] at hab
      rcases c with c | c <;> rcases d with d | d <;> simp_all [sameBlock]
  refine ⟨U, fun x => ?_⟩
  refine d₁.induction ?_ (isClosed_eq (U.continuous.comp (π₁.π x).continuous) ((π₂.π x).continuous.comp U.continuous))
  rintro _ ⟨w, rfl⟩
  have h0 : ((T.sq x : ℂˣ) : ℂ) ^ j₂ ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
  have h := main _ (mem_UJC T x) w
  simp only [twD, ContinuousLinearMap.smul_apply, det_rxC, ← sq_sqC, ← pow_mul] at h
  refine smul_right_injective _ h0 ?_
  beta_reduce
  rw [← map_smul U, hπ₁, hπ₂]
  simp only [ContinuousLinearMap.smul_apply, smul_smul, ← pow_add]
  rw [show j₂ + j₁ = 2 * m by omega, show j₂ + j₂ = 2 * j₂ by omega]
  exact h

end GlobalTheory.HcPort

end

section
namespace GlobalTheory.HcPort
open CompanionTheory.D.gk.HC

/- English proof (translation)
The claim follows from `uIrr_of K_finite_smooth_vectors casimirActsByScalar_indefUnitary`.
-/
theorem uIrr : UIrr := uIrr_of K_finite_smooth_vectors casimirActsByScalar_indefUnitary

/- English proof (translation)
The claim follows from `uAdm_of K_finite_smooth_vectors`.
-/
theorem uAdm : UAdm := uAdm_of K_finite_smooth_vectors

/- English proof (translation)
The claim follows from `clause1_of K_finite_smooth_vectors integral_weights uIrr uAdm`.
-/
theorem clause1 : Clause1 := clause1_of K_finite_smooth_vectors integral_weights uIrr uAdm

/- English proof (translation)
The claim follows from `clause2_of clause1 K_finite_smooth_vectors casimirActsByScalar_indefUnitary harish_chandra_descent`.
-/
theorem clause2 : Clause2 := clause2_of clause1 K_finite_smooth_vectors casimirActsByScalar_indefUnitary harish_chandra_descent

/- English proof (translation)
The claim follows from `hcm_of clause1 clause2 harishChandraThird_indefiniteUnitary kFiniteVectors_analytic_indefiniteUnitary`.
-/
theorem print_harishChandraModules : GlobalTheory.Published.HarishChandraModules :=
  hcm_of clause1 clause2 harishChandraThird_indefiniteUnitary kFiniteVectors_analytic_indefiniteUnitary

end GlobalTheory.HcPort

end
