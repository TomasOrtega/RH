import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundamentalDomainMeasureEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.TranslatedRow

variable {D : D7}

def Good (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (F : GA D (D.sp.Y 0) → ℂ) : Prop :=
  Continuous F ∧ (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) ∧ (∀ γ ∈ GQ (D.sp.Y 0), ∀ g, F (γ * g) = F g) ∧
    (∀ k ∈ J, ∀ g, F (g * k) = χ k * F g)

/- English proof (translation)
Take `⟨c1, ⟨C1, b1⟩, l1, r1⟩` from `hF`. Take `⟨c2, ⟨C2, b2⟩, l2, r2⟩` from `hG`. Use `⟨c1.add c2, ⟨C1 + C2, fun g => (norm_add_le _ _).trans (add_le_add (b1 g) (b2 g))⟩, fun γ hγ g => by simp [l1 γ hγ g, l2 γ hγ g], fun k hk g => by simp [r1 k hk g, r2 k hk g, mul_add]⟩` and prove the remaining obligations.
-/
theorem good_add {J : Set (GA D (D.sp.Y 0))} {χ : GA D (D.sp.Y 0) → ℂ} {F G : GA D (D.sp.Y 0) → ℂ}
    (hF : Good J χ F) (hG : Good J χ G) : Good J χ (F + G) := by
  obtain ⟨c1, ⟨C1, b1⟩, l1, r1⟩ := hF
  obtain ⟨c2, ⟨C2, b2⟩, l2, r2⟩ := hG
  refine ⟨c1.add c2, ⟨C1 + C2, fun g => (norm_add_le _ _).trans (add_le_add (b1 g) (b2 g))⟩,
    fun γ hγ g => by simp [l1 γ hγ g, l2 γ hγ g], fun k hk g => by simp [r1 k hk g, r2 k hk g, mul_add]⟩

/- English proof (translation)
Take `⟨c1, ⟨C1, b1⟩, l1, r1⟩` from `hF`. Use `⟨continuous_const.mul c1, ⟨‖c‖ * C1, fun g => ?_⟩, fun γ hγ g => by simp [l1 γ hγ g], fun k hk g => by simp [r1 k hk g]; ring⟩` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul, norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (b1 g) (norm_nonneg _)`.
-/
theorem good_smul {J : Set (GA D (D.sp.Y 0))} {χ : GA D (D.sp.Y 0) → ℂ} {F : GA D (D.sp.Y 0) → ℂ} (c : ℂ)
    (hF : Good J χ F) : Good J χ (c • F) := by
  obtain ⟨c1, ⟨C1, b1⟩, l1, r1⟩ := hF
  refine ⟨continuous_const.mul c1, ⟨‖c‖ * C1, fun g => ?_⟩, fun γ hγ g => by simp [l1 γ hγ g],
    fun k hk g => by simp [r1 k hk g]; ring⟩
  rw [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (b1 g) (norm_nonneg _)

/- English proof (translation)
Establish `h1` using `(GlobalTheory.MultMem.mem_mult_iff D θ _ S M J χ _).1 ((mem_multT θ M J χ T).1 hT)`. Proceed by induction on `x using PiTensorProduct.induction_on with`. Consider the case `smul_tprod c v`. Rewrite using `[map_smul]`. Use `good_smul c ?_` and prove the remaining obligations.

Establish `e : T (PiTensorProduct.tprod ℂ v) = (PiTensorProduct.lift.symm T) v`. Rewrite using `[PiTensorProduct.lift_symm]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `⟨(h1.aut v).cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (h1.aut v) (h1.cusp v), (h1.aut v).left, fun k hk g => h1.lev v k hk g⟩`.

Consider the case `add a b ha hb`. Rewrite using `[map_add]`. Conclude with `good_add ha hb`.
-/
theorem good_of_mem (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ) {S : D.what₂.Tau → SPar}
    {M : DSModel (D.sp.Y 0) S} {J : Set (GA D (D.sp.Y 0))} {χ : GA D (D.sp.Y 0) → ℂ}
    {T : SmT M →ₗ[ℂ] (GA D (D.sp.Y 0) → ℂ)} (hT : T ∈ MultT θ M J χ) (x : SmT M) : Good J χ (T x) := by
  have h1 := (GlobalTheory.MultMem.mem_mult_iff D θ _ S M J χ _).1 ((mem_multT θ M J χ T).1 hT)
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    rw [map_smul]
    refine good_smul c ?_
    have e : T (PiTensorProduct.tprod ℂ v) = (PiTensorProduct.lift.symm T) v := by
      rw [PiTensorProduct.lift_symm]; rfl
    rw [e]
    exact ⟨(h1.aut v).cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (h1.aut v) (h1.cusp v), (h1.aut v).left,
      fun k hk g => h1.lev v k hk g⟩
  | add a b ha hb =>
    rw [map_add]
    exact good_add ha hb

end GlobalTheory.Core.Mi.TranslatedRow

namespace GlobalTheory.Core.Mi.TranslatedRow

variable {D : D7}

/- English proof (translation)
Substitute `p` using the available equality. Conclude with `hγ`.
-/
theorem castGA_symm_mem' {I I' : Formalism.MainNotions.S.AutInst} (p : I = I') (γ : I'.GA) (hγ : γ ∈ I'.GFset) :
    (castGA p).symm γ ∈ I.GFset := by
  subst p
  exact hγ

/- English proof (translation)
Use `(Formalism.IndefR.RationalEmbedding.iota_rat D ((iotaX X h).symm γ)).2 ?_` and prove the remaining obligations. Use `show Formalism.IndefR.RationalEmbedding.iota D ((Formalism.IndefR.RationalEmbedding.iota D).symm ((castGA h.symm).symm γ)) ∈ _`. Rewrite using `[ContinuousMulEquiv.apply_symm_apply]`. Conclude with `castGA_symm_mem' _ γ hγ`.
-/
theorem rat_of_GF (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (γ : X.B.I.GA) (hγ : γ ∈ X.B.I.GFset) : (iotaX X h).symm γ ∈ GQ (D.sp.Y 0) := by
  refine (Formalism.IndefR.RationalEmbedding.iota_rat D ((iotaX X h).symm γ)).2 ?_
  show Formalism.IndefR.RationalEmbedding.iota D ((Formalism.IndefR.RationalEmbedding.iota D).symm ((castGA h.symm).symm γ)) ∈ _
  rw [ContinuousMulEquiv.apply_symm_apply]
  exact castGA_symm_mem' _ γ hγ

/- English proof (translation)
Take `⟨hc, ⟨C, hb⟩, hl, hr⟩` from `hF`. Use `⟨hc.comp ((iotaX X h).symm.continuous.mul continuous_const), ⟨C, fun x => hb _⟩, fun γ hγ x => ?_, fun k hk x => ?_⟩` and prove the remaining obligations. Use `show F ((iotaX X h).symm (γ * x) * t) = F ((iotaX X h).symm x * t)`. Rewrite using `[map_mul, mul_assoc]`. Conclude with `hl _ (rat_of_GF X h γ hγ) _`.

Use `show F ((iotaX X h).symm (x * (1, k)) * t) = star (X.chi2 k) * F ((iotaX X h).symm x * t) set κ := t⁻¹ * (iotaX X h).symm (1, k) * t with hκ`. Establish `hc1` using `hm.2 κ`. Establish `e1 : t⁻¹⁻¹ * κ * t⁻¹ = (iotaX X h).symm (1, k)` using `by simp [hκ, mul_assoc]`. Rewrite `hc1` using `[e1]`. Establish `hrow : (iotaX X h).symm (1, k) ∈ rowJ X h`.

Simplify using `only [rowJ, Set.mem_preimage, ContinuousMulEquiv.apply_symm_apply, Set.mem_setOf_eq]`. Conclude with `⟨trivial, hk⟩`. Establish `hκJ : κ ∈ J` using `hc1.1.2 hrow`. Establish `hχ` using `hc1.2 hκJ`. Establish `e2 : (iotaX X h).symm (x * (1, k)) * t = ((iotaX X h).symm x * t) * κ`.

Simplify using `[hκ, map_mul, mul_assoc]`. Establish `e3 : rowChi X h ((iotaX X h).symm (1, k)) = star (X.chi2 k)`. Simplify using `only [rowChi, ContinuousMulEquiv.apply_symm_apply]`. Rewrite using `[e2, hr κ hκJ, ← hχ, e3]`.
-/
theorem rowFun_of_good (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    {J : Set (GA D (D.sp.Y 0))} {χ : GA D (D.sp.Y 0) → ℂ} {t : GA D (D.sp.Y 0)} (hm : Matches X h J χ t)
    {F : GA D (D.sp.Y 0) → ℂ} (hF : Good J χ F) : RowFun X (evS X h t F) := by
  obtain ⟨hc, ⟨C, hb⟩, hl, hr⟩ := hF
  refine ⟨hc.comp ((iotaX X h).symm.continuous.mul continuous_const), ⟨C, fun x => hb _⟩, fun γ hγ x => ?_,
    fun k hk x => ?_⟩
  · show F ((iotaX X h).symm (γ * x) * t) = F ((iotaX X h).symm x * t)
    rw [map_mul, mul_assoc]
    exact hl _ (rat_of_GF X h γ hγ) _
  · show F ((iotaX X h).symm (x * (1, k)) * t) = star (X.chi2 k) * F ((iotaX X h).symm x * t)
    set κ := t⁻¹ * (iotaX X h).symm (1, k) * t with hκ
    have hc1 := hm.2 κ
    have e1 : t⁻¹⁻¹ * κ * t⁻¹ = (iotaX X h).symm (1, k) := by simp [hκ, mul_assoc]
    rw [e1] at hc1
    have hrow : (iotaX X h).symm (1, k) ∈ rowJ X h := by
      simp only [rowJ, Set.mem_preimage, ContinuousMulEquiv.apply_symm_apply, Set.mem_setOf_eq]
      exact ⟨trivial, hk⟩
    have hκJ : κ ∈ J := hc1.1.2 hrow
    have hχ := hc1.2 hκJ
    have e2 : (iotaX X h).symm (x * (1, k)) * t = ((iotaX X h).symm x * t) * κ := by
      simp [hκ, map_mul, mul_assoc]
    have e3 : rowChi X h ((iotaX X h).symm (1, k)) = star (X.chi2 k) := by
      simp only [rowChi, ContinuousMulEquiv.apply_symm_apply]
    rw [e2, hr κ hκJ, ← hχ, e3]

/- English proof (translation)
Use `⟨?_⟩` and prove the remaining obligations. Rewrite using `[Measure.restrict_apply_univ]`. Conclude with `(GlobalTheory.AdelicVol.vol_finite_pos X.B.I X.B.μf X.B.fund X.B.fund_spec).1`.
-/
theorem muX_finite (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : IsFiniteMeasure (muX X) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact (GlobalTheory.AdelicVol.vol_finite_pos X.B.I X.B.μf X.B.fund X.B.fund_spec).1

end GlobalTheory.Core.Mi.TranslatedRow

open GlobalTheory.Core.Mi.TranslatedRow in

/- English proof (translation)
Introduce `hP D X h θ S M J χ t hθ hm T hT x`. Establish `hg` using `good_of_mem hP hθ hT x`. Establish `hR` using `rowFun_of_good X h hm hg`. Use `⟨hR, ?_⟩` and prove the remaining obligations. Use `haveI := muX_finite X`.

Take `⟨C, hC⟩` from `hR.bdd`. Conclude with `MemLp.of_bound hR.cont.aestronglyMeasurable C (.of_forall hC)`.
-/
theorem GlobalTheory.Core.Mi.rowFun_evS : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)), IsInfFam θ → Matches X h J χ t → ∀ T ∈ MultT θ M J χ, ∀ x : SmT M, RowFun X (evS X h t (T x)) ∧ MemLp (evS X h t (T x)) 2 (muX X) := by
  intro hP D X h θ S M J χ t hθ hm T hT x
  have hg := good_of_mem hP hθ hT x
  have hR := rowFun_of_good X h hm hg
  refine ⟨hR, ?_⟩
  haveI := muX_finite X
  obtain ⟨C, hC⟩ := hR.bdd
  exact MemLp.of_bound hR.cont.aestronglyMeasurable C (.of_forall hC)

end
