import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiActionTargetFlagUnipotentHomEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsInvInvariantOfRight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureFundamentalDomainLtTop
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelBaseValueEquivariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatWeilRepresentationCores
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatSchwartzEquivariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingBasePointFourierJacobiGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaIntegrandLocallyUniformMajorant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMixedCoordinatesContinuousBoundedSupNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationRationalTranslateSubstitution
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.FlatEval

section Abstract

variable {U A B C : Type} [MeasurableSpace U] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

/- English proof (translation)
Rewrite using `[integral_prod _ (Integrable.of_bound hf.aestronglyMeasurable c (Filter.Eventually.of_forall hc))]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Conclude with `integral_prod (fun q => f (a, q)) (Integrable.of_bound (hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable c (Filter.Eventually.of_forall fun q => hc _))`.
-/
theorem integral_triple (α : Measure A) (β : Measure B) (γ : Measure C) [IsFiniteMeasure α] [IsFiniteMeasure β]
    [IsFiniteMeasure γ] {f : A × B × C → ℂ} (hf : StronglyMeasurable f) {c : ℝ} (hc : ∀ p, ‖f p‖ ≤ c) :
    ∫ p, f p ∂α.prod (β.prod γ) = ∫ a, ∫ b, ∫ x, f (a, b, x) ∂γ ∂β ∂α := by
  rw [integral_prod _ (Integrable.of_bound hf.aestronglyMeasurable c (Filter.Eventually.of_forall hc))]
  congr 1
  funext a
  exact integral_prod (fun q => f (a, q)) (Integrable.of_bound
    (hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable c (Filter.Eventually.of_forall fun q => hc _))

/- English proof (translation)
Establish `hI : Integrable H (ν.prod (α.prod (β.prod γ)))` using `(hM.comp_fst (α.prod (β.prod γ))).mono' hH.aestronglyMeasurable (Filter.Eventually.of_forall hb)`. Establish `e : ∀ u, ∫ p, H (u, p) ∂α.prod (β.prod γ) = ∫ a, ∫ b, ∫ x, H (u, a, b, x) ∂γ ∂β ∂α` using `fun u => integral_triple α β γ (hH.comp_measurable measurable_prodMk_left) fun p => hb (u, p)`. Use `⟨by simpa only [e] using hI.integral_prod_left, ?_⟩` and prove the remaining obligations. Establish `e2` using `integral_triple α β γ (f := fun p => ∫ u, H (u, p) ∂ν) hH.integral_prod_left' (c := ∫ u, M u ∂ν) fun p => norm_integral_le_of_norm_le hM (Filter.Eventually.of_forall fun u => hb (u, p))`. Rewrite using `[← e2, ← integral_prod_symm H hI, integral_prod H hI]`.

Simplify using `only [e]`.
-/
theorem exchange (ν : Measure U) [SFinite ν] (α : Measure A) (β : Measure B) (γ : Measure C) [IsFiniteMeasure α]
    [IsFiniteMeasure β] [IsFiniteMeasure γ] {H : U × A × B × C → ℂ} (hH : StronglyMeasurable H) {M : U → ℝ}
    (hM : Integrable M ν) (hb : ∀ p, ‖H p‖ ≤ M p.1) :
    Integrable (fun u => ∫ a, ∫ b, ∫ x, H (u, a, b, x) ∂γ ∂β ∂α) ν ∧
      ∫ a, ∫ b, ∫ x, ∫ u, H (u, a, b, x) ∂ν ∂γ ∂β ∂α = ∫ u, ∫ a, ∫ b, ∫ x, H (u, a, b, x) ∂γ ∂β ∂α ∂ν := by
  have hI : Integrable H (ν.prod (α.prod (β.prod γ))) :=
    (hM.comp_fst (α.prod (β.prod γ))).mono' hH.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have e : ∀ u, ∫ p, H (u, p) ∂α.prod (β.prod γ) = ∫ a, ∫ b, ∫ x, H (u, a, b, x) ∂γ ∂β ∂α := fun u =>
    integral_triple α β γ (hH.comp_measurable measurable_prodMk_left) fun p => hb (u, p)
  refine ⟨by simpa only [e] using hI.integral_prod_left, ?_⟩
  have e2 := integral_triple α β γ (f := fun p => ∫ u, H (u, p) ∂ν) hH.integral_prod_left' (c := ∫ u, M u ∂ν)
    fun p => norm_integral_le_of_norm_le hM (Filter.Eventually.of_forall fun u => hb (u, p))
  rw [← e2, ← integral_prod_symm H hI, integral_prod H hI]
  simp only [e]

/- English proof (translation)
Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ` as an intermediate fact. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ ν` as an intermediate fact. Establish `hp` using `measurePreserving_mul_right ν a`. Establish `h2 : IsFundamentalDomain Γ ((· * a) ⁻¹' 𝓝) ν` using `h.preimage_of_equiv hp.quasiMeasurePreserving (e := id) Function.bijective_id fun γ x => by`. Simplify using `only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]`.

Rewrite using `[← hp.setIntegral_preimage_emb (measurableEmbedding_mulRight a) f 𝓝]`. Conclude with `h.setIntegral_eq h2 fun γ x => by`. Simplify using `only [Subgroup.smul_def, smul_eq_mul, mul_assoc, hf γ γ.2]`.
-/
theorem setIntegral_mul_right {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ]
    {ν : Measure G} [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] {𝓝 : Set G} (h : IsFundamentalDomain Γ 𝓝 ν)
    (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ n, f (γ * n) = f n) (a : G) : ∫ n in 𝓝, f (n * a) ∂ν = ∫ n in 𝓝, f n ∂ν := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ ν
  have hp := measurePreserving_mul_right ν a
  have h2 : IsFundamentalDomain Γ ((· * a) ⁻¹' 𝓝) ν :=
    h.preimage_of_equiv hp.quasiMeasurePreserving (e := id) Function.bijective_id fun γ x => by
      simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  rw [← hp.setIntegral_preimage_emb (measurableEmbedding_mulRight a) f 𝓝]
  exact h.setIntegral_eq h2 fun γ x => by
    simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc, hf γ γ.2]

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem sFinite_haar {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] (ν : Measure G) [ν.IsHaarMeasure] : SFinite ν :=
  inferInstance

end Abstract

variable {D : D7}

/- English proof (translation)
Use `neg_mem ⟨vecMulVec z fun i : Fin ρ => if i.1 + 1 = ρ then (1 : D.host.E) else 0, ?_⟩` and prove the remaining obligations. Rewrite using `[zEll, GlobalTheory.CharLaws.ell_eq]`. Use function extensionality and compare the values at `i j`. Conclude with `map_mul (incA D) _ _`.
-/
theorem yZero_mem (S : HSp D) (ρ : ℕ) (z : Fin S.rank → D.host.E) : yZero S ρ z ∈ ratMx D S.rank ρ := by
  refine neg_mem ⟨vecMulVec z fun i : Fin ρ => if i.1 + 1 = ρ then (1 : D.host.E) else 0, ?_⟩
  rw [zEll, GlobalTheory.CharLaws.ell_eq]
  funext i j
  exact map_mul (incA D) _ _

/- English proof (translation)
Establish `h1 : d.incAdj S y ∈ ratMx D T.rank S.rank`. Rewrite using `[d.incAdj_apply, d.incY_apply]`. Conclude with `ratMx_mul (rat_mem _) (ratMx_smul _ (ratMx_mul (ratMx_adj hy) (rat_mem _)))`. Establish `h2 : mt T γ⁻¹ ⬝ d.incAdj S y ∈ ratMx D T.rank S.rank` using `ratMx_mul ((mem_GQ_iff T _).1 (inv_mem hγ)) h1`. Take `⟨a, ha⟩` from `(GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.2.2.1 _ h1 _ h2`.

Take `⟨p, hp⟩ : ptT d S y γ ∈ ratMx D T₀.rank S.rank` from `ratMx_mul (rat_mem _) h2`. Establish `hq` using `hf.quasi p 0`. Rewrite `hq` using `[add_zero, symplOH_zero_right, neg_zero, AddChar.map_zero_eq_one, one_mul]`. Express the relevant statement in the definitionally equal form `ψ (cenT d S y γ) * (ψ (symplOH S T₀ 0 _) * f (0 + ptT d S y γ)) = f 0`. Rewrite using `[cenT, ha, hψ.2.2.1, one_mul, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add, ← hq]`.

Conclude with `congrArg f hp.symm`.
-/
theorem jacT_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ)
    (S : HSp D) {y : Mx D S.rank ρ} (hy : y ∈ ratMx D S.rank ρ) {γ : GA D T} (hγ : γ ∈ GQ T) {f : WO S T₀ → ℂ}
    (hf : IsThetaFunO ψ S T₀ f) : jacT ψ d S y γ f 0 = f 0 := by
  have h1 : d.incAdj S y ∈ ratMx D T.rank S.rank := by
    rw [d.incAdj_apply, d.incY_apply]
    exact ratMx_mul (rat_mem _) (ratMx_smul _ (ratMx_mul (ratMx_adj hy) (rat_mem _)))
  have h2 : mt T γ⁻¹ ⬝ d.incAdj S y ∈ ratMx D T.rank S.rank := ratMx_mul ((mem_GQ_iff T _).1 (inv_mem hγ)) h1
  obtain ⟨a, ha⟩ := (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.2.2.1 _ h1 _ h2
  obtain ⟨p, hp⟩ : ptT d S y γ ∈ ratMx D T₀.rank S.rank := ratMx_mul (rat_mem _) h2
  have hq := hf.quasi p 0
  rw [add_zero, symplOH_zero_right, neg_zero, AddChar.map_zero_eq_one, one_mul] at hq
  change ψ (cenT d S y γ) * (ψ (symplOH S T₀ 0 _) * f (0 + ptT d S y γ)) = f 0
  rw [cenT, ha, hψ.2.2.1, one_mul, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add, ← hq]
  exact congrArg f hp.symm

/- English proof (translation)
Express the relevant statement in the definitionally equal form `‖ψ (cenT d S y n) * (ψ (symplOH S T₀ 0 _) * f (0 + ptT d S y n))‖ = _`. Rewrite using `[norm_mul, norm_mul, hψ.2.1, hψ.2.1, one_mul, one_mul, zero_add]`.
-/
theorem norm_jacT {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ)
    (S : HSp D) (y : Mx D S.rank ρ) (n : GA D T) (f : WO S T₀ → ℂ) :
    ‖jacT ψ d S y n f 0‖ = ‖f (ptT d S y n)‖ := by
  change ‖ψ (cenT d S y n) * (ψ (symplOH S T₀ 0 _) * f (0 + ptT d S y n))‖ = _
  rw [norm_mul, norm_mul, hψ.2.1, hψ.2.1, one_mul, one_mul, zero_add]

/- English proof (translation)
Use `d.ga_ext ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.levi_jX, cancel₂ (d.wittDecomp_anisotropicEmbedding_inclX h)]`. Rewrite using `[mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, d.wittDecomp_levi_inclAnisotropic, cancel₂ (d.wittDecomp_levi_inclAnisotropic a), d.wittDecomp_anisotropicEmbedding_inclAnisotropic]`. Rewrite using `[mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclY, d.levi_jY, cancel₂ (d.wittDecomp_anisotropicEmbedding_inclY h)]`.
-/
theorem levi_commutes_with_ext_zero {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (a : GL (Fin ρ) (AE D)) (h : GA D S₀) :
    d.levi a * d.emb0 h = d.emb0 h * d.levi a := by
  refine d.ga_ext ?_ ?_ ?_
  · rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.levi_jX, cancel₂ (d.wittDecomp_anisotropicEmbedding_inclX h)]
  · rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, d.wittDecomp_levi_inclAnisotropic, cancel₂ (d.wittDecomp_levi_inclAnisotropic a), d.wittDecomp_anisotropicEmbedding_inclAnisotropic]
  · rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclY, d.levi_jY, cancel₂ (d.wittDecomp_anisotropicEmbedding_inclY h)]

section Step

variable {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J)

def ev (Ψ : WO B.V J.W → ℂ) (x : Mx D J.W.rank ρ) : WO B.V₀ J.W₀ → ℂ :=
  evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ x (yZero B.V₀ ρ (vecB B.o B.ζ))

/- English proof (translation)
The claim follows from `(GlobalTheory.MixValues.mixed_values D ψ s.weil.std).2 _ _ _ _ _ _ _ s.vT.covol _ ((GlobalTheory.MixValues.mixed_values D ψ s.weil.std).1 _ _ _ _ _ _ _ s.vS.covol _ hΨ x) _`.
-/
theorem ev_theta {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) (x : Mx D J.W.rank ρ) :
    IsThetaFunO ψ B.V₀ J.W₀ (ev s Ψ x) :=
  (GlobalTheory.MixValues.mixed_values D ψ s.weil.std).2 _ _ _ _ _ _ _ s.vT.covol _
    ((GlobalTheory.MixValues.mixed_values D ψ s.weil.std).1 _ _ _ _ _ _ _ s.vS.covol _ hΨ x) _

/- English proof (translation)
Rewrite using `[map_mul, Module.End.mul_apply]`.
-/
theorem om_om (p q : GA D B.V × GA D J.W) (Ψ : WO B.V J.W → ℂ) : s.om p (s.om q Ψ) = s.om (p * q) Ψ := by
  rw [map_mul, Module.End.mul_apply]

variable {om' : Om B.V₀ J.W} (hom : IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om')
include hom

/- English proof (translation)
Take `⟨γ, hγ, b, c, rfl⟩` from `((flag_jacobi_structure D J.W J.W₀ ρ J.d).1 n).1 hn`. Establish `hr : J.d.nB b * J.d.nC c ∈ radX J.d` using `mul_mem (nB_mem_radX J.d b) (nC_mem_radX J.d c)`. Establish `e : s.om (embA B.d B.o h₀, J.d.levi γ * (J.d.nB b * J.d.nC c) * J.d.emb0 h') Ψ = s.om (1, J.d.levi γ) (s.om (embA B.d B.o h₀, J.d.nB b * J.d.nC c * J.d.emb0 h') Ψ)`. Rewrite using `[om_om, Prod.mk_mul_mk, one_mul, mul_assoc]`. Establish `e2 : mt J.W (J.d.levi γ * (J.d.nB b * J.d.nC c)) ⬝ (xZero J.d ⬝ v.1.1) = xZero J.d ⬝ ((⟨γ, hγ⟩ * v : UX D ρ)).1.1`.

Rewrite using `[mt_mul, Matrix.mul_assoc, cancel₂ (show mt J.W (J.d.nB b * J.d.nC c) ⬝ xZero J.d = xZero J.d from hr.2), cancel₂ (levi_xZero J.d γ), Matrix.mul_assoc]`. Both sides reduce to the same expression. Establish `h2` using `(GlobalTheory.Unf.evalAt_xZero_yZero D ψ ρ B J s om' hom _ (s.weil.om_pres (embA B.d B.o h₀, J.d.nB b * J.d.nC c * J.d.emb0 h') _ hΨ)).2 (⟨γ, hγ⟩ * v) ⟨γ, hγ⟩`. Rewrite `h2` using `[inv_mul_cancel_left]`. Rewrite using `[e, e2, ev, h2, (GlobalTheory.Unf.evalAt_xZero_yZero D ψ ρ B J s om' hom Ψ hΨ).1 v h₀ _ hr h', opA, opA, jacT_levi_mul ψ J.d B.V₀ _ (yZero_mul B.V₀ _ hγ), ev]`.
-/
theorem ev_om {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) (v : UX D ρ) (h₀ : GA D B.A) {n : GA D J.W}
    (hn : n ∈ flagN J.d) (h' : GA D J.W₀) :
    ev s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (mt J.W n ⬝ (xZero J.d ⬝ v.1.1)) =
      s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (ev s Ψ (xZero J.d ⬝ v.1.1))) := by
  obtain ⟨γ, hγ, b, c, rfl⟩ := ((flag_jacobi_structure D J.W J.W₀ ρ J.d).1 n).1 hn
  have hr : J.d.nB b * J.d.nC c ∈ radX J.d := mul_mem (nB_mem_radX J.d b) (nC_mem_radX J.d c)
  have e : s.om (embA B.d B.o h₀, J.d.levi γ * (J.d.nB b * J.d.nC c) * J.d.emb0 h') Ψ =
      s.om (1, J.d.levi γ) (s.om (embA B.d B.o h₀, J.d.nB b * J.d.nC c * J.d.emb0 h') Ψ) := by
    rw [om_om, Prod.mk_mul_mk, one_mul, mul_assoc]
  have e2 : mt J.W (J.d.levi γ * (J.d.nB b * J.d.nC c)) ⬝ (xZero J.d ⬝ v.1.1) =
      xZero J.d ⬝ ((⟨γ, hγ⟩ * v : UX D ρ)).1.1 := by
    rw [mt_mul, Matrix.mul_assoc, cancel₂ (show mt J.W (J.d.nB b * J.d.nC c) ⬝ xZero J.d = xZero J.d from hr.2),
      cancel₂ (levi_xZero J.d γ), Matrix.mul_assoc]
    rfl
  have h2 := (GlobalTheory.Unf.evalAt_xZero_yZero D ψ ρ B J s om' hom _ (s.weil.om_pres
    (embA B.d B.o h₀, J.d.nB b * J.d.nC c * J.d.emb0 h') _ hΨ)).2 (⟨γ, hγ⟩ * v) ⟨γ, hγ⟩
  rw [inv_mul_cancel_left] at h2
  rw [e, e2, ev, h2, (GlobalTheory.Unf.evalAt_xZero_yZero D ψ ρ B J s om' hom Ψ hΨ).1 v h₀ _ hr h', opA, opA,
    jacT_levi_mul ψ J.d B.V₀ _ (yZero_mul B.V₀ _ hγ), ev]

/- English proof (translation)
Establish `h` using `ev_om s hom hΨ v 1 hn 1`. Rewrite `h` using `[map_one, map_one, mul_one, Prod.mk_one_one, map_one, opA, Prod.mk_one_one, map_one, Module.End.one_apply, Module.End.one_apply]`. Then use the resulting hypothesis.
-/
theorem ev_jac {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) (v : UX D ρ) {n : GA D J.W} (hn : n ∈ flagN J.d) :
    ev s (s.om (1, n) Ψ) (mt J.W n ⬝ (xZero J.d ⬝ v.1.1)) =
      jacT ψ J.d B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ)) n (ev s Ψ (xZero J.d ⬝ v.1.1)) := by
  have h := ev_om s hom hΨ v 1 hn 1
  rwa [map_one, map_one, mul_one, Prod.mk_one_one, map_one, opA, Prod.mk_one_one, map_one, Module.End.one_apply,
    Module.End.one_apply] at h

/- English proof (translation)
Establish `h` using `ev_om s hom hΨ v h₀ (one_mem _) h'`. Rewrite `h` using `[one_mul, mt_one, Matrix.one_mul, opA, jacT_one, id, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]`. Then use the resulting hypothesis.
-/
theorem ev_core {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) (v : UX D ρ) (h₀ : GA D B.A) (h' : GA D J.W₀) :
    ev s (s.om (embA B.d B.o h₀, J.d.emb0 h') Ψ) (xZero J.d ⬝ v.1.1) =
      s.om₀ (B.o.emb (h₀, 1), h') (ev s Ψ (xZero J.d ⬝ v.1.1)) := by
  have h := ev_om s hom hΨ v h₀ (one_mem _) h'
  rwa [one_mul, mt_one, Matrix.one_mul, opA, jacT_one, id, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one,
    one_mul] at h

/- English proof (translation)
Rewrite using `[fjKer, ← ev_om s hom hΨ v h₀ hn h', ← ev_jac s hom (s.weil.om_pres _ _ hΨ) v hn, om_om, Prod.mk_mul_mk, one_mul]`.
-/
theorem ker_eq {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) (v : UX D ρ) (h₀ : GA D B.A) {n : GA D J.W}
    (hn : n ∈ flagN J.d) (h' : GA D J.W₀) :
    fjKer ψ J.d B.o B.ζ s.om₀ (ev s Ψ (xZero J.d ⬝ v.1.1)) h₀ n h' =
      jacT ψ J.d B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ)) n
        (ev s (s.om (embA B.d B.o h₀, J.d.emb0 h') Ψ) (xZero J.d ⬝ v.1.1)) 0 := by
  rw [fjKer, ← ev_om s hom hΨ v h₀ hn h', ← ev_jac s hom (s.weil.om_pres _ _ hΨ) v hn, om_om, Prod.mk_mul_mk, one_mul]

/- English proof (translation)
Rewrite using `[ker_eq s hom hΨ v h₀ (mul_mem hγ hn), ker_eq s hom hΨ v h₀ hn, GlobalTheory.MixPer.JacHom.jacT_mul ψ J.d B.V₀ _ (fun u hu => yZero_mul B.V₀ _ hu) hγ hn, ← ev_jac s hom (s.weil.om_pres _ _ hΨ) v hn]`. Conclude with `jacT_rat s.weil.std.1 J.d B.V₀ (yZero_mem _ _ _) hγ' (ev_theta s (s.weil.om_pres _ _ (s.weil.om_pres _ _ hΨ)) _)`.
-/
theorem ker_left {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) (v : UX D ρ) (h₀ : GA D B.A) {γ n : GA D J.W}
    (hγ : γ ∈ flagN J.d) (hγ' : γ ∈ GQ J.W) (hn : n ∈ flagN J.d) (h' : GA D J.W₀) :
    fjKer ψ J.d B.o B.ζ s.om₀ (ev s Ψ (xZero J.d ⬝ v.1.1)) h₀ (γ * n) h' =
      fjKer ψ J.d B.o B.ζ s.om₀ (ev s Ψ (xZero J.d ⬝ v.1.1)) h₀ n h' := by
  rw [ker_eq s hom hΨ v h₀ (mul_mem hγ hn), ker_eq s hom hΨ v h₀ hn,
    GlobalTheory.MixPer.JacHom.jacT_mul ψ J.d B.V₀ _ (fun u hu => yZero_mul B.V₀ _ hu) hγ hn,
    ← ev_jac s hom (s.weil.om_pres _ _ hΨ) v hn]
  exact jacT_rat s.weil.std.1 J.d B.V₀ (yZero_mem _ _ _) hγ'
    (ev_theta s (s.weil.om_pres _ _ (s.weil.om_pres _ _ hΨ)) _)

/- English proof (translation)
Take `⟨γ, hγ, b, c, rfl⟩` from `((flag_jacobi_structure D J.W J.W₀ ρ J.d).1 n).1 hn`. Establish `hr : J.d.nB b * J.d.nC c ∈ radX J.d` using `mul_mem (nB_mem_radX J.d b) (nC_mem_radX J.d c)`. Establish `e : ∀ Ξ, fjKer ψ J.d B.o B.ζ s.om₀ Ξ h₀ (J.d.levi γ * (J.d.nB b * J.d.nC c)) h' = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ (J.d.nB b * J.d.nC c) h' Ξ) 0` using `fun Ξ => by`. Rewrite using `[fjKer, opA, opA, jacT_levi_mul ψ J.d B.V₀ _ (yZero_mul B.V₀ _ hγ)]`. Simplify using `only [e, ev]`.

Rewrite using `[← GlobalTheory.Unf.FlatCommBF.flatBF_om D ψ ρ B J s om' hom Ψ hΨ h₀ _ hr h']`. Simplify using `only [← (GlobalTheory.Unf.evalAt_xZero_yZero D ψ ρ B J s om' hom Ψ hΨ).1 _ h₀ _ hr h']`. Both sides reduce to the same expression.
-/
theorem ker_flat {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) (h₀ : GA D B.A) {n : GA D J.W}
    (hn : n ∈ flagN J.d) (h' : GA D J.W₀) :
    fjKer ψ J.d B.o B.ζ s.om₀ (flatBF s Ψ) h₀ n h' =
      ∫ v : UX D ρ, star (psiUni ψ v.1) * fjKer ψ J.d B.o B.ζ s.om₀ (ev s Ψ (xZero J.d ⬝ v.1.1)) h₀ n h' ∂s.vU.ν := by
  obtain ⟨γ, hγ, b, c, rfl⟩ := ((flag_jacobi_structure D J.W J.W₀ ρ J.d).1 n).1 hn
  have hr : J.d.nB b * J.d.nC c ∈ radX J.d := mul_mem (nB_mem_radX J.d b) (nC_mem_radX J.d c)
  have e : ∀ Ξ, fjKer ψ J.d B.o B.ζ s.om₀ Ξ h₀ (J.d.levi γ * (J.d.nB b * J.d.nC c)) h' =
      s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ (J.d.nB b * J.d.nC c) h' Ξ) 0 := fun Ξ => by
    rw [fjKer, opA, opA, jacT_levi_mul ψ J.d B.V₀ _ (yZero_mul B.V₀ _ hγ)]
  simp only [e, ev]
  rw [← GlobalTheory.Unf.FlatCommBF.flatBF_om D ψ ρ B J s om' hom Ψ hΨ h₀ _ hr h']
  simp only [← (GlobalTheory.Unf.evalAt_xZero_yZero D ψ ρ B J s om' hom Ψ hΨ).1 _ h₀ _ hr h']
  rfl

/- English proof (translation)
Take `⟨KA, hKA, cA⟩` from `B.cpt`. Take `⟨K0, hK0, c0⟩` from `J.cpt`. Establish `hc : Continuous (embA B.d B.o)` using `B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))`. Take `⟨M, hM, hb⟩` from `GlobalTheory.Unf.flatFun_majorant D ψ _ _ _ _ ρ ρ B.d J.d s.vS s.vT _ _ s.om s.weil s.vU J.d.e (linInd_e J.d) Ψ hΨ _ ((hKA.image hc).prod (hK0.image J.d.continuous_embed))`. Use `⟨M, hM, fun v h₀ n hn h' => ?_⟩` and prove the remaining obligations.

Take `⟨γ, hγ, hk⟩` from `cA h₀`. Take `⟨γ', hγ', hk'⟩` from `c0 h'`. Establish `e : s.om (embA B.d B.o h₀, J.d.emb0 h') Ψ = s.om (embA B.d B.o γ⁻¹, J.d.emb0 γ'⁻¹) (s.om (embA B.d B.o (γ * h₀), J.d.emb0 (γ' * h')) Ψ)`. Rewrite using `[om_om, Prod.mk_mul_mk, ← map_mul, ← map_mul, inv_mul_cancel_left, inv_mul_cancel_left]`. Establish `ht` using `s.weil.om_pres (embA B.d B.o (γ * h₀), J.d.emb0 (γ' * h')) _ hΨ`.

Establish `e2` using `GlobalTheory.Unf.om_rat_mul D ψ _ _ _ _ s.om₀ s.weil₀ _ (ev_theta s ht (xZero J.d ⬝ v.1.1)) _ (B.o.emb_mem_GQ (inv_mem hγ) (one_mem _)) _ (inv_mem hγ') 1 1`. Simplify using `only [mul_one, Prod.mk_one_one, map_one, Module.End.one_apply] at e2`. Rewrite using `[ker_eq s hom hΨ v h₀ hn, norm_mul, norm_jacT s.weil.std.1, e, ev_core s hom ht, e2, ← norm_mul]`. Conclude with `hb (embA B.d B.o (γ * h₀), J.d.emb0 (γ' * h')) ⟨⟨_, hk, rfl⟩, ⟨_, hk', rfl⟩⟩ _ _ v`.
-/
theorem ker_bound {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) : ∃ M : UX D ρ → ℝ, Integrable M s.vU.ν ∧
    ∀ (v : UX D ρ) h₀, ∀ n ∈ flagN J.d, ∀ h',
      ‖star (psiUni ψ v.1) * fjKer ψ J.d B.o B.ζ s.om₀ (ev s Ψ (xZero J.d ⬝ v.1.1)) h₀ n h'‖ ≤ M v := by
  obtain ⟨KA, hKA, cA⟩ := B.cpt
  obtain ⟨K0, hK0, c0⟩ := J.cpt
  have hc : Continuous (embA B.d B.o) :=
    B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))
  obtain ⟨M, hM, hb⟩ := GlobalTheory.Unf.flatFun_majorant D ψ _ _ _ _ ρ ρ B.d J.d s.vS s.vT _ _ s.om s.weil s.vU J.d.e (linInd_e J.d) Ψ hΨ _
    ((hKA.image hc).prod (hK0.image J.d.continuous_embed))
  refine ⟨M, hM, fun v h₀ n hn h' => ?_⟩
  obtain ⟨γ, hγ, hk⟩ := cA h₀
  obtain ⟨γ', hγ', hk'⟩ := c0 h'
  have e : s.om (embA B.d B.o h₀, J.d.emb0 h') Ψ = s.om (embA B.d B.o γ⁻¹, J.d.emb0 γ'⁻¹)
      (s.om (embA B.d B.o (γ * h₀), J.d.emb0 (γ' * h')) Ψ) := by
    rw [om_om, Prod.mk_mul_mk, ← map_mul, ← map_mul, inv_mul_cancel_left, inv_mul_cancel_left]
  have ht := s.weil.om_pres (embA B.d B.o (γ * h₀), J.d.emb0 (γ' * h')) _ hΨ
  have e2 := GlobalTheory.Unf.om_rat_mul D ψ _ _ _ _ s.om₀ s.weil₀ _ (ev_theta s ht (xZero J.d ⬝ v.1.1)) _
    (B.o.emb_mem_GQ (inv_mem hγ) (one_mem _)) _ (inv_mem hγ') 1 1
  simp only [mul_one, Prod.mk_one_one, map_one, Module.End.one_apply] at e2
  rw [ker_eq s hom hΨ v h₀ hn, norm_mul, norm_jacT s.weil.std.1, e, ev_core s hom ht, e2, ← norm_mul]
  exact hb (embA B.d B.o (γ * h₀), J.d.emb0 (γ' * h')) ⟨⟨_, hk, rfl⟩, ⟨_, hk', rfl⟩⟩ _ _ v

/- English proof (translation)
Establish `: IsTopologicalRing (AE D)` using `IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)`. Take `⟨-, -, -, -, _, -⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W`. Establish `hc : Continuous (embA B.d B.o)` using `B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))`. Establish `hn : Continuous fun p : UX D ρ × GA D J.W₀ × flagN J.d × GA D B.A => p.2.2.1.1` using `continuous_subtype_val.comp continuous_snd.snd.fst`. Establish `h1 : Continuous fun p : UX D ρ × GA D J.W₀ × flagN J.d × GA D B.A => ((embA B.d B.o p.2.2.2, p.2.2.1.1 * J.d.emb0 p.2.1), mt J.W p.2.2.1.1 ⬝ (xZero J.d ⬝ p.1.1.1), yZero B.V₀ ρ (vecB B.o B.ζ), (0 : WO B.V₀ J.W₀))` using `((hc.comp continuous_snd.snd.snd).prodMk (hn.mul (J.d.continuous_embed.comp continuous_snd.fst))).prodMk ((((GlobalTheory.MixModel.continuous_mt J.W).comp hn).matrix_mul (continuous_const.matrix_mul ((GlobalTheory.UnitU.isClosedEmbedding_val D ρ).continuous.comp continuous_fst))) …`.

Use `((GlobalTheory.MixCont.mixed_coords_continuous D ψ _ _ _ _ ρ ρ B.d J.d s.vS s.vT _ _ s.om s.weil Ψ hΨ).2.comp h1).congr fun p => ?_` and prove the remaining obligations. Conclude with `congrFun (ev_om s hom hΨ p.1 p.2.2.2 p.2.2.1.2 p.2.1) 0`.
-/
theorem ker_cont {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) :
    Continuous fun p : UX D ρ × GA D J.W₀ × flagN J.d × GA D B.A =>
      fjKer ψ J.d B.o B.ζ s.om₀ (ev s Ψ (xZero J.d ⬝ p.1.1.1)) p.2.2.2 p.2.2.1.1 p.2.1 := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  obtain ⟨-, -, -, -, _, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  have hc : Continuous (embA B.d B.o) :=
    B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))
  have hn : Continuous fun p : UX D ρ × GA D J.W₀ × flagN J.d × GA D B.A => p.2.2.1.1 :=
    continuous_subtype_val.comp continuous_snd.snd.fst
  have h1 : Continuous fun p : UX D ρ × GA D J.W₀ × flagN J.d × GA D B.A =>
      ((embA B.d B.o p.2.2.2, p.2.2.1.1 * J.d.emb0 p.2.1), mt J.W p.2.2.1.1 ⬝ (xZero J.d ⬝ p.1.1.1),
        yZero B.V₀ ρ (vecB B.o B.ζ), (0 : WO B.V₀ J.W₀)) :=
    ((hc.comp continuous_snd.snd.snd).prodMk (hn.mul (J.d.continuous_embed.comp continuous_snd.fst))).prodMk
      ((((GlobalTheory.MixModel.continuous_mt J.W).comp hn).matrix_mul (continuous_const.matrix_mul
        ((GlobalTheory.UnitU.isClosedEmbedding_val D ρ).continuous.comp continuous_fst))).prodMk continuous_const)
  refine ((GlobalTheory.MixCont.mixed_coords_continuous D ψ _ _ _ _ ρ ρ B.d J.d s.vS s.vT _ _ s.om s.weil Ψ hΨ).2.comp h1).congr fun p => ?_
  exact congrFun (ev_om s hom hΨ p.1 p.2.2.2 p.2.2.1.2 p.2.1) 0

end Step

/- English proof (translation)
Take `⟨K, hK, h⟩` from `hV`. Take `⟨_, _, _, _, _, _, _⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V`. Use `v.haar` as an intermediate fact. Use `⟨isFiniteMeasure_restrict.2 (GlobalTheory.BesselConvDefinite.measure_fundamentalDomain_lt_top (GQ V) hK (fun g => ?_) v.μ v.fund).ne, fun φ hφ => (RapidDec.of_isCompact hφ.1 hφ.2 hK h).bounded⟩` and prove the remaining obligations. Take `⟨γ, hγ, hk⟩` from `h g`.

Conclude with `⟨γ⁻¹, inv_mem hγ, _, hk, (inv_mul_cancel_left γ g).symm⟩`.
-/
theorem cpt_facts {V : HSp D} (hV : CoCpt V) (v : Vol V) : IsFiniteMeasure (v.μ.restrict v.𝓕) ∧
    ∀ φ, IsContAut V φ → ∃ c, ∀ g, ‖φ g‖ ≤ c := by
  obtain ⟨K, hK, h⟩ := hV
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have := v.haar
  refine ⟨isFiniteMeasure_restrict.2 (GlobalTheory.BesselConvDefinite.measure_fundamentalDomain_lt_top (GQ V) hK (fun g => ?_)
    v.μ v.fund).ne, fun φ hφ => (RapidDec.of_isCompact hφ.1 hφ.2 hK h).bounded⟩
  obtain ⟨γ, hγ, hk⟩ := h g
  exact ⟨γ⁻¹, inv_mem hγ, _, hk, (inv_mul_cancel_left γ g).symm⟩

/- English proof (translation)
Use `psiFlag_levi_mul ψ d a (one_mem (stabX d))` as an intermediate fact. Rewrite `this` using `[mul_one]`. Then use the resulting hypothesis.
-/
theorem psiFlag_levi (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (a : GL (Fin ρ) (AE D)) :
    psiFlag ψ d (d.levi a) = psiUni ψ a := by
  have := psiFlag_levi_mul ψ d a (one_mem (stabX d))
  rwa [mul_one] at this

/- English proof (translation)
Take `⟨_, _, _, _, _, _, _⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W`. Take `⟨_, _, _, _⟩` from `GlobalTheory.Mem.TrueRecord.top_NFlag J.W (isIsoSub_e J.d)`. Take `⟨hH, hF, h1⟩` from `J.vN.unit`. Use `GlobalTheory.UnitU.isMulRightInvariant_of_fundamentalDomain _ J.vN.ν hF (by rw [h1]; exact one_ne_zero) (by rw [h1]; exact ENNReal.one_ne_top)` as an intermediate fact. Establish `hu` using `GlobalTheory.FlatEqui.levi_mem_flagN J.d u.2`.

Unfold `JacLev.perAll fjAll`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `h'`. Rewrite using `[← setIntegral_mul_right (NFlagQ J.W J.d.e) hF (fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ G _ h') ?_ ⟨_, hu⟩, ← integral_const_mul]`.

Use `congr 1`. Use function extensionality and compare the values at `n`. Establish `e1 : psiFlag ψ J.d n.1 = psiFlag ψ J.d (n.1 * J.d.levi u.1) * psiUni ψ (u⁻¹).1`. Rewrite using `[← psiFlag_levi ψ J.d, ← psiFlag_mul J.d ψ (mul_mem n.2 hu) (GlobalTheory.FlatEqui.levi_mem_flagN J.d (u⁻¹).2), mul_assoc, ← map_mul, Subgroup.coe_inv, mul_inv_cancel, map_one, mul_one]`. Simplify using `only [fjAllFun, rTrans, fjKer, opA, Subgroup.coe_mul, GlobalTheory.MixPer.JacHom.jacT_mul_levi ψ J.d B.V₀ _ (fun u hu => yZero_mul B.V₀ _ hu) _ u.2]`.

Rewrite using `[e1, star_mul', mul_assoc n.1 (J.d.levi _), levi_commutes_with_ext_zero, ← mul_assoc n.1]`. Expand and normalize the polynomial expressions, which then agree. Introduce `γ hγ n`. Establish `e1 : psiFlag ψ J.d γ.1 = 1`. Rewrite using `[psiFlag_eq]`.

Conclude with `GlobalTheory.CharLaws.psiBes_rat ψ J.d s.weil.std.1.2.2.1 1 0 hγ`. Simplify using `only [fjAllFun, Subgroup.coe_mul, ker_left s hom hΨ v _ γ.2 hγ n.2]`. Rewrite using `[psiFlag_mul J.d ψ γ.2 n.2, e1, one_mul, mul_assoc γ.1, hG γ.1 hγ]`.
-/
theorem per_levi {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J)
    {om' : Om B.V₀ J.W} (hom : IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om') {Ψ : WO B.V J.W → ℂ}
    (hΨ : IsThetaFunO ψ B.V J.W Ψ) (φ : GA D B.A → ℂ) {G : GA D J.W → ℂ} (hG : ∀ γ ∈ GQ J.W, ∀ g, G (γ * g) = G g)
    (u v : UX D ρ) :
    J.perAll ψ B s.om₀ φ (rTrans (J.d.levi u.1) G) (ev s Ψ (xZero J.d ⬝ v.1.1)) =
      star (psiUni ψ (u⁻¹).1) * J.perAll ψ B s.om₀ φ G (ev s Ψ (xZero J.d ⬝ v.1.1)) := by
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  obtain ⟨_, _, _, _⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag J.W (isIsoSub_e J.d)
  obtain ⟨hH, hF, h1⟩ := J.vN.unit
  have := GlobalTheory.UnitU.isMulRightInvariant_of_fundamentalDomain _ J.vN.ν hF (by rw [h1]; exact one_ne_zero)
    (by rw [h1]; exact ENNReal.one_ne_top)
  have hu := GlobalTheory.FlatEqui.levi_mem_flagN J.d u.2
  unfold JacLev.perAll fjAll
  rw [← integral_const_mul]
  congr 1
  funext h'
  rw [← setIntegral_mul_right (NFlagQ J.W J.d.e) hF (fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ G _ h') ?_ ⟨_, hu⟩,
    ← integral_const_mul]
  · congr 1
    funext n
    have e1 : psiFlag ψ J.d n.1 = psiFlag ψ J.d (n.1 * J.d.levi u.1) * psiUni ψ (u⁻¹).1 := by
      rw [← psiFlag_levi ψ J.d, ← psiFlag_mul J.d ψ (mul_mem n.2 hu) (GlobalTheory.FlatEqui.levi_mem_flagN J.d (u⁻¹).2),
        mul_assoc, ← map_mul, Subgroup.coe_inv, mul_inv_cancel, map_one, mul_one]
    simp only [fjAllFun, rTrans, fjKer, opA, Subgroup.coe_mul,
      GlobalTheory.MixPer.JacHom.jacT_mul_levi ψ J.d B.V₀ _ (fun u hu => yZero_mul B.V₀ _ hu) _ u.2]
    rw [e1, star_mul', mul_assoc n.1 (J.d.levi _), levi_commutes_with_ext_zero, ← mul_assoc n.1]
    ring
  · intro γ hγ n
    have e1 : psiFlag ψ J.d γ.1 = 1 := by
      rw [psiFlag_eq]
      exact GlobalTheory.CharLaws.psiBes_rat ψ J.d s.weil.std.1.2.2.1 1 0 hγ
    simp only [fjAllFun, Subgroup.coe_mul, ker_left s hom hΨ v _ γ.2 hγ n.2]
    rw [psiFlag_mul J.d ψ γ.2 n.2, e1, one_mul, mul_assoc γ.1, hG γ.1 hγ]

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `D ψ ρ B J s om' hom φ G Φ hφ hG hΦ h`. Take `⟨_, _, _, _, _, _, _⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W`. Take `⟨_, _, _, _, _, _, _⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W₀`. Take `⟨_, _, _, _, _, _, _⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A`. Take `⟨_, _, _, _⟩` from `GlobalTheory.Mem.TrueRecord.top_NFlag J.W (isIsoSub_e J.d)`.

Take `⟨_, _, _⟩` from `GlobalTheory.UnitU.topology D ρ`. Establish `: BorelSpace (UX D ρ)` using `⟨rfl⟩`. Use `s.vU.unit.1` as an intermediate fact. Use `(GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).2.2 _ s.vU.unit` as an intermediate fact. Use `GlobalTheory.CartanInt.isInvInvariant_of_right s.vU.ν` as an intermediate fact.

Establish `: SFinite s.vU.ν` using `sFinite_haar s.vU.ν`. Establish `hψ` using `s.weil.std.1`. Take `⟨_, hA⟩` from `cpt_facts B.cpt B.vA`. Take `⟨_, -⟩` from `cpt_facts J.cpt J.v0`. Establish `: IsFiniteMeasure (J.vN.ν.restrict J.vN.𝓝)` using `isFiniteMeasure_restrict.2 (by rw [J.vN.unit.2.2]; exact ENNReal.one_ne_top)`.

Take `⟨a, ha⟩` from `hA φ hφ`. Establish `hG'` using `hG.mul_right h`. Take `⟨c, hc⟩` from `hG'.bounded`. Use `set Ψ := s.om (1, h) Φ with hΨ'`. Establish `hΨ : IsThetaFunO ψ B.V J.W Ψ` using `s.weil.om_pres _ _ hΦ`.

Take `⟨M, hM, hb⟩` from `ker_bound s hom hΨ`. Establish `hfl : Continuous (psiFlag ψ J.d)`. Rewrite using `[funext (psiFlag_eq J.d ψ)]`. Conclude with `GlobalTheory.CharLaws.continuous_psiBes ψ J.d hψ.1 1 0`. Establish `hun : Continuous fun v : UX D ρ => psiUni ψ v.1`.

Simplify using `only [← psiFlag_levi ψ J.d]`. Conclude with `hfl.comp (J.d.continuous_levi.comp continuous_subtype_val)`. Set `H : UX D ρ × GA D J.W₀ × flagN J.d × GA D B.A → ℂ` to `fun p => rTrans h G (p.2.2.1.1 * J.d.emb0 p.2.1) * star (psiFlag ψ J.d p.2.2.1.1) * (φ p.2.2.2 * (star (psiUni ψ p.1.1) * fjKer ψ J.d B.o B.ζ s.om₀ (ev s Ψ (xZero J.d ⬝ p.1.1.1)) p.2.2.2 p.2.2.1.1 p.2.1))`. Establish `hn : Continuous fun p : UX D ρ × GA D J.W₀ × flagN J.d × GA D B.A => p.2.2.1.1` using `continuous_subtype_val.comp continuous_snd.snd.fst`. Establish `hH : Continuous H` using `((hG'.continuous.comp (hn.mul (J.d.continuous_embed.comp continuous_snd.fst))).mul (hfl.comp hn).star).mul ((hφ.2.comp continuous_snd.snd.snd).mul ((hun.comp continuous_fst).star.mul (ker_cont s hom hΨ)))`.

Establish `hHb : ∀ p, ‖H p‖ ≤ c * a * M p.1` using `fun p => by`. Establish `e : ‖star (psiFlag ψ J.d p.2.2.1.1)‖ = 1` using `by rw [norm_star]; exact hψ.2.1 _`. Simplify using `only [H]`. Rewrite using `[norm_mul, norm_mul, e, mul_one, norm_mul, mul_assoc]`. Conclude with `mul_le_mul (hc _) (mul_le_mul (ha _) (hb _ _ _ p.2.2.1.2 _) (norm_nonneg _) ((norm_nonneg _).trans (ha 1))) (by positivity) ((norm_nonneg _).trans (hc 1))`.

Take `⟨hI, hE⟩` from `exchange s.vU.ν (J.v0.μ.restrict J.v0.𝓕) (J.vN.ν.restrict J.vN.𝓝) (B.vA.μ.restrict B.vA.𝓕) hH.stronglyMeasurable (hM.const_mul (c * a)) hHb`. Establish `eR : ∀ v : UX D ρ, ∫ h' in J.v0.𝓕, ∫ n in J.vN.𝓝, ∫ h₀ in B.vA.𝓕, H (v, h', n, h₀) ∂B.vA.μ ∂J.vN.ν ∂J.v0.μ = star (psiUni ψ v.1) * J.perAll ψ B s.om₀ φ (rTrans h G) (ev s Ψ (xZero J.d ⬝ v.1.1))` using `fun v => by`. Unfold `JacLev.perAll fjAll fjAllFun`. Simplify using `only [← integral_const_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `h'`. Use `congr 1`. Use function extensionality and compare the values at `n`. Use `congr 1`. Use function extensionality and compare the values at `h₀`.

Simplify using `only [H]`. Expand and normalize the polynomial expressions, which then agree. Establish `eL : J.perAll ψ B s.om₀ φ (rTrans h G) (flatBF s Ψ) = ∫ h' in J.v0.𝓕, ∫ n in J.vN.𝓝, ∫ h₀ in B.vA.𝓕, ∫ v, H (v, h', n, h₀) ∂s.vU.ν ∂B.vA.μ ∂J.vN.ν ∂J.v0.μ`. Unfold `JacLev.perAll fjAll fjAllFun`. Use `congr 1`.

Use function extensionality and compare the values at `h'`. Use `congr 1`. Use function extensionality and compare the values at `n`. Simplify using `only [ker_flat s hom hΨ _ n.2, H, integral_const_mul]`. Establish `eU : ∀ u : UX D ρ, J.perAll ψ B s.om₀ φ (rTrans (J.d.levi u.1 * h) G) (evalBF s (s.om (1, (J.d.levi u.1 * h)) Φ)) = star (psiUni ψ (u⁻¹).1) * J.perAll ψ B s.om₀ φ (rTrans h G) (ev s Ψ (xZero J.d ⬝ (u⁻¹).1.1))` using `fun u => by`.

Establish `e1 : rTrans (J.d.levi u.1 * h) G = rTrans (J.d.levi u.1) (rTrans h G)`. Use function extensionality and compare the values at `g`. Simplify using `only [rTrans, mul_assoc]`. Establish `e2` using `(GlobalTheory.Unf.evalAt_xZero_yZero D ψ ρ B J s om' hom Ψ hΨ).2 1 u`. Rewrite `e2` using `[mul_one, hΨ', om_om, Prod.mk_mul_mk, one_mul, OneMemClass.coe_one, Units.val_one, Matrix.mul_one]`.

Rewrite using `[e1, ← per_levi s hom hΨ φ (G := rTrans h G) hG'.1 u u⁻¹]`. Conclude with `congrArg _ e2`. Simplify using `only [eR] at hI hE`. Simplify using `only [eU]`. Conclude with `⟨hI.comp_inv, by rw [eL, hE, ← integral_inv_eq_self]⟩`.
-/
theorem perAll_flat_eq_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ → ∀ h, Integrable (fun u : UX D ρ => J.perAll ψ B s.om₀ φ (rTrans (J.d.levi u.1 * h) G) (evalBF s (s.om (1, (J.d.levi u.1 * h)) Φ))) s.vU.ν ∧ J.perAll ψ B s.om₀ φ (rTrans h G) (flatBF s (s.om (1, h) Φ)) = ∫ u : UX D ρ, J.perAll ψ B s.om₀ φ (rTrans (J.d.levi u.1 * h) G) (evalBF s (s.om (1, (J.d.levi u.1 * h)) Φ)) ∂s.vU.ν := by
  intro D ψ ρ B J s om' hom φ G Φ hφ hG hΦ h
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W₀
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  obtain ⟨_, _, _, _⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag J.W (isIsoSub_e J.d)
  obtain ⟨_, _, _⟩ := GlobalTheory.UnitU.topology D ρ
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  have := s.vU.unit.1
  have := (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).2.2 _ s.vU.unit
  have := GlobalTheory.CartanInt.isInvInvariant_of_right s.vU.ν
  have : SFinite s.vU.ν := sFinite_haar s.vU.ν
  have hψ := s.weil.std.1
  obtain ⟨_, hA⟩ := cpt_facts B.cpt B.vA
  obtain ⟨_, -⟩ := cpt_facts J.cpt J.v0
  have : IsFiniteMeasure (J.vN.ν.restrict J.vN.𝓝) :=
    isFiniteMeasure_restrict.2 (by rw [J.vN.unit.2.2]; exact ENNReal.one_ne_top)
  obtain ⟨a, ha⟩ := hA φ hφ
  have hG' := hG.mul_right h
  obtain ⟨c, hc⟩ := hG'.bounded
  set Ψ := s.om (1, h) Φ with hΨ'
  have hΨ : IsThetaFunO ψ B.V J.W Ψ := s.weil.om_pres _ _ hΦ
  obtain ⟨M, hM, hb⟩ := ker_bound s hom hΨ
  have hfl : Continuous (psiFlag ψ J.d) := by
    rw [funext (psiFlag_eq J.d ψ)]
    exact GlobalTheory.CharLaws.continuous_psiBes ψ J.d hψ.1 1 0
  have hun : Continuous fun v : UX D ρ => psiUni ψ v.1 := by
    simp only [← psiFlag_levi ψ J.d]
    exact hfl.comp (J.d.continuous_levi.comp continuous_subtype_val)
  let H : UX D ρ × GA D J.W₀ × flagN J.d × GA D B.A → ℂ := fun p =>
    rTrans h G (p.2.2.1.1 * J.d.emb0 p.2.1) * star (psiFlag ψ J.d p.2.2.1.1) * (φ p.2.2.2 * (star (psiUni ψ p.1.1) *
      fjKer ψ J.d B.o B.ζ s.om₀ (ev s Ψ (xZero J.d ⬝ p.1.1.1)) p.2.2.2 p.2.2.1.1 p.2.1))
  have hn : Continuous fun p : UX D ρ × GA D J.W₀ × flagN J.d × GA D B.A => p.2.2.1.1 :=
    continuous_subtype_val.comp continuous_snd.snd.fst
  have hH : Continuous H :=
    ((hG'.continuous.comp (hn.mul (J.d.continuous_embed.comp continuous_snd.fst))).mul (hfl.comp hn).star).mul
      ((hφ.2.comp continuous_snd.snd.snd).mul ((hun.comp continuous_fst).star.mul (ker_cont s hom hΨ)))
  have hHb : ∀ p, ‖H p‖ ≤ c * a * M p.1 := fun p => by
    have e : ‖star (psiFlag ψ J.d p.2.2.1.1)‖ = 1 := by rw [norm_star]; exact hψ.2.1 _
    simp only [H]
    rw [norm_mul, norm_mul, e, mul_one, norm_mul, mul_assoc]
    exact mul_le_mul (hc _) (mul_le_mul (ha _) (hb _ _ _ p.2.2.1.2 _) (norm_nonneg _) ((norm_nonneg _).trans (ha 1)))
      (by positivity) ((norm_nonneg _).trans (hc 1))
  obtain ⟨hI, hE⟩ := exchange s.vU.ν (J.v0.μ.restrict J.v0.𝓕) (J.vN.ν.restrict J.vN.𝓝) (B.vA.μ.restrict B.vA.𝓕)
    hH.stronglyMeasurable (hM.const_mul (c * a)) hHb
  have eR : ∀ v : UX D ρ, ∫ h' in J.v0.𝓕, ∫ n in J.vN.𝓝, ∫ h₀ in B.vA.𝓕, H (v, h', n, h₀) ∂B.vA.μ ∂J.vN.ν ∂J.v0.μ =
      star (psiUni ψ v.1) * J.perAll ψ B s.om₀ φ (rTrans h G) (ev s Ψ (xZero J.d ⬝ v.1.1)) := fun v => by
    unfold JacLev.perAll fjAll fjAllFun
    simp only [← integral_const_mul]
    congr 1; funext h'; congr 1; funext n; congr 1; funext h₀
    simp only [H]
    ring
  have eL : J.perAll ψ B s.om₀ φ (rTrans h G) (flatBF s Ψ) = ∫ h' in J.v0.𝓕, ∫ n in J.vN.𝓝, ∫ h₀ in B.vA.𝓕,
      ∫ v, H (v, h', n, h₀) ∂s.vU.ν ∂B.vA.μ ∂J.vN.ν ∂J.v0.μ := by
    unfold JacLev.perAll fjAll fjAllFun
    congr 1; funext h'; congr 1; funext n
    simp only [ker_flat s hom hΨ _ n.2, H, integral_const_mul]
  have eU : ∀ u : UX D ρ, J.perAll ψ B s.om₀ φ (rTrans (J.d.levi u.1 * h) G)
      (evalBF s (s.om (1, (J.d.levi u.1 * h)) Φ)) = star (psiUni ψ (u⁻¹).1) *
        J.perAll ψ B s.om₀ φ (rTrans h G) (ev s Ψ (xZero J.d ⬝ (u⁻¹).1.1)) := fun u => by
    have e1 : rTrans (J.d.levi u.1 * h) G = rTrans (J.d.levi u.1) (rTrans h G) := by
      funext g; simp only [rTrans, mul_assoc]
    have e2 := (GlobalTheory.Unf.evalAt_xZero_yZero D ψ ρ B J s om' hom Ψ hΨ).2 1 u
    rw [mul_one, hΨ', om_om, Prod.mk_mul_mk, one_mul, OneMemClass.coe_one, Units.val_one, Matrix.mul_one] at e2
    rw [e1, ← per_levi s hom hΨ φ (G := rTrans h G) hG'.1 u u⁻¹]
    exact congrArg _ e2
  simp only [eR] at hI hE
  simp only [eU]
  exact ⟨hI.comp_inv, by rw [eL, hE, ← integral_inv_eq_self]⟩

end GlobalTheory.FlatEval

end
