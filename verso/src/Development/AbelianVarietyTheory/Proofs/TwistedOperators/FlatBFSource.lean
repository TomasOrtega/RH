import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandBesselPeriodInvariantProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleOrthogonalSumSourceStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.Unf.FB GlobalTheory.FinPl.HandInvPf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesMove

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

/- English proof (translation)
Establish `h : adj (xZero d' ⬝ w) ⬝ (gA T ⬝ (xZero d' ⬝ w)) = 0`. Rewrite using `[xZero, adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA T), ← Matrix.mul_assoc (adj d'.jX), d'.gram_XX, Matrix.zero_mul, Matrix.mul_zero]`. Rewrite using `[← cenS_nC, ← neg_inj, LinkPoint.neg_cenS_eq, h, Matrix.zero_mul, trace_zero, map_zero, neg_zero]`.
-/
theorem qS_xZero {S S₀ T T₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (d' : HypDec T T₀ ρ) (c : skewA D ρ) (w : Mx D ρ ρ) :
    d.qS T c (xZero d' ⬝ w) = 0 := by
  have h : adj (xZero d' ⬝ w) ⬝ (gA T ⬝ (xZero d' ⬝ w)) = 0 := by
    rw [xZero, adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA T), ← Matrix.mul_assoc (adj d'.jX), d'.gram_XX,
      Matrix.zero_mul, Matrix.mul_zero]
  rw [← cenS_nC, ← neg_inj, LinkPoint.neg_cenS_eq, h, Matrix.zero_mul, trace_zero, map_zero, neg_zero]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hψ` using `s.weil.std`. Take `⟨u, hu, b, c, rfl⟩` from `GlobalTheory.MixPer.Decomp.flag_decomp B.d hn`. Take `⟨om', hom'⟩` from `(GlobalTheory.Desc.weil_data_descend D ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d`. Establish `FS` using `fun f hf => GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS.μ s.vS.𝓕 s.vS.covol f hf`. Establish `MV` using `fun x => (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x`.

Establish `hfl : psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.levi u * (B.d.nB b * B.d.nC c)) = psiUni ψ u * psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b)`. Rewrite using `[psiBes_mul B.d ψ 1 _ (B.d.levi_mem_NFlag hu) (mul_mem (B.d.nB_mem_NFlag b) (B.d.nC_mem_NFlag c)), psiBes_mul B.d ψ 1 _ (B.d.nB_mem_NFlag b) (B.d.nC_mem_NFlag c), psiBes_nC, mul_one, psiBes_levi]`. Establish `hdet : Matrix.GeneralLinearGroup.det u = 1`. Establish `bt : Matrix.BlockTriangular u.1 id` using `fun a b h => (hu a b).1 h`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular bt, Units.val_one]`. Conclude with `Finset.prod_eq_one fun i _ => (hu i i).2`. Establish `hmod : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod J.W.rank u = 1`. Rewrite using `[GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, hdet, map_one, NNReal.coe_one, Real.one_rpow]`. Establish `h1` using `s.weil.om_pres (B.d.nC c, 1) Ψ hΨ`.

Establish `h2` using `s.weil.om_pres (B.d.nB b, 1) _ h1`. Establish `e : s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ = s.om (B.d.levi u, 1) (s.om (B.d.nB b, 1) (s.om (B.d.nC c, 1) Ψ))`. Rewrite using `[← om_mul, ← om_mul, mul_assoc, mul_one, mul_one]`. Set `u' : UX D ρ` to `⟨u, hu⟩`. Establish `key : ∀ v : UX D ρ, evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ) (xZero J.d ⬝ v.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b) • evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (v * u').1. …`.

Introduce `v`. Establish `ex : xZero J.d ⬝ v.1.1 ⬝ u.1 = xZero J.d ⬝ (v * u').1.1`. Rewrite using `[Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]`. Establish `t1` using `(FS _ h2).levi u (xZero J.d ⬝ v.1.1)`. Rewrite `t1` using `[hdet, hmod, map_one, inv_one, Circle.coe_one, Complex.ofReal_one, mul_one, one_smul, ex]`.

Establish `t2` using `(FS _ h1).unip b (xZero J.d ⬝ (v * u').1.1)`. Rewrite `t2` using `[Matrix.mul_assoc (xZero J.d)]`. Establish `t3 : B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 (s.om (B.d.nC c, 1) Ψ) (xZero J.d ⬝ (v * u').1.1) = ψ (B.d.qS J.W c (xZero J.d ⬝ (v * u').1.1)) • B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1)` using `(FS _ hΨ).centre c _`. Rewrite `t3` using `[qS_xZero, AddChar.map_zero_eq_one, one_smul]`. Establish `t4` using `(GlobalTheory.T.heisenbergThetaMixedModelTarget_of_mixedModel D ψ hψ B.V₀ J.W J.W₀ ρ J.d s.vT.μ s.vT.𝓕 s.vT.covol _ (MV (xZero J.d ⬝ (v * u').1.1))).1 ((v * u').1.1 ⬝ b) (yZero B.V₀ ρ (vecB B.o B.ζ))`.

Establish `t5 : ψ (symplO B.V₀ J.W (J.d.incAdj B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ))) (J.d.incX B.V₀ ((v * u').1.1 ⬝ b))) = psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b)`. Use `(psi_yZero ψ B.d J.d _ _).trans ?_` and prove the remaining obligations. Rewrite using `[psiBes_nB, psiBes_nB, ← Matrix.mulVec_mulVec, dotProduct_mulVec (ell D ρ) (v * u').1.1, ell_vecMul (v * u').2]`. Rewrite `t4` using `[t5]`. Unfold `evalAt`.

Rewrite using `[e, t1, t2, t3]`. Conclude with `t4`. Establish `: BorelSpace (UX D ρ)` using `⟨rfl⟩`. Take `⟨i1, i2, i3⟩` from `GlobalTheory.UnitU.topology D ρ`. Use `(GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).2.2 _ s.vU.unit` as an intermediate fact.

Establish `hmul : ∀ v : UX D ρ, psiUni ψ (v * u').1 = psiUni ψ v.1 * psiUni ψ u` using `fun v => by`. Rewrite using `[← ThLaws.psiFlag_levi ψ J.d, ← ThLaws.psiFlag_levi ψ J.d, ← ThLaws.psiFlag_levi ψ J.d, Subgroup.coe_mul, map_mul, psiFlag_mul J.d ψ (J.d.levi_mem_NFlag v.2) (J.d.levi_mem_NFlag hu)]`. Establish `hu1 : psiUni ψ u * star (psiUni ψ u) = 1` using `mul_star_psi hψ _`. Use function extensionality and compare the values at `w`. Rewrite using `[hfl]`.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Express the relevant statement in the definitionally equal form `∫ v, star (psiUni ψ v.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ) (xZero J.d ⬝ v.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν = _ * ∫ v, star (psiUni ψ v.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ v.1.1) …`. Use `conv_rhs => rw [← integral_mul_right_eq_self _ u', ← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `v`.

Rewrite using `[key, hmul, star_mul']`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Generalize the expression as in `evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) _ _ = z`. Take the linear combination `(-(star (psiUni ψ v.1) * psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b) * z)) * hu1`.
-/
theorem flatBF_source {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {Ψ : WO B.V J.W → ℂ}
    (hΨ : IsThetaFunO ψ B.V J.W Ψ) {n : GA D B.V} (hn : n ∈ flagN B.d) :
    flatBF s (s.om (n, 1) Ψ) = psiBes ψ B.d 1 (vecB B.o B.ζ) n • flatBF s Ψ := by
  have hψ := s.weil.std
  obtain ⟨u, hu, b, c, rfl⟩ := GlobalTheory.MixPer.Decomp.flag_decomp B.d hn
  obtain ⟨om', hom'⟩ := (GlobalTheory.Desc.weil_data_descend D ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  have FS := fun f hf => GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS.μ s.vS.𝓕 s.vS.covol f hf
  have MV := fun x => (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  have hfl : psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.levi u * (B.d.nB b * B.d.nC c)) =
      psiUni ψ u * psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b) := by
    rw [psiBes_mul B.d ψ 1 _ (B.d.levi_mem_NFlag hu) (mul_mem (B.d.nB_mem_NFlag b) (B.d.nC_mem_NFlag c)),
      psiBes_mul B.d ψ 1 _ (B.d.nB_mem_NFlag b) (B.d.nC_mem_NFlag c), psiBes_nC, mul_one, psiBes_levi]
  have hdet : Matrix.GeneralLinearGroup.det u = 1 := by
    have bt : Matrix.BlockTriangular u.1 id := fun a b h => (hu a b).1 h
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular bt, Units.val_one]
    exact Finset.prod_eq_one fun i _ => (hu i i).2
  have hmod : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod J.W.rank u = 1 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, hdet, map_one, NNReal.coe_one, Real.one_rpow]
  have h1 := s.weil.om_pres (B.d.nC c, 1) Ψ hΨ
  have h2 := s.weil.om_pres (B.d.nB b, 1) _ h1
  have e : s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ =
      s.om (B.d.levi u, 1) (s.om (B.d.nB b, 1) (s.om (B.d.nC c, 1) Ψ)) := by
    rw [← om_mul, ← om_mul, mul_assoc, mul_one, mul_one]
  let u' : UX D ρ := ⟨u, hu⟩
  have key : ∀ v : UX D ρ,
      evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ) (xZero J.d ⬝ v.1.1)
          (yZero B.V₀ ρ (vecB B.o B.ζ)) =
        psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b) •
          evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) := by
    intro v
    have ex : xZero J.d ⬝ v.1.1 ⬝ u.1 = xZero J.d ⬝ (v * u').1.1 := by
      rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
    have t1 := (FS _ h2).levi u (xZero J.d ⬝ v.1.1)
    rw [hdet, hmod, map_one, inv_one, Circle.coe_one, Complex.ofReal_one, mul_one, one_smul, ex] at t1
    have t2 := (FS _ h1).unip b (xZero J.d ⬝ (v * u').1.1)
    rw [Matrix.mul_assoc (xZero J.d)] at t2
    have t3 : B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 (s.om (B.d.nC c, 1) Ψ) (xZero J.d ⬝ (v * u').1.1) =
        ψ (B.d.qS J.W c (xZero J.d ⬝ (v * u').1.1)) • B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) :=
      (FS _ hΨ).centre c _
    rw [qS_xZero, AddChar.map_zero_eq_one, one_smul] at t3
    have t4 := (GlobalTheory.T.heisenbergThetaMixedModelTarget_of_mixedModel D ψ hψ B.V₀ J.W J.W₀ ρ J.d s.vT.μ s.vT.𝓕 s.vT.covol _ (MV (xZero J.d ⬝ (v * u').1.1))).1
      ((v * u').1.1 ⬝ b) (yZero B.V₀ ρ (vecB B.o B.ζ))
    have t5 : ψ (symplO B.V₀ J.W (J.d.incAdj B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ))) (J.d.incX B.V₀ ((v * u').1.1 ⬝ b))) =
        psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b) := by
      refine (psi_yZero ψ B.d J.d _ _).trans ?_
      rw [psiBes_nB, psiBes_nB, ← Matrix.mulVec_mulVec, dotProduct_mulVec (ell D ρ) (v * u').1.1, ell_vecMul (v * u').2]
    rw [t5] at t4
    unfold evalAt
    rw [e, t1, t2, t3]
    exact t4
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.UnitU.topology D ρ
  have := (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).2.2 _ s.vU.unit
  have hmul : ∀ v : UX D ρ, psiUni ψ (v * u').1 = psiUni ψ v.1 * psiUni ψ u := fun v => by
    rw [← ThLaws.psiFlag_levi ψ J.d, ← ThLaws.psiFlag_levi ψ J.d, ← ThLaws.psiFlag_levi ψ J.d, Subgroup.coe_mul, map_mul,
      psiFlag_mul J.d ψ (J.d.levi_mem_NFlag v.2) (J.d.levi_mem_NFlag hu)]
  have hu1 : psiUni ψ u * star (psiUni ψ u) = 1 := mul_star_psi hψ _
  funext w
  rw [hfl]
  simp only [Pi.smul_apply, smul_eq_mul]
  change ∫ v, star (psiUni ψ v.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕
      (s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ) (xZero J.d ⬝ v.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν = _ *
    ∫ v, star (psiUni ψ v.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ v.1.1)
      (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν
  conv_rhs => rw [← integral_mul_right_eq_self _ u', ← integral_const_mul]
  congr 1
  funext v
  rw [key, hmul, star_mul']
  simp only [Pi.smul_apply, smul_eq_mul]
  generalize evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) _ _ = z
  linear_combination (-(star (psiUni ψ v.1) * psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b) * z)) * hu1

/- English proof (translation)
Take `⟨om', hom'⟩` from `(GlobalTheory.Desc.weil_data_descend D ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d`. Establish `hΨ` using `s.weil.om_pres (g, h) Φ hΦ`. Establish `c` using `GlobalTheory.T.besselToJacobiFlatSchwartz_equivariant D ψ _ B J s om' hom' _ hΨ a 1 (one_mem _) 1`. Establish `p1 : psiFlag ψ J.d 1 = 1`. Use `psiFlag_levi_mul ψ J.d 1 (one_mem (stabX J.d))` as an intermediate fact.

Rewrite `this` using `[map_one, mul_one]`. Rewrite using `[this, psiUni, Units.val_one, upSum_one, psiE_zero]`. Rewrite `c` using `[map_one, mul_one, p1, star_one, one_smul, opA, jacT_one, id, show s.om₀ (1, 1) = 1 from map_one _, Module.End.one_apply]`. Rewrite using `[← c, ← flatBF_source s (s.weil.om_pres _ _ hΨ) hn, ← om_mul, ← om_mul, one_mul, one_mul]`.
-/
theorem flatBF_bes {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {Φ : WO B.V J.W → ℂ}
    (hΦ : IsThetaFunO ψ B.V J.W Φ) {n : GA D B.V} (hn : n ∈ flagN B.d) (a : GA D B.A) (g : GA D B.V) (h : GA D J.W) :
    flatBF s (s.om (n * embA B.d B.o a * g, h) Φ) =
      psiBes ψ B.d 1 (vecB B.o B.ζ) n • s.om₀ (B.o.emb (a, 1), 1) (flatBF s (s.om (g, h) Φ)) := by
  obtain ⟨om', hom'⟩ := (GlobalTheory.Desc.weil_data_descend D ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  have hΨ := s.weil.om_pres (g, h) Φ hΦ
  have c := GlobalTheory.T.besselToJacobiFlatSchwartz_equivariant D ψ _ B J s om' hom' _ hΨ a 1 (one_mem _) 1
  have p1 : psiFlag ψ J.d 1 = 1 := by
    have := psiFlag_levi_mul ψ J.d 1 (one_mem (stabX J.d))
    rw [map_one, mul_one] at this
    rw [this, psiUni, Units.val_one, upSum_one, psiE_zero]
  rw [map_one, mul_one, p1, star_one, one_smul, opA, jacT_one, id, show s.om₀ (1, 1) = 1 from map_one _,
    Module.End.one_apply] at c
  rw [← c, ← flatBF_source s (s.weil.om_pres _ _ hΨ) hn, ← om_mul, ← om_mul, one_mul, one_mul]

/- English proof (translation)
Establish `hact : actO V₀ S (o.emb (γ, 1)) 1 ((o.resS S).symm (0, y)) = (o.resS S).symm (0, y)`. Apply `(o.resS S).injective` to reduce the goal to its premises. Rewrite using `[o.resS_actO, AddEquiv.apply_symm_apply]`. Simplify using `only [actO_eq, inv_one, mt_one, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul]`. Establish `h0 : ∀ F : WO V₀ S → ℂ, ∀ p, heisO ψ V₀ S p F 0 = F p` using `fun F p => by`.

Rewrite using `[heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]`. Establish `h1` using `congrFun (hom.om_heis (o.emb (γ, 1)) 1 ((o.resS S).symm (0, y)) f hf) 0`. Rewrite `h1` using `[hact, h0]`. Rewrite using `[← h1, hom.om_aut _ (o.emb_mem_GQ hγ (one_mem _)) 1 (one_mem _) _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hom.std hf _), h0]`.
-/
theorem om_rat_line {V₀ A L S : HSp D} (o : OrthDec V₀ A L) {χ χ' : (AE D)ˣ →* Circle} {om : Om V₀ S}
    (hom : IsWeilDatumO ψ V₀ S χ χ' om) {γ : GA D A} (hγ : γ ∈ GQ A) {f : WO V₀ S → ℂ} (hf : IsThetaFunO ψ V₀ S f) (y : WO L S) :
    om (o.emb (γ, 1), 1) f ((o.resS S).symm (0, y)) = f ((o.resS S).symm (0, y)) := by
  have hact : actO V₀ S (o.emb (γ, 1)) 1 ((o.resS S).symm (0, y)) = (o.resS S).symm (0, y) := by
    apply (o.resS S).injective
    rw [o.resS_actO, AddEquiv.apply_symm_apply]
    simp only [actO_eq, inv_one, mt_one, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul]
  have h0 : ∀ F : WO V₀ S → ℂ, ∀ p, heisO ψ V₀ S p F 0 = F p := fun F p => by
    rw [heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]
  have h1 := congrFun (hom.om_heis (o.emb (γ, 1)) 1 ((o.resS S).symm (0, y)) f hf) 0
  rw [hact, h0] at h1
  rw [← h1, hom.om_aut _ (o.emb_mem_GQ hγ (one_mem _)) 1 (one_mem _) _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hom.std hf _), h0]

/- English proof (translation)
Use function extensionality and compare the values at `h w`. Unfold `handBF`. Use `congr 1`. Rewrite using `[← GlobalTheory.ChainOnto.setIntegral_fd_mul_right D B.A B.vA.μ B.vA.𝓕 B.vA.haar B.vA.fund (fun h₀ => φ h₀ * s.om₀ (B.o.emb (h₀, 1), h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w))) ?_ a]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Rewrite using `[map_smul, ← om_mul, ← map_mul, Prod.mk_mul_mk, mul_one, mul_one]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, rTrans]`. Take the linear combination `(φ (x * a) * s.om₀ (B.o.emb (x * a, 1), h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w))) * hc`. Introduce `γ hγ x`.

Establish `e : s.om₀ (B.o.emb (γ * x, 1), h) Ξ = s.om₀ (B.o.emb (γ, 1), 1) (s.om₀ (B.o.emb (x, 1), h) Ξ)`. Rewrite using `[← om_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]`. Simplify using `only [hφ γ hγ]`. Rewrite using `[e, om_rat_line B.o s.weil₀ hγ (s.weil₀.om_pres _ _ hΞ)]`.
-/
theorem handBF_move {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {L' : HSp D} {ζ' : Fin L'.rank → D.host.E}
    (l : Link B L' ζ') {φ : GA D B.A → ℂ} (hφ : ∀ γ ∈ GQ B.A, ∀ g, φ (γ * g) = φ g) {Ξ : WO B.V₀ J.W₀ → ℂ}
    (hΞ : IsThetaFunO ψ B.V₀ J.W₀ Ξ) (c : ℂ) (hc : c * star c = 1) (a : GA D B.A) :
    handBF s l (star c • rTrans a φ) (c • s.om₀ (B.o.emb (a, 1), 1) Ξ) = handBF s l φ Ξ := by
  funext h w
  unfold handBF
  congr 1
  rw [← GlobalTheory.ChainOnto.setIntegral_fd_mul_right D B.A B.vA.μ B.vA.𝓕 B.vA.haar B.vA.fund
    (fun h₀ => φ h₀ * s.om₀ (B.o.emb (h₀, 1), h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w))) ?_ a]
  · congr 1
    funext x
    rw [map_smul, ← om_mul, ← map_mul, Prod.mk_mul_mk, mul_one, mul_one]
    simp only [Pi.smul_apply, smul_eq_mul, rTrans]
    linear_combination (φ (x * a) * s.om₀ (B.o.emb (x * a, 1), h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w))) * hc
  · intro γ hγ x
    have e : s.om₀ (B.o.emb (γ * x, 1), h) Ξ = s.om₀ (B.o.emb (γ, 1), 1) (s.om₀ (B.o.emb (x, 1), h) Ξ) := by
      rw [← om_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    simp only [hφ γ hγ]
    rw [e, om_rat_line B.o s.weil₀ hγ (s.weil₀.om_pres _ _ hΞ)]

/- English proof (translation)
Establish `hD : Descent D` using `GlobalTheory.Desc.weil_data_descend D`. Establish `hΨ₂` using `s₂.weil.om_pres (h₁, h₂) Φ₂ hΦ₂`. Establish `e : flatFB s₂ (s₂.om (h₁, n * embA B'.d B'.o a * h₂) Φ₂) = star (psiBes ψ B'.d 1 (vecB B'.o B'.ζ) n) • s₂.om₀ (1, B'.o.emb (a, 1)) (flatFB s₂ (s₂.om (h₁, h₂) Φ₂))`. Establish `c` using `GlobalTheory.T.jacobiToBesselFlat_intertwines_weilAction D hD ψ σ J B' s₂ _ hΨ₂ 1 a`. Rewrite `c` using `[map_one]`.

Rewrite using `[← c, ← GlobalTheory.T.flatSchwartz_targetUnipotent_conj_besselCharacter D hD ψ σ J B' s₂ _ (s₂.weil.om_pres _ _ hΨ₂) n hn, ← om_mul, ← om_mul, one_mul, one_mul]`. Unfold `Chain.hand`. Rewrite using `[e, handFB_smul_om]`.
-/
theorem hand_right {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ} (s₁ : StepBF ψ B J)
    (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (Φ₁ : WO B.V J.W → ℂ) {Φ₂ : WO J.W B'.V → ℂ}
    (hΦ₂ : IsThetaFunO ψ J.W B'.V Φ₂) (φ : GA D B.A → ℂ) (g : GA D B.V) (h₁ : GA D J.W) (h₂ : GA D B'.V)
    {n : GA D B'.V} (hn : n ∈ flagN B'.d) (a : GA D B'.A) :
    Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ (n * embA B'.d B'.o a * h₂) =
      star (psiBes ψ B'.d 1 (vecB B'.o B'.ζ) n) • rTrans a (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂) := by
  have hD : Descent D := GlobalTheory.Desc.weil_data_descend D
  have hΨ₂ := s₂.weil.om_pres (h₁, h₂) Φ₂ hΦ₂
  have e : flatFB s₂ (s₂.om (h₁, n * embA B'.d B'.o a * h₂) Φ₂) = star (psiBes ψ B'.d 1 (vecB B'.o B'.ζ) n) •
      s₂.om₀ (1, B'.o.emb (a, 1)) (flatFB s₂ (s₂.om (h₁, h₂) Φ₂)) := by
    have c := GlobalTheory.T.jacobiToBesselFlat_intertwines_weilAction D hD ψ σ J B' s₂ _ hΨ₂ 1 a
    rw [map_one] at c
    rw [← c, ← GlobalTheory.T.flatSchwartz_targetUnipotent_conj_besselCharacter D hD ψ σ J B' s₂ _ (s₂.weil.om_pres _ _ hΨ₂) n hn, ← om_mul, ← om_mul, one_mul, one_mul]
  unfold Chain.hand
  rw [e, handFB_smul_om]

/- English proof (translation)
Establish `hΞ` using `(GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) ψ).1 _ B J s₁ _ (s₁.weil.om_pres (g, h₁) Φ₁ hΦ₁)`. Unfold `Chain.hand`. Rewrite using `[flatBF_bes s₁ hΦ₁ hn, handBF_move s₁ l hφ hΞ (psiBes ψ B.d 1 (vecB B.o B.ζ) n) (mul_star_psi s₁.weil.std _)]`.
-/
theorem hand_left {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ} (s₁ : StepBF ψ B J)
    (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) {Φ₁ : WO B.V J.W → ℂ} (Φ₂ : WO J.W B'.V → ℂ)
    (hΦ₁ : IsThetaFunO ψ B.V J.W Φ₁) {φ : GA D B.A → ℂ} (hφ : ∀ γ ∈ GQ B.A, ∀ g, φ (γ * g) = φ g)
    (g : GA D B.V) (h₁ : GA D J.W) (h₂ : GA D B'.V) {n : GA D B.V} (hn : n ∈ flagN B.d) (a : GA D B.A) :
    Chain.hand s₁ s₂ l vL Φ₁ Φ₂ (star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) • rTrans a φ) (n * embA B.d B.o a * g) h₁ h₂ =
      Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂ := by
  have hΞ := (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) ψ).1 _ B J s₁ _ (s₁.weil.om_pres (g, h₁) Φ₁ hΦ₁)
  unfold Chain.hand
  rw [flatBF_bes s₁ hΦ₁ hn, handBF_move s₁ l hφ hΞ (psiBes ψ B.d 1 (vecB B.o B.ζ) n) (mul_star_psi s₁.weil.std _)]

/- English proof (translation)
Establish `hsrc` using `GlobalTheory.T.thetaTensorRule_orthogonalSum_source D ψ h₁.std V₀ A L o S`. Establish `e0 : ∀ v, (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) = Φ₂ (o''.resT S v).1 • fun u => Ξ ((o.resS S).symm (u, GlobalTheory.FinPl.kap τ S (o''.resT S v).2))` using `fun v => rfl`. Establish `e1 : ∀ v, (fun u => GlobalTheory.FinPl.lastBi o o'' τ (c • om₁ (o.emb (a, 1), 1) Ξ) Φ₂ u v) = c • oma (a, 1) fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v` using `fun v => by`. Use function extensionality and compare the values at `u`. Establish `k` using `(hsrc.om_slice χA χz χS om₁ oma omz h₁ ha hz a 1 1 Ξ hΞ (GlobalTheory.FinPl.kap τ S (o''.resT S v).2)).2 u`.

Rewrite `k` using `[show omz (1, 1) = 1 from map_one _]`. Simplify using `only [Module.End.one_apply] at k`. Rewrite using `[e0, map_smul]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, GlobalTheory.FinPl.lastBi, OrthDec.boxT, k]`. Expand and normalize the polynomial expressions, which then agree.

Use function extensionality and compare the values at `h₂`. Unfold `GlobalTheory.SeeSaw.biLift`. Use `congr 1`. Use function extensionality and compare the values at `h`. Rewrite using `[← GlobalTheory.ChainOnto.setIntegral_fd_mul_right D A vA.μ vA.𝓕 vA.haar vA.fund (fun h₀ => φ h₀ * omb (h, h₂) (fun v => oma (h₀, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0) 0) ?_ a]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Establish `e2 : (fun v => oma (x, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ (c • om₁ (o.emb (a, 1), 1) Ξ) Φ₂ u v) 0) = c • fun v => oma (x * a, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0`. Use function extensionality and compare the values at `v`. Rewrite using `[e1, map_smul, ← om_mul, mul_one]`.

Both sides reduce to the same expression. Rewrite using `[e2, map_smul]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, rTrans]`. Take the linear combination `(φ (x * a) * omb (h, h₂) (fun v => oma (x * a, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0) 0) * hc`. Introduce `γ hγ x`.

Establish `e : ∀ v, oma (γ * x, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0 = oma (x, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0` using `fun v => by`. Establish `k` using `ha.om_aut γ hγ 1 (one_mem _) _ (ha.om_pres (x, h) _ ((hsrc.slice_theta Ξ hΞ).1 (GlobalTheory.FinPl.kap τ S (o''.resT S v).2)))`. Rewrite `k` using `[← om_mul, one_mul]`. Rewrite using `[e0, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, k]`. Simplify using `only [hφ γ hγ, e]`.
-/
theorem biLift_last {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) {χA χz χS : (AE D)ˣ →* Circle} {om₁ : Om V₀ S} {oma : Om A S} {omz : Om L S}
    (h₁ : IsWeilDatumO ψ V₀ S (χA * χz) χS om₁) (ha : IsWeilDatumO ψ A S χA χS oma) (hz : IsWeilDatumO ψ L S χz χS omz)
    (omb : Om S X) (vA : Vol A) (vS : Vol S) {φ : GA D A → ℂ} (hφ : ∀ γ ∈ GQ A, ∀ g, φ (γ * g) = φ g) {Ξ : WO V₀ S → ℂ}
    (hΞ : IsThetaFunO ψ V₀ S Ξ) (Φ₂ : WO S T → ℂ) (c : ℂ) (hc : c * star c = 1) (a : GA D A) :
    GlobalTheory.SeeSaw.biLift oma omb vA vS (star c • rTrans a φ) (GlobalTheory.FinPl.lastBi o o'' τ (c • om₁ (o.emb (a, 1), 1) Ξ) Φ₂) =
      GlobalTheory.SeeSaw.biLift oma omb vA vS φ (GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂) := by
  have hsrc := GlobalTheory.T.thetaTensorRule_orthogonalSum_source D ψ h₁.std V₀ A L o S
  have e0 : ∀ v, (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) =
      Φ₂ (o''.resT S v).1 • fun u => Ξ ((o.resS S).symm (u, GlobalTheory.FinPl.kap τ S (o''.resT S v).2)) := fun v => rfl
  have e1 : ∀ v, (fun u => GlobalTheory.FinPl.lastBi o o'' τ (c • om₁ (o.emb (a, 1), 1) Ξ) Φ₂ u v) =
      c • oma (a, 1) fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v := fun v => by
    funext u
    have k := (hsrc.om_slice χA χz χS om₁ oma omz h₁ ha hz a 1 1 Ξ hΞ (GlobalTheory.FinPl.kap τ S (o''.resT S v).2)).2 u
    rw [show omz (1, 1) = 1 from map_one _] at k
    simp only [Module.End.one_apply] at k
    rw [e0, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.FinPl.lastBi, OrthDec.boxT, k]
    ring
  funext h₂
  unfold GlobalTheory.SeeSaw.biLift
  congr 1
  funext h
  rw [← GlobalTheory.ChainOnto.setIntegral_fd_mul_right D A vA.μ vA.𝓕 vA.haar vA.fund
    (fun h₀ => φ h₀ * omb (h, h₂) (fun v => oma (h₀, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0) 0) ?_ a]
  · congr 1
    funext x
    have e2 : (fun v => oma (x, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ (c • om₁ (o.emb (a, 1), 1) Ξ) Φ₂ u v) 0) =
        c • fun v => oma (x * a, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0 := by
      funext v
      rw [e1, map_smul, ← om_mul, mul_one]
      rfl
    rw [e2, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, rTrans]
    linear_combination (φ (x * a) * omb (h, h₂) (fun v => oma (x * a, h)
      (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0) 0) * hc
  · intro γ hγ x
    have e : ∀ v, oma (γ * x, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0 =
        oma (x, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0 := fun v => by
      have k := ha.om_aut γ hγ 1 (one_mem _) _
        (ha.om_pres (x, h) _ ((hsrc.slice_theta Ξ hΞ).1 (GlobalTheory.FinPl.kap τ S (o''.resT S v).2)))
      rw [← om_mul, one_mul] at k
      rw [e0, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, k]
    simp only [hφ γ hγ, e]

end GlobalTheory.BesMove

end
