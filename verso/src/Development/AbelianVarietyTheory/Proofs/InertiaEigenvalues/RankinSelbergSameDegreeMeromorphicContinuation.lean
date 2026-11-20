import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGoodEmptyIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralContinuationNearRealHalfLinePoleOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalRankinSelbergLogarithmFormulaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedThetaIntegralEqMulPartialRankinSelbergLStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdeleLogAbsoluteValueEqLogIdeleModuleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemNatMultipleIntegralFiniteAdelesIffIdealFiniteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PetEqZeroOfNeOfHasCentChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurableCompInfGLProd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import GroundTheory.GlobalFields.TateThesis.AdeleIdealMeasure

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.UnitaryBC
  GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.RSNonvan
open scoped nonZeroDivisors

/- English proof (translation)
The claim follows from `GlobalTheory.T.ideleLogAbsoluteValue_eq_log_ideleModule E d`.
-/
theorem logNorm_eq_log_ideleModule (E : Type) [Field E] [NumberField E] (d : (AdeleRing (𝓞 E) E)ˣ) :
    GlobalTheory.Mem.Chr.CharModel.logNorm E d = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E d : ℝ) :=
  GlobalTheory.T.ideleLogAbsoluteValue_eq_log_ideleModule E d

/- English proof (translation)
The claim follows from `GlobalTheory.T.mem_natMultipleIntegralFiniteAdeles_iff_idealFiniteAdeles E N hN J hJ z`.
-/
theorem natLat_iff (E : Type) [Field E] [NumberField E] (N : ℕ) (hN : 0 < N) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (hJ : (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E)) (z : FiniteAdeleRing (𝓞 E) E) :
    z ∈ GlobalTheory.RSJ.natLat E N ↔ z ∈ GroundTheory.Global.idealFiniteAdeles J :=
  GlobalTheory.T.mem_natMultipleIntegralFiniteAdeles_iff_idealFiniteAdeles E N hN J hJ z

namespace GlobalTheory.RSNonvan

/- English proof (translation)
Establish `hpos` using `(ideleModule E (GeneralLinearGroup.det g)).2`. Rewrite using `[Real.rpow_def_of_pos hpos, ← logNorm_eq_log_ideleModule]`. Simplify using `only [GlobalTheory.RSJ.detPow, chiDet, GlobalTheory.HeckeGal.Model.absPow, MonoidHom.coe_comp, Function.comp_apply]`. Express the relevant statement in the definitionally equal form `‖Complex.exp ((x : ℂ) * (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det g) : ℂ))‖ = _`. Rewrite using `[Complex.norm_exp]`.

Use `congr 1`. Simplify using `[mul_comm]`.
-/
theorem detPow_eq {E : Type} [Field E] [NumberField E] {a : ℕ} (x : ℝ) (g : GA E a) :
    GlobalTheory.RSJ.detPow E a x g = ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ) := by
  have hpos := (ideleModule E (GeneralLinearGroup.det g)).2
  rw [Real.rpow_def_of_pos hpos, ← logNorm_eq_log_ideleModule]
  simp only [GlobalTheory.RSJ.detPow, chiDet, GlobalTheory.HeckeGal.Model.absPow, MonoidHom.coe_comp, Function.comp_apply]
  change ‖Complex.exp ((x : ℂ) * (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det g) : ℂ))‖ = _
  rw [Complex.norm_exp]
  congr 1
  simp [mul_comm]

/- English proof (translation)
Establish `hrow : GlobalTheory.RSJ.secRow u = GlobalTheory.RSTheta.rowMat ℓ u`. Use extensionality with `i j`. Simplify using `only [GlobalTheory.RSJ.secRow, GlobalTheory.RSTheta.rowMat, Matrix.of_apply, Matrix.updateRow_apply]`. Establish `: ((i : ℕ) + 1 = a) ↔ i = ℓ`. Prove the components needed by the constructor for the conclusion.

Introduce `h; exact Fin.ext (by omega)`. Introduce `h`. Substitute `h` using the available equality. Conclude with `hℓ`. Distinguish the cases in `h : i = ℓ`.

Simplify using `[h, hℓ]`. Rewrite using `[if_neg (fun h' => h (this.1 h')), if_neg h]`. Unfold `GlobalTheory.RSJ.secInv`. Distinguish the cases in `hu : IsUnit (u ℓ)`. Establish `hd : IsUnit (GlobalTheory.RSJ.secRow u).det` using `by rw [hrow, GlobalTheory.RSTheta.det_rowMat]; exact hu`.

Rewrite using `[dif_pos hd]`. Use `congr 1`. Use extensionality with `: 1`. Rewrite using `[GlobalTheory.RSTheta.val_rowGL hu, ← hrow]`. Both sides reduce to the same expression.

Establish `hd : ¬ IsUnit (GlobalTheory.RSJ.secRow u).det` using `by rw [hrow, GlobalTheory.RSTheta.det_rowMat]; exact hu`. Rewrite using `[dif_neg hd, GlobalTheory.RSTheta.rowGL, dif_neg hu, inv_one]`.
-/
theorem secInv_eq {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (ℓ : Fin a) (hℓ : (ℓ : ℕ) + 1 = a)
    (u : Fin a → Cinf E) : GlobalTheory.RSJ.secInv u = (GlobalTheory.RSTheta.rowGL ℓ u)⁻¹ := by
  have hrow : GlobalTheory.RSJ.secRow u = GlobalTheory.RSTheta.rowMat ℓ u := by
    ext i j
    simp only [GlobalTheory.RSJ.secRow, GlobalTheory.RSTheta.rowMat, Matrix.of_apply, Matrix.updateRow_apply]
    have : ((i : ℕ) + 1 = a) ↔ i = ℓ := by
      constructor
      · intro h; exact Fin.ext (by omega)
      · intro h; subst h; exact hℓ
    by_cases h : i = ℓ
    · simp [h, hℓ]
    · rw [if_neg (fun h' => h (this.1 h')), if_neg h]
  unfold GlobalTheory.RSJ.secInv
  by_cases hu : IsUnit (u ℓ)
  · have hd : IsUnit (GlobalTheory.RSJ.secRow u).det := by rw [hrow, GlobalTheory.RSTheta.det_rowMat]; exact hu
    rw [dif_pos hd]
    congr 1
    ext : 1
    rw [GlobalTheory.RSTheta.val_rowGL hu, ← hrow]
    rfl
  · have hd : ¬ IsUnit (GlobalTheory.RSJ.secRow u).det := by rw [hrow, GlobalTheory.RSTheta.det_rowMat]; exact hu
    rw [dif_neg hd, GlobalTheory.RSTheta.rowGL, dif_neg hu, inv_one]

/- English proof (translation)
Establish `key : (∀ i : Fin a, v i - (if (i : ℕ) + 1 = a then 1 else 0) ∈ GlobalTheory.RSJ.natLat E N) ↔ v - Pi.single ℓ 1 ∈ GlobalTheory.ThetaPoisson.latt a J`. Simplify using `only [GlobalTheory.ThetaPoisson.latt, Set.mem_setOf_eq, Pi.sub_apply]`. Use `forall_congr' fun i => ?_` and prove the remaining obligations. Establish `e : (if (i : ℕ) + 1 = a then (1 : Af E) else 0) = (Pi.single ℓ (1 : Af E) : Fin a → Af E) i`. Distinguish the cases in `h : i = ℓ`.

Substitute `h` using the available equality. Simplify using `[hℓ]`. Establish `: ¬ ((i : ℕ) + 1 = a)` using `fun h' => h (Fin.ext (by omega))`. Simplify using `[this, h]`. Rewrite using `[e, natLat_iff E N hN J hJ]`.

Unfold `GlobalTheory.RSJ.indN`. Distinguish the cases in `h : ∀ i : Fin a, v i - (if (i : ℕ) + 1 = a then 1 else 0) ∈ GlobalTheory.RSJ.natLat E N`. Rewrite using `[if_pos h, Set.indicator_of_mem (key.1 h)]`. Both sides reduce to the same expression. Rewrite using `[if_neg h, Set.indicator_of_notMem (fun h' => h (key.2 h'))]`.
-/
theorem indN_eq {E : Type} [Field E] [NumberField E] {a : ℕ} (N : ℕ) (hN : 0 < N) (ℓ : Fin a)
    (hℓ : (ℓ : ℕ) + 1 = a) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (hJ : (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E)) (v : Fin a → Af E) :
    GlobalTheory.RSJ.indN N v = (GlobalTheory.ThetaPoisson.latt a J).indicator 1 (v - Pi.single ℓ 1) := by
  have key : (∀ i : Fin a, v i - (if (i : ℕ) + 1 = a then 1 else 0) ∈ GlobalTheory.RSJ.natLat E N) ↔
      v - Pi.single ℓ 1 ∈ GlobalTheory.ThetaPoisson.latt a J := by
    simp only [GlobalTheory.ThetaPoisson.latt, Set.mem_setOf_eq, Pi.sub_apply]
    refine forall_congr' fun i => ?_
    have e : (if (i : ℕ) + 1 = a then (1 : Af E) else 0) = (Pi.single ℓ (1 : Af E) : Fin a → Af E) i := by
      by_cases h : i = ℓ
      · subst h; simp [hℓ]
      · have : ¬ ((i : ℕ) + 1 = a) := fun h' => h (Fin.ext (by omega))
        simp [this, h]
    rw [e, natLat_iff E N hN J hJ]
  unfold GlobalTheory.RSJ.indN
  by_cases h : ∀ i : Fin a, v i - (if (i : ℕ) + 1 = a then 1 else 0) ∈ GlobalTheory.RSJ.natLat E N
  · rw [if_pos h, Set.indicator_of_mem (key.1 h)]; rfl
  · rw [if_neg h, Set.indicator_of_notMem (fun h' => h (key.2 h'))]

/- English proof (translation)
Unfold `GlobalTheory.RSJ.Zint GlobalTheory.RSPole.thetaZ`. Use `congr 1`. Use function extensionality and compare the values at `g`. Rewrite using `[detPow_eq]`. Use `congr 1`.

Unfold `GlobalTheory.RSJ.thetaSum`. Use `tsum_congr fun ξ => ?_` and prove the remaining obligations. Simplify using `only [GlobalTheory.RSJ.Psi, GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, GlobalTheory.RSTheta.rsInf, GlobalTheory.RSJ.rowAct, secInv_eq ℓ hℓ, map_inv]`. Rewrite using `[indN_eq N hN ℓ hℓ J hJ]`. Both sides reduce to the same expression.
-/
theorem zint_eq_thetaZ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (μ : Measure (GA E a))
    (𝓕 : Set (GA E a)) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (N : ℕ) (hN : 0 < N) (ℓ : Fin a)
    (hℓ : (ℓ : ℕ) + 1 = a) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (hJ : (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E)) (x : ℝ) :
    GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ φ φ' Φ J (Pi.single ℓ 1) x := by
  unfold GlobalTheory.RSJ.Zint GlobalTheory.RSPole.thetaZ
  congr 1
  funext g
  rw [detPow_eq]
  congr 1
  unfold GlobalTheory.RSJ.thetaSum
  refine tsum_congr fun ξ => ?_
  simp only [GlobalTheory.RSJ.Psi, GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, GlobalTheory.RSTheta.rsInf, GlobalTheory.RSJ.rowAct, secInv_eq ℓ hℓ, map_inv]
  rw [indN_eq N hN ℓ hℓ J hJ]
  rfl

open GlobalTheory.CuspRep.CuspidalL2GL in
/- English proof (translation)
Use `haveI := CuspidalL2GL.locallyCompactSpace_GA E a`. Use `haveI := CuspidalL2GL.t2Space_GA E a`. Use `haveI := CuspidalL2GL.secondCountableTopology_GA E a`. Use `haveI : DiscreteTopology (ratGL E a).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E a`. Take `⟨𝓕, -, -, h𝓕⟩` from `GlobalTheory.exists_isFundamentalDomain_subgroup (ratGL E a).range`.

Take `⟨𝓕', -, -, h𝓕'⟩` from `GlobalTheory.exists_isFundamentalDomain_subgroup (latticeGL E a)`. Conclude with `⟨Measure.haar, inferInstance, 𝓕, 𝓕', h𝓕 _, h𝓕' _⟩`.
-/
theorem haarFD (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) :
    ∃ (μ : Measure (GA E a)) (_ : μ.IsHaarMeasure) (𝓕 𝓕' : Set (GA E a)),
      IsFundamentalDomain (ratGL E a).range 𝓕 μ ∧ IsFundamentalDomain (latticeGL E a) 𝓕' μ := by
  haveI := CuspidalL2GL.locallyCompactSpace_GA E a
  haveI := CuspidalL2GL.t2Space_GA E a
  haveI := CuspidalL2GL.secondCountableTopology_GA E a
  haveI : DiscreteTopology (ratGL E a).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E a
  obtain ⟨𝓕, -, -, h𝓕⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (ratGL E a).range
  obtain ⟨𝓕', -, -, h𝓕'⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (latticeGL E a)
  exact ⟨Measure.haar, inferInstance, 𝓕, 𝓕', h𝓕 _, h𝓕' _⟩

/- English proof (translation)
Introduce `E _ _ _ a σ σ' ha hσ hσ' T hT hu hu'`. Take `⟨N, Φ, π, π', φ, φ', hπ, hπ', hφ, hφ', -, -, hN, hΦc, hΦs, hΦr, hZ'⟩` from `GlobalTheory.T.unfoldedThetaIntegral_eq_mul_partialRankinSelbergL E a σ σ' ha hσ hσ' T hT.1 hT.2 hu hu'`. Take `⟨μ, hμ, 𝓕, 𝓕', h𝓕, h𝓕'⟩` from `haarFD E a`. Take `⟨H, hHd, hHpos, hZH⟩` from `hZ' μ 𝓕 h𝓕`. Take `⟨ω, hωu, hω⟩` from `id hσ`.

Take `⟨ω', hωu', hω'⟩` from `id hσ'`. Rewrite `hω` using `[← hπ]`. Rewrite `hω'` using `[← hπ']`. Rewrite `hω`, `hω'` using `[CG.hasCentChar_mk]`. Use `set ℓ : Fin a := ⟨a - 1, by omega⟩ with hℓdef`.

Establish `hℓ : (ℓ : ℕ) + 1 = a` using `by simp [ℓ]; omega`. Establish `hN0 : (N : E) ≠ 0` using `by exact_mod_cast hN.ne'`. Use `set J : (FractionalIdeal (𝓞 E)⁰ E)ˣ := Units.mk0 (FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E)) (FractionalIdeal.spanSingleton_ne_zero_iff.2 hN0) with hJdef`. Establish `hJ : (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E)` using `rfl`. Establish `hπu : π.IsUnitary` using `⟨ω, hωu, CuspSub.hasCentral_iff.2 hω⟩`.

Establish `hπu' : π'.IsUnitary` using `⟨ω', hωu', CuspSub.hasCentral_iff.2 hω'⟩`. Take `⟨φs, -, hφs⟩` from `GlobalTheory.JSW.mspanR_le GlobalTheory.CuspOrth.cuspFormsBounded hπu hφ`. Take `⟨φs', -, hφs'⟩` from `GlobalTheory.JSW.mspanR_le GlobalTheory.CuspOrth.cuspFormsBounded hπu' hφ'`. Establish `hφs1 : φs.1 = φ` using `hφs`. Establish `hφs1' : φs'.1 = φ'` using `hφs'`.

Take `⟨c, -, hc⟩` from `GlobalTheory.T.thetaIntegral_continuation_nearRealHalfLine_poleOne E a ℓ Φ hΦc hΦs (hΦr ℓ hℓ) J (Pi.single ℓ 1) μ 𝓕 𝓕' h𝓕 h𝓕'`. Take `⟨Fz, hFa, hFx, hF1, hF1'⟩` from `hc π π' ω ω' hωu hωu' hω hω' φs φs' (Or.inr (hφs1 ▸ hφ)) (Or.inr (hφs1' ▸ hφ'))`. Establish `hH0 : ∀ x : ℝ, H x ≠ 0` using `fun x h => by`. Use `(hHpos x).1` as an intermediate fact. Rewrite `this` using `[h]`.

Simplify using `at this`. Use `⟨fun s => Fz s / H s, fun x hx => (hFa x hx).div (hHd.analyticAt _) (hH0 x), fun hne => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1 : Fz 1 = 0`. Distinguish the cases in `hωω : ω = ω'`. Substitute `hωω` using the available equality.

Rewrite using `[hF1 rfl]`. Establish `hne' : CG.mk π ≠ CG.mk π'` using `by rw [hπ, hπ']; exact hne`. Establish `h0` using `fun φ hφ φ'' hφ'' => GlobalTheory.CuspOrth.pet_eq_zero_of_ne_of_hasCentChar E a μ π π' ω hωu hω hω' hne' φ hφ φ'' hφ''`. Rewrite using `[GlobalTheory.MspanROrth.setIntegral_mspanR_eq_zero E a ha π π' ω hωu hω hω' μ h0 𝓕' h𝓕' φs.1 (hφs1 ▸ hφ) φs'.1 (hφs1' ▸ hφ'), mul_zero]`. Conclude with `hF1' hωω`.

Simplify using `[h1]`. Take `⟨-, hprod⟩` from `(GlobalTheory.T.localRankinSelberg_logarithm_formula).2 E a a σ σ' hσ hσ' T hu hu' x hx`. Establish `hx1 : (x : ℂ) - 1 ≠ 0`. Rewrite using `[sub_ne_zero]`. Conclude with `hx.ne'` after adjusting the coercions.

Establish `e : Fz x / H x / ((x : ℂ) - 1) = ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1`. Rewrite using `[hFx x hx]`. Establish `h2` using `(hZH x hx).1`. Rewrite `h2` using `[zint_eq_thetaZ μ 𝓕 φ φ' Φ N hN ℓ hℓ J hJ x]`. Simplify using `only [GlobalTheory.RSPole.thetaZ] at h2`.

Rewrite using `[hφs1, hφs1', h2]`. Simplify using `only [lfac]`. Use `hH0 x` as an intermediate fact. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Express the relevant statement in the definitionally equal form `HasProd _ (Fz x / H x / ((x : ℂ) - 1))`. Rewrite using `[e]`. Conclude with `hprod.tprod_eq ▸ hprod`.
-/
theorem samedeg_continuation : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (σ σ' : CG E a), 1 ≤ a → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), IsGood T → UnrOutside T σ → UnrOutside T σ' → ∃ F : ℂ → ℂ, (∀ x : ℝ, 0 < x → AnalyticAt ℂ F (x : ℂ)) ∧ (σ ≠ σ' → F 1 = 0) ∧ ∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => lfac σ σ' (x : ℂ) w.1) (F x / ((x : ℂ) - 1)) := by
  intro E _ _ _ a σ σ' ha hσ hσ' T hT hu hu'
  obtain ⟨N, Φ, π, π', φ, φ', hπ, hπ', hφ, hφ', -, -, hN, hΦc, hΦs, hΦr, hZ'⟩ := GlobalTheory.T.unfoldedThetaIntegral_eq_mul_partialRankinSelbergL E a σ σ' ha hσ hσ' T hT.1 hT.2 hu hu'
  obtain ⟨μ, hμ, 𝓕, 𝓕', h𝓕, h𝓕'⟩ := haarFD E a
  obtain ⟨H, hHd, hHpos, hZH⟩ := hZ' μ 𝓕 h𝓕
  obtain ⟨ω, hωu, hω⟩ := id hσ
  obtain ⟨ω', hωu', hω'⟩ := id hσ'
  rw [← hπ] at hω
  rw [← hπ'] at hω'
  rw [CG.hasCentChar_mk] at hω hω'
  set ℓ : Fin a := ⟨a - 1, by omega⟩ with hℓdef
  have hℓ : (ℓ : ℕ) + 1 = a := by simp [ℓ]; omega
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  set J : (FractionalIdeal (𝓞 E)⁰ E)ˣ := Units.mk0 (FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E))
    (FractionalIdeal.spanSingleton_ne_zero_iff.2 hN0) with hJdef
  have hJ : (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) := rfl
  have hπu : π.IsUnitary := ⟨ω, hωu, CuspSub.hasCentral_iff.2 hω⟩
  have hπu' : π'.IsUnitary := ⟨ω', hωu', CuspSub.hasCentral_iff.2 hω'⟩
  obtain ⟨φs, -, hφs⟩ := GlobalTheory.JSW.mspanR_le GlobalTheory.CuspOrth.cuspFormsBounded hπu hφ
  obtain ⟨φs', -, hφs'⟩ := GlobalTheory.JSW.mspanR_le GlobalTheory.CuspOrth.cuspFormsBounded hπu' hφ'
  have hφs1 : φs.1 = φ := hφs
  have hφs1' : φs'.1 = φ' := hφs'
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.thetaIntegral_continuation_nearRealHalfLine_poleOne E a ℓ Φ hΦc hΦs (hΦr ℓ hℓ) J (Pi.single ℓ 1) μ 𝓕 𝓕' h𝓕 h𝓕'
  obtain ⟨Fz, hFa, hFx, hF1, hF1'⟩ := hc π π' ω ω' hωu hωu' hω hω' φs φs'
    (Or.inr (hφs1 ▸ hφ)) (Or.inr (hφs1' ▸ hφ'))
  have hH0 : ∀ x : ℝ, H x ≠ 0 := fun x h => by
    have := (hHpos x).1
    rw [h] at this
    simp at this
  refine ⟨fun s => Fz s / H s, fun x hx => (hFa x hx).div (hHd.analyticAt _) (hH0 x), fun hne => ?_, fun x hx => ?_⟩
  · have h1 : Fz 1 = 0 := by
      by_cases hωω : ω = ω'
      · subst hωω
        rw [hF1 rfl]
        have hne' : CG.mk π ≠ CG.mk π' := by rw [hπ, hπ']; exact hne
        have h0 := fun φ hφ φ'' hφ'' =>
          GlobalTheory.CuspOrth.pet_eq_zero_of_ne_of_hasCentChar E a μ π π' ω hωu hω hω' hne' φ hφ φ'' hφ''
        rw [GlobalTheory.MspanROrth.setIntegral_mspanR_eq_zero E a ha π π' ω hωu hω hω' μ h0 𝓕' h𝓕' φs.1
          (hφs1 ▸ hφ) φs'.1 (hφs1' ▸ hφ'), mul_zero]
      · exact hF1' hωω
    simp [h1]
  · obtain ⟨-, hprod⟩ := (GlobalTheory.T.localRankinSelberg_logarithm_formula).2 E a a σ σ' hσ hσ' T hu hu' x hx
    have hx1 : (x : ℂ) - 1 ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast hx.ne'
    have e : Fz x / H x / ((x : ℂ) - 1) = ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1 := by
      rw [hFx x hx]
      have h2 := (hZH x hx).1
      rw [zint_eq_thetaZ μ 𝓕 φ φ' Φ N hN ℓ hℓ J hJ x] at h2
      simp only [GlobalTheory.RSPole.thetaZ] at h2
      rw [hφs1, hφs1', h2]
      simp only [lfac]
      have := hH0 x
      push_cast
      field_simp
    change HasProd _ (Fz x / H x / ((x : ℂ) - 1))
    rw [e]
    exact hprod.tprod_eq ▸ hprod

end GlobalTheory.RSNonvan
