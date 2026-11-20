import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLsB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOfUnitVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntire
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConsecutiveStep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualImageOrthonormalFrameLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDifferentLatticeProductHermitianIsSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvSmulMemRationalHomLatticeScaledOfNormScaleStatement

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacRead

def posSig {D : D7} (S : HSp D) : HSp D := {S with sig := fun _ => (S.rank, 0)}

/- English proof (translation)
Use `⟨(Equiv.sumEmpty (Fin n) (Fin 0)).symm, 1, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Break down `i with i | i` into its components or cases. Break down `j with j | j` into its components or cases. Simplify using `[Formalism.UG.Jpq, Formalism.UG.cT, Matrix.one_apply]`.

Conclude with `j.elim0`. Conclude with `i.elim0`.
-/
theorem hasSignature_one (n : ℕ) : Formalism.UG.HasSignature (1 : Matrix (Fin n) (Fin n) ℂ) n 0 := by
  refine ⟨(Equiv.sumEmpty (Fin n) (Fin 0)).symm, 1, ?_⟩
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [Formalism.UG.Jpq, Formalism.UG.cT, Matrix.one_apply]
    · exact j.elim0
  · exact i.elim0

/- English proof (translation)
Introduce `τ`. Use `show Formalism.UG.HasSignature (S.gram.map τ) S.rank 0`. Rewrite using `[h, Matrix.map_one _ (map_zero τ) (map_one τ)]`. Conclude with `hasSignature_one _`.
-/
theorem sigOK_posSig {D : D7} (S : HSp D) (h : S.gram = 1) : (posSig S).SigOK := by
  intro τ
  show Formalism.UG.HasSignature (S.gram.map τ) S.rank 0
  rw [h, Matrix.map_one _ (map_zero τ) (map_one τ)]
  exact hasSignature_one _

open scoped ComplexOrder in
/- English proof (translation)
Establish `: gramAt D S τ = 1` using `by show (HSpace.gram S).map (tauE D τ) = 1`. Rewrite using `[h, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[this]`. Conclude with `⟨by simp, by simp, by simpa using (Matrix.PosDef.one : Matrix.PosDef (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ))⟩`.
-/
theorem isCartanInv_one {D : D7} (S : HSp D) (h : S.gram = 1) (τ : D.what₂.Tau) : IsCartanInv (gramAt D S τ) 1 := by
  have : gramAt D S τ = 1 := by
    show (HSpace.gram S).map (tauE D τ) = 1
    rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [this]
  exact ⟨by simp, by simp, by simpa using (Matrix.PosDef.one : Matrix.PosDef (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ))⟩

/- English proof (translation)
Take `⟨f, hf⟩` from `GlobalTheory.VacuumO.vacExists D ψ θ hψ hθ (posSig S) (posSig T) (fun _ => 1) (fun _ => 1) (sigOK_posSig S gS) (sigOK_posSig T gT) (isCartanInv_one S gS) (isCartanInv_one T gT) ΛS ΛT hS hT`. Conclude with `⟨f, hf.1, ⟨hf.2.inf, ⟨hf.2.theta.quasi, hf.2.theta.level, hf.2.theta.cont, hf.2.theta.smooth⟩, hf.2.lat, hf.2.fock, hf.2.norm⟩⟩`.
-/
theorem vac_exists_gram_one {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (S T : HSp D) (gS : S.gram = 1) (gT : T.gram = 1)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) :
    ∃ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) ΛS ΛT f := by
  obtain ⟨f, hf⟩ := GlobalTheory.VacuumO.vacExists D ψ θ hψ hθ (posSig S) (posSig T) (fun _ => 1) (fun _ => 1)
    (sigOK_posSig S gS) (sigOK_posSig T gT) (isCartanInv_one S gS) (isCartanInv_one T gT) ΛS ΛT hS hT
  exact ⟨f, hf.1, ⟨hf.2.inf, ⟨hf.2.theta.quasi, hf.2.theta.level, hf.2.theta.cont, hf.2.theta.smooth⟩, hf.2.lat,
    hf.2.fock, hf.2.norm⟩⟩

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E}

/- English proof (translation)
Establish `hr : r ≠ 0` using `IsScale.ne_zero hc.1.1 h`. Establish `hA` using `area_pos hc`. Establish `hx` using `xiR_pos D`. Establish `key : ∀ τ, Complex.normSq (embT D τ r) * area (lamOf D D.host.ccK δ) = area (lamOf D cc δ)`. Introduce `τ`.

Establish `h1` using `normSq_scale hc.1.1 h δ τ`. Establish `h2` using `normSq_scale D.host.ccK_ne_bot (isScale_one D) δ τ`. Rewrite `h2` using `[map_one, mul_one]`. Rewrite `h1` using `[Complex.normSq_mul, h2]`. Establish `h3 : (2 * Formalism.L2.Pj.xiR D) * (Complex.normSq (embT D τ r) * area (lamOf D D.host.ccK δ)) = (2 * Formalism.L2.Pj.xiR D) * area (lamOf D cc δ)` using `by rw [← h1]; ring`.

Conclude with `mul_left_cancel₀ (by positivity) h3`. Establish `hL : ∀ c : Ideal (𝓞 D.host.K), (tor0 D c δ).abelian₂ = lamOf D c δ` using `fun _ => rfl`. Rewrite using `[Formalism.MainNotions.TaylorLogMetric.Hf, Formalism.MainNotions.TaylorLogMetric.Hf, hL, hL, Finset.sum_div, Finset.sum_div]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_div, Finset.sum_div]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_div, Finset.sum_div]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `ht : embT D τ r ≠ 0` using `(map_ne_zero _).2 hr`. Establish `htc : starRingEnd ℂ (embT D τ r) ≠ 0` using `(map_ne_zero _).2 ht`.

Establish `hK : (area (lamOf D D.host.ccK δ) : ℂ) ≠ 0`. Establish `: 0 < area (lamOf D D.host.ccK δ)`. Use `key τ` as an intermediate fact. Establish `h0 : 0 < Complex.normSq (embT D τ r)` using `Complex.normSq_pos.2 ht`. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `this.ne'` after adjusting the coercions. Rewrite using `[← key τ, map_div₀]`. Use `push_cast`. Rewrite using `[← Complex.mul_conj]`. Clear the denominators using the available nonvanishing facts.
-/
theorem Hf_div_scale (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) (h : IsScale D cc r) {a d : ℕ} (z x : VC D a d) :
    Hf D (tor0 D D.host.ccK δ) (fun τ i j => z τ i j / embT D τ r) (fun τ i j => x τ i j / embT D τ r) =
      Hf D (tor0 D cc δ) z x := by
  have hr : r ≠ 0 := IsScale.ne_zero hc.1.1 h
  have hA := area_pos hc
  have hx := xiR_pos D
  have key : ∀ τ, Complex.normSq (embT D τ r) * area (lamOf D D.host.ccK δ) = area (lamOf D cc δ) := by
    intro τ
    have h1 := normSq_scale hc.1.1 h δ τ
    have h2 := normSq_scale D.host.ccK_ne_bot (isScale_one D) δ τ
    rw [map_one, mul_one] at h2
    rw [Complex.normSq_mul, h2] at h1
    have h3 : (2 * Formalism.L2.Pj.xiR D) * (Complex.normSq (embT D τ r) * area (lamOf D D.host.ccK δ)) =
        (2 * Formalism.L2.Pj.xiR D) * area (lamOf D cc δ) := by rw [← h1]; ring
    exact mul_left_cancel₀ (by positivity) h3
  have hL : ∀ c : Ideal (𝓞 D.host.K), (tor0 D c δ).abelian₂ = lamOf D c δ := fun _ => rfl
  rw [Formalism.MainNotions.TaylorLogMetric.Hf, Formalism.MainNotions.TaylorLogMetric.Hf, hL, hL, Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  have ht : embT D τ r ≠ 0 := (map_ne_zero _).2 hr
  have htc : starRingEnd ℂ (embT D τ r) ≠ 0 := (map_ne_zero _).2 ht
  have hK : (area (lamOf D D.host.ccK δ) : ℂ) ≠ 0 := by
    have : 0 < area (lamOf D D.host.ccK δ) := by
      have := key τ
      have h0 : 0 < Complex.normSq (embT D τ r) := Complex.normSq_pos.2 ht
      nlinarith
    exact_mod_cast this.ne'
  rw [← key τ, map_div₀]
  push_cast
  rw [← Complex.mul_conj]
  field_simp

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hl : Differentiable ℂ (fun Y : VC D a d => (fun τ i j => Y τ i j / embT D τ r : VC D a d))` using `by fun_prop`. Conclude with `hΦ.1.comp hl`. Introduce `x hx z`. Establish `e1` using `hΦ.2 _ (hLa x hx) (fun τ i j => z τ i j / embT D τ r)`.

Establish `hal : Formalism.MainNotions.TaylorLogMetric.al D (tor0 D cc δ) x = Formalism.MainNotions.TaylorLogMetric.al D (tor0 D D.host.ccK δ) (fun τ i j => x τ i j / embT D τ r)`. Simplify using `only [Formalism.MainNotions.TaylorLogMetric.al, Hf_div_scale hc h]`. Establish `hadd : (fun τ i j => (z + x) τ i j / embT D τ r) = (fun τ i j => z τ i j / embT D τ r) + (fun τ i j => x τ i j / embT D τ r)`. Use function extensionality and compare the values at `τ i j`. Simplify using `[add_div]`.

Use `show _ = Φ fun τ i j => z τ i j / embT D τ r`. Rewrite using `[← e1, hal]`. Simplify using `only [Formalism.MainNotions.TaylorLogMetric.U]`. Rewrite using `[Hf_div_scale hc h, Hf_div_scale hc h, hadd]`.
-/
theorem th_div_scale (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) (h : IsScale D cc r) {a d : ℕ}
    {L Ls : GlobalTheory.InertSign.Lat D a} {L' Lt : GlobalTheory.InertSign.Lat D d}
    (hLa : ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) L L',
      (fun τ i j => x τ i j / embT D τ r) ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) Ls Lt)
    {Φ : VC D a d → ℂ} (hΦ : Φ ∈ Th D (tor0 D D.host.ccK δ) Ls Lt) :
    (fun Y => Φ (fun τ i j => Y τ i j / embT D τ r)) ∈ Th D (tor0 D cc δ) L L' := by
  refine ⟨?_, ?_⟩
  · have hl : Differentiable ℂ (fun Y : VC D a d => (fun τ i j => Y τ i j / embT D τ r : VC D a d)) := by
      fun_prop
    exact hΦ.1.comp hl
  · intro x hx z
    have e1 := hΦ.2 _ (hLa x hx) (fun τ i j => z τ i j / embT D τ r)
    have hal : Formalism.MainNotions.TaylorLogMetric.al D (tor0 D cc δ) x =
        Formalism.MainNotions.TaylorLogMetric.al D (tor0 D D.host.ccK δ) (fun τ i j => x τ i j / embT D τ r) := by
      simp only [Formalism.MainNotions.TaylorLogMetric.al, Hf_div_scale hc h]
    have hadd : (fun τ i j => (z + x) τ i j / embT D τ r) =
        (fun τ i j => z τ i j / embT D τ r) + (fun τ i j => x τ i j / embT D τ r) := by
      funext τ i j
      simp [add_div]
    show _ = Φ fun τ i j => z τ i j / embT D τ r
    rw [← e1, hal]
    simp only [Formalism.MainNotions.TaylorLogMetric.U]
    rw [Hf_div_scale hc h, Hf_div_scale hc h, hadd]

end GlobalTheory.VacRead

namespace GlobalTheory.VacRead

/- English proof (translation)
Introduce `D ψ θ S T a d hS hT cc δ r hset`. Substitute `hS hT` using the available equality. Take `⟨hψ, hθ, gS, gT, crv, sc⟩` from `hset`. Establish `hc : cc ≠ ⊥` using `crv.1.1`. Establish `hr : r ≠ 0` using `IsScale.ne_zero hc sc`.

Establish `hδ : δ ≠ 0` using `delta_ne_zero crv`. Establish `hS1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin S.rank) D.host.E).1 * S.gram * (1 : GL (Fin S.rank) D.host.E).1 = 1`. Rewrite using `[gS]`. Simplify using `[Formalism.UG.cT]`. Establish `hT1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin T.rank) D.host.E).1 * T.gram * (1 : GL (Fin T.rank) D.host.E).1 = 1`.

Rewrite using `[gT]`. Simplify using `[Formalism.UG.cT]`. Establish `hLs : Formalism.MainNotions.StandardLatticesGL3.SD D (lsB D cc r S.rank)` using `GlobalTheory.T.invDifferentLatticeProductHermitian_isSelfDual D cc r S.rank hc sc`. Establish `hLt : Formalism.MainNotions.StandardLatticesGL3.SD D (stdL D T.rank)` using `GlobalTheory.MovedVacuum.sd_stdL D T.rank`. Take `⟨ΛS, hΛS, hSd⟩` from `GlobalTheory.MovedDict.isSelfDualC_inV S 1 hS1 _ hLs`.

Take `⟨ΛT, hΛT, hTd⟩` from `GlobalTheory.MovedDict.isSelfDualC_inV T 1 hT1 _ hLt`. Take `⟨f, hf⟩` from `vac_exists_gram_one ψ θ hψ hθ S T gS gT ΛS ΛT hSd hTd`. Rewrite `hf` using `[hΛS, hΛT]`. Take `⟨Φ, hΦd, hΦ⟩` from `GlobalTheory.FockPos.vacuum_real_entire ψ θ S T 1 1 _ _ hS1 hT1 f hf`. Establish `hth` using `theta_of_unit_vacuum ψ θ S T 1 1 hS1 hT1 δ hδ _ _ hLs hLt f hf Φ hΦd hΦ`.

Establish `hLa : ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) (stdL D S.rank) (stdL D T.rank), (fun τ i j => x τ i j / embT D τ r) ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) (lsB D cc r S.rank) (stdL D T.rank)`. Introduce `x hx`. Take `⟨z, hz, rfl⟩` from `GlobalTheory.ThetaLatImage.La_sub hx`. Establish `h2` using `GlobalTheory.ThetaLatImage.pt_mem_La (δ := δ) (GlobalTheory.T.inv_smul_mem_rationalHomLatticeScaled_of_normScale D cc r S.rank T.rank hc sc z hz) 1`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `τ i j`. Rewrite using `[one_smul, GlobalTheory.ThetaLatImage.pt_apply, GlobalTheory.ThetaLatImage.pt_apply]`. Establish `ht : embT D τ r ≠ 0` using `(map_ne_zero _).2 hr`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]`. Clear the denominators using the available nonvanishing facts.

Establish `hG` using `th_div_scale crv sc hLa hth`. Establish `hback : ∀ Z : VC D S.rank T.rank, (δ⁻¹ • fun τ i j => (δ * embT D τ r * Z τ i j) / embT D τ r : VC D S.rank T.rank) = Z`. Introduce `Z`. Use function extensionality and compare the values at `τ i j`. Establish `ht : embT D τ r ≠ 0` using `(map_ne_zero _).2 hr`.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Use `⟨_, hG, ?_, f, (reads_iff crv sc _ f).2 ⟨hf.2.theta, fun w hw => ?_⟩⟩` and prove the remaining obligations. Introduce `h0`. Apply `GlobalTheory.StepMove.vacO_ne_zero hf` to reduce the goal to its premises.

Use `GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real hf.2.theta fun w hw => ?_` and prove the remaining obligations. Rewrite using `[hΦ w hw]`. Establish `e` using `congrFun h0 (fun τ i j => δ * embT D τ r * GlobalTheory.FockPos.zCo θ 1 1 w τ i j)`. Simplify using `only [Pi.zero_apply, hback] at e`. Rewrite using `[e, mul_zero]`.

Rewrite using `[hΦ w hw]`. Simplify using `only [hback]`.
-/
theorem exists_vac_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∃ e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d), e0 ≠ 0 ∧ ∃ f₀, Reads ψ θ hS hT cc δ r e0 f₀ := by
  intro D ψ θ S T a d hS hT cc δ r hset
  subst hS hT
  obtain ⟨hψ, hθ, gS, gT, crv, sc⟩ := hset
  have hc : cc ≠ ⊥ := crv.1.1
  have hr : r ≠ 0 := IsScale.ne_zero hc sc
  have hδ : δ ≠ 0 := delta_ne_zero crv
  have hS1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin S.rank) D.host.E).1 * S.gram *
      (1 : GL (Fin S.rank) D.host.E).1 = 1 := by
    rw [gS]; simp [Formalism.UG.cT]
  have hT1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin T.rank) D.host.E).1 * T.gram *
      (1 : GL (Fin T.rank) D.host.E).1 = 1 := by
    rw [gT]; simp [Formalism.UG.cT]
  have hLs : Formalism.MainNotions.StandardLatticesGL3.SD D (lsB D cc r S.rank) := GlobalTheory.T.invDifferentLatticeProductHermitian_isSelfDual D cc r S.rank hc sc
  have hLt : Formalism.MainNotions.StandardLatticesGL3.SD D (stdL D T.rank) := GlobalTheory.MovedVacuum.sd_stdL D T.rank
  obtain ⟨ΛS, hΛS, hSd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV S 1 hS1 _ hLs
  obtain ⟨ΛT, hΛT, hTd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV T 1 hT1 _ hLt
  obtain ⟨f, hf⟩ := vac_exists_gram_one ψ θ hψ hθ S T gS gT ΛS ΛT hSd hTd
  rw [hΛS, hΛT] at hf
  obtain ⟨Φ, hΦd, hΦ⟩ := GlobalTheory.FockPos.vacuum_real_entire ψ θ S T 1 1 _ _ hS1 hT1 f hf
  have hth := theta_of_unit_vacuum ψ θ S T 1 1 hS1 hT1 δ hδ _ _ hLs hLt f hf Φ hΦd hΦ
  have hLa : ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) (stdL D S.rank) (stdL D T.rank),
      (fun τ i j => x τ i j / embT D τ r) ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) (lsB D cc r S.rank) (stdL D T.rank) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := GlobalTheory.ThetaLatImage.La_sub hx
    have h2 := GlobalTheory.ThetaLatImage.pt_mem_La (δ := δ) (GlobalTheory.T.inv_smul_mem_rationalHomLatticeScaled_of_normScale D cc r S.rank T.rank hc sc z hz) 1
    convert h2 using 1
    funext τ i j
    rw [one_smul, GlobalTheory.ThetaLatImage.pt_apply, GlobalTheory.ThetaLatImage.pt_apply]
    have ht : embT D τ r ≠ 0 := (map_ne_zero _).2 hr
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    field_simp
  have hG := th_div_scale crv sc hLa hth
  have hback : ∀ Z : VC D S.rank T.rank,
      (δ⁻¹ • fun τ i j => (δ * embT D τ r * Z τ i j) / embT D τ r : VC D S.rank T.rank) = Z := by
    intro Z
    funext τ i j
    have ht : embT D τ r ≠ 0 := (map_ne_zero _).2 hr
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  refine ⟨_, hG, ?_, f, (reads_iff crv sc _ f).2 ⟨hf.2.theta, fun w hw => ?_⟩⟩
  · intro h0
    apply GlobalTheory.StepMove.vacO_ne_zero hf
    refine GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real hf.2.theta fun w hw => ?_
    rw [hΦ w hw]
    have e := congrFun h0 (fun τ i j => δ * embT D τ r * GlobalTheory.FockPos.zCo θ 1 1 w τ i j)
    simp only [Pi.zero_apply, hback] at e
    rw [e, mul_zero]
  · rw [hΦ w hw]
    simp only [hback]

end GlobalTheory.VacRead
