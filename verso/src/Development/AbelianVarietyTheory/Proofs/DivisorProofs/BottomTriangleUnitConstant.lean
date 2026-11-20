import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyAt0Smul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumConjOfNegHermitianSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddEigenvectorUniqueUpToUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomPairBigMemberTwistedTuple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairsExistEveryTupleOfCmThetaHypotheses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntire
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerModelComplexConjugateNegFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicVacuumStandardLatticesReadsThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddEisensteinRatioAlgebraicUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuConductorExponentsPosProdEqModulusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealIndicatorReadsNormPowMulIntertwinedVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetIndicatorReadsAsTranslateCurveTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionIntegralPointCosetVectorEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstConjEqSumCosetIndicatorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitDetCharacterIntegralFramePowEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralMatrixFrameCompletedStandardLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterFiniteIdeleValueEqStatement

noncomputable section

section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

namespace GlobalTheory.StdRead

variable {D : D7}

/- English proof (translation)
Use function extensionality and compare the values at `z`. Take `⟨σ, hσ⟩` from `GlobalTheory.FockCompare.exists_chart hθ`. Establish `hsp : ∀ Z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ, (GlobalTheory.AdForm.realPt θ Z).map (finPart D) = 0 ∧ ∀ τ, compAt θ τ (GlobalTheory.AdForm.realPt θ Z) = Z τ` using `fun Z => by`. Use `Classical.epsilon_spec (p := fun w : Mx D T.rank S.rank => w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = Z τ) ⟨Matrix.of fun i j => σ fun τ => Z τ i j, ?_, fun τ => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Conclude with `hσ.fin _`. Use extensionality with `i j`. Conclude with `hσ.comp _ _`. Unfold `GlobalTheory.AdForm.xiN`. Take `⟨h1, h2⟩` from `hsp fun τ => Matrix.of fun i j => -((-δ)⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j))`.

Establish `hY : GlobalTheory.NormExact.coordY θ hS hT δ 1 (GlobalTheory.AdForm.realPt θ fun τ => Matrix.of fun i j => -((-δ)⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j))) = z`. Use function extensionality and compare the values at `τ i j`. Unfold `GlobalTheory.NormExact.coordY`. Rewrite using `[h2, map_one, mul_one, Matrix.of_apply, inv_neg, neg_mul, neg_neg, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]`. Both sides reduce to the same expression.

Rewrite using `[h.2 _ h1, hY, ← mul_assoc, ← Complex.exp_add]`. Establish `hH : Formalism.L2.Ker.HV (Formalism.MainNotions.TaylorLogMetric.area (lamOf D ⊤ δ))⁻¹ z z = Formalism.MainNotions.TaylorLogMetric.Hf D (tor0 D ⊤ δ) z z`. Express the relevant statement in the definitionally equal form `(((Formalism.MainNotions.TaylorLogMetric.area (lamOf D ⊤ δ))⁻¹ : ℝ) : ℂ) * _ = _ / ((Formalism.MainNotions.TaylorLogMetric.area (lamOf D ⊤ δ) : ℝ) : ℂ)`. Rewrite using `[div_eq_inv_mul, Complex.ofReal_inv]`. Rewrite using `[hH, neg_mul, add_neg_cancel, Complex.exp_zero, one_mul]`.
-/
theorem xiN_eq {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {a d : ℕ}
    (hS : S.rank = a) (hT : T.rank = d) {δ : ℂ} (hs : δ ≠ 0) {G : VC D a d → ℂ} {f : WO S T → ℂ}
    (h : Reads ψ θ hS hT ⊤ δ 1 G f) :
    GlobalTheory.AdForm.xiN θ S T hS hT (-δ) (Formalism.MainNotions.TaylorLogMetric.area (lamOf D ⊤ δ))⁻¹ f = G := by
  funext z
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  have hsp : ∀ Z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ,
      (GlobalTheory.AdForm.realPt θ Z).map (finPart D) = 0 ∧ ∀ τ, compAt θ τ (GlobalTheory.AdForm.realPt θ Z) = Z τ := fun Z => by
    refine Classical.epsilon_spec (p := fun w : Mx D T.rank S.rank => w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = Z τ)
      ⟨Matrix.of fun i j => σ fun τ => Z τ i j, ?_, fun τ => ?_⟩
    · ext i j; exact hσ.fin _
    · ext i j; exact hσ.comp _ _
  unfold GlobalTheory.AdForm.xiN
  obtain ⟨h1, h2⟩ := hsp fun τ => Matrix.of fun i j => -((-δ)⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j))
  have hY : GlobalTheory.NormExact.coordY θ hS hT δ 1 (GlobalTheory.AdForm.realPt θ
      fun τ => Matrix.of fun i j => -((-δ)⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j))) = z := by
    funext τ i j
    unfold GlobalTheory.NormExact.coordY
    rw [h2, map_one, mul_one, Matrix.of_apply, inv_neg, neg_mul, neg_neg, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]
    rfl
  rw [h.2 _ h1, hY, ← mul_assoc, ← Complex.exp_add]
  have hH : Formalism.L2.Ker.HV (Formalism.MainNotions.TaylorLogMetric.area (lamOf D ⊤ δ))⁻¹ z z = Formalism.MainNotions.TaylorLogMetric.Hf D (tor0 D ⊤ δ) z z := by
    change (((Formalism.MainNotions.TaylorLogMetric.area (lamOf D ⊤ δ))⁻¹ : ℝ) : ℂ) * _ = _ / ((Formalism.MainNotions.TaylorLogMetric.area (lamOf D ⊤ δ) : ℝ) : ℂ)
    rw [div_eq_inv_mul, Complex.ofReal_inv]
  rw [hH, neg_mul, add_neg_cancel, Complex.exp_zero, one_mul]

/- English proof (translation)
Proceed by induction on `R using Finset.induction_on with`. Consider the case `empty => exact ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩`. Consider the case `insert x s hx ih`. Rewrite using `[Finset.sum_insert hx, Finset.sum_insert hx]`. Conclude with `(h x (Finset.mem_insert_self _ _)).add (ih fun r hr => h r (Finset.mem_insert_of_mem hr))`.
-/
theorem reads_sum {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d}
    {δ : ℂ} {ι : Type} (R : Finset ι) (G : ι → VC D a d → ℂ) (f : ι → WO S T → ℂ)
    (h : ∀ r ∈ R, Reads ψ θ hS hT ⊤ δ 1 (G r) (f r)) : Reads ψ θ hS hT ⊤ δ 1 (∑ r ∈ R, G r) (∑ r ∈ R, f r) := by
  induction R using Finset.induction_on with
  | empty => exact ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    exact (h x (Finset.mem_insert_self _ _)).add (ih fun r hr => h r (Finset.mem_insert_of_mem hr))

def IsPh (u : ℂ) : Prop := ‖u‖ = 1 ∧ u ∈ Qbar ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ‖lamC lam u‖ = 1

/- English proof (translation)
Assemble the required witnesses or components as `⟨by rw [norm_mul, hu.1, hv.1, mul_one], mul_mem hu.2.1 hv.2.1, fun p _ lam => by rw [GlobalTheory.BotFormula.lamC_mul lam hu.2.1 hv.2.1, norm_mul, hu.2.2, hv.2.2, mul_one]⟩`.
-/
theorem IsPh.mul {u v : ℂ} (hu : IsPh u) (hv : IsPh v) : IsPh (u * v) :=
  ⟨by rw [norm_mul, hu.1, hv.1, mul_one], mul_mem hu.2.1 hv.2.1, fun p _ lam => by
    rw [GlobalTheory.BotFormula.lamC_mul lam hu.2.1 hv.2.1, norm_mul, hu.2.2, hv.2.2, mul_one]⟩

/- English proof (translation)
Unfold `lamC`. Rewrite using `[dif_pos (one_mem _)]`. Conclude with `map_one lam`.
-/
theorem lamC_one {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : lamC lam 1 = 1 := by
  unfold lamC
  rw [dif_pos (one_mem _)]
  exact map_one lam

/- English proof (translation)
Establish `h0 : u ≠ 0` using `fun h => by simpa [h] using hu.1`. Establish `e : starRingEnd ℂ u = u⁻¹` using `(Complex.inv_eq_conj hu.1).symm`. Use `⟨by rw [Complex.norm_conj, hu.1], e ▸ inv_mem hu.2.1, fun p _ lam => ?_⟩` and prove the remaining obligations. Establish `h` using `GlobalTheory.BotFormula.lamC_mul lam hu.2.1 (inv_mem hu.2.1)`. Rewrite `h` using `[mul_inv_cancel₀ h0, lamC_one]`.

Establish `h2` using `congrArg norm h`. Rewrite `h2` using `[norm_mul, hu.2.2, norm_one, one_mul]`. Rewrite using `[e, ← h2]`.
-/
theorem IsPh.conj {u : ℂ} (hu : IsPh u) : IsPh (starRingEnd ℂ u) := by
  have h0 : u ≠ 0 := fun h => by simpa [h] using hu.1
  have e : starRingEnd ℂ u = u⁻¹ := (Complex.inv_eq_conj hu.1).symm
  refine ⟨by rw [Complex.norm_conj, hu.1], e ▸ inv_mem hu.2.1, fun p _ lam => ?_⟩
  have h := GlobalTheory.BotFormula.lamC_mul lam hu.2.1 (inv_mem hu.2.1)
  rw [mul_inv_cancel₀ h0, lamC_one] at h
  have h2 := congrArg norm h
  rw [norm_mul, hu.2.2, norm_one, one_mul] at h2
  rw [e, ← h2]

/- English proof (translation)
Establish `hQ : u ∈ Qbar`. Rewrite using `[mem_algebraicClosure_iff]`. Conclude with `(IsIntegral.of_pow hm (h ▸ isIntegral_one)).isAlgebraic`. Use `⟨(pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 (by rw [← norm_pow, h, norm_one]), hQ, fun p _ lam => ?_⟩` and prove the remaining obligations. Use `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 ?_` and prove the remaining obligations.

Unfold `lamC`. Rewrite using `[dif_pos hQ, ← norm_pow, ← map_pow, show (⟨u, hQ⟩ : Qbar) ^ m = 1 from Subtype.ext h, map_one, norm_one]`.
-/
theorem isPh_of_pow {u : ℂ} {m : ℕ} (hm : 0 < m) (h : u ^ m = 1) : IsPh u := by
  have hQ : u ∈ Qbar := by
    rw [mem_algebraicClosure_iff]
    exact (IsIntegral.of_pow hm (h ▸ isIntegral_one)).isAlgebraic
  refine ⟨(pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 (by rw [← norm_pow, h, norm_one]), hQ, fun p _ lam => ?_⟩
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 ?_
  unfold lamC
  rw [dif_pos hQ, ← norm_pow, ← map_pow, show (⟨u, hQ⟩ : Qbar) ^ m = 1 from Subtype.ext h, map_one, norm_one]

/- English proof (translation)
Distinguish the cases in `hex : ∃ e1, Crv D ⊤ δ ∧ oddE0 D ⊤ δ t0 a d e1 ∧ e1 ≠ 0`. Take `⟨e1, hC, h1, hne⟩` from `hex`. Establish `k0` using `GlobalTheory.NormSum.VacMove.klat (D := D) (tor0 D ⊤ δ) (GlobalTheory.NormSum.VacMove.moves_one D a) (GlobalTheory.NormSum.VacMove.moves_one D d)`. Take `⟨hline, -⟩` from `GlobalTheory.ThetaLine.theta_line D hI.g1 ⊤ δ hC a d _ k0`. Take `⟨κ, hκ⟩` from `hline G hG e1 h1.1 hne`.

Use `⟨κ, fun h => h0 (by rw [hκ, h, zero_smul]), fun e0 _ ht he hn => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, e⟩` from `GlobalTheory.VacuumUnique.vacuum_unique hI hC he h1 hn`. Take `⟨a1, a2⟩` from `GlobalTheory.T.odd_eisenstein_ratio_algebraic_unit hI hC ht he h1 hn u e`. Conclude with `⟨u, ⟨hu, a1, a2⟩, by rw [hκ, e, smul_smul]⟩`. Conclude with `⟨1, one_ne_zero, fun e0 hC _ he hn => absurd ⟨e0, hC, he, hn⟩ hex⟩`.
-/
theorem exists_const (hI : GlobalTheory.NormSum.Inp D) (δ t0 : ℂ) {a d : ℕ} (G : VC D a d → ℂ)
    (hG : G ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d)) (h0 : G ≠ 0) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ e0, Crv D ⊤ δ → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → oddE0 D ⊤ δ t0 a d e0 → e0 ≠ 0 →
      ∃ u, IsPh u ∧ G = (κ * u) • e0 := by
  by_cases hex : ∃ e1, Crv D ⊤ δ ∧ oddE0 D ⊤ δ t0 a d e1 ∧ e1 ≠ 0
  · obtain ⟨e1, hC, h1, hne⟩ := hex
    have k0 := GlobalTheory.NormSum.VacMove.klat (D := D) (tor0 D ⊤ δ) (GlobalTheory.NormSum.VacMove.moves_one D a)
      (GlobalTheory.NormSum.VacMove.moves_one D d)
    obtain ⟨hline, -⟩ := GlobalTheory.ThetaLine.theta_line D hI.g1 ⊤ δ hC a d _ k0
    obtain ⟨κ, hκ⟩ := hline G hG e1 h1.1 hne
    refine ⟨κ, fun h => h0 (by rw [hκ, h, zero_smul]), fun e0 _ ht he hn => ?_⟩
    obtain ⟨u, hu, e⟩ := GlobalTheory.VacuumUnique.vacuum_unique hI hC he h1 hn
    obtain ⟨a1, a2⟩ := GlobalTheory.T.odd_eisenstein_ratio_algebraic_unit hI hC ht he h1 hn u e
    exact ⟨u, ⟨hu, a1, a2⟩, by rw [hκ, e, smul_smul]⟩
  · exact ⟨1, one_ne_zero, fun e0 hC _ he hn => absurd ⟨e0, hC, he, hn⟩ hex⟩

/- English proof (translation)
Take `⟨R, hR1, hR2, hF⟩` from `hstd`. Take `⟨b1, b2⟩` from `GlobalTheory.T.isIntegralMatrix_frame_completedStandardLattice β hβ`. Take `⟨m, hm0, hpow⟩` from `GlobalTheory.T.unitDetCharacter_integralFrame_pow_eq_one e 𝔪 hm ν hk β b1 b2`. Use `choose! z hz using fun (k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) (hk : k ∈ intG D P.a) => exists_approx hm.ne_bot 0 P.d hk`. Establish `hz' : ∀ r ∈ R, IsIntE (z r) ∧ Approx 𝔪 0 r (z r)` using `fun r hr => hz r (hR1 r hr)`.

Establish `h0` using `GlobalTheory.T.idealIndicator_reads_norm_pow_mul_intertwinedVacuum ψ θ S T hS hT δ hcc hs v hv _ hc hr e 𝔪 hm Tm hTm`. Establish `h1` using `GlobalTheory.T.cosetIndicator_reads_as_translate_curveTheta ψ θ S T hS hT δ hcc hs v hv _ hc hr e 𝔪 hm Tm hTm h0`. Use `⟨_, (isPh_of_pow hm0 hpow).conj, ?_⟩` and prove the remaining obligations. Rewrite using `[hf, GlobalTheory.T.standardPairFirst_conj_eq_sum_cosetIndicators S T hS hT P.a_le e 𝔪 hm ν hk β b1 b2 R hR1 hR2 z hz', map_smul, map_sum, mul_comm c, mul_smul, hF, Finset.smul_sum]`. Use `Reads.smul (reads_sum R _ _ fun r hr => ?_) _` and prove the remaining obligations.

Rewrite using `[GlobalTheory.T.weilAction_integralPoint_cosetVector_eq hI P hm.ne_bot 0 r (hR1 r hr) _ (GlobalTheory.T.integral_action_unit_character_eigen hI P e 𝔪 hm ν hν hk r (hR1 r hr)) (z r) (hz' r hr).1 (hz' r hr).2, map_smul, smul_comm c, ← cosV_smul]`. Conclude with `(h1 (z r) (hz' r hr).1).smul _`.
-/
theorem reads_std (hI : GlobalTheory.NormSum.Inp D) {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {S T : HSp D} (hS : S.rank = P.a) (hT : T.rank = P.d) (hcc : D.host.ccK = ⊤) (hs : Setup ψ θ S T ⊤ δ 1) {v f : WO S T → ℂ}
    (hv : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (stdL D S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) v)
    {c : ℂ} (hc : c • P.e0 ∈ Th D (tor0 D ⊤ δ) (stdL D P.a) (stdL D P.d)) (hr : Reads ψ θ hS hT ⊤ δ 1 (c • P.e0) v)
    {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (hm : GoodMod e 𝔪) {ν : (AE D)ˣ →* Circle} (hν : HasFinPart ν⁻¹ P.W.chV' P.W.ep')
    (hk : KillsCong ν 𝔪) {β : GL (Fin S.rank) (EAf D)} (hβ : Formalism.L2.DIV.IsFrame β (stdL D S.rank))
    (hstd : GlobalTheory.FunObj.SqNum.IsStdDatum P 𝔪 0) {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True) 1 v Tm)
    (hf : f = Tm fun w => starRingEnd ℂ (stdFst ν e 𝔪 S T β 1 w)) :
    ∃ u, IsPh u ∧ Reads ψ θ hS hT ⊤ δ 1 ((c * u) • P.F) f := by
  obtain ⟨R, hR1, hR2, hF⟩ := hstd
  obtain ⟨b1, b2⟩ := GlobalTheory.T.isIntegralMatrix_frame_completedStandardLattice β hβ
  obtain ⟨m, hm0, hpow⟩ := GlobalTheory.T.unitDetCharacter_integralFrame_pow_eq_one e 𝔪 hm ν hk β b1 b2
  choose! z hz using fun (k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) (hk : k ∈ intG D P.a) => exists_approx hm.ne_bot 0 P.d hk
  have hz' : ∀ r ∈ R, IsIntE (z r) ∧ Approx 𝔪 0 r (z r) := fun r hr => hz r (hR1 r hr)
  have h0 := GlobalTheory.T.idealIndicator_reads_norm_pow_mul_intertwinedVacuum ψ θ S T hS hT δ hcc hs v hv _ hc hr e 𝔪 hm Tm hTm
  have h1 := GlobalTheory.T.cosetIndicator_reads_as_translate_curveTheta ψ θ S T hS hT δ hcc hs v hv _ hc hr e 𝔪 hm Tm hTm h0
  refine ⟨_, (isPh_of_pow hm0 hpow).conj, ?_⟩
  rw [hf, GlobalTheory.T.standardPairFirst_conj_eq_sum_cosetIndicators S T hS hT P.a_le e 𝔪 hm ν hk β b1 b2 R hR1 hR2 z hz', map_smul, map_sum, mul_comm c, mul_smul, hF,
    Finset.smul_sum]
  refine Reads.smul (reads_sum R _ _ fun r hr => ?_) _
  rw [GlobalTheory.T.weilAction_integralPoint_cosetVector_eq hI P hm.ne_bot 0 r (hR1 r hr) _ (GlobalTheory.T.integral_action_unit_character_eigen hI P e 𝔪 hm ν hν hk r (hR1 r hr)) (z r) (hz' r hr).1 (hz' r hr).2,
    map_smul, smul_comm c, ← cosV_smul]
  exact (h1 (z r) (hz' r hr).1).smul _

variable {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

open GlobalTheory.FunObj.SqNum GlobalTheory.FunObj.StdDatum GlobalTheory.Mem.Col2.SplitChar in

/- English proof (translation)
Introduce `x u hxu hu hm`. Establish `hle` using `Ideal.mul_mono (TwBig.modT_le_condE G t) (TwBig.conj_smul_mono (TwBig.modT_le_condE G t))`. Establish `h1` using `TwBig.nuInv_base_eq_one hL G i j u hu (TwBig.hatId_mono hle hm)`. Establish `h2` using `GlobalTheory.BotPairSmall.CondXi.xiH_eq_one_of_cong hL G t u hu hm`. Establish `e : nuH G t i j = nuH G μ₀ i j * L.xiH t` using `by show L.C.mu0 j * L.xiH t / G.ch.chiH (D.R.m - i) = L.C.mu0 j * L.xiH μ₀ / G.ch.chiH (D.R.m - i) * L.xiH t`.

Rewrite using `[hL.xi_base, mul_one, mul_div_right_comm]`. Establish `h3` using `GlobalTheory.T.heckeCharacter_finiteIdele_value_eq _ _ (chrEq_nu G t i j hL) x u hxu`. Establish `e1 : (nuH G μ₀ i j * L.xiH t).1 (finIdl D u) = (nuH G μ₀ i j).1 (finIdl D u) * (L.xiH t).1 (finIdl D u)` using `rfl`. Establish `e2 : (nuH G μ₀ i j).1 (finIdl D u) = 1` using `inv_eq_one.1 h1`. Rewrite `h3` using `[e, e1, e2, h2, mul_one]`.

Conclude with `Circle.coe_injective (by simpa using h3)`.
-/
theorem killsCong {μ₀ : T} (hL : L.Is μ₀) (G : GlobalTheory.ChiGrid.GridData L sc) (t : T) (i j : Fin D.R.m) :
    KillsCong (G.nu t i (j + 1)) (GlobalTheory.SqTop.modT G t) := by
  intro x u hxu hu hm
  have hle := Ideal.mul_mono (TwBig.modT_le_condE G t) (TwBig.conj_smul_mono (TwBig.modT_le_condE G t))
  have h1 := TwBig.nuInv_base_eq_one hL G i j u hu (TwBig.hatId_mono hle hm)
  have h2 := GlobalTheory.BotPairSmall.CondXi.xiH_eq_one_of_cong hL G t u hu hm
  have e : nuH G t i j = nuH G μ₀ i j * L.xiH t := by
    show L.C.mu0 j * L.xiH t / G.ch.chiH (D.R.m - i) = L.C.mu0 j * L.xiH μ₀ / G.ch.chiH (D.R.m - i) * L.xiH t
    rw [hL.xi_base, mul_one, mul_div_right_comm]
  have h3 := GlobalTheory.T.heckeCharacter_finiteIdele_value_eq _ _ (chrEq_nu G t i j hL) x u hxu
  have e1 : (nuH G μ₀ i j * L.xiH t).1 (finIdl D u) = (nuH G μ₀ i j).1 (finIdl D u) * (L.xiH t).1 (finIdl D u) := rfl
  have e2 : (nuH G μ₀ i j).1 (finIdl D u) = 1 := inv_eq_one.1 h1
  rw [e, e1, e2, h2, mul_one] at h3
  exact Circle.coe_injective (by simpa using h3)

end GlobalTheory.StdRead

end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdRead

/- English proof (translation)
Introduce `_ _ _ hInp _`. Use `⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩` and prove the remaining obligations. Introduce `W hW i j A A' WW X δ t0 hX hβ r rc _ hr hrc _`. Establish `hI` using `hInp D`. Distinguish the cases in `hC : Crv D ⊤ δ`.

Use `swap`. Conclude with `⟨1, one_ne_zero, fun s Q P _ _ => absurd P.crv hC⟩`. Take `rfl` from `hr hC`. Establish `hcc : D.host.ccK = ⊤` using `hR.size.2.2.2.2.2.2.2.2.2.2.2.2.2`. Establish `hIs` using `hX.is`.

Establish `hθ : IsInfFam W.θ` using `hIs.isVac.2.inf`. Establish `hsc : GlobalTheory.NormExact.IsScale D ⊤ 1` using `hcc ▸ GlobalTheory.NormExact.isScale_one D`. Establish `hs : GlobalTheory.NormExact.Setup W.ψ W.θ A WW ⊤ δ 1` using `⟨hW, hθ, hX.std.1, hX.stdW.1, hC, hsc⟩`. Establish `hδ` using `GlobalTheory.NormExact.delta_ne_zero hC`. Establish `hrc' : rc = (area (lamOf D ⊤ δ))⁻¹`.

Take `⟨τ⟩ : Nonempty D.what₂.Tau` from `⟨D.eTau.symm 1⟩`. Establish `h1` using `hrc τ`. Establish `h2` using `GlobalTheory.NormExact.normSq_scale top_ne_bot hsc δ τ`. Establish `hA` using `GlobalTheory.NormExact.area_pos hC`. Establish `hx` using `GlobalTheory.NormExact.xiR_pos D`.

Rewrite `h2` using `[map_one, mul_one]`. Rewrite `h1` using `[norm_neg, ← Complex.normSq_eq_norm_sq, h2, GlobalTheory.FockPos.norm_embedding_xi0_eq]`. Clear the denominators using the available nonvanishing facts. Establish `: 2 * Formalism.L2.Pj.xiR D * (rc * area (lamOf D ⊤ δ) - 1) = 0` using `by linear_combination h1`. Establish `h3` using `(mul_eq_zero.1 this).resolve_left (by positivity)`.

Combine the linear equalities and inequalities to obtain the conclusion. Substitute `hrc'` using the available equality. Establish `hΛ : ∀ {V : HSp D} (ρ : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V), ρ.IsStd → ρ.Λ = stdL D V.rank` using `fun ρ h => by`. Use extensionality with `y`. Rewrite using `[h.2.1]`.

Simplify using `[stdL, Submodule.mem_pi, Submodule.mem_one]`. Establish `hΛA` using `hΛ X.rA hX.std`. Establish `hΛW` using `hΛ X.rW hX.stdW`. Establish `hv : IsVacO W.ψ W.θ A WW (fun _ => 1) (fun _ => 1) (stdL D A.rank : Set (Fin A.rank → D.host.E)) (stdL D WW.rank : Set (Fin WW.rank → D.host.E)) (fun w => starRingEnd ℂ (X.vac w))`. Establish `h` using `GlobalTheory.VacConj.isVacO_conj_negSp W.ψ W.θ A WW X.rA.s X.rW.s _ _ X.vac hIs.isVac`.

Rewrite `h` using `[hΛA, hΛW, show X.rA.s = fun _ => 1 from funext fun τ => (hX.std.2.2 τ).1, show X.rW.s = fun _ => 1 from funext fun τ => (hX.stdW.2.2 τ).1]`. Then use the resulting hypothesis. Take `⟨G0, hG0, hne, hread⟩` from `GlobalTheory.T.adelicVacuum_standardLattices_readsTheta W.ψ W.θ A WW rfl rfl δ hcc hs _ hv`. Take `⟨κ, hκ, hc⟩` from `exists_const hI δ t0 G0 hG0 hne`. Establish `hc' : ∀ (a d : ℕ) (ea : a = A.rank) (ed : d = WW.rank) (e0 : VC D a d → ℂ), GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → oddE0 D ⊤ δ t0 a d e0 → e0 ≠ 0 → ∃ u, IsPh u ∧ (κ * u) • e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) ∧ GlobalTheory.NormExact.Reads W.ψ W.θ ea.symm …`. Introduce and unpack `a d rfl rfl e0 h1 h2 h3`.

Take `⟨u, hu, e⟩` from `hc e0 hC h1 h2 h3`. Conclude with `⟨u, hu, e ▸ hG0, e ▸ hread⟩`. Use `⟨κ, hκ, fun s Q P P' hB => ?_⟩` and prove the remaining obligations. Establish `ea : P.a = A.rank` using `hB.rank.1.trans hX.rank.symm`. Establish `ed : P.d = WW.rank` using `by rw [hB.rank.2.2.1, ← hIs.rank, hX.rank, hX.rank']`.

Take `⟨u, hu, hTh, hrd⟩` from `hc' _ _ ea ed P.e0 P.pt0 P.vac P.W.nz`. Take `⟨c0, cI⟩` from `GlobalTheory.T.squareNuConductorExponents_pos_prod_eq_modulus G hL s i j (X.c s) (hIs.expo s)`. Take `⟨q1, q2⟩` from `GlobalTheory.SqTop.BotT.pde_ne_q hR`. Establish `hm : GoodMod (X.e s) (GlobalTheory.SqTop.modT G s)` using `⟨_, _, hIs.idem s, c0, cI.symm, GlobalTheory.FunObj.StdDatum.TwBig.modT_isCoprime_bb hL G s (GlobalTheory.T.gridConductorIdealCM_isCoprime_halfDifferent G.pl q1 q2)⟩`. Establish `hν : GlobalTheory.NormExact.HasFinPart (G.nu s i (j + 1))⁻¹ P.W.chV' P.W.ep'` using `fun x y hxy => by`.

Rewrite using `[hB.chars.2 y, MonoidHom.inv_apply, Circle.coe_inv, GlobalTheory.T.heckeCharacter_finiteIdele_value_eq _ _ (chrEq_nu G s i j hL) x y hxy]`. Conclude with `(Units.val_inv_eq_inv_val _).symm`. Take `⟨Tm, hTm, hf⟩` from `GlobalTheory.T.schrodingerModel_complexConjugate_negForm W.ψ hW A WW _ _ _ _ _ _ (hIs.fst s)`. Establish `eν : Lc.mu s (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) = G.nu s i (j + 1)` using `mul_div_mul_right_eq_div _ _ _`. Establish `eI : X.ideal (locPl G) s = GlobalTheory.SqTop.modT G s` using `cI`.

Rewrite `hTm` using `[hΛA, hΛW]`. Rewrite `hf` using `[eν, eI, hβ]`. Take `⟨u', hu', hrf⟩` from `reads_std hI P ea.symm ed.symm hcc hs hv hTh hrd hm hν (killsCong hL G s i j) (hΛA ▸ hIs.rigA.2.1) hB.std hTm hf`. Establish `hw` using `(hu.mul hu').conj`. Use `⟨_, fun h => by simpa [h] using hw.1, hw.2.1, fun p _ _ lam => hw.2.2 p lam, fun ea' ed' => ?_⟩` and prove the remaining obligations.

Rewrite using `[xiN_eq hθ _ _ hδ hrf, Complex.conj_conj, mul_assoc]`.
-/
theorem bottom_datum : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∀ (r : ℂ) (rc : ℝ), r ≠ 0 → (Formalism.MainNotions.StandardLatticesGL3.Crv D ⊤ δ → r = -δ) → (∀ τ, rc * ‖r‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) →
        (∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) ∈ TT D (tor0 D ⊤ δ) P.a P.d ∧
            ∀ (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
              GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
              GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
                P.W.Om x h (GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)))) →
      ∃ κ : ℂ, κ ≠ 0 ∧
        ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) = (κ * starRingEnd ℂ u) • P.F := by
  intro _ _ _ hInp _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro W hW i j A A' WW X δ t0 hX hβ r rc _ hr hrc _
  have hI := hInp D
  by_cases hC : Crv D ⊤ δ
  swap
  · exact ⟨1, one_ne_zero, fun s Q P _ _ => absurd P.crv hC⟩
  obtain rfl := hr hC
  have hcc : D.host.ccK = ⊤ := hR.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hIs := hX.is
  have hθ : IsInfFam W.θ := hIs.isVac.2.inf
  have hsc : GlobalTheory.NormExact.IsScale D ⊤ 1 := hcc ▸ GlobalTheory.NormExact.isScale_one D
  have hs : GlobalTheory.NormExact.Setup W.ψ W.θ A WW ⊤ δ 1 := ⟨hW, hθ, hX.std.1, hX.stdW.1, hC, hsc⟩
  have hδ := GlobalTheory.NormExact.delta_ne_zero hC
  have hrc' : rc = (area (lamOf D ⊤ δ))⁻¹ := by
    obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
    have h1 := hrc τ
    have h2 := GlobalTheory.NormExact.normSq_scale top_ne_bot hsc δ τ
    have hA := GlobalTheory.NormExact.area_pos hC
    have hx := GlobalTheory.NormExact.xiR_pos D
    rw [map_one, mul_one] at h2
    rw [norm_neg, ← Complex.normSq_eq_norm_sq, h2, GlobalTheory.FockPos.norm_embedding_xi0_eq] at h1
    field_simp
    have : 2 * Formalism.L2.Pj.xiR D * (rc * area (lamOf D ⊤ δ) - 1) = 0 := by linear_combination h1
    have h3 := (mul_eq_zero.1 this).resolve_left (by positivity)
    linarith
  subst hrc'
  have hΛ : ∀ {V : HSp D} (ρ : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V), ρ.IsStd → ρ.Λ = stdL D V.rank := fun ρ h => by
    ext y
    rw [h.2.1]
    simp [stdL, Submodule.mem_pi, Submodule.mem_one]
  have hΛA := hΛ X.rA hX.std
  have hΛW := hΛ X.rW hX.stdW
  have hv : IsVacO W.ψ W.θ A WW (fun _ => 1) (fun _ => 1) (stdL D A.rank : Set (Fin A.rank → D.host.E))
      (stdL D WW.rank : Set (Fin WW.rank → D.host.E)) (fun w => starRingEnd ℂ (X.vac w)) := by
    have h := GlobalTheory.VacConj.isVacO_conj_negSp W.ψ W.θ A WW X.rA.s X.rW.s _ _ X.vac hIs.isVac
    rwa [hΛA, hΛW, show X.rA.s = fun _ => 1 from funext fun τ => (hX.std.2.2 τ).1,
      show X.rW.s = fun _ => 1 from funext fun τ => (hX.stdW.2.2 τ).1] at h
  obtain ⟨G0, hG0, hne, hread⟩ := GlobalTheory.T.adelicVacuum_standardLattices_readsTheta W.ψ W.θ A WW rfl rfl δ hcc hs _ hv
  obtain ⟨κ, hκ, hc⟩ := exists_const hI δ t0 G0 hG0 hne
  have hc' : ∀ (a d : ℕ) (ea : a = A.rank) (ed : d = WW.rank) (e0 : VC D a d → ℂ), GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 →
      oddE0 D ⊤ δ t0 a d e0 → e0 ≠ 0 → ∃ u, IsPh u ∧ (κ * u) • e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) ∧
        GlobalTheory.NormExact.Reads W.ψ W.θ ea.symm ed.symm ⊤ δ 1 ((κ * u) • e0) (fun w => starRingEnd ℂ (X.vac w)) := by
    rintro a d rfl rfl e0 h1 h2 h3
    obtain ⟨u, hu, e⟩ := hc e0 hC h1 h2 h3
    exact ⟨u, hu, e ▸ hG0, e ▸ hread⟩
  refine ⟨κ, hκ, fun s Q P P' hB => ?_⟩
  have ea : P.a = A.rank := hB.rank.1.trans hX.rank.symm
  have ed : P.d = WW.rank := by rw [hB.rank.2.2.1, ← hIs.rank, hX.rank, hX.rank']
  obtain ⟨u, hu, hTh, hrd⟩ := hc' _ _ ea ed P.e0 P.pt0 P.vac P.W.nz
  obtain ⟨c0, cI⟩ := GlobalTheory.T.squareNuConductorExponents_pos_prod_eq_modulus G hL s i j (X.c s) (hIs.expo s)
  obtain ⟨q1, q2⟩ := GlobalTheory.SqTop.BotT.pde_ne_q hR
  have hm : GoodMod (X.e s) (GlobalTheory.SqTop.modT G s) := ⟨_, _, hIs.idem s, c0, cI.symm,
    GlobalTheory.FunObj.StdDatum.TwBig.modT_isCoprime_bb hL G s (GlobalTheory.T.gridConductorIdealCM_isCoprime_halfDifferent G.pl q1 q2)⟩
  have hν : GlobalTheory.NormExact.HasFinPart (G.nu s i (j + 1))⁻¹ P.W.chV' P.W.ep' := fun x y hxy => by
    rw [hB.chars.2 y, MonoidHom.inv_apply, Circle.coe_inv, GlobalTheory.T.heckeCharacter_finiteIdele_value_eq _ _ (chrEq_nu G s i j hL) x y hxy]
    exact (Units.val_inv_eq_inv_val _).symm
  obtain ⟨Tm, hTm, hf⟩ := GlobalTheory.T.schrodingerModel_complexConjugate_negForm W.ψ hW A WW _ _ _ _ _ _ (hIs.fst s)
  have eν : Lc.mu s (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) =
      G.nu s i (j + 1) := mul_div_mul_right_eq_div _ _ _
  have eI : X.ideal (locPl G) s = GlobalTheory.SqTop.modT G s := cI
  rw [hΛA, hΛW] at hTm
  rw [eν, eI, hβ] at hf
  obtain ⟨u', hu', hrf⟩ := reads_std hI P ea.symm ed.symm hcc hs hv hTh hrd hm hν (killsCong hL G s i j)
    (hΛA ▸ hIs.rigA.2.1) hB.std hTm hf
  have hw := (hu.mul hu').conj
  refine ⟨_, fun h => by simpa [h] using hw.1, hw.2.1, fun p _ _ lam => hw.2.2 p lam, fun ea' ed' => ?_⟩
  rw [xiN_eq hθ _ _ hδ hrf, Complex.conj_conj, mul_assoc]

end GlobalTheory.StdRead

end
