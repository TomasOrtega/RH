import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussGLZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVecExistsUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameMatrixIntegralOfConjugateHalf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixReductionEqOfHalfIdempotentSubset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualHalfLatticeDetectingCharacter
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformiserFamilyHostFieldIntegersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralScalarInverseUniformisersIdempotentSumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeHalfIffFrameMatrixIntegralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumIntegralDivUniformisersIffReductionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralLiftResiduesIdempotentSumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateHalfPrescribedAdjointFrameMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeConjugateHalfIffDualStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHalfRepresentativesModReductionsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

namespace GlobalTheory.ZRep

open Formalism.IndefR.Fin.LevelGroupLemmas.Lat (mt_one isHalf_actO redM_of_int)

variable {D : D7}

/- English proof (translation)
Unfold `actO`. Rewrite using `[hg, mt_one, Matrix.one_mul]`. Use extensionality with `i j`. Simplify using `[Matrix.mul_diagonal, Matrix.smul_apply, mul_comm]`.
-/
theorem actO_one_eq {S T : HSp D} (g : GA D S) (s : AE D) (hg : mt S g⁻¹ = Matrix.diagonal (fun _ => s)) (w : WO S T) :
    actO S T g 1 w = s • w := by
  unfold actO
  rw [hg, mt_one, Matrix.one_mul]
  ext i j
  simp [Matrix.mul_diagonal, Matrix.smul_apply, mul_comm]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, mul_assoc, hw i j]`.
-/
theorem smul_half {m n : ℕ} {e : AE D} (s : AE D) {w : Mx D m n} (hw : IsHalf e w) : s • w = (s * e) • w := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, hw i j]

/- English proof (translation)
Introduce `i j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[mul_left_comm, hw i j]`.
-/
theorem isHalf_smul {m n : ℕ} {e : AE D} (s : AE D) {w : Mx D m n} (hw : IsHalf e w) : IsHalf e (s • w) := by
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [mul_left_comm, hw i j]

/- English proof (translation)
Introduce `i j`. Simplify using `only [Matrix.sub_apply, mul_sub, hw i j, hw' i j]`.
-/
theorem isHalf_sub {m n : ℕ} {e : AE D} {w w' : Mx D m n} (hw : IsHalf e w) (hw' : IsHalf e w') : IsHalf e (w - w') := by
  intro i j
  simp only [Matrix.sub_apply, mul_sub, hw i j, hw' i j]

/- English proof (translation)
Use extensionality with `i j`. Establish `hNM : IsIntM (N - M)` using `fun i j => sub_mem (hN i j) (hM i j)`. Rewrite using `[Matrix.sub_apply, redM_of_int PP hNM, redM_of_int PP hN, redM_of_int PP hM, ← map_sub]`. Both sides reduce to the same expression.
-/
theorem redM_sub (PP : Pl D.host.E) {b a : ℕ} {N M : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) (hM : IsIntM M) :
    redM PP (N - M) = redM PP N - redM PP M := by
  ext i j
  have hNM : IsIntM (N - M) := fun i j => sub_mem (hN i j) (hM i j)
  rw [Matrix.sub_apply, redM_of_int PP hNM, redM_of_int PP hN, redM_of_int PP hM, ← map_sub]
  rfl

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hN i j)`.
-/
theorem isIntM_smul {b a : ℕ} {c : EAf D} (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) {N : Matrix (Fin b) (Fin a) (EAf D)}
    (hN : IsIntM N) : IsIntM (c • N) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hN i j)

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapO_add, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapO_neg, ← sub_eq_add_neg]`.
-/
theorem frMapO_sub {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (w w' : WO S T) :
    frMapO S T βS βT (w - w') = frMapO S T βS βT w - frMapO S T βS βT w' := by
  rw [sub_eq_add_neg, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapO_add, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapO_neg, ← sub_eq_add_neg]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapAdj_add, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapAdj_neg, ← sub_eq_add_neg]`.
-/
theorem frMapAdj_sub {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (w w' : WO S T) :
    frMapAdj S T βS βT (w - w') = frMapAdj S T βS βT w - frMapAdj S T βS βT w' := by
  rw [sub_eq_add_neg, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapAdj_add, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapAdj_neg, ← sub_eq_add_neg]

/- English proof (translation)
Establish `key : ∀ i j, (toEAf D (∑ PP ∈ Q, es PP * incA D ((ϖ PP : D.host.E)⁻¹)) * N i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ ∀ PP ∈ Q, resS D.host.F PP ⟨N i j, hN i j⟩ = 0)` using `fun i j => GlobalTheory.T.idempotentSum_integral_div_uniformisers_iff_reduction_zero D Q es ϖ hes hc hϖ (N i j) (hN i j) (by`. Use `congrFun (congrFun he i) j` as an intermediate fact. Rewrite using `[Matrix.smul_apply, smul_eq_mul] at this)` and apply the resulting hypothesis. Prove the components needed by the constructor for the conclusion. Introduce `h PP hPP`.

Use extensionality with `i j`. Rewrite using `[redM_of_int PP hN, Matrix.zero_apply]`. Conclude with `(key i j).1 (by simpa [Matrix.smul_apply] using h i j) PP hPP`. Introduce `h i j`. Rewrite using `[Matrix.smul_apply, smul_eq_mul]`.

Use `(key i j).2 fun PP hPP => ?_` and prove the remaining obligations. Use `congrFun (congrFun (h PP hPP) i) j` as an intermediate fact. Rewrite `this` using `[redM_of_int PP hN]`. Then use the resulting hypothesis.
-/
theorem isIntM_smul_iff (Q : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D) (ϖ : Pl D.host.E → 𝓞 D.host.E)
    (hes : ∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) (hc : (∑ PP ∈ Q, es PP) * cA D (∑ PP ∈ Q, es PP) = 0)
    (hϖ : ∀ PP ∈ Q, ϖ PP ∈ PP.asIdeal ∧ ϖ PP ∉ PP.asIdeal ^ 2) {b a : ℕ} (N : Matrix (Fin b) (Fin a) (EAf D))
    (hN : IsIntM N) (he : toEAf D (∑ PP ∈ Q, es PP) • N = N) :
    IsIntM (toEAf D (∑ PP ∈ Q, es PP * incA D ((ϖ PP : D.host.E)⁻¹)) • N) ↔ ∀ PP ∈ Q, redM PP N = 0 := by
  have key : ∀ i j, (toEAf D (∑ PP ∈ Q, es PP * incA D ((ϖ PP : D.host.E)⁻¹)) * N i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      ∀ PP ∈ Q, resS D.host.F PP ⟨N i j, hN i j⟩ = 0) := fun i j =>
    GlobalTheory.T.idempotentSum_integral_div_uniformisers_iff_reduction_zero D Q es ϖ hes hc hϖ (N i j) (hN i j) (by
      have := congrFun (congrFun he i) j
      rwa [Matrix.smul_apply, smul_eq_mul] at this)
  constructor
  · intro h PP hPP
    ext i j
    rw [redM_of_int PP hN, Matrix.zero_apply]
    exact (key i j).1 (by simpa [Matrix.smul_apply] using h i j) PP hPP
  · intro h i j
    rw [Matrix.smul_apply, smul_eq_mul]
    refine (key i j).2 fun PP hPP => ?_
    have := congrFun (congrFun (h PP hPP) i) j
    rwa [redM_of_int PP hN] at this

end GlobalTheory.ZRep

open GlobalTheory.ZRep in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F hR hQ i t`. Take `⟨hvac, -, -, -⟩` from `hR.thP.vP i t`. Establish `hψ : IsStdChar D R.ψ (-1)` using `hvac.1`. Take `⟨cV, hcV⟩` from `hR.lev.βV i`. Take `⟨cW, hcW⟩` from `hR.lev.βW i`.

Establish `fV : Formalism.L2.DIV.IsFrame (R.βV i) (R.ΛV i)` using `hcV.1`. Establish `fW : Formalism.L2.DIV.IsFrame (R.βW i) (R.ΛW i)` using `hcW.1`. Establish `sV : IsSelfDualC (Vc D i) (R.ΛV i)` using `GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βV i))`. Establish `sW : IsSelfDualC (Wc D i) (R.ΛW i)` using `GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βW i))`. Establish `hP` using `hQ.2 t`.

Use `⟨?_, GlobalTheory.T.exists_uniformiser_family_hostField_integers D, ?_⟩` and prove the remaining obligations. Take `⟨f, eg, eQ, fg, -, hq, -⟩` from `(GlobalTheory.FlatVecExist.flatVec_existsUnique D G Pl0 T0 A Ks R F hR hQ i t).1`. Conclude with `⟨eQ, hq⟩`. Introduce `eQ es ϖ hq hes hϖ heQ`. Substitute `heQ` using the available equality.

Establish `hc : (∑ PP ∈ R.Q t, es PP) * cA D (∑ PP ∈ R.Q t, es PP) = 0` using `hq.2`. Establish `hϖ0 : ∀ PP ∈ R.Q t, ϖ PP ≠ 0` using `fun PP hPP h0 => (hϖ PP hPP).2 (by rw [h0]; exact zero_mem _)`. Take `⟨hex, hZ⟩` from `GlobalTheory.T.centralScalar_inverse_uniformisers_idempotent_sum D (Vc D i) (R.Q t) es ϖ hes hc hϖ0`. Use `⟨hex, fun z hz Λ hΛ => ?_⟩` and prove the remaining obligations. Take `⟨hcen, hGf, hsupp, hdet, hinv, ha1, ha2, ha3, ha4⟩` from `hZ z hz`.

Establish `act1 : ∀ w : WO (Vc D i) (Wc D i), actO (Vc D i) (Wc D i) z 1 w = cA D (1 + ∑ PP ∈ R.Q t, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) • w` using `fun w => actO_one_eq z _ hinv w`. Establish `act2 : ∀ w : WO (Vc D i) (Wc D i), actO (Vc D i) (Wc D i) z⁻¹ 1 w = (1 + ∑ PP ∈ R.Q t, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) • w` using `fun w => actO_one_eq z⁻¹ _ (by rw [inv_inv]; exact hz) w`. Establish `zz : ∀ w : WO (Vc D i) (Wc D i), actO (Vc D i) (Wc D i) z 1 (actO (Vc D i) (Wc D i) z⁻¹ 1 w) = w` using `fun w => by`. Rewrite using `[Formalism.IndefR.Fin.LevelGroupLemmas.Lat.actO_actO, mul_inv_cancel, mul_one, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.actO_one]`. Establish `z'z : ∀ w : WO (Vc D i) (Wc D i), actO (Vc D i) (Wc D i) z⁻¹ 1 (actO (Vc D i) (Wc D i) z 1 w) = w` using `fun w => by`.

Rewrite using `[Formalism.IndefR.Fin.LevelGroupLemmas.Lat.actO_actO, inv_mul_cancel, mul_one, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.actO_one]`. Establish `actsub : ∀ (g : GA D (Vc D i)) (x y : WO (Vc D i) (Wc D i)), actO (Vc D i) (Wc D i) g 1 (x - y) = actO (Vc D i) (Wc D i) g 1 x - actO (Vc D i) (Wc D i) g 1 y` using `fun g x y => by`. Unfold `actO`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul]`. Use `set e := ∑ PP ∈ R.Q t, es PP with he`.

Use `set π := ∑ PP ∈ R.Q t, es PP * incA D (ϖ PP : D.host.E) with hπ`. Use `set π' := ∑ PP ∈ R.Q t, es PP * incA D ((ϖ PP : D.host.E)⁻¹) with hπ'`. Establish `part1 : IsCentAt i (R.Q t) z ∧ SuppAt e (Vc D i) z ∧ (∃ x : (AE D)ˣ, IsDetAt (cA D e) (Vc D i) z x ∧ (x : AE D) = 1 + ∑ PP ∈ R.Q t, cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) ^ (Vc D i).rank - 1)) ∧ (∀ w : WO (Vc D i) (Wc D i), IsHalf e w → actO (Vc D i) (Wc D i) z 1 w = π • …`. Use `⟨⟨hcen, hGf, e, hq, hsupp⟩, hsupp, hdet, fun w hw => ⟨?_, ?_⟩, fun w hw => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[act1, smul_half _ hw, ha2]`.

Rewrite using `[act2, smul_half _ hw, ha1]`. Rewrite using `[act1, smul_half _ hw, ha4]`. Rewrite using `[act2, smul_half _ hw, ha3]`. Use `⟨part1, ?_⟩` and prove the remaining obligations. Establish `he_idem : e * e = e` using `GlobalTheory.PlaceDatum.idemSum_mul_self hq`.

Establish `heInt : finPart D e ∈ intAE D` using `GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he_idem])`. Establish `heInf : infPart D e = 0` using `Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_of_idemSum hq`. Establish `hceInt : finPart D (cA D e) ∈ intAE D`. Rewrite using `[Formalism.IndefR.Fin.LevelGroupLemmas.Lat.finPart_cA]`. Conclude with `Formalism.IndefR.Fin.LevelGroupLemmas.Lat.cA_mem_intAE heInt`.

Establish `hceInf : infPart D (cA D e) = 0` using `Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_cA_idemSum hq`. Establish `hce_idem : cA D e * cA D e = cA D e` using `by rw [← map_mul, he_idem]`. Establish `hcc : cA D e * cA D (cA D e) = 0` using `by rw [cA_cA, mul_comm, hc]`. Establish `hπi : toEAf D π ∈ Formalism.L2.Herm.intAf D.host.F D.host.E`. Rewrite using `[hπ, map_sum]`.

Conclude with `sum_mem fun PP hPP => by`. Rewrite using `[map_mul]`. Conclude with `mul_mem (GlobalTheory.IdemRes.resS_idem_eq_one D _ PP (hes PP hPP)).1 (GlobalTheory.IdemIntegral.eToEAf_int D (ϖ PP))`. Substitute `hΛ` using the available equality. Use `set Λ := latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (fun _ => True) with hΛ`.

Establish `H1e : ∀ w : WO (Vc D i) (Wc D i), IsHalf e w → (w ∈ Λ ↔ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w))` using `GlobalTheory.T.mem_completedLattice_half_iff_frameMatrix_integral D _ _ _ _ _ _ sV sW fV fW (R.Q t) e hq hP`. Establish `H1c : ∀ w : WO (Vc D i) (Wc D i), IsHalf (cA D e) w → (w ∈ Λ ↔ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w))` using `fun w hw => ⟨fun h => GlobalTheory.HalfAdjInt.frMapAdj_int_of_half D _ _ _ _ _ _ sV sW fV fW _ e hq hP w h hw, fun h => GlobalTheory.HalfAdjLattice.mem_latO_of_adj_int D _ _ _ _ _ _ sV sW fV fW _ e hq hP w hw h⟩`. Establish `smulΛe : ∀ c : AE D, toEAf D c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → ∀ w ∈ Λ, IsHalf e w → c • w ∈ Λ` using `fun c hci w hw hh => (H1e _ (isHalf_smul c hh)).2 (by`. Rewrite using `[GlobalTheory.RedHalfDrop.frMapO_smul_eq]`. Conclude with `isIntM_smul hci ((H1e w hh).1 hw))`.

Establish `smulΛc : ∀ c : AE D, toEAf D (cA D c) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → ∀ w ∈ Λ, IsHalf (cA D e) w → c • w ∈ Λ` using `fun c hci w hw hh => (H1c _ (isHalf_smul c hh)).2 (by`. Rewrite using `[GlobalTheory.RedHalfDrop.frMapAdj_smul_eq]`. Conclude with `isIntM_smul hci ((H1c w hh).1 hw))`. Establish `hπci : toEAf D (cA D (cA D π)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E` using `by rw [cA_cA]; exact hπi`. Establish `Dc` using `GlobalTheory.T.mem_completedLattice_conjugateHalf_iff_dual D R.ψ _ _ _ _ hψ sV sW e he_idem hc heInf heInt`.

Establish `De` using `GlobalTheory.T.mem_completedLattice_conjugateHalf_iff_dual D R.ψ _ _ _ _ hψ sV sW (cA D e) hce_idem hcc hceInf hceInt`. Set `Λe : AddSubgroup (WO (Vc D i) (Wc D i))` to `{ carrier := {w | IsHalf e w ∧ actO (Vc D i) (Wc D i) z⁻¹ 1 w ∈ Λ} add_mem' := fun {x y} hx hy => ⟨Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_add hx.1 hy.1, by`. Rewrite using `[act2, smul_add, ← act2, ← act2]`. Conclude with `add_mem hx.2 hy.2⟩`. Use the proof step `zero_mem' := ⟨Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_zero e, by rw [act2, smul_zero]; exact zero_mem _⟩`.

Use the proof step `neg_mem' := fun {x} hx => ⟨by`. Use `isHalf_smul (-1 : AE D) hx.1; rwa [neg_one_smul] at this, by` as an intermediate fact. Rewrite using `[act2, smul_neg, ← act2]`. Conclude with `neg_mem hx.2⟩ }`. Set `Λc : AddSubgroup (WO (Vc D i) (Wc D i))` to `{ carrier := {w | IsHalf (cA D e) w ∧ actO (Vc D i) (Wc D i) z 1 w ∈ Λ} add_mem' := fun {x y} hx hy => ⟨Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_add hx.1 hy.1, by`.

Rewrite using `[act1, smul_add, ← act1, ← act1]`. Conclude with `add_mem hx.2 hy.2⟩`. Use the proof step `zero_mem' := ⟨Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_zero _, by rw [act1, smul_zero]; exact zero_mem _⟩`. Use the proof step `neg_mem' := fun {x} hx => ⟨by`. Use `isHalf_smul (-1 : AE D) hx.1; rwa [neg_one_smul] at this, by` as an intermediate fact.

Rewrite using `[act1, smul_neg, ← act1]`. Conclude with `neg_mem hx.2⟩ }`. Establish `memΛe : ∀ w, w ∈ Λe ↔ IsHalf e w ∧ actO (Vc D i) (Wc D i) z⁻¹ 1 w ∈ Λ` using `fun w => Iff.rfl`. Establish `memΛc : ∀ w, w ∈ Λc ↔ IsHalf (cA D e) w ∧ actO (Vc D i) (Wc D i) z 1 w ∈ Λ` using `fun w => Iff.rfl`. Establish `H2e : ∀ w ∈ Λ, ∀ w' ∈ Λ, IsHalf e w → IsHalf e w' → (w - w' ∈ Λe ↔ ∀ PP ∈ R.Q t, redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) = redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w'))`.

Introduce `w hw w' hw' hh hh'`. Establish `hd` using `isHalf_sub hh hh'`. Establish `hi` using `(H1e w hh).1 hw`. Establish `hi'` using `(H1e w' hh').1 hw'`. Establish `hN : IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (w - w'))` using `(H1e _ hd).1 (sub_mem hw hw')`.

Establish `heN : toEAf D e • frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (w - w') = frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (w - w')`. Rewrite using `[← GlobalTheory.RedHalfDrop.frMapO_smul_eq]`. Use `congr 1`. Use extensionality with `a b`. Conclude with `hd a b`.

Rewrite using `[memΛe, act2, smul_half _ hd, ha1, H1e _ (isHalf_smul _ hd), GlobalTheory.RedHalfDrop.frMapO_smul_eq, isIntM_smul_iff (R.Q t) es ϖ hes hc hϖ _ hN heN]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h⟩ PP hPP`. Use `h PP hPP` as an intermediate fact. Rewrite `this` using `[frMapO_sub, redM_sub PP hi hi']`.

Conclude with `sub_eq_zero.1 this`. Introduce `h`. Use `⟨hd, fun PP hPP => ?_⟩` and prove the remaining obligations. Rewrite using `[frMapO_sub, redM_sub PP hi hi', h PP hPP, sub_self]`. Establish `H2c : ∀ w ∈ Λ, ∀ w' ∈ Λ, IsHalf (cA D e) w → IsHalf (cA D e) w' → (w - w' ∈ Λc ↔ ∀ PP ∈ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) = redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w'))`.

Introduce `w hw w' hw' hh hh'`. Establish `hd` using `isHalf_sub hh hh'`. Establish `hi` using `(H1c w hh).1 hw`. Establish `hi'` using `(H1c w' hh').1 hw'`. Establish `hN : IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (w - w'))` using `(H1c _ hd).1 (sub_mem hw hw')`.

Establish `heN : toEAf D e • frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (w - w') = frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (w - w')`. Use `GlobalTheory.RedHalfDrop.frMapAdj_smul_eq (R.βV i) (R.βW i) (cA D e) (w - w')` as an intermediate fact. Rewrite `this` using `[cA_cA]`. Rewrite using `[← this]`. Use `congr 1`.

Use extensionality with `a b`. Conclude with `hd a b`. Rewrite using `[memΛc, act1, smul_half _ hd, ha4, H1c _ (isHalf_smul _ hd), GlobalTheory.RedHalfDrop.frMapAdj_smul_eq, cA_cA, isIntM_smul_iff (R.Q t) es ϖ hes hc hϖ _ hN heN]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h⟩ PP hPP`.

Use `h PP hPP` as an intermediate fact. Rewrite `this` using `[frMapAdj_sub, redM_sub PP hi hi']`. Conclude with `sub_eq_zero.1 this`. Introduce `h`. Use `⟨hd, fun PP hPP => ?_⟩` and prove the remaining obligations.

Rewrite using `[frMapAdj_sub, redM_sub PP hi hi', h PP hPP, sub_self]`. Establish `H3e : ∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (kP PP), ∃ w, IsHalf e w ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) ∧ ∀ PP ∈ R.Q t, redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) = Y PP`. Introduce `Y`. Use `choose N hN heN hNY using fun (ij : Fin (Wc D i).rank × Fin (Vc D i).rank) => GlobalTheory.T.exists_integral_lift_residues_idempotentSum D (R.Q t) es hes hc (fun PP => Y PP ij.1 ij.2)`. Take `⟨y, hyh, -, hyz⟩` from `GlobalTheory.HalfDuality.exists_half_frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) e he_idem (fun a b => N (a, b)) (fun a b => heN (a, b))`.

Establish `hI : IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) y)` using `by rw [hyz]; exact fun a b => hN (a, b)`. Use `⟨y, hyh, hI, fun PP hPP => ?_⟩` and prove the remaining obligations. Use extensionality with `a b`. Rewrite using `[Formalism.IndefR.Fin.LevelGroupLemmas.Lat.redM_of_int PP hI]`. Use `hNY (a, b) PP hPP` as an intermediate fact.

Use `this using 2` and compare the differences between its conclusion and the goal. Conclude with `Subtype.ext (congrFun (congrFun hyz a) b)`. Establish `WeightCompositions : ∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP), ∃ w, IsHalf (cA D e) w ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) ∧ ∀ PP ∈ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) = Y PP`. Introduce `Y`. Use `choose N hN heN hNY using fun (ij : Fin (Vc D i).rank × Fin (Wc D i).rank) => GlobalTheory.T.exists_integral_lift_residues_idempotentSum D (R.Q t) es hes hc (fun PP => Y PP ij.1 ij.2)`.

Take `⟨y, hyh, -, hyz⟩` from `GlobalTheory.T.exists_conjugateHalf_prescribed_adjoint_frameMatrix D (Vc D i) (Wc D i) (R.βV i) (R.βW i) e he_idem (fun a b => N (a, b)) (fun a b => heN (a, b))`. Establish `hI : IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y)` using `by rw [hyz]; exact fun a b => hN (a, b)`. Use `⟨y, hyh, hI, fun PP hPP => ?_⟩` and prove the remaining obligations. Use extensionality with `a b`. Rewrite using `[Formalism.IndefR.Fin.LevelGroupLemmas.Lat.redM_of_int PP hI]`.

Use `hNY (a, b) PP hPP` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal. Conclude with `Subtype.ext (congrFun (congrFun hyz a) b)`. Take `⟨Xe, hXe1, hXe2, hXecard, hXeY⟩` from `GlobalTheory.T.lattice_half_representatives_mod_reductions D (Vc D i) (Wc D i) Λ Λe e (R.Q t) (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)) (frMapO_sub _ _) H1e H2e H3e`. Take `⟨Xc, hXc1, hXc2, hXccard, hXcY⟩` from `GlobalTheory.T.lattice_half_representatives_mod_reductions D (Vc D i) (Wc D i) Λ Λc (cA D e) (R.Q t) (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i)) (frMapAdj_sub _ _) H1c H2c WeightCompositions`.

Establish `cl6e : ∀ u, IsHalf (cA D e) u → ((∀ l ∈ Λe, IsHalf e l → R.ψ (symplO (Vc D i) (Wc D i) l u) = 1) ↔ actO (Vc D i) (Wc D i) z⁻¹ 1 u ∈ Λ)`. Introduce `u hu`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `(Dc _ (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hu)).2 fun l hl hlh => ?_` and prove the remaining obligations.

Use `h (actO (Vc D i) (Wc D i) z 1 l) ⟨Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh, by rw [z'z]; exact hl⟩ (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh)` as an intermediate fact. Rewrite using `[← GlobalTheory.SplitHecke.symplO_actO _ _ z 1, zz]`. Conclude with `this`. Introduce `h l hl hlh`. Use `(Dc _ (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hu)).1 h (actO (Vc D i) (Wc D i) z⁻¹ 1 l) hl.2 (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh)` as an intermediate fact.

Rewrite `this` using `[GlobalTheory.SplitHecke.symplO_actO]`. Then use the resulting hypothesis. Establish `cl6c : ∀ u, IsHalf (cA D (cA D e)) u → ((∀ l ∈ Λc, IsHalf (cA D e) l → R.ψ (symplO (Vc D i) (Wc D i) l u) = 1) ↔ actO (Vc D i) (Wc D i) z 1 u ∈ Λ)`. Introduce `u hu`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `(De _ (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hu)).2 fun l hl hlh => ?_` and prove the remaining obligations. Use `h (actO (Vc D i) (Wc D i) z⁻¹ 1 l) ⟨Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh, by rw [zz]; exact hl⟩ (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh)` as an intermediate fact. Rewrite using `[← GlobalTheory.SplitHecke.symplO_actO _ _ z⁻¹ 1, z'z]`. Conclude with `this`. Introduce `h l hl hlh`.

Use `(De _ (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hu)).1 h (actO (Vc D i) (Wc D i) z 1 l) hl.2 (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh)` as an intermediate fact. Rewrite `this` using `[GlobalTheory.SplitHecke.symplO_actO]`. Then use the resulting hypothesis. Establish `cl13e : ∀ w, actO (Vc D i) (Wc D i) z⁻¹ 1 w ∈ Λ → IsHalf (cA D e) w → ∃! v, v ∈ Xc.image (actO (Vc D i) (Wc D i) z 1) ∧ w - v ∈ Λ`. Introduce `w hw hwh`. Take `⟨x, ⟨hxX, hxd⟩, hxu⟩` from `hXc2 _ hw (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hwh)`.

Use `⟨actO (Vc D i) (Wc D i) z 1 x, ⟨Finset.mem_image_of_mem _ hxX, by` and prove the remaining obligations. Use `hxd.2` as an intermediate fact. Rewrite using `[actsub, zz] at this⟩, ?_⟩` and apply the resulting hypothesis. Introduce and unpack `v ⟨hv, hvw⟩`. Take `⟨x', hx', rfl⟩` from `Finset.mem_image.1 hv`.

Rewrite using `[hxu x' ⟨hx', isHalf_sub (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hwh) (hXc1 x' hx').2, by`. Rewrite using `[actsub, zz]`. Conclude with `hvw⟩]`. Establish `cl13c : ∀ w, actO (Vc D i) (Wc D i) z 1 w ∈ Λ → IsHalf (cA D (cA D e)) w → ∃! v, v ∈ Xe.image (actO (Vc D i) (Wc D i) z⁻¹ 1) ∧ w - v ∈ Λ`. Introduce `w hw hwh`.

Rewrite `hwh` using `[cA_cA]`. Take `⟨x, ⟨hxX, hxd⟩, hxu⟩` from `hXe2 _ hw (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hwh)`. Use `⟨actO (Vc D i) (Wc D i) z⁻¹ 1 x, ⟨Finset.mem_image_of_mem _ hxX, by` and prove the remaining obligations. Use `hxd.2` as an intermediate fact. Rewrite using `[actsub, z'z] at this⟩, ?_⟩` and apply the resulting hypothesis.

Introduce and unpack `v ⟨hv, hvw⟩`. Take `⟨x', hx', rfl⟩` from `Finset.mem_image.1 hv`. Rewrite using `[hxu x' ⟨hx', isHalf_sub (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hwh) (hXe1 x' hx').2, by`. Rewrite using `[actsub, z'z]`. Conclude with `hvw⟩]`.

Establish `injz : Function.Injective (actO (Vc D i) (Wc D i) z 1)` using `fun x y h => by rw [← z'z x, h, z'z]`. Establish `injz' : Function.Injective (actO (Vc D i) (Wc D i) z⁻¹ 1)` using `fun x y h => by rw [← zz x, h, zz]`. Use `⟨Λe, Λc, Xe, Xc, Xe.image (actO (Vc D i) (Wc D i) z⁻¹ 1), Xc.image (actO (Vc D i) (Wc D i) z 1), rfl, rfl, ?_, ?_⟩` and prove the remaining obligations. Use `⟨memΛe, fun u hu => ?_, fun w hw => ?_, fun w hw hh => ?_, Dc, cl6e, fun d hd hdh hdn => ?_, hXe1, hXe2, fun u hu => ?_, fun u hu h => cl13e u ((cl6e u hu).1 h) hu, fun u hu => ?_, cl13e, by rw [hXecard, mul_comm], by rw [Finset.card_image_of_injective _ injz, hXccard], H1e, H2e, …` and prove the remaining obligations. Establish `e1 : u.map (fun y => e * y) = e • u` using `by ext a b; simp [Matrix.smul_apply]`.

Rewrite using `[e1]`. Conclude with `Formalism.IndefR.Fin.LevelGroupLemmas.Lat.smul_mem_latAll heInt hu`. Take `⟨hh, hm⟩` from `hw`. Establish `hh'` using `Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ z⁻¹ 1 hh`. Rewrite using `[← zz w, (part1.2.2.2.1 _ hh').1]`.

Conclude with `smulΛe π hπi _ hm hh'`. Rewrite using `[(part1.2.2.2.1 _ hh).1]`. Conclude with `smulΛe π hπi w hw hh`. Establish `hv : actO (Vc D i) (Wc D i) z⁻¹ 1 d ∉ Λ` using `fun h => hdn ⟨hdh, h⟩`. Establish `hvh : IsHalf (cA D (cA D e)) (actO (Vc D i) (Wc D i) z⁻¹ 1 d)`.

Rewrite using `[cA_cA]`. Conclude with `Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hdh`. Choose the witnesses or unpack the hypotheses as in `⟨l, hl, hlh, hne⟩ : ∃ l ∈ Λ, IsHalf (cA D e) l ∧ R.ψ (symplO (Vc D i) (Wc D i) l (actO (Vc D i) (Wc D i) z⁻¹ 1 d)) ≠ 1 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Conclude with `hv ((De _ hvh).2 hcon)`. Use `⟨actO (Vc D i) (Wc D i) z 1 l, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh, (cl6e _ (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh)).2 (by rw [z'z]; exact hl), ?_⟩` and prove the remaining obligations. Rewrite using `[← GlobalTheory.SplitHecke.symplO_actO _ _ z⁻¹ 1, z'z, GlobalTheory.OrientedHeis.symplO_skew, AddChar.map_neg_eq_inv]`. Conclude with `fun h => hne (inv_eq_one.1 h)`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 hu`.

Conclude with `⟨Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ (hXc1 x hx).2, (cl6e _ (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ (hXc1 x hx).2)).2 (by rw [z'z]; exact (hXc1 x hx).1)⟩`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 hu`. Conclude with `⟨by rw [z'z]; exact (hXc1 x hx).1, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ (hXc1 x hx).2⟩`. Use `⟨memΛc, fun u hu => ?_, fun w hw => ?_, fun w hw hh => ?_, De, cl6c, fun d hd hdh hdn => ?_, hXc1, hXc2, fun u hu => ?_, fun u hu h => cl13c u ((cl6c u hu).1 h) hu, fun u hu => ?_, cl13c, hXccard, by rw [Finset.card_image_of_injective _ injz', hXecard, mul_comm], H1c, H2c, hXcY⟩` and prove the remaining obligations. Establish `e1 : u.map (fun y => cA D e * y) = cA D e • u` using `by ext a b; simp [Matrix.smul_apply]`.

Rewrite using `[e1]`. Conclude with `Formalism.IndefR.Fin.LevelGroupLemmas.Lat.smul_mem_latAll hceInt hu`. Take `⟨hh, hm⟩` from `hw`. Establish `hh'` using `Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ z 1 hh`. Rewrite using `[← z'z w, (part1.2.2.2.2 _ hh').2]`.

Conclude with `smulΛc (cA D π) hπci _ hm hh'`. Rewrite using `[(part1.2.2.2.2 _ hh).2]`. Conclude with `smulΛc (cA D π) hπci w hw hh`. Establish `hv : actO (Vc D i) (Wc D i) z 1 d ∉ Λ` using `fun h => hdn ⟨hdh, h⟩`. Establish `hvh : IsHalf (cA D e) (actO (Vc D i) (Wc D i) z 1 d)` using `Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hdh`.

Choose the witnesses or unpack the hypotheses as in `⟨l, hl, hlh, hne⟩ : ∃ l ∈ Λ, IsHalf e l ∧ R.ψ (symplO (Vc D i) (Wc D i) l (actO (Vc D i) (Wc D i) z 1 d)) ≠ 1 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hv ((Dc _ hvh).2 hcon)`. Establish `hlh' : IsHalf (cA D (cA D e)) (actO (Vc D i) (Wc D i) z⁻¹ 1 l)`.

Rewrite using `[cA_cA]`. Conclude with `Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh`. Use `⟨actO (Vc D i) (Wc D i) z⁻¹ 1 l, hlh', (cl6c _ hlh').2 (by rw [zz]; exact hl), ?_⟩` and prove the remaining obligations. Rewrite using `[← GlobalTheory.SplitHecke.symplO_actO _ _ z 1, zz, GlobalTheory.OrientedHeis.symplO_skew, AddChar.map_neg_eq_inv]`. Conclude with `fun h => hne (inv_eq_one.1 h)`.

Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 hu`. Establish `hxh : IsHalf (cA D (cA D e)) (actO (Vc D i) (Wc D i) z⁻¹ 1 x)`. Rewrite using `[cA_cA]`. Conclude with `Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ (hXe1 x hx).2`. Conclude with `⟨hxh, (cl6c _ hxh).2 (by rw [zz]; exact (hXe1 x hx).1)⟩`.

Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 hu`. Conclude with `⟨by rw [zz]; exact (hXe1 x hx).1, by rw [cA_cA]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ (hXe1 x hx).2⟩`.
-/
theorem GlobalTheory.ZRep.central_reps : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0
    : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra
    Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i
    : Fin D.R.m) (t : T0), (∃ eQ : AE D, IsIdemSum eQ (R.Q
    t)) ∧ (∃ ϖ : Pl D.host.E → 𝓞 D.host.E, ∀ PP : Pl D.host.E, ϖ PP ∈ PP.asIdeal ∧ ϖ PP ∉ PP.asIdeal ^ 2) ∧ ∀ (eQ
    : AE D) (es : Pl D.host.E → AE D) (ϖ : Pl D.host.E → 𝓞 D.host.E), IsIdemSum eQ (R.Q
    t) → (∀ PP ∈ R.Q t, Formalism.L2.NTheta.IsIdemAt (es
    PP) PP) → (∀ PP ∈ R.Q t, ϖ PP ∈ PP.asIdeal ∧ ϖ PP ∉ PP.asIdeal ^ 2) → eQ = ∑ PP ∈ R.Q t, es PP → (∃ z : GA D (Vc
    D i), mt (Vc D i) z = Matrix.diagonal fun _ => (1 + ∑ PP ∈ R.Q t, (es PP * (incA D ((ϖ PP
    : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)))) ∧ ∀ z : GA D (Vc D
    i), (mt (Vc D i) z = Matrix.diagonal fun _ => (1 + ∑ PP ∈ R.Q t, (es PP * (incA D ((ϖ PP
    : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) -
    1)))) → ∀ Λ : AddSubgroup (WO (Vc D i) (Wc D i)), Λ = latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW
    i) (fun _ => True) → (IsCentAt i (R.Q t) z ∧ SuppAt eQ (Vc D i) z ∧ (∃ x : (AE D)ˣ, IsDetAt (cA
    D eQ) (Vc D i) z x ∧ (x : AE D) = 1 + ∑ PP ∈ R.Q t, cA D (es PP) * (incA D (star (ϖ PP
    : D.host.E)) ^ (Vc D i).rank - 1)) ∧ (∀ w : WO (Vc D i) (Wc D i), IsHalf eQ w → actO (Vc D
    i) (Wc D i) z 1 w = (∑ PP ∈ R.Q t, es PP * incA D (ϖ PP : D.host.E)) • w ∧ actO (Vc D i) (Wc D
    i) z⁻¹ 1 w = (∑ PP ∈ R.Q t, es PP * incA D ((ϖ PP : D.host.E)⁻¹)) • w) ∧ (∀ w : WO (Vc D i) (Wc
    D i), IsHalf (cA D eQ) w → actO (Vc D i) (Wc D i) z 1 w = cA D (∑ PP ∈ R.Q t, es PP * incA D ((ϖ
    PP : D.host.E)⁻¹)) • w ∧ actO (Vc D i) (Wc D i) z⁻¹ 1 w = cA D (∑ PP ∈ R.Q t, es PP * incA D (ϖ
    PP : D.host.E)) • w)) ∧ ∃ (Λe Λc : AddSubgroup (WO (Vc D i) (Wc D i))) (Xe Xc Re Rc : Finset (WO
    (Vc D i) (Wc D i))), Rc = Xc.image (actO (Vc D i) (Wc D i) z 1) ∧ Re = Xe.image (actO (Vc D i)
    (Wc D i) z⁻¹ 1) ∧ ((∀ w, w ∈ Λe ↔ IsHalf eQ w ∧ actO (Vc D i) (Wc D i) z⁻¹ 1 w ∈ Λ) ∧
    (∀ u ∈ Λ, u.map (fun y => eQ * y) ∈ Λ) ∧ Λe ≤ Λ ∧ (∀ w ∈ Λ, IsHalf eQ w → actO (Vc D i) (Wc D
    i) z 1 w ∈ Λ) ∧ (∀ u, IsHalf (cA D eQ) u → (u ∈ Λ ↔ ∀ l ∈ Λ, IsHalf eQ l → R.ψ (symplO (Vc D i)
    (Wc D i) l u) = 1)) ∧ (∀ u, IsHalf (cA D eQ) u → ((∀ l ∈ Λe, IsHalf eQ l → R.ψ (symplO (Vc D i)
    (Wc D i) l u) = 1) ↔ actO (Vc D i) (Wc D i) z⁻¹ 1 u ∈ Λ)) ∧
    (∀ d ∈ Λ, IsHalf eQ d → d ∉ Λe → ∃ u, IsHalf (cA D eQ) u ∧ (∀ l ∈ Λe, IsHalf eQ l → R.ψ (symplO
    (Vc D i) (Wc D i) l u) = 1) ∧ R.ψ (symplO (Vc D i) (Wc D i) d u) ≠ 1) ∧
    (∀ x ∈ Xe, x ∈ Λ ∧ IsHalf eQ x) ∧ (∀ w ∈ Λ, IsHalf eQ w → ∃! x, x ∈ Xe ∧ w - x ∈ Λe) ∧
    (∀ u ∈ Rc, IsHalf (cA D eQ) u ∧ ∀ l ∈ Λe, IsHalf eQ l → R.ψ (symplO (Vc D i) (Wc D i) l u) = 1)
    ∧ (∀ u, IsHalf (cA D eQ) u → (∀ l ∈ Λe, IsHalf eQ l → R.ψ (symplO (Vc D i) (Wc D i) l
    u) = 1) → ∃! v, v ∈ Rc ∧ u - v ∈ Λ) ∧ (∀ u ∈ Rc, actO (Vc D i) (Wc D i) z⁻¹ 1 u ∈ Λ ∧ IsHalf (cA
    D eQ) u) ∧ (∀ w, actO (Vc D i) (Wc D i) z⁻¹ 1 w ∈ Λ → IsHalf (cA D
    eQ) w → ∃! v, v ∈ Rc ∧ w - v ∈ Λ) ∧ Xe.card = (∏ PP ∈ R.Q t, Nat.card (kP PP)) ^ ((Vc D i).rank
    * (Wc D i).rank) ∧ Rc.card = (∏ PP ∈ R.Q t, Nat.card (kP PP)) ^ ((Vc D i).rank * (Wc D i).rank)
    ∧ (∀ w, IsHalf eQ w → (w ∈ Λ ↔ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w))) ∧
    (∀ w ∈ Λ, ∀ w' ∈ Λ, IsHalf eQ w → IsHalf eQ w' → (w - w' ∈ Λe ↔ ∀ PP ∈ R.Q t, redM PP (frMapO
    (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) = redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
    w'))) ∧ (∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (kP
    PP), ∃! x, x ∈ Xe ∧ ∀ PP ∈ R.Q t, redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
    x) = Y PP)) ∧ ((∀ w, w ∈ Λc ↔ IsHalf (cA D eQ) w ∧ actO (Vc D i) (Wc D i) z 1 w ∈ Λ) ∧
    (∀ u ∈ Λ, u.map (fun y => (cA D eQ) * y) ∈ Λ) ∧ Λc ≤ Λ ∧ (∀ w ∈ Λ, IsHalf (cA D eQ) w → actO (Vc
    D i) (Wc D i) z⁻¹ 1 w ∈ Λ) ∧ (∀ u, IsHalf (cA D (cA D eQ)) u → (u ∈ Λ ↔ ∀ l ∈ Λ, IsHalf (cA D
    eQ) l → R.ψ (symplO (Vc D i) (Wc D i) l u) = 1)) ∧ (∀ u, IsHalf (cA D (cA D
    eQ)) u → ((∀ l ∈ Λc, IsHalf (cA D eQ) l → R.ψ (symplO (Vc D i) (Wc D i) l u) = 1) ↔ actO (Vc D
    i) (Wc D i) z 1 u ∈ Λ)) ∧ (∀ d ∈ Λ, IsHalf (cA D eQ) d → d ∉ Λc → ∃ u, IsHalf (cA D (cA D
    eQ)) u ∧ (∀ l ∈ Λc, IsHalf (cA D eQ) l → R.ψ (symplO (Vc D i) (Wc D i) l u) = 1) ∧ R.ψ (symplO
    (Vc D i) (Wc D i) d u) ≠ 1) ∧ (∀ x ∈ Xc, x ∈ Λ ∧ IsHalf (cA D eQ) x) ∧ (∀ w ∈ Λ, IsHalf (cA D
    eQ) w → ∃! x, x ∈ Xc ∧ w - x ∈ Λc) ∧ (∀ u ∈ Re, IsHalf (cA D (cA D eQ)) u ∧ ∀ l ∈ Λc, IsHalf (cA
    D eQ) l → R.ψ (symplO (Vc D i) (Wc D i) l u) = 1) ∧ (∀ u, IsHalf (cA D (cA D
    eQ)) u → (∀ l ∈ Λc, IsHalf (cA D eQ) l → R.ψ (symplO (Vc D i) (Wc D i) l
    u) = 1) → ∃! v, v ∈ Re ∧ u - v ∈ Λ) ∧ (∀ u ∈ Re, actO (Vc D i) (Wc D i) z 1 u ∈ Λ ∧ IsHalf (cA D
    (cA D eQ)) u) ∧ (∀ w, actO (Vc D i) (Wc D i) z 1 w ∈ Λ → IsHalf (cA D (cA D
    eQ)) w → ∃! v, v ∈ Re ∧ w - v ∈ Λ) ∧ Xc.card = (∏ PP ∈ R.Q t, Nat.card (kP PP)) ^ ((Vc D i).rank
    * (Wc D i).rank) ∧ Re.card = (∏ PP ∈ R.Q t, Nat.card (kP PP)) ^ ((Vc D i).rank * (Wc D i).rank)
    ∧ (∀ w, IsHalf (cA D eQ) w → (w ∈ Λ ↔ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w)))
    ∧ (∀ w ∈ Λ, ∀ w' ∈ Λ, IsHalf (cA D eQ) w → IsHalf (cA D eQ) w' → (w - w' ∈ Λc ↔
    ∀ PP ∈ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) = redM PP (frMapAdj (Vc D
    i) (Wc D i) (R.βV i) (R.βW i) w'))) ∧ (∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin
    (Wc D i).rank) (kP PP), ∃! x, x ∈ Xc ∧ ∀ PP ∈ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV
    i) (R.βW i) x) = Y PP)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR hQ i t
  obtain ⟨hvac, -, -, -⟩ := hR.thP.vP i t
  have hψ : IsStdChar D R.ψ (-1) := hvac.1
  obtain ⟨cV, hcV⟩ := hR.lev.βV i
  obtain ⟨cW, hcW⟩ := hR.lev.βW i
  have fV : Formalism.L2.DIV.IsFrame (R.βV i) (R.ΛV i) := hcV.1
  have fW : Formalism.L2.DIV.IsFrame (R.βW i) (R.ΛW i) := hcW.1
  have sV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βV i))
  have sW : IsSelfDualC (Wc D i) (R.ΛW i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βW i))
  have hP := hQ.2 t
  refine ⟨?_, GlobalTheory.T.exists_uniformiser_family_hostField_integers D, ?_⟩
  · obtain ⟨f, eg, eQ, fg, -, hq, -⟩ := (GlobalTheory.FlatVecExist.flatVec_existsUnique D G Pl0 T0 A Ks R F hR hQ i t).1
    exact ⟨eQ, hq⟩
  intro eQ es ϖ hq hes hϖ heQ
  subst heQ
  have hc : (∑ PP ∈ R.Q t, es PP) * cA D (∑ PP ∈ R.Q t, es PP) = 0 := hq.2
  have hϖ0 : ∀ PP ∈ R.Q t, ϖ PP ≠ 0 := fun PP hPP h0 => (hϖ PP hPP).2 (by rw [h0]; exact zero_mem _)
  obtain ⟨hex, hZ⟩ := GlobalTheory.T.centralScalar_inverse_uniformisers_idempotent_sum D (Vc D i) (R.Q t) es ϖ hes hc hϖ0
  refine ⟨hex, fun z hz Λ hΛ => ?_⟩
  obtain ⟨hcen, hGf, hsupp, hdet, hinv, ha1, ha2, ha3, ha4⟩ := hZ z hz

  have act1 : ∀ w : WO (Vc D i) (Wc D i), actO (Vc D i) (Wc D i) z 1 w = cA D (1 + ∑ PP ∈ R.Q t, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) • w := fun w => actO_one_eq z _ hinv w
  have act2 : ∀ w : WO (Vc D i) (Wc D i), actO (Vc D i) (Wc D i) z⁻¹ 1 w = (1 + ∑ PP ∈ R.Q t, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) • w := fun w =>
    actO_one_eq z⁻¹ _ (by rw [inv_inv]; exact hz) w
  have zz : ∀ w : WO (Vc D i) (Wc D i), actO (Vc D i) (Wc D i) z 1 (actO (Vc D i) (Wc D i) z⁻¹ 1 w) = w := fun w => by
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.actO_actO, mul_inv_cancel, mul_one, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.actO_one]
  have z'z : ∀ w : WO (Vc D i) (Wc D i), actO (Vc D i) (Wc D i) z⁻¹ 1 (actO (Vc D i) (Wc D i) z 1 w) = w := fun w => by
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.actO_actO, inv_mul_cancel, mul_one, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.actO_one]
  have actsub : ∀ (g : GA D (Vc D i)) (x y : WO (Vc D i) (Wc D i)), actO (Vc D i) (Wc D i) g 1 (x - y) =
      actO (Vc D i) (Wc D i) g 1 x - actO (Vc D i) (Wc D i) g 1 y := fun g x y => by
    unfold actO; rw [Matrix.mul_sub, Matrix.sub_mul]
  set e := ∑ PP ∈ R.Q t, es PP with he
  set π := ∑ PP ∈ R.Q t, es PP * incA D (ϖ PP : D.host.E) with hπ
  set π' := ∑ PP ∈ R.Q t, es PP * incA D ((ϖ PP : D.host.E)⁻¹) with hπ'
  have part1 : IsCentAt i (R.Q t) z ∧ SuppAt e (Vc D i) z ∧ (∃ x : (AE D)ˣ, IsDetAt (cA D e) (Vc D i) z x ∧ (x : AE D) = 1 + ∑ PP ∈ R.Q t, cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) ^ (Vc D i).rank - 1)) ∧ (∀ w : WO (Vc D i) (Wc D i), IsHalf e w → actO (Vc D i) (Wc D i) z 1 w = π • w ∧ actO (Vc D i) (Wc D i) z⁻¹ 1 w = π' • w) ∧ (∀ w : WO (Vc D i) (Wc D i), IsHalf (cA D e) w → actO (Vc D i) (Wc D i) z 1 w = cA D π' • w ∧ actO (Vc D i) (Wc D i) z⁻¹ 1 w = cA D π • w) := by
    refine ⟨⟨hcen, hGf, e, hq, hsupp⟩, hsupp, hdet, fun w hw => ⟨?_, ?_⟩, fun w hw => ⟨?_, ?_⟩⟩
    · rw [act1, smul_half _ hw, ha2]
    · rw [act2, smul_half _ hw, ha1]
    · rw [act1, smul_half _ hw, ha4]
    · rw [act2, smul_half _ hw, ha3]
  refine ⟨part1, ?_⟩
  have he_idem : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hq
  have heInt : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he_idem])
  have heInf : infPart D e = 0 := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_of_idemSum hq
  have hceInt : finPart D (cA D e) ∈ intAE D := by
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.finPart_cA]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.cA_mem_intAE heInt
  have hceInf : infPart D (cA D e) = 0 := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_cA_idemSum hq
  have hce_idem : cA D e * cA D e = cA D e := by rw [← map_mul, he_idem]
  have hcc : cA D e * cA D (cA D e) = 0 := by rw [cA_cA, mul_comm, hc]
  have hπi : toEAf D π ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [hπ, map_sum]
    exact sum_mem fun PP hPP => by
      rw [map_mul]
      exact mul_mem (GlobalTheory.IdemRes.resS_idem_eq_one D _ PP (hes PP hPP)).1 (GlobalTheory.IdemIntegral.eToEAf_int D (ϖ PP))
  subst hΛ
  set Λ := latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (fun _ => True) with hΛ
  have H1e : ∀ w : WO (Vc D i) (Wc D i), IsHalf e w → (w ∈ Λ ↔ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w)) :=
    GlobalTheory.T.mem_completedLattice_half_iff_frameMatrix_integral D _ _ _ _ _ _ sV sW fV fW (R.Q t) e hq hP
  have H1c : ∀ w : WO (Vc D i) (Wc D i), IsHalf (cA D e) w → (w ∈ Λ ↔ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w)) :=
    fun w hw => ⟨fun h => GlobalTheory.HalfAdjInt.frMapAdj_int_of_half D _ _ _ _ _ _ sV sW fV fW _ e hq hP w h hw,
      fun h => GlobalTheory.HalfAdjLattice.mem_latO_of_adj_int D _ _ _ _ _ _ sV sW fV fW _ e hq hP w hw h⟩
  have smulΛe : ∀ c : AE D, toEAf D c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → ∀ w ∈ Λ, IsHalf e w → c • w ∈ Λ :=
    fun c hci w hw hh => (H1e _ (isHalf_smul c hh)).2 (by
      rw [GlobalTheory.RedHalfDrop.frMapO_smul_eq]; exact isIntM_smul hci ((H1e w hh).1 hw))
  have smulΛc : ∀ c : AE D, toEAf D (cA D c) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → ∀ w ∈ Λ, IsHalf (cA D e) w → c • w ∈ Λ :=
    fun c hci w hw hh => (H1c _ (isHalf_smul c hh)).2 (by
      rw [GlobalTheory.RedHalfDrop.frMapAdj_smul_eq]; exact isIntM_smul hci ((H1c w hh).1 hw))
  have hπci : toEAf D (cA D (cA D π)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by rw [cA_cA]; exact hπi
  have Dc := GlobalTheory.T.mem_completedLattice_conjugateHalf_iff_dual D R.ψ _ _ _ _ hψ sV sW e he_idem hc heInf heInt
  have De := GlobalTheory.T.mem_completedLattice_conjugateHalf_iff_dual D R.ψ _ _ _ _ hψ sV sW (cA D e) hce_idem hcc hceInf hceInt

  let Λe : AddSubgroup (WO (Vc D i) (Wc D i)) :=
    { carrier := {w | IsHalf e w ∧ actO (Vc D i) (Wc D i) z⁻¹ 1 w ∈ Λ}
      add_mem' := fun {x y} hx hy => ⟨Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_add hx.1 hy.1, by
        rw [act2, smul_add, ← act2, ← act2]; exact add_mem hx.2 hy.2⟩
      zero_mem' := ⟨Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_zero e, by rw [act2, smul_zero]; exact zero_mem _⟩
      neg_mem' := fun {x} hx => ⟨by
        have := isHalf_smul (-1 : AE D) hx.1; rwa [neg_one_smul] at this, by
        rw [act2, smul_neg, ← act2]; exact neg_mem hx.2⟩ }
  let Λc : AddSubgroup (WO (Vc D i) (Wc D i)) :=
    { carrier := {w | IsHalf (cA D e) w ∧ actO (Vc D i) (Wc D i) z 1 w ∈ Λ}
      add_mem' := fun {x y} hx hy => ⟨Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_add hx.1 hy.1, by
        rw [act1, smul_add, ← act1, ← act1]; exact add_mem hx.2 hy.2⟩
      zero_mem' := ⟨Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_zero _, by rw [act1, smul_zero]; exact zero_mem _⟩
      neg_mem' := fun {x} hx => ⟨by
        have := isHalf_smul (-1 : AE D) hx.1; rwa [neg_one_smul] at this, by
        rw [act1, smul_neg, ← act1]; exact neg_mem hx.2⟩ }
  have memΛe : ∀ w, w ∈ Λe ↔ IsHalf e w ∧ actO (Vc D i) (Wc D i) z⁻¹ 1 w ∈ Λ := fun w => Iff.rfl
  have memΛc : ∀ w, w ∈ Λc ↔ IsHalf (cA D e) w ∧ actO (Vc D i) (Wc D i) z 1 w ∈ Λ := fun w => Iff.rfl
  have H2e : ∀ w ∈ Λ, ∀ w' ∈ Λ, IsHalf e w → IsHalf e w' → (w - w' ∈ Λe ↔ ∀ PP ∈ R.Q t,
      redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) = redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w')) := by
    intro w hw w' hw' hh hh'
    have hd := isHalf_sub hh hh'
    have hi := (H1e w hh).1 hw
    have hi' := (H1e w' hh').1 hw'
    have hN : IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (w - w')) := (H1e _ hd).1 (sub_mem hw hw')
    have heN : toEAf D e • frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (w - w') = frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (w - w') := by
      rw [← GlobalTheory.RedHalfDrop.frMapO_smul_eq]; congr 1; ext a b; exact hd a b
    rw [memΛe, act2, smul_half _ hd, ha1, H1e _ (isHalf_smul _ hd), GlobalTheory.RedHalfDrop.frMapO_smul_eq,
      isIntM_smul_iff (R.Q t) es ϖ hes hc hϖ _ hN heN]
    constructor
    · rintro ⟨-, h⟩ PP hPP
      have := h PP hPP
      rw [frMapO_sub, redM_sub PP hi hi'] at this
      exact sub_eq_zero.1 this
    · intro h
      refine ⟨hd, fun PP hPP => ?_⟩
      rw [frMapO_sub, redM_sub PP hi hi', h PP hPP, sub_self]
  have H2c : ∀ w ∈ Λ, ∀ w' ∈ Λ, IsHalf (cA D e) w → IsHalf (cA D e) w' → (w - w' ∈ Λc ↔ ∀ PP ∈ R.Q t,
      redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) = redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w')) := by
    intro w hw w' hw' hh hh'
    have hd := isHalf_sub hh hh'
    have hi := (H1c w hh).1 hw
    have hi' := (H1c w' hh').1 hw'
    have hN : IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (w - w')) := (H1c _ hd).1 (sub_mem hw hw')
    have heN : toEAf D e • frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (w - w') = frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (w - w') := by
      have := GlobalTheory.RedHalfDrop.frMapAdj_smul_eq (R.βV i) (R.βW i) (cA D e) (w - w')
      rw [cA_cA] at this
      rw [← this]; congr 1; ext a b; exact hd a b
    rw [memΛc, act1, smul_half _ hd, ha4, H1c _ (isHalf_smul _ hd), GlobalTheory.RedHalfDrop.frMapAdj_smul_eq, cA_cA,
      isIntM_smul_iff (R.Q t) es ϖ hes hc hϖ _ hN heN]
    constructor
    · rintro ⟨-, h⟩ PP hPP
      have := h PP hPP
      rw [frMapAdj_sub, redM_sub PP hi hi'] at this
      exact sub_eq_zero.1 this
    · intro h
      refine ⟨hd, fun PP hPP => ?_⟩
      rw [frMapAdj_sub, redM_sub PP hi hi', h PP hPP, sub_self]
  have H3e : ∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (kP PP), ∃ w, IsHalf e w ∧
      IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) ∧ ∀ PP ∈ R.Q t, redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) = Y PP := by
    intro Y
    choose N hN heN hNY using fun (ij : Fin (Wc D i).rank × Fin (Vc D i).rank) =>
      GlobalTheory.T.exists_integral_lift_residues_idempotentSum D (R.Q t) es hes hc (fun PP => Y PP ij.1 ij.2)
    obtain ⟨y, hyh, -, hyz⟩ := GlobalTheory.HalfDuality.exists_half_frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) e he_idem
      (fun a b => N (a, b)) (fun a b => heN (a, b))
    have hI : IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) y) := by rw [hyz]; exact fun a b => hN (a, b)
    refine ⟨y, hyh, hI, fun PP hPP => ?_⟩
    ext a b
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.redM_of_int PP hI]
    have := hNY (a, b) PP hPP
    convert this using 2
    exact Subtype.ext (congrFun (congrFun hyz a) b)
  have WeightCompositions : ∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP), ∃ w, IsHalf (cA D e) w ∧
      IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) ∧ ∀ PP ∈ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) = Y PP := by
    intro Y
    choose N hN heN hNY using fun (ij : Fin (Vc D i).rank × Fin (Wc D i).rank) =>
      GlobalTheory.T.exists_integral_lift_residues_idempotentSum D (R.Q t) es hes hc (fun PP => Y PP ij.1 ij.2)
    obtain ⟨y, hyh, -, hyz⟩ := GlobalTheory.T.exists_conjugateHalf_prescribed_adjoint_frameMatrix D (Vc D i) (Wc D i) (R.βV i) (R.βW i) e he_idem
      (fun a b => N (a, b)) (fun a b => heN (a, b))
    have hI : IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y) := by rw [hyz]; exact fun a b => hN (a, b)
    refine ⟨y, hyh, hI, fun PP hPP => ?_⟩
    ext a b
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.redM_of_int PP hI]
    have := hNY (a, b) PP hPP
    convert this using 2
    exact Subtype.ext (congrFun (congrFun hyz a) b)
  obtain ⟨Xe, hXe1, hXe2, hXecard, hXeY⟩ := GlobalTheory.T.lattice_half_representatives_mod_reductions D (Vc D i) (Wc D i) Λ Λe e (R.Q t)
    (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)) (frMapO_sub _ _) H1e H2e H3e
  obtain ⟨Xc, hXc1, hXc2, hXccard, hXcY⟩ := GlobalTheory.T.lattice_half_representatives_mod_reductions D (Vc D i) (Wc D i) Λ Λc (cA D e) (R.Q t)
    (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i)) (frMapAdj_sub _ _) H1c H2c WeightCompositions

  have cl6e : ∀ u, IsHalf (cA D e) u → ((∀ l ∈ Λe, IsHalf e l → R.ψ (symplO (Vc D i) (Wc D i) l u) = 1) ↔
      actO (Vc D i) (Wc D i) z⁻¹ 1 u ∈ Λ) := by
    intro u hu
    constructor
    · intro h
      refine (Dc _ (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hu)).2 fun l hl hlh => ?_
      have := h (actO (Vc D i) (Wc D i) z 1 l) ⟨Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh, by rw [z'z]; exact hl⟩
        (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh)
      rw [← GlobalTheory.SplitHecke.symplO_actO _ _ z 1, zz]; exact this
    · intro h l hl hlh
      have := (Dc _ (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hu)).1 h (actO (Vc D i) (Wc D i) z⁻¹ 1 l) hl.2
        (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh)
      rwa [GlobalTheory.SplitHecke.symplO_actO] at this
  have cl6c : ∀ u, IsHalf (cA D (cA D e)) u → ((∀ l ∈ Λc, IsHalf (cA D e) l → R.ψ (symplO (Vc D i) (Wc D i) l u) = 1) ↔
      actO (Vc D i) (Wc D i) z 1 u ∈ Λ) := by
    intro u hu
    constructor
    · intro h
      refine (De _ (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hu)).2 fun l hl hlh => ?_
      have := h (actO (Vc D i) (Wc D i) z⁻¹ 1 l) ⟨Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh, by rw [zz]; exact hl⟩
        (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh)
      rw [← GlobalTheory.SplitHecke.symplO_actO _ _ z⁻¹ 1, z'z]; exact this
    · intro h l hl hlh
      have := (De _ (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hu)).1 h (actO (Vc D i) (Wc D i) z 1 l) hl.2
        (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh)
      rwa [GlobalTheory.SplitHecke.symplO_actO] at this
  have cl13e : ∀ w, actO (Vc D i) (Wc D i) z⁻¹ 1 w ∈ Λ → IsHalf (cA D e) w →
      ∃! v, v ∈ Xc.image (actO (Vc D i) (Wc D i) z 1) ∧ w - v ∈ Λ := by
    intro w hw hwh
    obtain ⟨x, ⟨hxX, hxd⟩, hxu⟩ := hXc2 _ hw (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hwh)
    refine ⟨actO (Vc D i) (Wc D i) z 1 x, ⟨Finset.mem_image_of_mem _ hxX, by
      have := hxd.2; rwa [actsub, zz] at this⟩, ?_⟩
    rintro v ⟨hv, hvw⟩
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hv
    rw [hxu x' ⟨hx', isHalf_sub (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hwh) (hXc1 x' hx').2, by
      rw [actsub, zz]; exact hvw⟩]
  have cl13c : ∀ w, actO (Vc D i) (Wc D i) z 1 w ∈ Λ → IsHalf (cA D (cA D e)) w →
      ∃! v, v ∈ Xe.image (actO (Vc D i) (Wc D i) z⁻¹ 1) ∧ w - v ∈ Λ := by
    intro w hw hwh
    rw [cA_cA] at hwh
    obtain ⟨x, ⟨hxX, hxd⟩, hxu⟩ := hXe2 _ hw (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hwh)
    refine ⟨actO (Vc D i) (Wc D i) z⁻¹ 1 x, ⟨Finset.mem_image_of_mem _ hxX, by
      have := hxd.2; rwa [actsub, z'z] at this⟩, ?_⟩
    rintro v ⟨hv, hvw⟩
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hv
    rw [hxu x' ⟨hx', isHalf_sub (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hwh) (hXe1 x' hx').2, by
      rw [actsub, z'z]; exact hvw⟩]
  have injz : Function.Injective (actO (Vc D i) (Wc D i) z 1) := fun x y h => by rw [← z'z x, h, z'z]
  have injz' : Function.Injective (actO (Vc D i) (Wc D i) z⁻¹ 1) := fun x y h => by rw [← zz x, h, zz]
  refine ⟨Λe, Λc, Xe, Xc, Xe.image (actO (Vc D i) (Wc D i) z⁻¹ 1), Xc.image (actO (Vc D i) (Wc D i) z 1), rfl, rfl, ?_, ?_⟩
  · refine ⟨memΛe, fun u hu => ?_, fun w hw => ?_, fun w hw hh => ?_, Dc, cl6e, fun d hd hdh hdn => ?_, hXe1, hXe2,
      fun u hu => ?_, fun u hu h => cl13e u ((cl6e u hu).1 h) hu, fun u hu => ?_, cl13e, by rw [hXecard, mul_comm],
      by rw [Finset.card_image_of_injective _ injz, hXccard], H1e, H2e, hXeY⟩
    · have e1 : u.map (fun y => e * y) = e • u := by ext a b; simp [Matrix.smul_apply]
      rw [e1]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.smul_mem_latAll heInt hu
    · obtain ⟨hh, hm⟩ := hw
      have hh' := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ z⁻¹ 1 hh
      rw [← zz w, (part1.2.2.2.1 _ hh').1]
      exact smulΛe π hπi _ hm hh'
    · rw [(part1.2.2.2.1 _ hh).1]; exact smulΛe π hπi w hw hh
    · have hv : actO (Vc D i) (Wc D i) z⁻¹ 1 d ∉ Λ := fun h => hdn ⟨hdh, h⟩
      have hvh : IsHalf (cA D (cA D e)) (actO (Vc D i) (Wc D i) z⁻¹ 1 d) := by
        rw [cA_cA]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hdh
      obtain ⟨l, hl, hlh, hne⟩ : ∃ l ∈ Λ, IsHalf (cA D e) l ∧
          R.ψ (symplO (Vc D i) (Wc D i) l (actO (Vc D i) (Wc D i) z⁻¹ 1 d)) ≠ 1 := by
        by_contra hcon
        push Not at hcon
        exact hv ((De _ hvh).2 hcon)
      refine ⟨actO (Vc D i) (Wc D i) z 1 l, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh,
        (cl6e _ (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh)).2 (by rw [z'z]; exact hl), ?_⟩
      rw [← GlobalTheory.SplitHecke.symplO_actO _ _ z⁻¹ 1, z'z, GlobalTheory.OrientedHeis.symplO_skew, AddChar.map_neg_eq_inv]
      exact fun h => hne (inv_eq_one.1 h)
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
      exact ⟨Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ (hXc1 x hx).2,
        (cl6e _ (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ (hXc1 x hx).2)).2 (by rw [z'z]; exact (hXc1 x hx).1)⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
      exact ⟨by rw [z'z]; exact (hXc1 x hx).1, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ (hXc1 x hx).2⟩
  · refine ⟨memΛc, fun u hu => ?_, fun w hw => ?_, fun w hw hh => ?_, De, cl6c, fun d hd hdh hdn => ?_, hXc1, hXc2,
      fun u hu => ?_, fun u hu h => cl13c u ((cl6c u hu).1 h) hu, fun u hu => ?_, cl13c, hXccard,
      by rw [Finset.card_image_of_injective _ injz', hXecard, mul_comm], H1c, H2c, hXcY⟩
    · have e1 : u.map (fun y => cA D e * y) = cA D e • u := by ext a b; simp [Matrix.smul_apply]
      rw [e1]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.smul_mem_latAll hceInt hu
    · obtain ⟨hh, hm⟩ := hw
      have hh' := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ z 1 hh
      rw [← z'z w, (part1.2.2.2.2 _ hh').2]
      exact smulΛc (cA D π) hπci _ hm hh'
    · rw [(part1.2.2.2.2 _ hh).2]; exact smulΛc (cA D π) hπci w hw hh
    · have hv : actO (Vc D i) (Wc D i) z 1 d ∉ Λ := fun h => hdn ⟨hdh, h⟩
      have hvh : IsHalf (cA D e) (actO (Vc D i) (Wc D i) z 1 d) := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hdh
      obtain ⟨l, hl, hlh, hne⟩ : ∃ l ∈ Λ, IsHalf e l ∧
          R.ψ (symplO (Vc D i) (Wc D i) l (actO (Vc D i) (Wc D i) z 1 d)) ≠ 1 := by
        by_contra hcon
        push Not at hcon
        exact hv ((Dc _ hvh).2 hcon)
      have hlh' : IsHalf (cA D (cA D e)) (actO (Vc D i) (Wc D i) z⁻¹ 1 l) := by
        rw [cA_cA]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh
      refine ⟨actO (Vc D i) (Wc D i) z⁻¹ 1 l, hlh', (cl6c _ hlh').2 (by rw [zz]; exact hl), ?_⟩
      rw [← GlobalTheory.SplitHecke.symplO_actO _ _ z 1, zz, GlobalTheory.OrientedHeis.symplO_skew, AddChar.map_neg_eq_inv]
      exact fun h => hne (inv_eq_one.1 h)
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
      have hxh : IsHalf (cA D (cA D e)) (actO (Vc D i) (Wc D i) z⁻¹ 1 x) := by
        rw [cA_cA]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ (hXe1 x hx).2
      exact ⟨hxh, (cl6c _ hxh).2 (by rw [zz]; exact (hXe1 x hx).1)⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
      exact ⟨by rw [zz]; exact (hXe1 x hx).1, by rw [cA_cA]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ (hXe1 x hx).2⟩
