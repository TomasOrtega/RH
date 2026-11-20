import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatCoordCont
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingAffine
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBPin
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabUMapEqOfRoots
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealBesselSubgroupActsFrameUpperUnitriangularStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalBesselFrameRealPlaceLinearIndependentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalRootCoordinatesEqFrameMatrixStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameMatrixMemUnipotentStabilizerFrameGramStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameGramMulEqConjTransposeMulFrameMatricesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalFrameGramEmbedEqRealFrameGramStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointRationalIsometryActsFrameMatrixStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalLinkConjugateMemIntegralRealPointsStatement
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Matrix

noncomputable section

open scoped Classical
open MeasureTheory

namespace GlobalTheory.LoopVol

def actSgn (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.diagonal fun b => (-1 : ℂ) ^ (r - b.val)

/- English proof (translation)
Rewrite using `[actSgn, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `b`. Rewrite using `[← mul_pow]`. Evaluate the numerical expressions.
-/
theorem actSgn_mul_self (r : ℕ) : actSgn r * actSgn r = 1 := by
  rw [actSgn, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← mul_pow]
  norm_num

/- English proof (translation)
Simplify using `[actSgn, Matrix.diagonal_mul, Matrix.mul_diagonal]`.
-/
theorem actSgn_conj_apply {r : ℕ} (M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (i j : Fin (r + 1)) :
    (actSgn r * M * actSgn r) i j = (-1 : ℂ) ^ (r - i.val) * M i j * (-1) ^ (r - j.val) := by
  simp [actSgn, Matrix.diagonal_mul, Matrix.mul_diagonal]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[Formalism.L2.SG.RealObj.ZhatO, actSgn, Matrix.mul_diagonal, mul_comm]`.
-/
theorem act_zhatO_eq {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    Formalism.L2.SG.RealObj.ZhatO Z = Z * actSgn r := by
  ext a b
  simp [Formalism.L2.SG.RealObj.ZhatO, actSgn, Matrix.mul_diagonal, mul_comm]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[ZhatOM, actSgn, Matrix.mul_diagonal, mul_comm]`.
-/
theorem act_zhatOM_map {K : Type} [Field K] {r : ℕ} (ψ : K →+* ℂ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    (ZhatOM Z).map ψ = Z.map ψ * actSgn r := by
  ext a b
  simp [ZhatOM, actSgn, Matrix.mul_diagonal, mul_comm]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[actSgn_conj_apply]`. Unfold `GlobalTheory.LoopV.ofRoots`. Use `split_ifs with h1 h2`. Both sides reduce to the same expression.

Substitute `h2` using the available equality. Rewrite using `[mul_one, ← mul_pow]`. Evaluate the numerical expressions. Simplify using the standard rewrite rules.
-/
theorem actSgn_conj_ofRoots {r : ℕ} (R : Finset (Fin (r + 1) × Fin (r + 1))) (c : R → ℂ) :
    actSgn r * GlobalTheory.LoopV.ofRoots R c * actSgn r =
      GlobalTheory.LoopV.ofRoots R (fun q => (-1 : ℂ) ^ (r - q.1.1.val) * c q * (-1) ^ (r - q.1.2.val)) := by
  ext i j
  rw [actSgn_conj_apply]
  unfold GlobalTheory.LoopV.ofRoots
  split_ifs with h1 h2
  · rfl
  · subst h2
    rw [mul_one, ← mul_pow]
    norm_num
  · simp

/- English proof (translation)
Introduce `i j` and use `⟨fun hij => by rw [actSgn_conj_apply, (h i j).1 hij]; simp, fun hij => by subst hij; rw [actSgn_conj_apply, (h i i).2 rfl, mul_one, ← mul_pow]; norm_num⟩`.
-/
theorem act_isUpUni_sgn {r : ℕ} {M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (h : IsUpUni M) :
    IsUpUni (actSgn r * M * actSgn r) := fun i j =>
  ⟨fun hij => by rw [actSgn_conj_apply, (h i j).1 hij]; simp,
   fun hij => by subst hij; rw [actSgn_conj_apply, (h i i).2 rfl, mul_one, ← mul_pow]; norm_num⟩

/- English proof (translation)
Introduce `i j` and use `⟨fun hij => by simp [(h i j).1 hij], fun hij => by subst hij; simp [(h i i).2 rfl]⟩`.
-/
theorem act_isUpUni_map {K : Type} [Field K] {N : ℕ} (ψ : K →+* ℂ) {M : Matrix (Fin N) (Fin N) K}
    (h : IsUpUni M) : IsUpUni (M.map ψ) := fun i j =>
  ⟨fun hij => by simp [(h i j).1 hij], fun hij => by subst hij; simp [(h i i).2 rfl]⟩

/- English proof (translation)
Introduce `i j` and use `⟨fun hij => by simp [(h i j).1 hij], fun hij => by subst hij; simp [(h i i).2 rfl]⟩`.
-/
theorem act_isLoUni_map {K : Type} [Field K] {N : ℕ} (ψ : K →+* ℂ) {M : Matrix (Fin N) (Fin N) K}
    (h : IsLoUni M) : IsLoUni (M.map ψ) := fun i j =>
  ⟨fun hij => by simp [(h i j).1 hij], fun hij => by subst hij; simp [(h i i).2 rfl]⟩

/- English proof (translation)
Introduce `i j` and use `⟨fun hij => by simp [Matrix.conjTranspose_apply, (h j i).1 hij], fun hij => by subst hij; simp [Matrix.conjTranspose_apply, (h i i).2 rfl]⟩`.
-/
theorem act_isLoUni_conjTranspose {N : ℕ} {C : Matrix (Fin N) (Fin N) ℂ} (h : IsUpUni C) : IsLoUni Cᴴ :=
  fun i j => ⟨fun hij => by simp [Matrix.conjTranspose_apply, (h j i).1 hij],
    fun hij => by subst hij; simp [Matrix.conjTranspose_apply, (h i i).2 rfl]⟩

/- English proof (translation)
Use `⟨act_isUpUni_sgn hm.1, ?_⟩` and prove the remaining obligations. Establish `hss` using `actSgn_mul_self r`. Establish `hsi : (actSgn r)⁻¹ = actSgn r` using `Matrix.inv_eq_left_inv hss`. Establish `e : P * (actSgn r * m * actSgn r) * P⁻¹ = Z * m * Z⁻¹`. Rewrite using `[← hP, Matrix.mul_inv_rev, hsi]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (actSgn r) (actSgn r), hss, Matrix.one_mul, ← Matrix.mul_assoc (actSgn r) (actSgn r), hss, Matrix.one_mul]`. Rewrite using `[e]`. Conclude with `hm.2`.
-/
theorem act_sgn_mem {r : ℕ} {Z P m : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hZ : IsUnit Z.det)
    (hP : Z * actSgn r = P) (hm : m ∈ GlobalTheory.LoopV.stabU Z) : actSgn r * m * actSgn r ∈ GlobalTheory.LoopV.stabU P := by
  refine ⟨act_isUpUni_sgn hm.1, ?_⟩
  have hss := actSgn_mul_self r
  have hsi : (actSgn r)⁻¹ = actSgn r := Matrix.inv_eq_left_inv hss
  have e : P * (actSgn r * m * actSgn r) * P⁻¹ = Z * m * Z⁻¹ := by
    rw [← hP, Matrix.mul_inv_rev, hsi]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (actSgn r) (actSgn r), hss, Matrix.one_mul, ← Matrix.mul_assoc (actSgn r) (actSgn r), hss,
      Matrix.one_mul]
  rw [e]
  exact hm.2

/- English proof (translation)
Establish `h1` using `GlobalTheory.LoopAct.stabU_map_eq_ofRoots ψ p _ (act_sgn_mem hZ hP hm)`. Establish `hss` using `actSgn_mul_self r`. Establish `h2 : actSgn r * (actSgn r * m * actSgn r) * actSgn r = actSgn r * GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat p)) (fun q => (actSgn r * m * actSgn r) q.1.1 q.1.2) * actSgn r` using `congrArg (fun M => actSgn r * M * actSgn r) h1`. Rewrite `h2` using `[actSgn_conj_ofRoots]`. Establish `e : actSgn r * (actSgn r * m * actSgn r) * actSgn r = m`.

Simplify using `only [← Matrix.mul_assoc, hss, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, hss, Matrix.mul_one]`. Rewrite `h2` using `[e]`. Use `h2.trans (congrArg (GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat p))) ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `q`.

Rewrite using `[actSgn_conj_apply]`. Establish `ha : ((-1 : ℂ) ^ (r - q.1.1.val)) * (-1) ^ (r - q.1.1.val) = 1` using `by rw [← mul_pow]; norm_num`. Establish `hb : ((-1 : ℂ) ^ (r - q.1.2.val)) * (-1) ^ (r - q.1.2.val) = 1` using `by rw [← mul_pow]; norm_num`. Take the linear combination `(m q.1.1 q.1.2 * (-1 : ℂ) ^ (r - q.1.2.val) * (-1) ^ (r - q.1.2.val)) * ha + m q.1.1 q.1.2 * hb`.
-/
theorem act_eq_ofRoots {K : Type} [Field K] {r : ℕ} (ψ : K →+* ℂ) (p : Point K (r + 1))
    {Z m : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hZ : IsUnit Z.det) (hP : Z * actSgn r = (ptMat p).map ψ)
    (hm : m ∈ GlobalTheory.LoopV.stabU Z) : m = GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat p)) (fun q => m q.1.1 q.1.2) := by
  have h1 := GlobalTheory.LoopAct.stabU_map_eq_ofRoots ψ p _ (act_sgn_mem hZ hP hm)
  have hss := actSgn_mul_self r
  have h2 : actSgn r * (actSgn r * m * actSgn r) * actSgn r = actSgn r * GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat p))
      (fun q => (actSgn r * m * actSgn r) q.1.1 q.1.2) * actSgn r := congrArg (fun M => actSgn r * M * actSgn r) h1
  rw [actSgn_conj_ofRoots] at h2
  have e : actSgn r * (actSgn r * m * actSgn r) * actSgn r = m := by
    simp only [← Matrix.mul_assoc, hss, Matrix.one_mul]
    rw [Matrix.mul_assoc, hss, Matrix.mul_one]
  rw [e] at h2
  refine h2.trans (congrArg (GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat p))) ?_)
  funext q
  rw [actSgn_conj_apply]
  have ha : ((-1 : ℂ) ^ (r - q.1.1.val)) * (-1) ^ (r - q.1.1.val) = 1 := by rw [← mul_pow]; norm_num
  have hb : ((-1 : ℂ) ^ (r - q.1.2.val)) * (-1) ^ (r - q.1.2.val) = 1 := by rw [← mul_pow]; norm_num
  linear_combination (m q.1.1 q.1.2 * (-1 : ℂ) ^ (r - q.1.2.val) * (-1) ^ (r - q.1.2.val)) * ha + m q.1.1 q.1.2 * hb

/- English proof (translation)
Rewrite using `[← pow_add, neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := r - i.val + (r - j.val))]`. Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem act_sign_pow (r : ℕ) (i j : Fin (r + 1)) :
    (-1 : ℂ) ^ (i.val + j.val) = (-1 : ℂ) ^ (r - i.val) * (-1) ^ (r - j.val) := by
  rw [← pow_add, neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := r - i.val + (r - j.val))]
  have hi := i.isLt
  have hj := j.isLt
  congr 1
  omega

/- English proof (translation)
Break down `neg_one_pow_eq_or ℂ k with h | h` into its components or cases. Simplify using `only [h, one_mul]`. Conclude with `MeasurePreserving.id volume`. Simplify using `only [h, neg_one_mul]`. Conclude with `Measure.measurePreserving_neg volume`.
-/
theorem act_neg_one_mp (k : ℕ) : MeasurePreserving (fun x : ℂ => (-1 : ℂ) ^ k * x) volume volume := by
  rcases neg_one_pow_eq_or ℂ k with h | h
  · simp only [h, one_mul]
    exact MeasurePreserving.id volume
  · simp only [h, neg_one_mul]
    exact Measure.measurePreserving_neg volume

open GlobalTheory.LoopAct in
/- English proof (translation)
Introduce `Cg cb Cu cT CT C0 A D X Y W large₂ u u' C' Cl hH s hrel hG w γw sf s' hat hrep hsf hs' hdec L U hL hU hZ Ω hcov`. Use `set R := GlobalTheory.LoopV.roots (ptMat w) with hR`. Establish `hRlt : ∀ q ∈ R, q.1 < q.2`. Introduce `q hq`. Simplify using `only [hR, GlobalTheory.LoopV.roots, Finset.mem_filter] at hq`.

Conclude with `hq.2.1`. Establish `hs'i : s'⁻¹ ∈ X.SinfU u'` using `Formalism.L2.SG.Pf.Sinf.sinf_inv' X u' hs'`. Establish `hsfi : sf⁻¹ ∈ X.SinfU u` using `Formalism.L2.SG.Pf.Sinf.sinf_inv' X u hsf`. Use `choose B hBu hBm using fun τ : D.what₂.Tau => GlobalTheory.T.realBesselSubgroup_acts_frame_upperUnitriangular D X u' s'⁻¹ hs'i (X.pl.symm τ)`. Use `choose Cm hCu hCm using fun τ : D.what₂.Tau => GlobalTheory.T.realBesselSubgroup_acts_frame_upperUnitriangular D X u sf⁻¹ hsfi (X.pl.symm τ)`.

Establish `hUi` using `Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv hU`. Use `set sg := actSgn D.R.rS with hsg`. Establish `hss : sg * sg = 1` using `actSgn_mul_self _`. Establish `hss' : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ, sg * (sg * M) = M` using `fun M => by`. Rewrite using `[← Matrix.mul_assoc, hss, Matrix.one_mul]`.

Use `set Uc : D.what₂.Tau → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ := fun τ => U.map (embS D τ) with hUc`. Establish `hUcu : ∀ τ, IsUpUni (Uc τ)` using `fun τ => act_isUpUni_map _ hU`. Establish `hBi : ∀ τ, (B τ)⁻¹ * B τ = 1 ∧ B τ * (B τ)⁻¹ = 1` using `fun τ => (Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv (hBu τ)).2`. Establish `hUci : ∀ τ, (Uc τ)⁻¹ * Uc τ = 1 ∧ Uc τ * (Uc τ)⁻¹ = 1` using `fun τ => (Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv (hUcu τ)).2`. Establish `hUcinv : ∀ τ, (U⁻¹).map (embS D τ) = (Uc τ)⁻¹` using `fun τ => by`.

Use `(Matrix.inv_eq_left_inv ?_).symm` and prove the remaining obligations. Simplify using `only [hUc]`. Rewrite using `[← Matrix.map_mul, hUi.2.1, Matrix.map_one _ (map_zero _) (map_one _)]`. Use `set Xm : D.what₂.Tau → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ := fun τ => Uc τ * sg * (B τ)⁻¹ with hXm`. Establish `hXinv : ∀ τ, (Xm τ)⁻¹ = B τ * sg * (Uc τ)⁻¹` using `fun τ => by`.

Use `Matrix.inv_eq_right_inv ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hXm, Matrix.mul_assoc]`. Use `_ = 1 := by rw [(hBi τ).1, Matrix.one_mul, hss', (hUci τ).2]`. Use `set T : (D.what₂.Tau → R → ℂ) → (D.what₂.Tau → R → ℂ) := fun c τ q => (Xm τ * GlobalTheory.LoopV.ofRoots R (c τ) * (Xm τ)⁻¹) q.1.1 q.1.2 with hTdef`.

Use `⟨T, ?_, ?_⟩` and prove the remaining obligations. Use `set a : D.what₂.Tau → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ := fun τ => Uc τ * (sg * (B τ)⁻¹ * sg) with ha set b : D.what₂.Tau → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ := fun τ => sg * B τ * sg * (Uc τ)⁻¹ with hb`. Establish `hau : ∀ τ, IsUpUni (a τ)` using `fun τ => Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_mul (hUcu τ) (act_isUpUni_sgn (Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv (hBu τ)).1)`. Establish `hbu : ∀ τ, IsUpUni (b τ)` using `fun τ => Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_mul (act_isUpUni_sgn (hBu τ)) (Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv (hUcu τ)).1`. Establish `hconj : ∀ τ (M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), Xm τ * M * (Xm τ)⁻¹ = a τ * (sg * M * sg) * b τ` using `fun τ M => by`.

Rewrite using `[hXinv]`. Simplify using `only [hXm, ha, hb, Matrix.mul_assoc, hss']`. Establish `hTc : T = (fun (c : D.what₂.Tau → R → ℂ) τ (q : R) => (a τ * GlobalTheory.LoopV.ofRoots R (c τ) * b τ) q.1.1 q.1.2) ∘ (fun (c : D.what₂.Tau → R → ℂ) τ => (fun (c' : R → ℂ) (q : R) => (-1 : ℂ) ^ (D.R.rS - q.1.1.val + (D.R.rS - q.1.2.val)) * c' q) (c τ))`. Use function extensionality and compare the values at `c τ q`. Simplify using `only [hTdef, Function.comp, hconj, hsg, actSgn_conj_ofRoots]`.

Establish `hfun : (fun q' : R => (-1 : ℂ) ^ (D.R.rS - q'.1.1.val) * c τ q' * (-1) ^ (D.R.rS - q'.1.2.val)) = fun q' : R => (-1 : ℂ) ^ (D.R.rS - q'.1.1.val + (D.R.rS - q'.1.2.val)) * c τ q'`. Use function extensionality and compare the values at `q'`. Rewrite using `[pow_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfun]`.

Rewrite using `[hTc]`. Use `(GlobalTheory.LoopVol.measurePreserving_mul_pi R hRlt a b hau hbu).comp ?_` and prove the remaining obligations. Conclude with `volume_preserving_pi fun _ => volume_preserving_pi fun q => act_neg_one_mp _`. Introduce `r hr`. Establish `hstr` using `Formalism.L2.SG.LoopTerm.stInf_conj_inv hsf hs' hdec hr`.

Establish `hyr : γw⁻¹ * (sf⁻¹ * r * sf) * γw ∈ X.SinfU u'` using `fun v => (hstr.2 v).1`. Use `choose Mr hMru hMrm using fun τ : D.what₂.Tau => GlobalTheory.T.realBesselSubgroup_acts_frame_upperUnitriangular D X u' _ hyr (X.pl.symm τ)`. Take `⟨n, hn, a, ha, hΩ⟩` from `hcov (T (GlobalTheory.LoopVol.ratCoord X u' w γw sf r))`. Take `⟨x, hx, hq⟩` from `GlobalTheory.T.rationalLink_conjugate_mem_integralRealPoints D X Y W u u' s n hn`. Use `⟨x.1, hq, ?_⟩` and prove the remaining obligations.

Establish `hqR` using `Formalism.L2.SG.Pf.LoopBPin.roinf_sub_rset s hq`. Establish `hstq` using `Formalism.L2.SG.LoopTerm.stInf_conj_inv hsf hs' hdec hqR`. Establish `hyq : γw⁻¹ * (sf⁻¹ * x.1 * sf) * γw ∈ X.SinfU u'` using `fun v => (hstq.2 v).1`. Use `set Ar : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E := Matrix.of fun i j => (-1) ^ (i.val + j.val) * a i j with hAr`. Establish `hnA : ∀ j, ((W.δ u)⁻¹ * n * W.δ u) (frame s.frame j) = ∑ i, Ar i j • frame s.frame i`.

Introduce `j`. Establish `e1 : ∀ i, frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) i = W.δ u (frame s.frame i)` using `fun i => by show (Formalism.L2.SG.Saturated.mapFlag (W.δ u) (W.isom u) s.frame.fl).fvec i = _`. Rewrite using `[Formalism.L2.SG.Saturated.fvec_mapFlag]`. Establish `h` using `ha j`. Simplify using `only [e1] at h`.

Use `show (W.δ u).symm (n (W.δ u (frame s.frame j))) = _`. Rewrite using `[h, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, LinearEquiv.symm_apply_apply]`. Both sides reduce to the same expression.

Establish `hum : ∀ (g h : X.B.I.Ginf) v, uMat ((g * h) v) = uMat (g v) * uMat (h v)`. Introduce `g h v`. Simplify using `[uMat]`. Establish `huinv : ∀ (g : X.B.I.Ginf) v, uMat (g⁻¹ v) * uMat (g v) = 1`. Introduce `g v`.

Rewrite using `[← hum, inv_mul_cancel]`. Simplify using `[uMat]`. Use `hΩ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `τ q`. Use `set v := X.pl.symm τ with hv`.

Establish `hplv : X.pl v = τ` using `X.pl.apply_symm_apply τ`. Use `set Zv := Formalism.L2.SG.RealObj.ZX X u u' 1 γw v with hZv`. Establish `hptC : Formalism.L2.SG.RealObj.ptC X v w = (ptMat w).map (embS D τ)`. Use extensionality with `i j`. Simplify using `only [Formalism.L2.SG.RealObj.ptC, Matrix.map_apply, X.φ_eq, RingEquiv.apply_symm_apply, hplv]`.

Establish `hZs : Zv * sg = (ptMat w).map (embS D τ)`. Rewrite using `[hZv, hsg, ← act_zhatO_eq, hrep v, hptC]`. Establish `hZu : IsUnit Zv.det`. Establish `h1 : IsUnit (Zv * sg).det`. Rewrite using `[hZs]`.

Establish `h2` using `(GlobalTheory.LoopV.Cell.ptMat_det w).map (embS D τ)`. Rewrite `h2` using `[RingHom.map_det]`. Conclude with `h2`. Rewrite `h1` using `[Matrix.det_mul]`. Conclude with `isUnit_of_mul_isUnit_left h1`.

Establish `hMrs : Mr τ ∈ GlobalTheory.LoopV.stabU Zv` using `GlobalTheory.T.frameMatrix_mem_unipotentStabilizer_frameGram D X u u' γw _ v (Mr τ) hstr (hMru τ) (hMrm τ) hZu`. Take `⟨Mq, hMqu, hMqm⟩` from `GlobalTheory.T.realBesselSubgroup_acts_frame_upperUnitriangular D X u' _ hyq v`. Establish `hMqs : Mq ∈ GlobalTheory.LoopV.stabU Zv` using `GlobalTheory.T.frameMatrix_mem_unipotentStabilizer_frameGram D X u u' γw _ v Mq hstq hMqu hMqm hZu`. Establish `hrc : GlobalTheory.LoopV.ofRoots R (GlobalTheory.LoopVol.ratCoord X u' w γw sf r τ) = Mr τ`. Establish `e : GlobalTheory.LoopVol.ratCoord X u' w γw sf r τ = fun q' : R => Mr τ q'.1.1 q'.1.2`.

Use function extensionality and compare the values at `(GlobalTheory.T.rationalRootCoordinates_eq_frameMatrix D X u' w γw sf r τ (Mr τ) (hMrm τ))`. Rewrite using `[e]`. Conclude with `(act_eq_ofRoots (embS D τ) w hZu hZs hMrs).symm`. Establish `hyqr : γw⁻¹ * (sf⁻¹ * (x.1 * r) * sf) * γw = (γw⁻¹ * (sf⁻¹ * x.1 * sf) * γw) * (γw⁻¹ * (sf⁻¹ * r * sf) * γw)` using `by group`. Establish `hMqrm : IsMatOn (uMat ((γw⁻¹ * (sf⁻¹ * (x.1 * r) * sf) * γw) v)) (Formalism.L2.SG.RealObj.frm X u' 1 v) (Mq * Mr τ)`.

Rewrite using `[hyqr, hum]`. Conclude with `isMatOn_mul hMqm (hMrm τ)`. Establish `hqrc : GlobalTheory.LoopV.ofRoots R (GlobalTheory.LoopVol.ratCoord X u' w γw sf (x.1 * r) τ) = Mq * Mr τ`. Establish `e : GlobalTheory.LoopVol.ratCoord X u' w γw sf (x.1 * r) τ = fun q' : R => (Mq * Mr τ) q'.1.1 q'.1.2`. Use function extensionality and compare the values at `(GlobalTheory.T.rationalRootCoordinates_eq_frameMatrix D X u' w γw sf (x.1 * r) τ (Mq * Mr τ) hMqrm)`.

Rewrite using `[e]`. Conclude with `(act_eq_ofRoots (embS D τ) w hZu hZs (stabU_mul hZu hMqs hMrs)).symm`. Establish `hAq` using `GlobalTheory.T.realPoint_rationalIsometry_acts_frame_matrix D X Y u u' s _ x Ar hx hnA v`. Rewrite `hAq` using `[hplv]`. Establish `hc1` using `isMatOn_conj hAq (huinv s.pt.1 v)`.

Establish `e1 : uMat (s.pt.1⁻¹ v) * uMat (x.1 v) * uMat (s.pt.1 v) = uMat ((s' * (γw⁻¹ * (sf⁻¹ * x.1 * sf) * γw) * s'⁻¹) v)`. Rewrite using `[← hum, ← hum]`. Use `congr 2`. Rewrite using `[hdec]`. Use `group`.

Rewrite `hc1` using `[e1]`. Establish `hc2` using `isMatOn_mul (hBm τ) hc1`. Establish `hc3` using `isMatOn_mul hMqm (hBm τ)`. Rewrite `hc2`, `hc3` using `[← hum]`. Establish `e2 : s'⁻¹ * (s' * (γw⁻¹ * (sf⁻¹ * x.1 * sf) * γw) * s'⁻¹) = (γw⁻¹ * (sf⁻¹ * x.1 * sf) * γw) * s'⁻¹` using `by group`.

Rewrite `hc2` using `[e2]`. Establish `heq` using `isMatOn_unique (GlobalTheory.T.rationalBesselFrame_realPlace_linearIndependent D X u' v) hc3 hc2`. Establish `hA' : Ar.map (embS D τ) = sg * a.map (embS D τ) * sg`. Use extensionality with `i j`. Rewrite using `[hsg, actSgn_conj_apply]`.

Simplify using `only [hAr, Matrix.map_apply, Matrix.of_apply, map_mul, map_pow, map_neg, map_one]`. Rewrite using `[act_sign_pow D.R.rS i j]`. Expand and normalize the polynomial expressions, which then agree. Establish `hMq : Mq = B τ * (sg * a.map (embS D τ) * sg) * (B τ)⁻¹`. Rewrite using `[← hA', ← heq, Matrix.mul_assoc, (hBi τ).2, Matrix.mul_one]`.

Establish `hzr` using `GlobalTheory.T.rationalFrameGram_embed_eq_realFrameGram D X Y W u u' s τ`. Establish `hzm` using `GlobalTheory.T.frameGram_mul_eq_conjTranspose_mul_frameMatrices D X u u' sf γw s'⁻¹ v (Cm τ) (B τ) (hCm τ) (hBm τ)`. Establish `hkey : (Cm τ)ᴴ * Zv * B τ * sg = L.map (embS D τ) * (Zv * sg) * Uc τ`. Establish `h : Matrix.map (ZhatOM (ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame))) (embS D τ) = Matrix.map (L * ptMat w * U) (embS D τ)` using `congrArg (fun M => Matrix.map M (embS D τ)) hZ`. Rewrite `h` using `[act_zhatOM_map, hzr, hdec, hzm, Matrix.map_mul, Matrix.map_mul, ← hZs]`.

Conclude with `h`. Use `set g0 := B τ * (sg * (Uc τ)⁻¹ * sg) with hg0`. Establish `hCl` using `act_isLoUni_conjTranspose (hCu τ)`. Establish `hCli` using `Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hCl`. Establish `hZg : Zv * g0 * Zv⁻¹ = ((Cm τ)ᴴ)⁻¹ * L.map (embS D τ)`.

Establish `h1 : (Cm τ)ᴴ * (Zv * g0) = L.map (embS D τ) * Zv`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hg0, Matrix.mul_assoc]`. Use `_ = L.map (embS D τ) * Zv := by`. Rewrite using `[hkey]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (Uc τ) (Uc τ)⁻¹, (hUci τ).2, Matrix.one_mul, hss, Matrix.mul_one]`. Establish `h2 : Zv * g0 = ((Cm τ)ᴴ)⁻¹ * (L.map (embS D τ) * Zv)`. Rewrite using `[← h1, ← Matrix.mul_assoc ((Cm τ)ᴴ)⁻¹, hCli.2.1, Matrix.one_mul]`. Rewrite using `[h2, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hZu, Matrix.mul_one]`.

Establish `hg0s : g0 ∈ GlobalTheory.LoopV.stabU Zv`. Use `⟨Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_mul (hBu τ) (act_isUpUni_sgn (Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv (hUcu τ)).1), ?_⟩` and prove the remaining obligations. Rewrite using `[hZg]`. Conclude with `Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_mul hCli.1 (act_isLoUni_map _ hL)`. Establish `hg0i : g0⁻¹ = sg * Uc τ * sg * (B τ)⁻¹`.

Use `Matrix.inv_eq_right_inv ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hg0, Matrix.mul_assoc]`. Use `_ = 1 := by rw [hss', ← Matrix.mul_assoc (Uc τ)⁻¹, (hUci τ).1, Matrix.one_mul, hss', (hBi τ).2]`. Establish `hXr : Xm τ * Mr τ * (Xm τ)⁻¹ = sg * (g0⁻¹ * Mr τ * g0) * sg`.

Rewrite using `[hg0i, hXinv]`. Simplify using `only [hXm, hg0, Matrix.mul_assoc, hss', hss, Matrix.mul_one]`. Establish `hXrs : GlobalTheory.LoopV.ofRoots R (T (GlobalTheory.LoopVol.ratCoord X u' w γw sf r) τ) = Xm τ * Mr τ * (Xm τ)⁻¹`. Establish `hm` using `act_sgn_mem hZu hZs (stabU_mul hZu (stabU_mul hZu (stabU_inv hZu hg0s) hMrs) hg0s)`. Establish `h1` using `GlobalTheory.LoopAct.stabU_map_eq_ofRoots (embS D τ) w _ hm`.

Rewrite `h1` using `[← hXr]`. Rewrite using `[h1]`. Use `congrArg (GlobalTheory.LoopV.ofRoots R) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `q'`. Simplify using `only [hTdef]`.

Rewrite using `[hrc]`. Rewrite using `[hXrs]`. Simplify using `only [hTdef]`. Establish `hB1 : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ, (B τ)⁻¹ * (B τ * M) = M` using `fun M => by`. Rewrite using `[← Matrix.mul_assoc, (hBi τ).1, Matrix.one_mul]`.

Establish `hU1 : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ, (Uc τ)⁻¹ * (Uc τ * M) = M` using `fun M => by`. Rewrite using `[← Matrix.mul_assoc, (hUci τ).1, Matrix.one_mul]`. Establish `hfin : ∀ P : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ, Xm τ * (B τ * (sg * P * sg) * (B τ)⁻¹ * Mr τ) * (B τ * sg * (Uc τ)⁻¹) = Uc τ * P * (Uc τ)⁻¹ * (Xm τ * Mr τ * (B τ * sg * (Uc τ)⁻¹))` using `fun P => by`. Simplify using `only [hXm, Matrix.mul_assoc, hB1, hU1, hss']`. Rewrite using `[hqrc, Matrix.map_mul, Matrix.map_mul, hUcinv, hMq, hXinv, hfin]`.
-/
theorem cover_action : ∀ Cg cb Cu cT CT C0 A : ℝ, ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ s : TT Y u u', s.relevant → s.G ≠ 0 → ∀ (w : Point D.host.E (D.R.rS + 1)) (γw sf s' : X.B.I.Ginf), s.toTerm.atPt w → Formalism.L2.SG.RealObj.IsPtRep X u u' w γw → sf ∈ X.SinfU u → s' ∈ X.SinfU u' → s.pt.1 = sf * γw * s'⁻¹ → ∀ (L U : Formalism.MainNotions.S.Cnt.GramM D), IsLoUni L → IsUpUni U → ZhatOM (ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame)) = L * ptMat w * U → ∀ Ω : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), (∀ c : D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ, ∃ n ∈ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u)) ∩ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame), ∃ a : Formalism.MainNotions.S.Cnt.GramM D, (∀ j : Fin (D.R.rS + 1), n (frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) j) = ∑ i : Fin (D.R.rS + 1), ((-1) ^ (i.val + j.val) * a i j) • frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) i) ∧ (fun τ (q : GlobalTheory.LoopV.roots (ptMat w)) => ((U * a * U⁻¹).map (embS D τ) * GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat w)) (c τ) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ) q.1.1 q.1.2) ∈ Ω) → ∃ T : (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ) → (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), MeasureTheory.MeasurePreserving T MeasureTheory.volume MeasureTheory.volume ∧ ∀ r ∈ Formalism.L2.SG.TermOp.Vanish.Rset s, ∃ q ∈ Formalism.L2.SG.TermOp.ROinf s, T (GlobalTheory.LoopVol.ratCoord X u' w γw sf (q * r)) ∈ Ω := by
  intro Cg cb Cu cT CT C0 A D X Y W large₂ u u' C' Cl hH s hrel hG w γw sf s' hat hrep hsf hs' hdec L U hL hU hZ Ω hcov
  set R := GlobalTheory.LoopV.roots (ptMat w) with hR
  have hRlt : ∀ q ∈ R, q.1 < q.2 := by
    intro q hq
    simp only [hR, GlobalTheory.LoopV.roots, Finset.mem_filter] at hq
    exact hq.2.1
  have hs'i : s'⁻¹ ∈ X.SinfU u' := Formalism.L2.SG.Pf.Sinf.sinf_inv' X u' hs'
  have hsfi : sf⁻¹ ∈ X.SinfU u := Formalism.L2.SG.Pf.Sinf.sinf_inv' X u hsf
  choose B hBu hBm using fun τ : D.what₂.Tau => GlobalTheory.T.realBesselSubgroup_acts_frame_upperUnitriangular D X u' s'⁻¹ hs'i (X.pl.symm τ)
  choose Cm hCu hCm using fun τ : D.what₂.Tau => GlobalTheory.T.realBesselSubgroup_acts_frame_upperUnitriangular D X u sf⁻¹ hsfi (X.pl.symm τ)
  have hUi := Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv hU
  set sg := actSgn D.R.rS with hsg
  have hss : sg * sg = 1 := actSgn_mul_self _
  have hss' : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ, sg * (sg * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hss, Matrix.one_mul]
  set Uc : D.what₂.Tau → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ := fun τ => U.map (embS D τ) with hUc
  have hUcu : ∀ τ, IsUpUni (Uc τ) := fun τ => act_isUpUni_map _ hU
  have hBi : ∀ τ, (B τ)⁻¹ * B τ = 1 ∧ B τ * (B τ)⁻¹ = 1 := fun τ => (Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv (hBu τ)).2
  have hUci : ∀ τ, (Uc τ)⁻¹ * Uc τ = 1 ∧ Uc τ * (Uc τ)⁻¹ = 1 := fun τ =>
    (Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv (hUcu τ)).2
  have hUcinv : ∀ τ, (U⁻¹).map (embS D τ) = (Uc τ)⁻¹ := fun τ => by
    refine (Matrix.inv_eq_left_inv ?_).symm
    simp only [hUc]
    rw [← Matrix.map_mul, hUi.2.1, Matrix.map_one _ (map_zero _) (map_one _)]
  set Xm : D.what₂.Tau → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ := fun τ => Uc τ * sg * (B τ)⁻¹ with hXm
  have hXinv : ∀ τ, (Xm τ)⁻¹ = B τ * sg * (Uc τ)⁻¹ := fun τ => by
    refine Matrix.inv_eq_right_inv ?_
    calc Xm τ * (B τ * sg * (Uc τ)⁻¹) = Uc τ * (sg * (((B τ)⁻¹ * B τ) * (sg * (Uc τ)⁻¹))) := by
          simp only [hXm, Matrix.mul_assoc]
      _ = 1 := by rw [(hBi τ).1, Matrix.one_mul, hss', (hUci τ).2]

  set T : (D.what₂.Tau → R → ℂ) → (D.what₂.Tau → R → ℂ) :=
    fun c τ q => (Xm τ * GlobalTheory.LoopV.ofRoots R (c τ) * (Xm τ)⁻¹) q.1.1 q.1.2 with hTdef
  refine ⟨T, ?_, ?_⟩
  · set a : D.what₂.Tau → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ := fun τ => Uc τ * (sg * (B τ)⁻¹ * sg) with ha
    set b : D.what₂.Tau → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ := fun τ => sg * B τ * sg * (Uc τ)⁻¹ with hb
    have hau : ∀ τ, IsUpUni (a τ) := fun τ => Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_mul (hUcu τ)
      (act_isUpUni_sgn (Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv (hBu τ)).1)
    have hbu : ∀ τ, IsUpUni (b τ) := fun τ => Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_mul (act_isUpUni_sgn (hBu τ))
      (Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv (hUcu τ)).1
    have hconj : ∀ τ (M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ),
        Xm τ * M * (Xm τ)⁻¹ = a τ * (sg * M * sg) * b τ := fun τ M => by
      rw [hXinv]
      simp only [hXm, ha, hb, Matrix.mul_assoc, hss']
    have hTc : T = (fun (c : D.what₂.Tau → R → ℂ) τ (q : R) => (a τ * GlobalTheory.LoopV.ofRoots R (c τ) * b τ) q.1.1 q.1.2) ∘
        (fun (c : D.what₂.Tau → R → ℂ) τ => (fun (c' : R → ℂ) (q : R) =>
          (-1 : ℂ) ^ (D.R.rS - q.1.1.val + (D.R.rS - q.1.2.val)) * c' q) (c τ)) := by
      funext c τ q
      simp only [hTdef, Function.comp, hconj, hsg, actSgn_conj_ofRoots]
      have hfun : (fun q' : R => (-1 : ℂ) ^ (D.R.rS - q'.1.1.val) * c τ q' * (-1) ^ (D.R.rS - q'.1.2.val)) =
          fun q' : R => (-1 : ℂ) ^ (D.R.rS - q'.1.1.val + (D.R.rS - q'.1.2.val)) * c τ q' := by
        funext q'
        rw [pow_add]
        ring
      rw [hfun]
    rw [hTc]
    refine (GlobalTheory.LoopVol.measurePreserving_mul_pi R hRlt a b hau hbu).comp ?_
    exact volume_preserving_pi fun _ => volume_preserving_pi fun q => act_neg_one_mp _
  · intro r hr
    have hstr := Formalism.L2.SG.LoopTerm.stInf_conj_inv hsf hs' hdec hr
    have hyr : γw⁻¹ * (sf⁻¹ * r * sf) * γw ∈ X.SinfU u' := fun v => (hstr.2 v).1
    choose Mr hMru hMrm using fun τ : D.what₂.Tau => GlobalTheory.T.realBesselSubgroup_acts_frame_upperUnitriangular D X u' _ hyr (X.pl.symm τ)
    obtain ⟨n, hn, a, ha, hΩ⟩ := hcov (T (GlobalTheory.LoopVol.ratCoord X u' w γw sf r))
    obtain ⟨x, hx, hq⟩ := GlobalTheory.T.rationalLink_conjugate_mem_integralRealPoints D X Y W u u' s n hn
    refine ⟨x.1, hq, ?_⟩
    have hqR := Formalism.L2.SG.Pf.LoopBPin.roinf_sub_rset s hq
    have hstq := Formalism.L2.SG.LoopTerm.stInf_conj_inv hsf hs' hdec hqR
    have hyq : γw⁻¹ * (sf⁻¹ * x.1 * sf) * γw ∈ X.SinfU u' := fun v => (hstq.2 v).1
    set Ar : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E :=
      Matrix.of fun i j => (-1) ^ (i.val + j.val) * a i j with hAr
    have hnA : ∀ j, ((W.δ u)⁻¹ * n * W.δ u) (frame s.frame j) = ∑ i, Ar i j • frame s.frame i := by
      intro j
      have e1 : ∀ i, frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) i = W.δ u (frame s.frame i) :=
        fun i => by
          show (Formalism.L2.SG.Saturated.mapFlag (W.δ u) (W.isom u) s.frame.fl).fvec i = _
          rw [Formalism.L2.SG.Saturated.fvec_mapFlag]
      have h := ha j
      simp only [e1] at h
      show (W.δ u).symm (n (W.δ u (frame s.frame j))) = _
      rw [h, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, LinearEquiv.symm_apply_apply]
      rfl
    have hum : ∀ (g h : X.B.I.Ginf) v, uMat ((g * h) v) = uMat (g v) * uMat (h v) := by
      intro g h v
      simp [uMat]
    have huinv : ∀ (g : X.B.I.Ginf) v, uMat (g⁻¹ v) * uMat (g v) = 1 := by
      intro g v
      rw [← hum, inv_mul_cancel]
      simp [uMat]
    convert hΩ using 1
    funext τ q
    set v := X.pl.symm τ with hv
    have hplv : X.pl v = τ := X.pl.apply_symm_apply τ
    set Zv := Formalism.L2.SG.RealObj.ZX X u u' 1 γw v with hZv
    have hptC : Formalism.L2.SG.RealObj.ptC X v w = (ptMat w).map (embS D τ) := by
      ext i j
      simp only [Formalism.L2.SG.RealObj.ptC, Matrix.map_apply, X.φ_eq, RingEquiv.apply_symm_apply, hplv]
    have hZs : Zv * sg = (ptMat w).map (embS D τ) := by
      rw [hZv, hsg, ← act_zhatO_eq, hrep v, hptC]
    have hZu : IsUnit Zv.det := by
      have h1 : IsUnit (Zv * sg).det := by
        rw [hZs]
        have h2 := (GlobalTheory.LoopV.Cell.ptMat_det w).map (embS D τ)
        rw [RingHom.map_det] at h2
        exact h2
      rw [Matrix.det_mul] at h1
      exact isUnit_of_mul_isUnit_left h1
    have hMrs : Mr τ ∈ GlobalTheory.LoopV.stabU Zv := GlobalTheory.T.frameMatrix_mem_unipotentStabilizer_frameGram D X u u' γw _ v (Mr τ) hstr (hMru τ) (hMrm τ) hZu
    obtain ⟨Mq, hMqu, hMqm⟩ := GlobalTheory.T.realBesselSubgroup_acts_frame_upperUnitriangular D X u' _ hyq v
    have hMqs : Mq ∈ GlobalTheory.LoopV.stabU Zv := GlobalTheory.T.frameMatrix_mem_unipotentStabilizer_frameGram D X u u' γw _ v Mq hstq hMqu hMqm hZu

    have hrc : GlobalTheory.LoopV.ofRoots R (GlobalTheory.LoopVol.ratCoord X u' w γw sf r τ) = Mr τ := by
      have e : GlobalTheory.LoopVol.ratCoord X u' w γw sf r τ = fun q' : R => Mr τ q'.1.1 q'.1.2 :=
        funext (GlobalTheory.T.rationalRootCoordinates_eq_frameMatrix D X u' w γw sf r τ (Mr τ) (hMrm τ))
      rw [e]
      exact (act_eq_ofRoots (embS D τ) w hZu hZs hMrs).symm
    have hyqr : γw⁻¹ * (sf⁻¹ * (x.1 * r) * sf) * γw =
        (γw⁻¹ * (sf⁻¹ * x.1 * sf) * γw) * (γw⁻¹ * (sf⁻¹ * r * sf) * γw) := by group
    have hMqrm : IsMatOn (uMat ((γw⁻¹ * (sf⁻¹ * (x.1 * r) * sf) * γw) v)) (Formalism.L2.SG.RealObj.frm X u' 1 v)
        (Mq * Mr τ) := by
      rw [hyqr, hum]
      exact isMatOn_mul hMqm (hMrm τ)
    have hqrc : GlobalTheory.LoopV.ofRoots R (GlobalTheory.LoopVol.ratCoord X u' w γw sf (x.1 * r) τ) = Mq * Mr τ := by
      have e : GlobalTheory.LoopVol.ratCoord X u' w γw sf (x.1 * r) τ = fun q' : R => (Mq * Mr τ) q'.1.1 q'.1.2 :=
        funext (GlobalTheory.T.rationalRootCoordinates_eq_frameMatrix D X u' w γw sf (x.1 * r) τ (Mq * Mr τ) hMqrm)
      rw [e]
      exact (act_eq_ofRoots (embS D τ) w hZu hZs (stabU_mul hZu hMqs hMrs)).symm

    have hAq := GlobalTheory.T.realPoint_rationalIsometry_acts_frame_matrix D X Y u u' s _ x Ar hx hnA v
    rw [hplv] at hAq
    have hc1 := isMatOn_conj hAq (huinv s.pt.1 v)
    have e1 : uMat (s.pt.1⁻¹ v) * uMat (x.1 v) * uMat (s.pt.1 v) =
        uMat ((s' * (γw⁻¹ * (sf⁻¹ * x.1 * sf) * γw) * s'⁻¹) v) := by
      rw [← hum, ← hum]
      congr 2
      rw [hdec]
      group
    rw [e1] at hc1
    have hc2 := isMatOn_mul (hBm τ) hc1
    have hc3 := isMatOn_mul hMqm (hBm τ)
    rw [← hum] at hc2 hc3
    have e2 : s'⁻¹ * (s' * (γw⁻¹ * (sf⁻¹ * x.1 * sf) * γw) * s'⁻¹) = (γw⁻¹ * (sf⁻¹ * x.1 * sf) * γw) * s'⁻¹ := by
      group
    rw [e2] at hc2
    have heq := isMatOn_unique (GlobalTheory.T.rationalBesselFrame_realPlace_linearIndependent D X u' v) hc3 hc2
    have hA' : Ar.map (embS D τ) = sg * a.map (embS D τ) * sg := by
      ext i j
      rw [hsg, actSgn_conj_apply]
      simp only [hAr, Matrix.map_apply, Matrix.of_apply, map_mul, map_pow, map_neg, map_one]
      rw [act_sign_pow D.R.rS i j]
      ring
    have hMq : Mq = B τ * (sg * a.map (embS D τ) * sg) * (B τ)⁻¹ := by
      rw [← hA', ← heq, Matrix.mul_assoc, (hBi τ).2, Matrix.mul_one]

    have hzr := GlobalTheory.T.rationalFrameGram_embed_eq_realFrameGram D X Y W u u' s τ
    have hzm := GlobalTheory.T.frameGram_mul_eq_conjTranspose_mul_frameMatrices D X u u' sf γw s'⁻¹ v (Cm τ) (B τ) (hCm τ) (hBm τ)
    have hkey : (Cm τ)ᴴ * Zv * B τ * sg = L.map (embS D τ) * (Zv * sg) * Uc τ := by
      have h : Matrix.map (ZhatOM (ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame)))
          (embS D τ) = Matrix.map (L * ptMat w * U) (embS D τ) := congrArg (fun M => Matrix.map M (embS D τ)) hZ
      rw [act_zhatOM_map, hzr, hdec, hzm, Matrix.map_mul, Matrix.map_mul, ← hZs] at h
      exact h
    set g0 := B τ * (sg * (Uc τ)⁻¹ * sg) with hg0
    have hCl := act_isLoUni_conjTranspose (hCu τ)
    have hCli := Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hCl
    have hZg : Zv * g0 * Zv⁻¹ = ((Cm τ)ᴴ)⁻¹ * L.map (embS D τ) := by
      have h1 : (Cm τ)ᴴ * (Zv * g0) = L.map (embS D τ) * Zv := by
        calc (Cm τ)ᴴ * (Zv * g0) = ((Cm τ)ᴴ * Zv * B τ * sg) * ((Uc τ)⁻¹ * sg) := by
              simp only [hg0, Matrix.mul_assoc]
          _ = L.map (embS D τ) * Zv := by
              rw [hkey]
              simp only [Matrix.mul_assoc]
              rw [← Matrix.mul_assoc (Uc τ) (Uc τ)⁻¹, (hUci τ).2, Matrix.one_mul, hss, Matrix.mul_one]
      have h2 : Zv * g0 = ((Cm τ)ᴴ)⁻¹ * (L.map (embS D τ) * Zv) := by
        rw [← h1, ← Matrix.mul_assoc ((Cm τ)ᴴ)⁻¹, hCli.2.1, Matrix.one_mul]
      rw [h2, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hZu, Matrix.mul_one]
    have hg0s : g0 ∈ GlobalTheory.LoopV.stabU Zv := by
      refine ⟨Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_mul (hBu τ)
        (act_isUpUni_sgn (Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv (hUcu τ)).1), ?_⟩
      rw [hZg]
      exact Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_mul hCli.1 (act_isLoUni_map _ hL)
    have hg0i : g0⁻¹ = sg * Uc τ * sg * (B τ)⁻¹ := by
      refine Matrix.inv_eq_right_inv ?_
      calc g0 * (sg * Uc τ * sg * (B τ)⁻¹) = B τ * (sg * ((Uc τ)⁻¹ * (sg * (sg * (Uc τ * (sg * (B τ)⁻¹)))))) := by
            simp only [hg0, Matrix.mul_assoc]
        _ = 1 := by rw [hss', ← Matrix.mul_assoc (Uc τ)⁻¹, (hUci τ).1, Matrix.one_mul, hss', (hBi τ).2]
    have hXr : Xm τ * Mr τ * (Xm τ)⁻¹ = sg * (g0⁻¹ * Mr τ * g0) * sg := by
      rw [hg0i, hXinv]
      simp only [hXm, hg0, Matrix.mul_assoc, hss', hss, Matrix.mul_one]
    have hXrs : GlobalTheory.LoopV.ofRoots R (T (GlobalTheory.LoopVol.ratCoord X u' w γw sf r) τ) = Xm τ * Mr τ * (Xm τ)⁻¹ := by
      have hm := act_sgn_mem hZu hZs (stabU_mul hZu (stabU_mul hZu (stabU_inv hZu hg0s) hMrs) hg0s)
      have h1 := GlobalTheory.LoopAct.stabU_map_eq_ofRoots (embS D τ) w _ hm
      rw [← hXr] at h1
      rw [h1]
      refine congrArg (GlobalTheory.LoopV.ofRoots R) ?_
      funext q'
      simp only [hTdef]
      rw [hrc]

    rw [hXrs]
    simp only [hTdef]
    have hB1 : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ, (B τ)⁻¹ * (B τ * M) = M := fun M => by
      rw [← Matrix.mul_assoc, (hBi τ).1, Matrix.one_mul]
    have hU1 : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ, (Uc τ)⁻¹ * (Uc τ * M) = M := fun M => by
      rw [← Matrix.mul_assoc, (hUci τ).1, Matrix.one_mul]
    have hfin : ∀ P : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ,
        Xm τ * (B τ * (sg * P * sg) * (B τ)⁻¹ * Mr τ) * (B τ * sg * (Uc τ)⁻¹) =
          Uc τ * P * (Uc τ)⁻¹ * (Xm τ * Mr τ * (B τ * sg * (Uc τ)⁻¹)) := fun P => by
      simp only [hXm, Matrix.mul_assoc, hB1, hU1, hss']
    rw [hqrc, Matrix.map_mul, Matrix.map_mul, hUcinv, hMq, hXinv, hfin]

end GlobalTheory.LoopVol

end
