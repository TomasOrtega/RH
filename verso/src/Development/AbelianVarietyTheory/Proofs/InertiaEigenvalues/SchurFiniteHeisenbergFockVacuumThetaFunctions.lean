import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionEqZeroOfMeanSquareZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimensionalThetaFunctionsLevelFockDegree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCartanInvOneOfOnb
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockCoefficientExtremalEqDiscreteSeries
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RieszEigenvectorSesquilinearFunctionSpaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionHeisenbergIrreducibleOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisenbergRealPointFockVacuumPairingScalarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.VacSchurFin

/- English proof (translation)
The claim follows from `GlobalTheory.T.riesz_eigenvector_sesquilinear_function_space`.
-/
theorem fin_riesz_eigen : ∀ (X : Type) (C : Submodule ℂ (X → ℂ)), FiniteDimensional ℂ C →
    ∀ (ip Φ : (X → ℂ) → (X → ℂ) → ℂ),
    (∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → ip (a • f + f') g = star a * ip f g + ip f' g) →
    (∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → ip f (a • g + g') = a * ip f g + ip f g') →
    (∀ f g : X → ℂ, f ∈ C → g ∈ C → ip g f = star (ip f g)) →
    (∀ f : X → ℂ, f ∈ C → f ≠ 0 → 0 < (ip f f).re) →
    (∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → Φ (a • f + f') g = star a * Φ f g + Φ f' g) →
    (∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → Φ f (a • g + g') = a * Φ f g + Φ f g') →
    (∀ f : X → ℂ, f ∈ C → ∃ h : X → ℂ, h ∈ C ∧ ∀ g : X → ℂ, g ∈ C → ip h g = Φ f g) ∧
    (C ≠ ⊥ → ∃ c : ℂ, ∃ e : X → ℂ, e ∈ C ∧ e ≠ 0 ∧ ∀ f : X → ℂ, f ∈ C → Φ f e = c * ip f e) :=
  GlobalTheory.T.riesz_eigenvector_sesquilinear_function_space

/- English proof (translation)
The claim follows from `GlobalTheory.T.thetaFunction_heisenberg_irreducible_orthogonal`.
-/
theorem irr_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
    ∀ h e : WO S T → ℂ, IsThetaFunO ψ S T h → IsThetaFunO ψ S T e →
    (∀ w : WO S T, thetaIP μ 𝓕 h (heisO ψ S T w e) = 0) → h = 0 ∨ e = 0 :=
  GlobalTheory.T.thetaFunction_heisenberg_irreducible_orthogonal

/- English proof (translation)
The claim follows from `GlobalTheory.T.heisenberg_realPoint_fockVacuum_pairing_scalar`.
-/
theorem comp_real : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) →
    IsInfFam θ → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ),
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
    ∀ w : WO S T, w.map (finPart D) = 0 → ∃ κ : ℂ, ∀ h e : WO S T → ℂ, IsThetaFunO ψ S T h → IsThetaFunO ψ S T e →
    (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) h) →
    (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) e) →
    thetaIP μ 𝓕 h (heisO ψ S T w e) = κ * thetaIP μ 𝓕 h e :=
  GlobalTheory.T.heisenberg_realPoint_fockVacuum_pairing_scalar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [heisO, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem heisO_add' (u : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T u (f + g) = heisO ψ S T u f + heisO ψ S T u g := by
  funext x
  simp only [heisO, Pi.add_apply]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [heisO, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem heisO_smul' (u : WO S T) (a : ℂ) (f : WO S T → ℂ) : heisO ψ S T u (a • f) = a • heisO ψ S T u f := by
  funext x
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Introduce `τ z`. Establish `h` using `hf τ z`. Unfold `annih at h ⊢`. Rewrite using `[← GlobalTheory.Hk3.FiniteHeis.heisO_dRho ψ hθ hu, ← GlobalTheory.Hk3.FiniteHeis.heisO_dRho ψ hθ hu, ← heisO_smul', ← heisO_add', h]`. Use function extensionality and compare the values at `x`.

Simplify using `[heisO]`.
-/
theorem vac_heisO_fin (hθ : IsInfFam θ)
    {J : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ}
    {u : WO S T} (hu : u.map (infPart D) = 0) {f : WO S T → ℂ}
    (hf : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (J τ) f) :
    ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (J τ) (heisO ψ S T u f) := by
  intro τ z
  have h := hf τ z
  unfold annih at h ⊢
  rw [← GlobalTheory.Hk3.FiniteHeis.heisO_dRho ψ hθ hu, ← GlobalTheory.Hk3.FiniteHeis.heisO_dRho ψ hθ hu, ← heisO_smul',
    ← heisO_add', h]
  funext x
  simp [heisO]

/- English proof (translation)
Unfold `thetaIP GlobalTheory.Ker.ipO`. Use `congr 1`. Use function extensionality and compare the values at `w`. Rewrite using `[mul_comm]`. Both sides reduce to the same expression.
-/
theorem thetaIP_eq_ipO (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f g : WO S T → ℂ) :
    thetaIP μ 𝓕 f g = GlobalTheory.Ker.ipO μ 𝓕 g f := by
  unfold thetaIP GlobalTheory.Ker.ipO
  congr 1
  funext w
  rw [mul_comm]
  rfl

variable {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

/- English proof (translation)
Rewrite using `[thetaIP_eq_ipO, thetaIP_eq_ipO, GlobalTheory.Size.ipO_heisO hψ hcv.1 hcv.2.1 hb ha]`.
-/
theorem thetaInner_heisenberg (hψ : IsStdChar D ψ (-1)) (hcv : IsCovolOne (ratL T S) μ 𝓕) {a b : WO S T → ℂ}
    (ha : IsThetaFunO ψ S T a) (hb : IsThetaFunO ψ S T b) (w : WO S T) :
    thetaIP μ 𝓕 (heisO ψ S T w a) (heisO ψ S T w b) = thetaIP μ 𝓕 a b := by
  rw [thetaIP_eq_ipO, thetaIP_eq_ipO, GlobalTheory.Size.ipO_heisO hψ hcv.1 hcv.2.1 hb ha]

/- English proof (translation)
Rewrite using `[thetaIP_eq_ipO, thetaIP_eq_ipO, thetaIP_eq_ipO, GlobalTheory.Size.ipO_add_right hψ hcv.1 hcv.2.1 hg (GlobalTheory.WeilVacMove.isTheta_smul a hf) hf', GlobalTheory.Size.ipO_smul_right]`. Both sides reduce to the same expression.
-/
theorem thetaInner_left (hψ : IsStdChar D ψ (-1)) (hcv : IsCovolOne (ratL T S) μ 𝓕) (a : ℂ) {f f' g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') (hg : IsThetaFunO ψ S T g) :
    thetaIP μ 𝓕 (a • f + f') g = star a * thetaIP μ 𝓕 f g + thetaIP μ 𝓕 f' g := by
  rw [thetaIP_eq_ipO, thetaIP_eq_ipO, thetaIP_eq_ipO,
    GlobalTheory.Size.ipO_add_right hψ hcv.1 hcv.2.1 hg (GlobalTheory.WeilVacMove.isTheta_smul a hf) hf', GlobalTheory.Size.ipO_smul_right]
  rfl

/- English proof (translation)
Rewrite using `[thetaIP_eq_ipO, thetaIP_eq_ipO, thetaIP_eq_ipO, GlobalTheory.Size.ipO_add_left hψ hcv.1 hcv.2.1 (GlobalTheory.WeilVacMove.isTheta_smul a hg) hg' hf, GlobalTheory.Size.ipO_smul_left]`.
-/
theorem thetaInner_right (hψ : IsStdChar D ψ (-1)) (hcv : IsCovolOne (ratL T S) μ 𝓕) (a : ℂ) {f g g' : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) (hg' : IsThetaFunO ψ S T g') :
    thetaIP μ 𝓕 f (a • g + g') = a * thetaIP μ 𝓕 f g + thetaIP μ 𝓕 f g' := by
  rw [thetaIP_eq_ipO, thetaIP_eq_ipO, thetaIP_eq_ipO,
    GlobalTheory.Size.ipO_add_left hψ hcv.1 hcv.2.1 (GlobalTheory.WeilVacMove.isTheta_smul a hg) hg' hf, GlobalTheory.Size.ipO_smul_left]

/- English proof (translation)
Unfold `thetaIP`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem thetaInner_smul_right (a : ℂ) (f g : WO S T → ℂ) : thetaIP μ 𝓕 f (a • g) = a * thetaIP μ 𝓕 f g := by
  unfold thetaIP
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Establish `e : thetaIP μ 𝓕 f f = ((∫ w in 𝓕, ‖f w‖ ^ 2 ∂μ : ℝ) : ℂ)`. Unfold `thetaIP`. Rewrite using `[← integral_complex_ofReal]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)` and prove the remaining obligations. Simplify using `only [Complex.ofReal_pow]`.

Conclude with `Complex.conj_mul' (f w)`. Establish `hne` using `GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hψ hf h0 hcv`. Rewrite `hne`, the goal using `[e]`. Rewrite using `[Complex.ofReal_re]`. Establish `hnn : 0 ≤ ∫ w in 𝓕, ‖f w‖ ^ 2 ∂μ` using `integral_nonneg fun w => by positivity`.

Use `lt_of_le_of_ne hnn fun h => hne ?_` and prove the remaining obligations. Rewrite using `[← h, Complex.ofReal_zero]`.
-/
theorem thetaInner_re_pos (hψ : IsStdChar D ψ (-1)) (hcv : IsCovolOne (ratL T S) μ 𝓕) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (h0 : f ≠ 0) : 0 < (thetaIP μ 𝓕 f f).re := by
  have e : thetaIP μ 𝓕 f f = ((∫ w in 𝓕, ‖f w‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    unfold thetaIP
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Complex.ofReal_pow]
    exact Complex.conj_mul' (f w)
  have hne := GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hψ hf h0 hcv
  rw [e] at hne ⊢
  rw [Complex.ofReal_re]
  have hnn : 0 ≤ ∫ w in 𝓕, ‖f w‖ ^ 2 ∂μ := integral_nonneg fun w => by positivity
  refine lt_of_le_of_ne hnn fun h => hne ?_
  rw [← h, Complex.ofReal_zero]

/- English proof (translation)
Establish `h1 : symplO S T (-b) a = -symplO S T b a`. Use `GlobalTheory.SplitScalar.symplO_sub_left S T 0 b a` as an intermediate fact. Rewrite `this` using `[zero_sub, GlobalTheory.SplitScalar.symplO_zero_left, zero_sub]`. Then use the resulting hypothesis. Rewrite using `[GlobalTheory.SplitScalar.symplO_skew S T (-b) a, h1, GlobalTheory.SplitScalar.symplO_skew S T a b, neg_neg]`.
-/
theorem symplO_neg_right' (a b : WO S T) : symplO S T a (-b) = -symplO S T a b := by
  have h1 : symplO S T (-b) a = -symplO S T b a := by
    have := GlobalTheory.SplitScalar.symplO_sub_left S T 0 b a
    rwa [zero_sub, GlobalTheory.SplitScalar.symplO_zero_left, zero_sub] at this
  rw [GlobalTheory.SplitScalar.symplO_skew S T (-b) a, h1, GlobalTheory.SplitScalar.symplO_skew S T a b, neg_neg]

def vacSub (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (U : AddSubgroup (WO S T)) :
    Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f ∧ (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u f = f) ∧
    ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f}
  add_mem' := fun {f g} hf hg => ⟨GlobalTheory.WeilVacMove.isTheta_add hf.1 hg.1,
    fun u hu h0 => by rw [heisO_add', hf.2.1 u hu h0, hg.2.1 u hu h0],
    fun τ z => by rw [GlobalTheory.FockIndep.annih_add hψ hθ τ _ z hf.1 hg.1, hf.2.2 τ z, hg.2.2 τ z, add_zero]⟩
  zero_mem' := ⟨GlobalTheory.WeilVacMove.isTheta_zero, fun u _ _ => funext fun x => by simp [heisO],
    fun τ z => by
      have := GlobalTheory.FockIndep.annih_smul hψ hθ τ (cplxO (sS τ) (sT τ)) z 0
        (GlobalTheory.WeilVacMove.isTheta_zero (ψ := ψ) (S := S) (T := T))
      simpa using this⟩
  smul_mem' := fun a f hf => ⟨GlobalTheory.WeilVacMove.isTheta_smul a hf.1,
    fun u hu h0 => by rw [heisO_smul', hf.2.1 u hu h0],
    fun τ z => by rw [GlobalTheory.FockIndep.annih_smul hψ hθ τ _ z a hf.1, hf.2.2 τ z, smul_zero]⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_vacSub {hψ : IsStdChar D ψ (-1)} {hθ : IsInfFam θ}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {U : AddSubgroup (WO S T)} {f : WO S T → ℂ} :
    f ∈ vacSub hψ hθ sS sT U ↔ IsThetaFunO ψ S T f ∧ (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u f = f) ∧
      ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f := Iff.rfl

/- English proof (translation)
Use `haveI := GlobalTheory.FockLevelDim.finiteDimensional_level_degree D ψ θ S T sS sT hψ hθ hcS hcT U hU 1`. Establish `hle : vacSub hψ hθ sS sT U ≤ Submodule.span ℂ {f : WO S T → ℂ | IsThetaFunO ψ S T f ∧ (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u f = f) ∧ ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), l.length = 1 → l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p. …`. Introduce `f hf`. Use `Submodule.subset_span ?_` and prove the remaining obligations. Take `⟨h1, h2, h3⟩` from `mem_vacSub.1 hf`.

Use `⟨h1, h2, fun l hl => ?_⟩` and prove the remaining obligations. Take `⟨p, rfl⟩` from `List.length_eq_one_iff.1 hl`. Simplify using `using h3 p.1 p.2`. Conclude with `Submodule.finiteDimensional_of_le hle`.
-/
theorem fd_vacSub (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hcS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hcT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (U : AddSubgroup (WO S T)) (hU : IsOpen (U : Set (WO S T))) : FiniteDimensional ℂ (vacSub hψ hθ sS sT U) := by
  haveI := GlobalTheory.FockLevelDim.finiteDimensional_level_degree D ψ θ S T sS sT hψ hθ hcS hcT U hU 1
  have hle : vacSub hψ hθ sS sT U ≤ Submodule.span ℂ {f : WO S T → ℂ | IsThetaFunO ψ S T f ∧
      (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u f = f) ∧
      ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), l.length = 1 →
        l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) f = 0} := by
    intro f hf
    refine Submodule.subset_span ?_
    obtain ⟨h1, h2, h3⟩ := mem_vacSub.1 hf
    refine ⟨h1, h2, fun l hl => ?_⟩
    obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hl
    simpa using h3 p.1 p.2
  exact Submodule.finiteDimensional_of_le hle

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

/- English proof (translation)
Introduce `D ψ θ S T hψ hθ sS sT hcS hcT μ 𝓕 hcv h e hh he vh ve hw`. Use `irr_theta D ψ S T hψ μ 𝓕 hcv h e hh he fun w => ?_` and prove the remaining obligations. Use `set wr : WO S T := w.map fun z => GlobalTheory.SplitScalar.realIdem D * z with hwr`. Use `set wf : WO S T := w - wr with hwf`. Establish `hfin : wf.map (infPart D) = 0`.

Use extensionality with `i j`. Use `show infPart D (w i j - GlobalTheory.SplitScalar.realIdem D * w i j) = 0`. Rewrite using `[RingHom.map_sub, RingHom.map_mul, GlobalTheory.SplitScalar.infPart_realIdem, one_mul, sub_self]`. Establish `hreal : wr.map (finPart D) = 0`. Use extensionality with `i j`.

Use `show finPart D (GlobalTheory.SplitScalar.realIdem D * w i j) = 0`. Rewrite using `[RingHom.map_mul, GlobalTheory.SplitScalar.finPart_realIdem, zero_mul]`. Take `⟨κ, hκ⟩` from `comp_real D ψ θ S T hψ hθ sS sT hcS hcT μ 𝓕 hcv wr hreal`. Establish `laws` using `GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T`. Establish `hs : wr + wf = w` using `by rw [hwf]; abel`.

Establish `e1 : heisO ψ S T wr (heisO ψ S T wf e) = ψ (symplOH S T wr wf) • heisO ψ S T w e`. Rewrite using `[GlobalTheory.SplitScalar.heisO_heisO, hs]`. Establish `e2` using `hκ h (heisO ψ S T wf e) hh (laws.1 wf e he) vh (vac_heisO_fin hθ hfin ve)`. Rewrite `e2` using `[e1, thetaInner_smul_right, hw wf hfin, mul_zero]`. Conclude with `(mul_eq_zero.1 e2).resolve_left (GlobalTheory.ThetaSchurBdd.psi_ne_zero hψ _)`.
-/
theorem irr_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) →
    IsInfFam θ → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ),
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
    ∀ h e : WO S T → ℂ, IsThetaFunO ψ S T h → IsThetaFunO ψ S T e →
    (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) h) →
    (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) e) →
    (∀ w : WO S T, w.map (infPart D) = 0 → thetaIP μ 𝓕 h (heisO ψ S T w e) = 0) → h = 0 ∨ e = 0 := by
  intro D ψ θ S T hψ hθ sS sT hcS hcT μ 𝓕 hcv h e hh he vh ve hw
  refine irr_theta D ψ S T hψ μ 𝓕 hcv h e hh he fun w => ?_
  set wr : WO S T := w.map fun z => GlobalTheory.SplitScalar.realIdem D * z with hwr
  set wf : WO S T := w - wr with hwf
  have hfin : wf.map (infPart D) = 0 := by
    ext i j
    show infPart D (w i j - GlobalTheory.SplitScalar.realIdem D * w i j) = 0
    rw [RingHom.map_sub, RingHom.map_mul, GlobalTheory.SplitScalar.infPart_realIdem, one_mul, sub_self]
  have hreal : wr.map (finPart D) = 0 := by
    ext i j
    show finPart D (GlobalTheory.SplitScalar.realIdem D * w i j) = 0
    rw [RingHom.map_mul, GlobalTheory.SplitScalar.finPart_realIdem, zero_mul]
  obtain ⟨κ, hκ⟩ := comp_real D ψ θ S T hψ hθ sS sT hcS hcT μ 𝓕 hcv wr hreal
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have hs : wr + wf = w := by rw [hwf]; abel
  have e1 : heisO ψ S T wr (heisO ψ S T wf e) = ψ (symplOH S T wr wf) • heisO ψ S T w e := by
    rw [GlobalTheory.SplitScalar.heisO_heisO, hs]
  have e2 := hκ h (heisO ψ S T wf e) hh (laws.1 wf e he) vh (vac_heisO_fin hθ hfin ve)
  rw [e1, thetaInner_smul_right, hw wf hfin, mul_zero] at e2
  exact (mul_eq_zero.1 e2).resolve_left (GlobalTheory.ThetaSchurBdd.psi_ne_zero hψ _)

end GlobalTheory.VacSchurFin

namespace GlobalTheory.VacSchurFin

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {μ : Measure (WO S T)}
  {𝓕 : Set (WO S T)}

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Use `haveI := fd_vacSub hψ hθ sS sT hcS hcT U hU`. Use `set C := vacSub hψ hθ sS sT U with hC`. Establish `ipl : ∀ (a : ℂ) (f f' g : WO S T → ℂ), f ∈ C → f' ∈ C → g ∈ C → thetaIP μ 𝓕 (a • f + f') g = star a * thetaIP μ 𝓕 f g + thetaIP μ 𝓕 f' g` using `fun a f f' g hf hf' hg => thetaInner_left hψ hcv a (mem_vacSub.1 hf).1 (mem_vacSub.1 hf').1 (mem_vacSub.1 hg).1`. Establish `ipr : ∀ (a : ℂ) (f g g' : WO S T → ℂ), f ∈ C → g ∈ C → g' ∈ C → thetaIP μ 𝓕 f (a • g + g') = a * thetaIP μ 𝓕 f g + thetaIP μ 𝓕 f g'` using `fun a f g g' hf hg hg' => thetaInner_right hψ hcv a (mem_vacSub.1 hf).1 (mem_vacSub.1 hg).1 (mem_vacSub.1 hg').1`. Establish `ips : ∀ f g : WO S T → ℂ, f ∈ C → g ∈ C → thetaIP μ 𝓕 g f = star (thetaIP μ 𝓕 f g)` using `fun f g _ _ => (GlobalTheory.RawLift.FockCoef.thetaInner_star f g).symm`.

Establish `ipp : ∀ f : WO S T → ℂ, f ∈ C → f ≠ 0 → 0 < (thetaIP μ 𝓕 f f).re` using `fun f hf h0 => thetaInner_re_pos hψ hcv (mem_vacSub.1 hf).1 h0`. Establish `Φl : ∀ (a : ℂ) (f f' g : WO S T → ℂ), f ∈ C → f' ∈ C → g ∈ C → Φ (a • f + f') g = star a * Φ f g + Φ f' g` using `fun a f f' g hf hf' hg => hl a f f' g (mem_vacSub.1 hf).1 (mem_vacSub.1 hf').1 (mem_vacSub.1 hg).1 (mem_vacSub.1 hf).2.2 (mem_vacSub.1 hf').2.2 (mem_vacSub.1 hg).2.2`. Establish `Φr : ∀ (a : ℂ) (f g g' : WO S T → ℂ), f ∈ C → g ∈ C → g' ∈ C → Φ f (a • g + g') = a * Φ f g + Φ f g'` using `fun a f g g' hf hg hg' => hr a f g g' (mem_vacSub.1 hf).1 (mem_vacSub.1 hg).1 (mem_vacSub.1 hg').1 (mem_vacSub.1 hf).2.2 (mem_vacSub.1 hg).2.2 (mem_vacSub.1 hg').2.2`. Establish `hCne : C ≠ ⊥` using `fun h => hne ((Submodule.mem_bot ℂ).1 (h ▸ h₀))`. Take `⟨c, e, heC, he0, hce⟩` from `(fin_riesz_eigen (WO S T) C inferInstance (thetaIP μ 𝓕) Φ ipl ipr ips ipp Φl Φr).2 hCne`.

Use `set Ψ : (WO S T → ℂ) → (WO S T → ℂ) → ℂ := fun f g => Φ f g - c * thetaIP μ 𝓕 f g with hΨ`. Establish `Ψl : ∀ (a : ℂ) (f f' g : WO S T → ℂ), f ∈ C → f' ∈ C → g ∈ C → Ψ (a • f + f') g = star a * Ψ f g + Ψ f' g` using `fun a f f' g hf hf' hg => by`. Simplify using `only [hΨ]`. Rewrite using `[Φl a f f' g hf hf' hg, ipl a f f' g hf hf' hg]`. Expand and normalize the polynomial expressions, which then agree.

Establish `Ψr : ∀ (a : ℂ) (f g g' : WO S T → ℂ), f ∈ C → g ∈ C → g' ∈ C → Ψ f (a • g + g') = a * Ψ f g + Ψ f g'` using `fun a f g g' hf hg hg' => by`. Simplify using `only [hΨ]`. Rewrite using `[Φr a f g g' hf hg hg', ipr a f g g' hf hg hg']`. Expand and normalize the polynomial expressions, which then agree. Establish `hR` using `(fin_riesz_eigen (WO S T) C inferInstance (thetaIP μ 𝓕) Ψ ipl ipr ips ipp Ψl Ψr).1`.

Take `⟨heT, heL, heV⟩` from `mem_vacSub.1 heC`. Establish `laws` using `GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T`. Establish `key : ∀ f g : WO S T → ℂ, f ∈ C → g ∈ C → Ψ f g = 0`. Introduce `f g hf hg`. Take `⟨hfT, hfL, hfV⟩` from `mem_vacSub.1 hf`.

Take `⟨h, hhC, hh⟩` from `hR f hf`. Take `⟨hhT, hhL, hhV⟩` from `mem_vacSub.1 hhC`. It suffices to establish `h0 : h = 0 by`. Rewrite using `[← hh g hg, h0]`. Simplify using `[thetaIP]`.

Use `(irr_vac D ψ θ S T hψ hθ sS sT hcS hcT μ 𝓕 hcv h e hhT heT hhV heV fun w hw => ?_).resolve_right he0` and prove the remaining obligations. Establish `hwe : IsThetaFunO ψ S T (heisO ψ S T w e)` using `laws.1 w e heT`. Distinguish the cases in `hA : ∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO S T u w) = 1`. Establish `hwC : heisO ψ S T w e ∈ C` using `mem_vacSub.2 ⟨hwe, fun u hu h0 => by`. Rewrite using `[GlobalTheory.SplitScalar.heisO_comm, hA u hu h0, one_smul, heL u hu h0], vac_heisO_fin hθ hw heV⟩`.

Rewrite using `[hh _ hwC]`. Establish `hnw : (-w).map (infPart D) = 0`. Use extensionality with `i j`. Establish `h1 : infPart D (w i j) = 0` using `congrFun (congrFun hw i) j`. Use `show infPart D (-(w i j)) = 0`.

Rewrite using `[RingHom.map_neg, h1, neg_zero]`. Establish `hfC : heisO ψ S T (-w) f ∈ C` using `mem_vacSub.2 ⟨laws.1 _ f hfT, fun u hu h0 => by`. Rewrite using `[GlobalTheory.SplitScalar.heisO_comm, hfL u hu h0, symplO_neg_right', AddChar.map_neg_eq_inv, hA u hu h0, inv_one, one_smul], vac_heisO_fin hθ hnw hfV⟩`. Take `⟨hfT', -, hfV'⟩` from `mem_vacSub.1 hfC`. Establish `e1 : heisO ψ S T w (heisO ψ S T (-w) f) = ψ (symplOH S T w (-w)) • f`.

Rewrite using `[GlobalTheory.SplitScalar.heisO_heisO, add_neg_cancel, GlobalTheory.SplitScalar.heisO_zero]`. Establish `e2 : Ψ (heisO ψ S T w (heisO ψ S T (-w) f)) (heisO ψ S T w e) = 0`. Simplify using `only [hΨ]`. Rewrite using `[hi w hw _ e hfT' heT hfV' heV, thetaInner_heisenberg hψ hcv hfT' heT, hce _ hfC, sub_self]`. Establish `z` using `Ψl 1 0 0 (heisO ψ S T w e) C.zero_mem C.zero_mem hwC`.

Simplify using `only [smul_zero, add_zero, star_one, one_mul] at z`. Establish `z0 : Ψ 0 (heisO ψ S T w e) = 0` using `by linear_combination -z`. Establish `e3` using `Ψl (ψ (symplOH S T w (-w))) f 0 (heisO ψ S T w e) hf C.zero_mem hwC`. Rewrite `e3` using `[add_zero, z0, add_zero, ← e1, e2]`. Conclude with `(mul_eq_zero.1 e3.symm).resolve_left (star_ne_zero.2 (GlobalTheory.ThetaSchurBdd.psi_ne_zero hψ _))`.

Use `push_neg at hA`. Take `⟨u, hu, h0, hne1⟩` from `hA`. Establish `e1 : thetaIP μ 𝓕 h (heisO ψ S T w e) = thetaIP μ 𝓕 (heisO ψ S T u h) (heisO ψ S T u (heisO ψ S T w e))` using `(thetaInner_heisenberg hψ hcv hhT hwe u).symm`. Rewrite `e1` using `[hhL u hu h0, GlobalTheory.SplitScalar.heisO_comm, heL u hu h0, thetaInner_smul_right]`. Establish `: (1 - ψ (symplO S T u w)) * thetaIP μ 𝓕 h (heisO ψ S T w e) = 0` using `by linear_combination e1`.

Conclude with `(mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hne1))`. Establish `hΦC : ∀ f g : WO S T → ℂ, f ∈ C → g ∈ C → Φ f g = c * thetaIP μ 𝓕 f g` using `fun f g hf hg => sub_eq_zero.1 (key f g hf hg)`. Establish `hc : Φ f₀ f₀ / thetaIP μ 𝓕 f₀ f₀ = c`. Rewrite using `[hΦC f₀ f₀ h₀ h₀, mul_div_assoc, div_self (GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hψ (mem_vacSub.1 h₀).1 hne hcv), mul_one]`. Rewrite using `[hc]`.

Conclude with `hΦC f g hf hg`.
-/
theorem lev (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hcS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hcT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (hcv : IsCovolOne (ratL T S) μ 𝓕) (Φ : (WO S T → ℂ) → (WO S T → ℂ) → ℂ)
    (hl : ∀ (a : ℂ) (f f' g : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → IsThetaFunO ψ S T g →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f') →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → Φ (a • f + f') g = star a * Φ f g + Φ f' g)
    (hr : ∀ (a : ℂ) (f g g' : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g') → Φ f (a • g + g') = a * Φ f g + Φ f g')
    (hi : ∀ w : WO S T, w.map (infPart D) = 0 → ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) →
      Φ (heisO ψ S T w f) (heisO ψ S T w g) = Φ f g)
    (U : AddSubgroup (WO S T)) (hU : IsOpen (U : Set (WO S T))) {f₀ : WO S T → ℂ}
    (h₀ : f₀ ∈ vacSub hψ hθ sS sT U) (hne : f₀ ≠ 0) (f g : WO S T → ℂ) (hf : f ∈ vacSub hψ hθ sS sT U)
    (hg : g ∈ vacSub hψ hθ sS sT U) : Φ f g = Φ f₀ f₀ / thetaIP μ 𝓕 f₀ f₀ * thetaIP μ 𝓕 f g := by
  haveI := fd_vacSub hψ hθ sS sT hcS hcT U hU
  set C := vacSub hψ hθ sS sT U with hC
  have ipl : ∀ (a : ℂ) (f f' g : WO S T → ℂ), f ∈ C → f' ∈ C → g ∈ C →
      thetaIP μ 𝓕 (a • f + f') g = star a * thetaIP μ 𝓕 f g + thetaIP μ 𝓕 f' g :=
    fun a f f' g hf hf' hg => thetaInner_left hψ hcv a (mem_vacSub.1 hf).1 (mem_vacSub.1 hf').1 (mem_vacSub.1 hg).1
  have ipr : ∀ (a : ℂ) (f g g' : WO S T → ℂ), f ∈ C → g ∈ C → g' ∈ C →
      thetaIP μ 𝓕 f (a • g + g') = a * thetaIP μ 𝓕 f g + thetaIP μ 𝓕 f g' :=
    fun a f g g' hf hg hg' => thetaInner_right hψ hcv a (mem_vacSub.1 hf).1 (mem_vacSub.1 hg).1 (mem_vacSub.1 hg').1
  have ips : ∀ f g : WO S T → ℂ, f ∈ C → g ∈ C → thetaIP μ 𝓕 g f = star (thetaIP μ 𝓕 f g) :=
    fun f g _ _ => (GlobalTheory.RawLift.FockCoef.thetaInner_star f g).symm
  have ipp : ∀ f : WO S T → ℂ, f ∈ C → f ≠ 0 → 0 < (thetaIP μ 𝓕 f f).re :=
    fun f hf h0 => thetaInner_re_pos hψ hcv (mem_vacSub.1 hf).1 h0
  have Φl : ∀ (a : ℂ) (f f' g : WO S T → ℂ), f ∈ C → f' ∈ C → g ∈ C → Φ (a • f + f') g = star a * Φ f g + Φ f' g :=
    fun a f f' g hf hf' hg => hl a f f' g (mem_vacSub.1 hf).1 (mem_vacSub.1 hf').1 (mem_vacSub.1 hg).1
      (mem_vacSub.1 hf).2.2 (mem_vacSub.1 hf').2.2 (mem_vacSub.1 hg).2.2
  have Φr : ∀ (a : ℂ) (f g g' : WO S T → ℂ), f ∈ C → g ∈ C → g' ∈ C → Φ f (a • g + g') = a * Φ f g + Φ f g' :=
    fun a f g g' hf hg hg' => hr a f g g' (mem_vacSub.1 hf).1 (mem_vacSub.1 hg).1 (mem_vacSub.1 hg').1
      (mem_vacSub.1 hf).2.2 (mem_vacSub.1 hg).2.2 (mem_vacSub.1 hg').2.2
  have hCne : C ≠ ⊥ := fun h => hne ((Submodule.mem_bot ℂ).1 (h ▸ h₀))
  obtain ⟨c, e, heC, he0, hce⟩ :=
    (fin_riesz_eigen (WO S T) C inferInstance (thetaIP μ 𝓕) Φ ipl ipr ips ipp Φl Φr).2 hCne
  set Ψ : (WO S T → ℂ) → (WO S T → ℂ) → ℂ := fun f g => Φ f g - c * thetaIP μ 𝓕 f g with hΨ
  have Ψl : ∀ (a : ℂ) (f f' g : WO S T → ℂ), f ∈ C → f' ∈ C → g ∈ C → Ψ (a • f + f') g = star a * Ψ f g + Ψ f' g :=
    fun a f f' g hf hf' hg => by
      simp only [hΨ]
      rw [Φl a f f' g hf hf' hg, ipl a f f' g hf hf' hg]
      ring
  have Ψr : ∀ (a : ℂ) (f g g' : WO S T → ℂ), f ∈ C → g ∈ C → g' ∈ C → Ψ f (a • g + g') = a * Ψ f g + Ψ f g' :=
    fun a f g g' hf hg hg' => by
      simp only [hΨ]
      rw [Φr a f g g' hf hg hg', ipr a f g g' hf hg hg']
      ring
  have hR := (fin_riesz_eigen (WO S T) C inferInstance (thetaIP μ 𝓕) Ψ ipl ipr ips ipp Ψl Ψr).1
  obtain ⟨heT, heL, heV⟩ := mem_vacSub.1 heC
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have key : ∀ f g : WO S T → ℂ, f ∈ C → g ∈ C → Ψ f g = 0 := by
    intro f g hf hg
    obtain ⟨hfT, hfL, hfV⟩ := mem_vacSub.1 hf
    obtain ⟨h, hhC, hh⟩ := hR f hf
    obtain ⟨hhT, hhL, hhV⟩ := mem_vacSub.1 hhC
    suffices h0 : h = 0 by
      rw [← hh g hg, h0]
      simp [thetaIP]
    refine (irr_vac D ψ θ S T hψ hθ sS sT hcS hcT μ 𝓕 hcv h e hhT heT hhV heV fun w hw => ?_).resolve_right he0
    have hwe : IsThetaFunO ψ S T (heisO ψ S T w e) := laws.1 w e heT
    by_cases hA : ∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO S T u w) = 1
    · have hwC : heisO ψ S T w e ∈ C := mem_vacSub.2 ⟨hwe, fun u hu h0 => by
          rw [GlobalTheory.SplitScalar.heisO_comm, hA u hu h0, one_smul, heL u hu h0], vac_heisO_fin hθ hw heV⟩
      rw [hh _ hwC]
      have hnw : (-w).map (infPart D) = 0 := by
        ext i j
        have h1 : infPart D (w i j) = 0 := congrFun (congrFun hw i) j
        show infPart D (-(w i j)) = 0
        rw [RingHom.map_neg, h1, neg_zero]
      have hfC : heisO ψ S T (-w) f ∈ C := mem_vacSub.2 ⟨laws.1 _ f hfT, fun u hu h0 => by
          rw [GlobalTheory.SplitScalar.heisO_comm, hfL u hu h0, symplO_neg_right', AddChar.map_neg_eq_inv, hA u hu h0, inv_one,
            one_smul], vac_heisO_fin hθ hnw hfV⟩
      obtain ⟨hfT', -, hfV'⟩ := mem_vacSub.1 hfC
      have e1 : heisO ψ S T w (heisO ψ S T (-w) f) = ψ (symplOH S T w (-w)) • f := by
        rw [GlobalTheory.SplitScalar.heisO_heisO, add_neg_cancel, GlobalTheory.SplitScalar.heisO_zero]
      have e2 : Ψ (heisO ψ S T w (heisO ψ S T (-w) f)) (heisO ψ S T w e) = 0 := by
        simp only [hΨ]
        rw [hi w hw _ e hfT' heT hfV' heV, thetaInner_heisenberg hψ hcv hfT' heT, hce _ hfC, sub_self]
      have z := Ψl 1 0 0 (heisO ψ S T w e) C.zero_mem C.zero_mem hwC
      simp only [smul_zero, add_zero, star_one, one_mul] at z
      have z0 : Ψ 0 (heisO ψ S T w e) = 0 := by linear_combination -z
      have e3 := Ψl (ψ (symplOH S T w (-w))) f 0 (heisO ψ S T w e) hf C.zero_mem hwC
      rw [add_zero, z0, add_zero, ← e1, e2] at e3
      exact (mul_eq_zero.1 e3.symm).resolve_left (star_ne_zero.2 (GlobalTheory.ThetaSchurBdd.psi_ne_zero hψ _))
    · push_neg at hA
      obtain ⟨u, hu, h0, hne1⟩ := hA
      have e1 : thetaIP μ 𝓕 h (heisO ψ S T w e) =
          thetaIP μ 𝓕 (heisO ψ S T u h) (heisO ψ S T u (heisO ψ S T w e)) :=
        (thetaInner_heisenberg hψ hcv hhT hwe u).symm
      rw [hhL u hu h0, GlobalTheory.SplitScalar.heisO_comm, heL u hu h0, thetaInner_smul_right] at e1
      have : (1 - ψ (symplO S T u w)) * thetaIP μ 𝓕 h (heisO ψ S T w e) = 0 := by linear_combination e1
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hne1))
  have hΦC : ∀ f g : WO S T → ℂ, f ∈ C → g ∈ C → Φ f g = c * thetaIP μ 𝓕 f g :=
    fun f g hf hg => sub_eq_zero.1 (key f g hf hg)
  have hc : Φ f₀ f₀ / thetaIP μ 𝓕 f₀ f₀ = c := by
    rw [hΦC f₀ f₀ h₀ h₀, mul_div_assoc,
      div_self (GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hψ (mem_vacSub.1 h₀).1 hne hcv), mul_one]
  rw [hc]
  exact hΦC f g hf hg

end GlobalTheory.VacSchurFin

/- English proof (translation)
Introduce `D ψ θ S T hψ hθ sS sT hcS hcT μ 𝓕 hcv Φ hl hr _ hi`. Distinguish the cases in `hV : ∃ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ ∧ (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f₀) ∧ f₀ ≠ 0`. Take `⟨f₀, h0t, h0v, h0ne⟩` from `hV`. Use `⟨Φ f₀ f₀ / thetaIP μ 𝓕 f₀ f₀, fun f g hf hg vf vg => ?_⟩` and prove the remaining obligations. Take `⟨U₀, o₀, l₀⟩` from `h0t.level`.

Take `⟨U₁, o₁, l₁⟩` from `hf.level`. Take `⟨U₂, o₂, l₂⟩` from `hg.level`. Establish `hU : IsOpen ((U₀ ⊓ U₁ ⊓ U₂ : AddSubgroup (WO S T)) : Set (WO S T))`. Rewrite using `[AddSubgroup.coe_inf, AddSubgroup.coe_inf]`. Conclude with `(o₀.inter o₁).inter o₂`.

Establish `m : ∀ {u : WO S T}, u ∈ U₀ ⊓ U₁ ⊓ U₂ → u ∈ U₀ ∧ u ∈ U₁ ∧ u ∈ U₂` using `fun hu => ⟨(AddSubgroup.mem_inf.1 (AddSubgroup.mem_inf.1 hu).1).1, (AddSubgroup.mem_inf.1 (AddSubgroup.mem_inf.1 hu).1).2, (AddSubgroup.mem_inf.1 hu).2⟩`. Conclude with `GlobalTheory.VacSchurFin.lev hψ hθ sS sT hcS hcT hcv Φ hl hr hi (U₀ ⊓ U₁ ⊓ U₂) hU (GlobalTheory.VacSchurFin.mem_vacSub.2 ⟨h0t, fun u hu h => l₀ u (m hu).1 h, h0v⟩) h0ne f g (GlobalTheory.VacSchurFin.mem_vacSub.2 ⟨hf, fun u hu h => l₁ u (m hu).2.1 h, vf⟩) (GlobalTheory.VacSchurFin …`. Use `push_neg at hV`. Use `⟨0, fun f g hf hg vf vg => ?_⟩` and prove the remaining obligations. Establish `hf0 : f = 0` using `hV f hf vf`.

Substitute `hf0` using the available equality. Establish `z` using `hl 1 0 0 g hf hf hg vf vf vg`. Simplify using `only [smul_zero, add_zero, star_one, one_mul] at z`. Rewrite using `[zero_mul]`. Take the linear combination `-z`.
-/
theorem GlobalTheory.VacSchurFin.vacSchur : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ Φ : (WO S T → ℂ) → (WO S T → ℂ) → ℂ, (∀ (a : ℂ) (f f' g : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f') → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → Φ (a • f + f') g = star a * Φ f g + Φ f' g) → (∀ (a : ℂ) (f g g' : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g') → Φ f (a • g + g') = a * Φ f g + Φ f g') → (∃ C : ℝ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → ‖Φ f g‖ ^ 2 ≤ C * (nrm2 μ 𝓕 f * nrm2 μ 𝓕 g)) → (∀ w : WO S T, w.map (infPart D) = 0 → ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → Φ (heisO ψ S T w f) (heisO ψ S T w g) = Φ f g) → ∃ c : ℂ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → Φ f g = c * thetaIP μ 𝓕 f g := by
  intro D ψ θ S T hψ hθ sS sT hcS hcT μ 𝓕 hcv Φ hl hr _ hi
  by_cases hV : ∃ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ ∧
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f₀) ∧ f₀ ≠ 0
  · obtain ⟨f₀, h0t, h0v, h0ne⟩ := hV
    refine ⟨Φ f₀ f₀ / thetaIP μ 𝓕 f₀ f₀, fun f g hf hg vf vg => ?_⟩
    obtain ⟨U₀, o₀, l₀⟩ := h0t.level
    obtain ⟨U₁, o₁, l₁⟩ := hf.level
    obtain ⟨U₂, o₂, l₂⟩ := hg.level
    have hU : IsOpen ((U₀ ⊓ U₁ ⊓ U₂ : AddSubgroup (WO S T)) : Set (WO S T)) := by
      rw [AddSubgroup.coe_inf, AddSubgroup.coe_inf]
      exact (o₀.inter o₁).inter o₂
    have m : ∀ {u : WO S T}, u ∈ U₀ ⊓ U₁ ⊓ U₂ → u ∈ U₀ ∧ u ∈ U₁ ∧ u ∈ U₂ := fun hu =>
      ⟨(AddSubgroup.mem_inf.1 (AddSubgroup.mem_inf.1 hu).1).1, (AddSubgroup.mem_inf.1 (AddSubgroup.mem_inf.1 hu).1).2,
        (AddSubgroup.mem_inf.1 hu).2⟩
    exact GlobalTheory.VacSchurFin.lev hψ hθ sS sT hcS hcT hcv Φ hl hr hi (U₀ ⊓ U₁ ⊓ U₂) hU
      (GlobalTheory.VacSchurFin.mem_vacSub.2 ⟨h0t, fun u hu h => l₀ u (m hu).1 h, h0v⟩) h0ne f g
      (GlobalTheory.VacSchurFin.mem_vacSub.2 ⟨hf, fun u hu h => l₁ u (m hu).2.1 h, vf⟩)
      (GlobalTheory.VacSchurFin.mem_vacSub.2 ⟨hg, fun u hu h => l₂ u (m hu).2.2 h, vg⟩)
  · push_neg at hV
    refine ⟨0, fun f g hf hg vf vg => ?_⟩
    have hf0 : f = 0 := hV f hf vf
    subst hf0
    have z := hl 1 0 0 g hf hf hg vf vf vg
    simp only [smul_zero, add_zero, star_one, one_mul] at z
    rw [zero_mul]
    linear_combination -z
