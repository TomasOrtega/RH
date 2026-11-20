import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFiniteHeisenbergFockVacuumThetaFunctions
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelAlgebraicExpansion
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.AlgPair

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

/- English proof (translation)
Rewrite `ha`, the goal using `[mem_algebraicClosure_iff]`. Conclude with `ha.algHom ((Complex.conjAe.restrictScalars ℚ).toAlgHom)`.
-/
theorem alg_star {a : ℂ} (ha : a ∈ algebraicClosure ℚ ℂ) : star a ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff] at ha ⊢
  exact ha.algHom ((Complex.conjAe.restrictScalars ℚ).toAlgHom)

/- English proof (translation)
Use extensionality with `i j`. Establish `h` using `congrFun (congrFun hx i) j`. Simplify using `only [Matrix.map_apply, Matrix.neg_apply, Matrix.zero_apply] at h ⊢`. Rewrite using `[RingHom.map_neg, h, neg_zero]`.
-/
theorem fin_neg {x : WO S T} (hx : x.map (infPart D) = 0) : (-x).map (infPart D) = 0 := by
  ext i j
  have h := congrFun (congrFun hx i) j
  simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.zero_apply] at h ⊢
  rw [RingHom.map_neg, h, neg_zero]

/- English proof (translation)
Use extensionality with `i j`. Establish `h` using `congrFun (congrFun hx i) j`. Establish `h'` using `congrFun (congrFun hy i) j`. Simplify using `only [Matrix.map_apply, Matrix.add_apply, Matrix.zero_apply] at h h' ⊢`. Rewrite using `[RingHom.map_add, h, h', add_zero]`.
-/
theorem fin_add {x y : WO S T} (hx : x.map (infPart D) = 0) (hy : y.map (infPart D) = 0) :
    (x + y).map (infPart D) = 0 := by
  ext i j
  have h := congrFun (congrFun hx i) j
  have h' := congrFun (congrFun hy i) j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.zero_apply] at h h' ⊢
  rw [RingHom.map_add, h, h', add_zero]

variable {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

/- English proof (translation)
Establish `h` using `GlobalTheory.RawLift.thetaInner_smul_left μ 𝓕 0 0 G`. Simplify using `using h`.
-/
theorem thetaInner_zero_left (G : WO S T → ℂ) : GlobalTheory.RawLift.thetaIP μ 𝓕 0 G = 0 := by
  have h := GlobalTheory.RawLift.thetaInner_smul_left μ 𝓕 0 0 G
  simpa using h

/- English proof (translation)
Establish `h` using `GlobalTheory.RawLift.thetaInner_smul_right μ 𝓕 0 G 0`. Simplify using `using h`.
-/
theorem thetaInner_zero_right (G : WO S T → ℂ) : GlobalTheory.RawLift.thetaIP μ 𝓕 G 0 = 0 := by
  have h := GlobalTheory.RawLift.thetaInner_smul_right μ 𝓕 0 G 0
  simpa using h

/- English proof (translation)
The claim follows from `| 0, c, g, _ => by simp only [Finset.univ_eq_empty, Finset.sum_empty] exact ⟨GlobalTheory.WeilVacMove.isTheta_zero, thetaInner_zero_left G⟩ | n + 1, c, g, hg => by obtain ⟨ht, he⟩ := sum_left hψ hcv hG (fun p => c p.succ) (fun p => g p.succ) fun p => hg _ rw [Fin.sum_univ_succ, F …`.
-/
theorem sum_left (hψ : IsStdChar D ψ (-1)) (hcv : IsCovolOne (ratL T S) μ 𝓕) {G : WO S T → ℂ}
    (hG : IsThetaFunO ψ S T G) : ∀ {n : ℕ} (c : Fin n → ℂ) (g : Fin n → WO S T → ℂ), (∀ p, IsThetaFunO ψ S T (g p)) →
    IsThetaFunO ψ S T (∑ p, c p • g p) ∧
      GlobalTheory.RawLift.thetaIP μ 𝓕 (∑ p, c p • g p) G = ∑ p, star (c p) * GlobalTheory.RawLift.thetaIP μ 𝓕 (g p) G
  | 0, c, g, _ => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_zero, thetaInner_zero_left G⟩
  | n + 1, c, g, hg => by
    obtain ⟨ht, he⟩ := sum_left hψ hcv hG (fun p => c p.succ) (fun p => g p.succ) fun p => hg _
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_add (GlobalTheory.WeilVacMove.isTheta_smul _ (hg 0)) ht,
      by rw [GlobalTheory.VacSchurFin.thetaInner_left hψ hcv _ (hg 0) ht hG, he]⟩

/- English proof (translation)
The claim follows from `| 0, c, g, _ => by simp only [Finset.univ_eq_empty, Finset.sum_empty] exact ⟨GlobalTheory.WeilVacMove.isTheta_zero, thetaInner_zero_right f⟩ | n + 1, c, g, hg => by obtain ⟨ht, he⟩ := sum_right hψ hcv hf (fun p => c p.succ) (fun p => g p.succ) fun p => hg _ rw [Fin.sum_univ_succ, …`.
-/
theorem sum_right (hψ : IsStdChar D ψ (-1)) (hcv : IsCovolOne (ratL T S) μ 𝓕) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : ∀ {n : ℕ} (c : Fin n → ℂ) (g : Fin n → WO S T → ℂ), (∀ p, IsThetaFunO ψ S T (g p)) →
    IsThetaFunO ψ S T (∑ p, c p • g p) ∧
      GlobalTheory.RawLift.thetaIP μ 𝓕 f (∑ p, c p • g p) = ∑ p, c p * GlobalTheory.RawLift.thetaIP μ 𝓕 f (g p)
  | 0, c, g, _ => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_zero, thetaInner_zero_right f⟩
  | n + 1, c, g, hg => by
    obtain ⟨ht, he⟩ := sum_right hψ hcv hf (fun p => c p.succ) (fun p => g p.succ) fun p => hg _
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_add (GlobalTheory.WeilVacMove.isTheta_smul _ (hg 0)) ht,
      by rw [GlobalTheory.VacSchurFin.thetaInner_right hψ hcv _ hf (hg 0) ht, he]⟩

variable {θ : InfFam D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
  {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {v : WO S T → ℂ}

/- English proof (translation)
Establish `hψ : IsStdChar D ψ (-1)` using `hv.1`. Establish `hvt : IsThetaFunO ψ S T v` using `hv.2.theta`. Establish `hlat` using `hv.2.lat`. Establish `laws` using `GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T`. Take `⟨h1, -, h3⟩` from `GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT`.

Distinguish the cases in `hmem : u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)`. Take `⟨ε, hε, hεv⟩` from `h3 v hlat u hmem`. Establish `hself : GlobalTheory.RawLift.thetaIP μ 𝓕 v v = 1`. Rewrite using `[GlobalTheory.RawLift.thetaInner_self]`. Establish `hn` using `hv.2.norm.2 (μ, 𝓕) hcv`.

Simplify using `only [nrm2] at hn`. Rewrite using `[hn, Complex.ofReal_one]`. Rewrite using `[hεv v hlat, GlobalTheory.RawLift.thetaInner_smul_right, hself, mul_one]`. Break down `hε with rfl | rfl` into its components or cases. Conclude with `one_mem _`.

Conclude with `neg_mem (one_mem _)`. Establish `hne : ∃ u' ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), ψ (symplO S T u u') ≠ 1`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hmem ((h1 u hu).2 hcon)`.

Take `⟨u', hu', hψu⟩` from `hne`. Take `⟨ε, hε, hεv⟩` from `h3 v hlat u' hu'`. Establish `hεv'` using `hεv v hlat`. Establish `comm` using `GlobalTheory.SplitScalar.heisO_comm ψ S T u u' v`. Rewrite `comm` using `[hεv', GlobalTheory.VacSchurFin.heisO_smul']`.

Establish `inv` using `GlobalTheory.VacSchurFin.thetaInner_heisenberg hψ hcv hvt (laws.1 u v hvt) u'`. Rewrite `inv` using `[hεv']`. Establish `hεε : star ε * ε = 1`. Apply the tactic sequence `rcases hε with h | h <;> rw [h] <;> simp only [star_one, star_neg, one_mul, neg_mul_neg]`. Establish `hfix : ψ (symplO S T u u') * GlobalTheory.RawLift.thetaIP μ 𝓕 v (heisO ψ S T u v) = GlobalTheory.RawLift.thetaIP μ 𝓕 v (heisO ψ S T u v)` using `by conv_lhs => rw [← inv, ← GlobalTheory.RawLift.thetaInner_smul_right, ← comm, GlobalTheory.RawLift.thetaInner_smul_left, GlobalTheory.RawLift.thetaInner_smul_right, ← mul_assoc, hεε, one_mul]`.

Establish `h0 : (ψ (symplO S T u u') - 1) * GlobalTheory.RawLift.thetaIP μ 𝓕 v (heisO ψ S T u v) = 0`. Rewrite using `[sub_mul, hfix, one_mul, sub_self]`. Rewrite using `[(mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hψu)]`. Conclude with `zero_mem _`.
-/
theorem vac_translate (hv : IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v)
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hcv : IsCovolOne (ratL T S) μ 𝓕) {u : WO S T}
    (hu : u.map (infPart D) = 0) : GlobalTheory.RawLift.thetaIP μ 𝓕 v (heisO ψ S T u v) ∈ algebraicClosure ℚ ℂ := by
  have hψ : IsStdChar D ψ (-1) := hv.1
  have hvt : IsThetaFunO ψ S T v := hv.2.theta
  have hlat := hv.2.lat
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  obtain ⟨h1, -, h3⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  by_cases hmem : u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
  · obtain ⟨ε, hε, hεv⟩ := h3 v hlat u hmem
    have hself : GlobalTheory.RawLift.thetaIP μ 𝓕 v v = 1 := by
      rw [GlobalTheory.RawLift.thetaInner_self]
      have hn := hv.2.norm.2 (μ, 𝓕) hcv
      simp only [nrm2] at hn
      rw [hn, Complex.ofReal_one]
    rw [hεv v hlat, GlobalTheory.RawLift.thetaInner_smul_right, hself, mul_one]
    rcases hε with rfl | rfl
    · exact one_mem _
    · exact neg_mem (one_mem _)
  · have hne : ∃ u' ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        ψ (symplO S T u u') ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hmem ((h1 u hu).2 hcon)
    obtain ⟨u', hu', hψu⟩ := hne
    obtain ⟨ε, hε, hεv⟩ := h3 v hlat u' hu'
    have hεv' := hεv v hlat
    have comm := GlobalTheory.SplitScalar.heisO_comm ψ S T u u' v
    rw [hεv', GlobalTheory.VacSchurFin.heisO_smul'] at comm
    have inv := GlobalTheory.VacSchurFin.thetaInner_heisenberg hψ hcv hvt (laws.1 u v hvt) u'
    rw [hεv'] at inv
    have hεε : star ε * ε = 1 := by
      rcases hε with h | h <;> rw [h] <;> simp only [star_one, star_neg, one_mul, neg_mul_neg]
    have hfix : ψ (symplO S T u u') * GlobalTheory.RawLift.thetaIP μ 𝓕 v (heisO ψ S T u v) =
        GlobalTheory.RawLift.thetaIP μ 𝓕 v (heisO ψ S T u v) := by
      conv_lhs => rw [← inv, ← GlobalTheory.RawLift.thetaInner_smul_right, ← comm, GlobalTheory.RawLift.thetaInner_smul_left,
        GlobalTheory.RawLift.thetaInner_smul_right, ← mul_assoc, hεε, one_mul]
    have h0 : (ψ (symplO S T u u') - 1) * GlobalTheory.RawLift.thetaIP μ 𝓕 v (heisO ψ S T u v) = 0 := by
      rw [sub_mul, hfix, one_mul, sub_self]
    rw [(mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hψu)]
    exact zero_mem _

/- English proof (translation)
Establish `hψ : IsStdChar D ψ (-1)` using `hv.1`. Establish `hvt : IsThetaFunO ψ S T v` using `hv.2.theta`. Establish `laws` using `GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T`. Establish `e1 : heisO ψ S T (-x) (heisO ψ S T x v) = ψ (symplOH S T (-x) x) • v`. Rewrite using `[GlobalTheory.SplitScalar.heisO_heisO, neg_add_cancel, GlobalTheory.SplitScalar.heisO_zero]`.

Establish `e2 : heisO ψ S T (-x) (heisO ψ S T y v) = ψ (symplOH S T (-x) y) • heisO ψ S T (-x + y) v` using `GlobalTheory.SplitScalar.heisO_heisO ψ S T (-x) y v`. Rewrite using `[← GlobalTheory.VacSchurFin.thetaInner_heisenberg hψ hcv (laws.1 x v hvt) (laws.1 y v hvt) (-x), e1, e2, GlobalTheory.RawLift.thetaInner_smul_left, GlobalTheory.RawLift.thetaInner_smul_right]`. Use `mul_mem (alg_star (GlobalTheory.BotFourier.psiH_mem hψ hS hT (fin_neg hx) hx)) (mul_mem (GlobalTheory.BotFourier.psiH_mem hψ hS hT (fin_neg hx) hy) ?_)` and prove the remaining obligations. Conclude with `vac_translate hv hS hT hcv (fin_add (fin_neg hx) hy)`.
-/
theorem translates (hv : IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v)
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hcv : IsCovolOne (ratL T S) μ 𝓕) {x y : WO S T}
    (hx : x.map (infPart D) = 0) (hy : y.map (infPart D) = 0) :
    GlobalTheory.RawLift.thetaIP μ 𝓕 (heisO ψ S T x v) (heisO ψ S T y v) ∈ algebraicClosure ℚ ℂ := by
  have hψ : IsStdChar D ψ (-1) := hv.1
  have hvt : IsThetaFunO ψ S T v := hv.2.theta
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have e1 : heisO ψ S T (-x) (heisO ψ S T x v) = ψ (symplOH S T (-x) x) • v := by
    rw [GlobalTheory.SplitScalar.heisO_heisO, neg_add_cancel, GlobalTheory.SplitScalar.heisO_zero]
  have e2 : heisO ψ S T (-x) (heisO ψ S T y v) = ψ (symplOH S T (-x) y) • heisO ψ S T (-x + y) v :=
    GlobalTheory.SplitScalar.heisO_heisO ψ S T (-x) y v
  rw [← GlobalTheory.VacSchurFin.thetaInner_heisenberg hψ hcv (laws.1 x v hvt) (laws.1 y v hvt) (-x), e1, e2,
    GlobalTheory.RawLift.thetaInner_smul_left, GlobalTheory.RawLift.thetaInner_smul_right]
  refine mul_mem (alg_star (GlobalTheory.BotFourier.psiH_mem hψ hS hT (fin_neg hx) hx))
    (mul_mem (GlobalTheory.BotFourier.psiH_mem hψ hS hT (fin_neg hx) hy) ?_)
  exact vac_translate hv hS hT hcv (fin_add (fin_neg hx) hy)

/- English proof (translation)
Introduce `D ψ θ S T sS sT ΛS ΛT v hv hS hT μ 𝓕 hcv F F' hF hF'`. Take `⟨n, c, w, hc, hw, rfl⟩` from `hF`. Take `⟨m, c', w', hc', hw', rfl⟩` from `hF'`. Establish `hψ : IsStdChar D ψ (-1)` using `hv.1`. Establish `hvt : IsThetaFunO ψ S T v` using `hv.2.theta`.

Establish `laws` using `GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T`. Establish `hth : ∀ x, IsThetaFunO ψ S T (heisO ψ S T x v)` using `fun x => laws.1 x v hvt`. Establish `hR` using `(sum_right hψ hcv (hth 0) c' (fun q => heisO ψ S T (w' q) v) fun q => hth _).1`. Rewrite using `[(sum_left hψ hcv hR c (fun p => heisO ψ S T (w p) v) fun p => hth _).2, ← mem_algebraicClosure_iff]`. Use `Subalgebra.sum_mem _ fun p _ => mul_mem (alg_star (mem_algebraicClosure_iff.2 (hc p))) ?_` and prove the remaining obligations.

Rewrite using `[(sum_right hψ hcv (hth (w p)) c' (fun q => heisO ψ S T (w' q) v) fun q => hth _).2]`. Conclude with `Subalgebra.sum_mem _ fun q _ => mul_mem (mem_algebraicClosure_iff.2 (hc' q)) (translates hv hS hT hcv (hw p) (hw' q))`.
-/
theorem thetaIP_algComb : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ F F' : WO S T → ℂ,
    GlobalTheory.MovedAlg.IsAlgComb ψ S T v F → GlobalTheory.MovedAlg.IsAlgComb ψ S T v F' → IsAlgebraic ℚ (GlobalTheory.RawLift.thetaIP μ 𝓕 F F') := by
  intro D ψ θ S T sS sT ΛS ΛT v hv hS hT μ 𝓕 hcv F F' hF hF'
  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  obtain ⟨m, c', w', hc', hw', rfl⟩ := hF'
  have hψ : IsStdChar D ψ (-1) := hv.1
  have hvt : IsThetaFunO ψ S T v := hv.2.theta
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have hth : ∀ x, IsThetaFunO ψ S T (heisO ψ S T x v) := fun x => laws.1 x v hvt
  have hR := (sum_right hψ hcv (hth 0) c' (fun q => heisO ψ S T (w' q) v) fun q => hth _).1
  rw [(sum_left hψ hcv hR c (fun p => heisO ψ S T (w p) v) fun p => hth _).2, ← mem_algebraicClosure_iff]
  refine Subalgebra.sum_mem _ fun p _ => mul_mem (alg_star (mem_algebraicClosure_iff.2 (hc p))) ?_
  rw [(sum_right hψ hcv (hth (w p)) c' (fun q => heisO ψ S T (w' q) v) fun q => hth _).2]
  exact Subalgebra.sum_mem _ fun q _ =>
    mul_mem (mem_algebraicClosure_iff.2 (hc' q)) (translates hv hS hT hcv (hw p) (hw' q))

end GlobalTheory.AlgPair

end
