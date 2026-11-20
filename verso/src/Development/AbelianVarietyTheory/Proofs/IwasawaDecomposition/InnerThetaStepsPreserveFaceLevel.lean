import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IoUniq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilFockVectorEigenOfFiniteStepEigenStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfVanishIt
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.DTheta

/- English proof (translation)
Introduce `hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH b t k hk y hy`. Establish `hx0` using `(R.ioY t k y).2`. Establish `hT` using `Formalism.IndefR.Eqv.contAt_of_mem ((mem_multT _ _ _ _ _).1 hx0)`. Establish `hx` using `hx0`. Rewrite `hx`, the goal using `[mem_multT, GlobalTheory.MultMem.mem_mult_iff]`.

Use `⟨hx.aut, hx.cusp, ?_, hx.equiv, hx.cont⟩` and prove the remaining obligations. Introduce `v κ hκ g`. Take `⟨κ', hκ', hω⟩` from `GlobalTheory.Mem.R3.DTheta.StepLevLift.stepLev_lift D G Pl0 I0 T A3 Ks R F cG hP hH b t k hk κ hκ`. Establish `hpt` using `GlobalTheory.T.weilFock_vector_eigen_of_finite_step_eigen D G Pl0 I0 T A3 Ks R F cG hP hH t k hk κ hκ.1 κ' hκ'.1 _ hω`. Establish `hval` using `GlobalTheory.Mem.R3.DTheta.stepLev_change D G Pl0 I0 T A3 Ks R F cG hP hH b t k hk κ κ' hκ' _ hpt y hy`.

Use `set x := (R.ioY t k y).1 with hxdef`. Use `set c0 := levChi (Yc D k) (R.βY k) (R.datYt t k (R.toRealDat.levR F.lv2 b)) κ with hc0`. Use `set c1 := levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) κ' with hc1`. Establish `hne : c1 ≠ 0` using `by rw [hc1]; unfold levChi; exact Units.ne_zero _`. Set `u : MMap (R.MY k)` to `(LinearMap.funLeft ℂ ℂ (fun h : GA D (Yc D k) => h * κ)).compMultilinearMap (PiTensorProduct.lift.symm x) - c0 • PiTensorProduct.lift.symm x`.

Establish `hu : Formalism.IndefR.Eqv.ContAt (R.MY k) u`. Introduce `τ v' z`. Take `⟨ℓ₁, s₁, e₁⟩` from `hT τ v' (z * κ)`. Take `⟨ℓ₂, s₂, e₂⟩` from `hT τ v' z`. Use `⟨ℓ₁ + (-c0) • ℓ₂, GlobalTheory.MultMem.sobCont_add s₁ (GlobalTheory.MultMem.sobCont_smul _ s₂), fun w => ?_⟩` and prove the remaining obligations.

Simplify using `only [u, LinearMap.add_apply, LinearMap.smul_apply, e₁, e₂, MultilinearMap.sub_apply, MultilinearMap.smul_apply, LinearMap.compMultilinearMap_apply, Pi.sub_apply, Pi.smul_apply, LinearMap.funLeft_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hz : ∀ φ w, PiTensorProduct.lift u (R.ItY k φ w) = 0`. Introduce `φ w`. Establish `e : PiTensorProduct.lift u = (LinearMap.funLeft ℂ ℂ (fun h : GA D (Yc D k) => h * κ)) ∘ₗ x - c0 • x`.

Apply `PiTensorProduct.ext` to reduce the goal to its premises. Use extensionality with `v'`. Simplify using `[u]`. Rewrite using `[e]`. Use function extensionality and compare the values at `g'`.

Simplify using `only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply, LinearMap.funLeft_apply, smul_eq_mul, Pi.zero_apply]`. Rewrite using `[hval φ w g']`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h0` using `GlobalTheory.Mem.R3.StepUniq.eq_zero_of_vanish_it hC.1 hC.2.1 D G Pl0 I0 T A3 Ks R F cG hP hH t k hk u hu hz`.

Establish `h1` using `congrFun (congrArg (fun U : MMap (R.MY k) => U v) h0) g`. Simplify using `only [u, MultilinearMap.sub_apply, MultilinearMap.smul_apply, LinearMap.compMultilinearMap_apply, Pi.sub_apply, Pi.smul_apply, LinearMap.funLeft_apply, smul_eq_mul, MultilinearMap.zero_apply, Pi.zero_apply] at h1`. Take the linear combination `h1`.
-/
theorem stepLev_holds : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → GlobalTheory.Mem.R3.DTheta.StepLev R.toRealDat F.lv2 := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH b t k hk y hy
  have hx0 := (R.ioY t k y).2
  have hT := Formalism.IndefR.Eqv.contAt_of_mem ((mem_multT _ _ _ _ _).1 hx0)
  have hx := hx0
  rw [mem_multT, GlobalTheory.MultMem.mem_mult_iff] at hx ⊢
  refine ⟨hx.aut, hx.cusp, ?_, hx.equiv, hx.cont⟩
  intro v κ hκ g
  obtain ⟨κ', hκ', hω⟩ := GlobalTheory.Mem.R3.DTheta.StepLevLift.stepLev_lift D G Pl0 I0 T A3 Ks R F cG hP hH b t k hk κ hκ
  have hpt := GlobalTheory.T.weilFock_vector_eigen_of_finite_step_eigen D G Pl0 I0 T A3 Ks R F cG hP hH t k hk κ hκ.1 κ' hκ'.1 _ hω
  have hval := GlobalTheory.Mem.R3.DTheta.stepLev_change D G Pl0 I0 T A3 Ks R F cG hP hH b t k hk κ κ' hκ' _ hpt y hy
  set x := (R.ioY t k y).1 with hxdef
  set c0 := levChi (Yc D k) (R.βY k) (R.datYt t k (R.toRealDat.levR F.lv2 b)) κ with hc0
  set c1 := levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) κ' with hc1
  have hne : c1 ≠ 0 := by rw [hc1]; unfold levChi; exact Units.ne_zero _
  let u : MMap (R.MY k) := (LinearMap.funLeft ℂ ℂ (fun h : GA D (Yc D k) => h * κ)).compMultilinearMap
    (PiTensorProduct.lift.symm x) - c0 • PiTensorProduct.lift.symm x
  have hu : Formalism.IndefR.Eqv.ContAt (R.MY k) u := by
    intro τ v' z
    obtain ⟨ℓ₁, s₁, e₁⟩ := hT τ v' (z * κ)
    obtain ⟨ℓ₂, s₂, e₂⟩ := hT τ v' z
    refine ⟨ℓ₁ + (-c0) • ℓ₂, GlobalTheory.MultMem.sobCont_add s₁ (GlobalTheory.MultMem.sobCont_smul _ s₂), fun w => ?_⟩
    simp only [u, LinearMap.add_apply, LinearMap.smul_apply, e₁, e₂, MultilinearMap.sub_apply,
      MultilinearMap.smul_apply, LinearMap.compMultilinearMap_apply, Pi.sub_apply, Pi.smul_apply,
      LinearMap.funLeft_apply, smul_eq_mul]
    ring
  have hz : ∀ φ w, PiTensorProduct.lift u (R.ItY k φ w) = 0 := by
    intro φ w
    have e : PiTensorProduct.lift u = (LinearMap.funLeft ℂ ℂ (fun h : GA D (Yc D k) => h * κ)) ∘ₗ x - c0 • x := by
      apply PiTensorProduct.ext
      ext v'
      simp [u]
    rw [e]
    funext g'
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply,
      LinearMap.funLeft_apply, smul_eq_mul, Pi.zero_apply]
    rw [hval φ w g']
    field_simp
    ring
  have h0 := GlobalTheory.Mem.R3.StepUniq.eq_zero_of_vanish_it hC.1 hC.2.1 D G Pl0 I0 T A3 Ks R F cG hP hH t k hk u hu hz
  have h1 := congrFun (congrArg (fun U : MMap (R.MY k) => U v) h0) g
  simp only [u, MultilinearMap.sub_apply, MultilinearMap.smul_apply, LinearMap.compMultilinearMap_apply, Pi.sub_apply,
    Pi.smul_apply, LinearMap.funLeft_apply, smul_eq_mul, MultilinearMap.zero_apply, Pi.zero_apply] at h1
  linear_combination h1

end GlobalTheory.Mem.R3.DTheta
