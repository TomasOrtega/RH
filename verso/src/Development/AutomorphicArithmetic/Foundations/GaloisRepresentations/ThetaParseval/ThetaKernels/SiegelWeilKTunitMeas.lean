import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnitaryChartEquiv.CEquivApply
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTbijChart

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.KTunit
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
open PositivityTheory.SiegelWeilFormula.TBij.Adp
local instance (priority := high)  {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] :
    MeasurableSpace (κ → AF F) := borel _
local instance  {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] : BorelSpace (κ → AF F) := ⟨rfl⟩
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def cmap_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (X : Mx F E d.m d.n) : κ → AF F := fun k => d.crd X (τ k)
def cinv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (c : κ → AF F) : Mx F E d.m d.n := d.cmb fun k => c (τ.symm k)
/- English proof (translation)
Establish `: (fun k => _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ X (τ.symm k)) = d.crd X` using `funext fun k => by simp [_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k]`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k, this, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd]`.
-/
theorem cinv_cmap_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k d τ (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ X) = X := by
  have : (fun k => _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ X (τ.symm k)) = d.crd X := funext fun k => by simp [_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k, this, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd]
/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k, _root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_cmb]`.
-/
theorem cmap_cinv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (c : κ → AF F) : _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k d τ c) = c := by
  funext k
  simp [_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k, _root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_cmb]
/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k, _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, map_add]`.
-/
theorem cmap_add_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (X Y : Mx F E d.m d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ (X + Y) = _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ X + _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ Y := by
  funext k
  simp [_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k, _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, map_add]
/- English proof (translation)
Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Establish `hr` using `(GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ d.ok.good.cm (AF F)).2.2.2.2.2.2.1 2 d.bs`. Use `continuous_pi fun k => ?_` and prove the remaining obligations. Conclude with `(continuous_apply (τ k).2.2).comp (hr.continuous.comp (continuous_id.matrix_elem (τ k).1 (τ k).2.1))`.
-/
theorem cont_cmap_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ) := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hr := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ d.ok.good.cm (AF F)).2.2.2.2.2.2.1 2 d.bs
  refine continuous_pi fun k => ?_
  exact (continuous_apply (τ k).2.2).comp (hr.continuous.comp (continuous_id.matrix_elem (τ k).1 (τ k).2.1))
/- English proof (translation)
Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Establish `hr` using `(GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ d.ok.good.cm (AF F)).2.2.2.2.2.2.1 2 d.bs`. Use `set h := hr.homeomorph with hh`. Establish `e : ∀ c i j, _root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k d τ c i j = h.symm (fun l => c (τ.symm (i, j, l)))` using `fun c i j => by`. Apply `h.injective` to reduce the goal to its premises.

Rewrite using `[Homeomorph.apply_symm_apply]`. Use function extensionality and compare the values at `l`. Conclude with `congrFun (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_cmb d (fun k => c (τ.symm k))) (i, j, l)`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [e]`.

Conclude with `h.symm.continuous.comp (continuous_pi fun l => continuous_apply _)`.
-/
theorem cont_cinv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k d τ) := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hr := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ d.ok.good.cm (AF F)).2.2.2.2.2.2.1 2 d.bs
  set h := hr.homeomorph with hh
  have e : ∀ c i j, _root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k d τ c i j = h.symm (fun l => c (τ.symm (i, j, l))) := fun c i j => by
    apply h.injective
    rw [Homeomorph.apply_symm_apply]
    funext l
    exact congrFun (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_cmb d (fun k => c (τ.symm k))) (i, j, l)
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [e]
  exact h.symm.continuous.comp (continuous_pi fun l => continuous_apply _)
def cEquiv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) : Mx F E d.m d.n ≃ₜ+ (κ → AF F) where
  toFun := _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ
  invFun := _root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_k d τ
  left_inv := _root_.PositivityTheory.SiegelWeilFormula.KTunit.cinv_cmap_k d τ
  right_inv := _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_cinv_k d τ
  map_add' := _root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_add_k d τ
  continuous_toFun := _root_.PositivityTheory.SiegelWeilFormula.KTunit.cont_cmap_k d τ
  continuous_invFun := _root_.PositivityTheory.SiegelWeilFormula.KTunit.cont_cinv_k d τ
/- English proof (translation)
Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Establish `P` using `GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ d.ok.good.cm (AF F)`. Use `haveI : IsTopologicalRing (AE F E) := P.1`. Use `haveI : BorelSpace (Mx F E d.m d.n) := P.2.2.2.2.2.2.2.1 d.m d.n`. Use `haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstance`.

Use `⟨?_, fun f => ?_⟩` and prove the remaining obligations. Conclude with `ContinuousAddEquiv.isAddHaarMeasure_map ν (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cEquiv_k d τ)`. Establish `h` using `integral_map_equiv (μ := ν) (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cEquiv_k d τ).toHomeomorph.toMeasurableEquiv f`. Conclude with `h.symm`.
-/
theorem map_haar_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (ν : Measure (Mx F E d.m d.n))
    (hν : ν.IsAddHaarMeasure) :
    (ν.map (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ)).IsAddHaarMeasure ∧
      ∀ f : (κ → AF F) → ℂ, ∫ X, f (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ X) ∂ν = ∫ y, f y ∂(ν.map (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have P := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ d.ok.good.cm (AF F)
  haveI : IsTopologicalRing (AE F E) := P.1
  haveI : BorelSpace (Mx F E d.m d.n) := P.2.2.2.2.2.2.2.1 d.m d.n
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstance
  refine ⟨?_, fun f => ?_⟩
  · exact ContinuousAddEquiv.isAddHaarMeasure_map ν (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cEquiv_k d τ)
  · have h := integral_map_equiv (μ := ν) (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cEquiv_k d τ).toHomeomorph.toMeasurableEquiv f
    exact h.symm
end PositivityTheory.SiegelWeilFormula.KTunit
end
end
