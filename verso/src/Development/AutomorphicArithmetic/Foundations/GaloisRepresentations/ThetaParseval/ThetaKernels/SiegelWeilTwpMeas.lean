import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylIntegralCovariance.IntegralCovGen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTbijChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitMeasTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKTunitMeas

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
set_option linter.style.haveILetI false
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.TW.Twp
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
open PositivityTheory.SiegelWeilFormula.TBij.Adp
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
/- English proof (translation)
Set `c : Mx F E d.m d.n →+ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → AF F)` to `{ toFun := d.crd, map_zero' := by funext k; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd], map_add' := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_add d }`. Prove the components needed by the constructor for the conclusion. Introduce `hX`. Establish `hle : d.ratM ≤ (GroundTheory.Automorphic.FourierWhittaker.vecLattice F (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d)).comap c`. Use `(AddSubgroup.closure_le _).mpr ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨M, rfl⟩`. Use `⟨fun k => d.bs.repr (M k.1 k.2.1) k.2.2, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Conclude with `(_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_incM d M k).symm`. Conclude with `hle hX`.

Introduce and unpack `⟨ξ, hξ⟩`. Set `M : Matrix (Fin d.m) (Fin d.n) E` to `Matrix.of fun i j => ∑ k, ξ (i, j, k) • d.bs k`. Establish `e1 : d.crd (incM F M) = d.crd X`. Use function extensionality and compare the values at `k`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_incM d _ k]`.

Establish `h2` using `congrFun hξ k`. Simplify using `only [AddMonoidHom.compLeft, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply] at h2`. Rewrite using `[← h2]`. Use `show _ = algebraMap F (AF F) (ξ k)`. Use `congr 1`.

Conclude with `congrFun (d.bs.repr_sum_self fun k' => ξ (k.1, k.2.1, k')) k.2.2`. Establish `e2 : incM F M = X`. Rewrite using `[← _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd d (incM F _), e1, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd]`. Rewrite using `[← e2]`. Conclude with `AddSubgroup.subset_closure ⟨_, rfl⟩`.
-/
theorem ratM_iff_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Mx F E d.m d.n) :
    X ∈ d.ratM ↔ d.crd X ∈ GroundTheory.Automorphic.FourierWhittaker.vecLattice F (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) := by
  let c : Mx F E d.m d.n →+ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → AF F) :=
    { toFun := d.crd, map_zero' := by funext k; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd], map_add' := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_add d }
  constructor
  · intro hX
    have hle : d.ratM ≤ (GroundTheory.Automorphic.FourierWhittaker.vecLattice F (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d)).comap c := by
      refine (AddSubgroup.closure_le _).mpr ?_
      rintro _ ⟨M, rfl⟩
      refine ⟨fun k => d.bs.repr (M k.1 k.2.1) k.2.2, ?_⟩
      funext k
      exact (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_incM d M k).symm
    exact hle hX
  · rintro ⟨ξ, hξ⟩
    let M : Matrix (Fin d.m) (Fin d.n) E := Matrix.of fun i j => ∑ k, ξ (i, j, k) • d.bs k
    have e1 : d.crd (incM F M) = d.crd X := by
      funext k
      rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_incM d _ k]
      have h2 := congrFun hξ k
      simp only [AddMonoidHom.compLeft, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply] at h2
      rw [← h2]
      show _ = algebraMap F (AF F) (ξ k)
      congr 1
      exact congrFun (d.bs.repr_sum_self fun k' => ξ (k.1, k.2.1, k')) k.2.2
    have e2 : incM F M = X := by
      rw [← _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd d (incM F _), e1, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd]
    rw [← e2]
    exact AddSubgroup.subset_closure ⟨_, rfl⟩
/- English proof (translation)
Take `⟨hT, hLC, hSC, hB, hC⟩` from `_root_.PositivityTheory.SiegelWeilFormula.KWhit.meas_mx_top'_k d`. Use `haveI := hT`. Use `haveI := hLC`. Use `haveI := hSC`. Use `haveI := hB`.

Use `haveI := hC`. Take `⟨hH, 𝓕, h𝓕, h1⟩` from `hν`. Use `haveI := hH`. Conclude with `integral_cov_gen (hBor := hB) (hνH := hH) d.ratM (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cEquiv_k d (Equiv.refl (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d))) (fun X => _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.ratM_iff_k d X) ν 𝓕 h𝓕 h1 h`.
-/
theorem integral_cov_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ν : Measure (Mx F E d.m d.n)) (hν : d.IsCov ν) (h : Mx F E d.m d.n → ℂ) :
    ∫ Z, h Z ∂ν = ∫ c, h (d.cmb c) ∂(GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F (ι := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d)) := by
  obtain ⟨hT, hLC, hSC, hB, hC⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.meas_mx_top'_k d
  haveI := hT; haveI := hLC; haveI := hSC; haveI := hB; haveI := hC
  obtain ⟨hH, 𝓕, h𝓕, h1⟩ := hν
  haveI := hH
  exact integral_cov_gen (hBor := hB) (hνH := hH) d.ratM (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cEquiv_k d (Equiv.refl (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d))) (fun X => _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.ratM_iff_k d X) ν 𝓕 h𝓕 h1 h
end PositivityTheory.SiegelWeilFormula.TW.Twp
end
end
