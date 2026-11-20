import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

/- English proof (translation)
Introduce `E _ _ _ n hn π`. Take `⟨κ, hκ⟩` from `GlobalTheory.CuspRep.Central.exists_hasCentral E n π`. Set `z : {r : ℝ // 0 < r} →* (Ad E)ˣ` to `(Reduction.posIdeleHom E).comp (Reduction.rpowHom ((n * Module.finrank ℚ E : ℝ))⁻¹)`. Establish `hz : ∀ s, Reduction.centralSection E n s = GeneralLinearGroup.scalar (Fin n) (z s)` using `fun s => Units.ext rfl`. Establish `hc : Continuous z` using `Reduction.continuous_posIdeleHom.comp (Reduction.continuous_rpowHom _)`.

Establish `hm : ∀ s, GroundTheory.Global.IdeleGroup.ideleModule E (z s ^ n) = s` using `fun s => by`. Establish `h` using `Reduction.detModule_centralSection (K := E) hn s`. Rewrite `h` using `[hz]`. Use `Eq.trans (congrArg _ (Units.ext ?_)) h` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = Matrix.det (Matrix.diagonal fun _ : Fin n => (z s).val)`.

Simplify using the standard rewrite rules. Set `ν : Formalism.L2.Host.HChar E` to `⟨(κ⁻¹.1.comp z).comp (GroundTheory.Global.IdeleGroup.ideleModule E), (κ⁻¹.2.1.comp hc).comp GroundTheory.Global.IdeleGroup.continuous_ideleModule, fun k => by`. Establish `h` using `GroundTheory.Global.IdeleGroup.ideleModule_diagonal (K := E) k`. Conclude with `(congrArg (κ⁻¹.1.comp z) h).trans (map_one _)⟩`. Use `⟨ν, fun φ hφ s g => ?_⟩` and prove the remaining obligations.

Rewrite using `[hz, (hκ.twist ν).apply hφ]`. Establish `e : (κ * ν ^ n).1 (z s) = 1`. Express the relevant statement in the definitionally equal form `κ.1 (z s) * (ν.1 ^ n) (z s) = 1`. Rewrite using `[MonoidHom.pow_apply, ← map_pow]`. Express the relevant statement in the definitionally equal form `κ.1 (z s) * (κ.1 (z (GroundTheory.Global.IdeleGroup.ideleModule E (z s ^ n))))⁻¹ = 1`.

Rewrite using `[hm, mul_inv_cancel]`. Rewrite using `[e]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Af.StrongMultiplicityOne.normTwist :
    UpperTheory.V.Af.StrongMultiplicityOne.NormTwist := by
  intro E _ _ _ n hn π
  obtain ⟨κ, hκ⟩ := GlobalTheory.CuspRep.Central.exists_hasCentral E n π
  let z : {r : ℝ // 0 < r} →* (Ad E)ˣ :=
    (Reduction.posIdeleHom E).comp (Reduction.rpowHom ((n * Module.finrank ℚ E : ℝ))⁻¹)
  have hz : ∀ s, Reduction.centralSection E n s = GeneralLinearGroup.scalar (Fin n) (z s) := fun s => Units.ext rfl
  have hc : Continuous z := Reduction.continuous_posIdeleHom.comp (Reduction.continuous_rpowHom _)
  have hm : ∀ s, GroundTheory.Global.IdeleGroup.ideleModule E (z s ^ n) = s := fun s => by
    have h := Reduction.detModule_centralSection (K := E) hn s
    rw [hz] at h
    refine Eq.trans (congrArg _ (Units.ext ?_)) h
    change _ = Matrix.det (Matrix.diagonal fun _ : Fin n => (z s).val)
    simp
  let ν : Formalism.L2.Host.HChar E := ⟨(κ⁻¹.1.comp z).comp (GroundTheory.Global.IdeleGroup.ideleModule E),
    (κ⁻¹.2.1.comp hc).comp GroundTheory.Global.IdeleGroup.continuous_ideleModule, fun k => by
      have h := GroundTheory.Global.IdeleGroup.ideleModule_diagonal (K := E) k
      exact (congrArg (κ⁻¹.1.comp z) h).trans (map_one _)⟩
  refine ⟨ν, fun φ hφ s g => ?_⟩
  rw [hz, (hκ.twist ν).apply hφ]
  have e : (κ * ν ^ n).1 (z s) = 1 := by
    change κ.1 (z s) * (ν.1 ^ n) (z s) = 1
    rw [MonoidHom.pow_apply, ← map_pow]
    change κ.1 (z s) * (κ.1 (z (GroundTheory.Global.IdeleGroup.ideleModule E (z s ^ n))))⁻¹ = 1
    rw [hm, mul_inv_cancel]
  rw [e]
  simp
