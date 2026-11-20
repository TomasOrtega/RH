import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.WeakStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatakeGLOfHasSatakeParametersPrincipalSeries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSatakeParameterOfIsSubquotientOfInjective

noncomputable section

open NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory.C GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions UpperTheory.CBC

namespace UpperTheory.ConvolutionTheory.Sph

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

A detailed English derivation is pending.
-/
private theorem hasSat_iff {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} (π : CuspSub K n)
    (v : HeightOneSpectrum (𝓞 K)) (τ : SmIrr (GL (Fin n) (v.adicCompletion K))) (hτ : π.IsLocComp v τ)
    (B : Multiset ℂˣ) : (Cusp.cx π).sat v B ↔ GlobalTheory.LFun.HasSatGL v τ.ρ B := by
  refine ⟨fun hB => ?_, fun h => GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hτ h⟩
  have hB' : GlobalTheory.LFun.HasSatGL v (π.locRep v) B := hB
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hB'.1
  obtain ⟨y, hy0, hy⟩ := LocSph.exists_fixed_of_mem_iSup ((finRep K n).comp (locGL K n v)) τ.ρ τ.irred
    (fun f : LocSph.Maps π v τ => f.1) (fun f => f.2.2) (GlobalTheory.LFun.KGL v n : Set _) x.1 (fun e => hx0 (Subtype.ext e))
    (fun k hk => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx k hk))
    (by rw [LocSph.iSup_range_eq π v τ hτ]; exact x.2)
  obtain ⟨B', hB''⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible τ.smooth τ.irred
    ((Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.LGrp.mem_fixed.2 hy, hy0⟩)
  exact (GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hτ hB'').unique hB' ▸ hB''

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
private theorem isSpherical_iff {K : Type} [Field K] [NumberField K] {n : ℕ} (v : HeightOneSpectrum (𝓞 K))
    (τ : SmIrr (GL (Fin n) (v.adicCompletion K))) :
    IsSpherical τ.ρ ↔ GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.LFun.KGL v n) ≠ ⊥ := by
  have hK := GlobalTheory.SmGL.SphCompletion.KO_completion (F := K) v n
  unfold GlobalTheory.SmGL.IsSpherical GlobalTheory.SmGL.IsSphericalFor
  rw [hK]

end UpperTheory.ConvolutionTheory.Sph

open UpperTheory.ConvolutionTheory.Sph in
/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.ConvolutionTheory.Sph.satDict :
    UpperTheory.ConvolutionTheory.Sph.SatDict := by
  refine ⟨1, Or.inl rfl, ?_⟩
  intro K _ _ _ n π v τ hτ
  have hτ' : π.IsLocComp v τ := hτ
  refine ⟨?_, fun hs => ?_, fun α hs hα => ?_⟩
  · rintro ⟨B, hB⟩
    exact (isSpherical_iff v τ).2 ((hasSat_iff π v τ hτ' B).1 hB).1
  · refine GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries
      ((GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness _).1 (Fin n) τ.V τ.ρ τ.smooth τ.irred) τ.irred ?_
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hs
    exact (Submodule.ne_bot_iff _).2 ⟨x, fun h => hx ⟨h.1, iwahori_le_KO _ _ h.2⟩, hx0⟩
  · have h := GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake K v n τ.V τ.ρ α ⟨τ.irred, hs, hα⟩
    have e : (Finset.univ.val.map fun i => α i ^ (1 : ℤ)) = Finset.univ.val.map α := by simp
    rw [e]
    exact (hasSat_iff π v τ hτ' _).2 h
