import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatTuple
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SchwartzBruhatEqSumPure
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterArchimedeanFormStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ _ d b n M N hN`. Establish `hNF : (N : F) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : IsUnit (N : Af F) := by`. Establish `h1 : IsUnit (algebraMap F (Af F) (N : F))` using `(IsUnit.mk0 _ hNF).map _`. Rewrite `h1` using `[map_natCast]`. Then use the resulting hypothesis.

Establish `hSo : IsOpen {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z}`. Establish `hpre : {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} = (fun y => (↑u⁻¹ : Af F) * y) ⁻¹' Oh F`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩ show (↑u⁻¹ : Af F) * ((N : Af F) * z) ∈ Oh F`.

Rewrite using `[← hu, ← mul_assoc, Units.inv_mul, one_mul]`. Conclude with `hz`. Introduce `hy`. Conclude with `⟨(↑u⁻¹ : Af F) * y, hy, by rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]⟩`. Rewrite using `[hpre]`.

Conclude with `(AfTop.isOpen_Oh F).preimage (continuous_const_mul _)`. Establish `hSc : IsCompact {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z}`. Establish `himg : {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} = (fun z => (N : Af F) * z) '' Oh F`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `⟨z, hz, rfl⟩`. Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `⟨z, hz, rfl⟩`. Rewrite using `[himg]`.

Conclude with `(AfTop.isCompact_Oh F).image (continuous_const_mul _)`. Use `haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩`. Set `Bs` to `Algebra.TensorProduct.basis (Af F) b`. Set `e : (Af F ⊗[F] E) ≃ₜ (Fin d → Af F)` to `{ Bs.equivFun.toEquiv with continuous_toFun := IsModuleTopology.continuous_of_linearMap Bs.equivFun.toLinearMap continuous_invFun := IsModuleTopology.continuous_of_linearMap Bs.equivFun.symm.toLinearMap }`. Establish `hT : {x : Af F ⊗[F] E | InNOh b N x} = e ⁻¹' Set.univ.pi (fun _ => {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z})`.

Use extensionality with `x`. Rewrite using `[Set.mem_preimage, Set.mem_univ_pi]`. Conclude with `Iff.rfl`. Establish `hlat : (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) = Set.univ.pi (fun _ => Set.univ.pi (fun _ => {x : Af F ⊗[F] E | InNOh b N x}))`. Use extensionality with `X`.

Simplify using `only [Set.mem_univ_pi]`. Conclude with `Iff.rfl`. Establish `hTo : IsOpen {x : Af F ⊗[F] E | InNOh b N x}`. Rewrite using `[hT]`. Conclude with `(isOpen_set_pi Set.finite_univ fun _ _ => hSo).preimage e.continuous`.

Establish `hTc : IsCompact {x : Af F ⊗[F] E | InNOh b N x}`. Rewrite using `[hT]`. Conclude with `e.isCompact_preimage.mpr (isCompact_univ_pi fun _ => hSc)`. Rewrite using `[hlat]`. Conclude with `⟨isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hTo, isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hTc⟩`.
-/
theorem latN_isOpen_isCompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M N : ℕ), 0 < N →
    IsOpen (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) ∧
    IsCompact (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ _ d b n M N hN
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  obtain ⟨u, hu⟩ : IsUnit (N : Af F) := by
    have h1 : IsUnit (algebraMap F (Af F) (N : F)) := (IsUnit.mk0 _ hNF).map _
    rwa [map_natCast] at h1
  have hSo : IsOpen {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} := by
    have hpre : {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} = (fun y => (↑u⁻¹ : Af F) * y) ⁻¹' Oh F := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        show (↑u⁻¹ : Af F) * ((N : Af F) * z) ∈ Oh F
        rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
        exact hz
      · intro hy
        exact ⟨(↑u⁻¹ : Af F) * y, hy, by rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]⟩
    rw [hpre]
    exact (AfTop.isOpen_Oh F).preimage (continuous_const_mul _)
  have hSc : IsCompact {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} := by
    have himg : {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} = (fun z => (N : Af F) * z) '' Oh F := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
    rw [himg]
    exact (AfTop.isCompact_Oh F).image (continuous_const_mul _)
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  let Bs := Algebra.TensorProduct.basis (Af F) b
  let e : (Af F ⊗[F] E) ≃ₜ (Fin d → Af F) :=
    { Bs.equivFun.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap Bs.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap Bs.equivFun.symm.toLinearMap }
  have hT : {x : Af F ⊗[F] E | InNOh b N x} =
      e ⁻¹' Set.univ.pi (fun _ => {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z}) := by
    ext x
    rw [Set.mem_preimage, Set.mem_univ_pi]
    exact Iff.rfl
  have hlat : (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) =
      Set.univ.pi (fun _ => Set.univ.pi (fun _ => {x : Af F ⊗[F] E | InNOh b N x})) := by
    ext X
    simp only [Set.mem_univ_pi]
    exact Iff.rfl
  have hTo : IsOpen {x : Af F ⊗[F] E | InNOh b N x} := by
    rw [hT]
    exact (isOpen_set_pi Set.finite_univ fun _ _ => hSo).preimage e.continuous
  have hTc : IsCompact {x : Af F ⊗[F] E | InNOh b N x} := by
    rw [hT]
    exact e.isCompact_preimage.mpr (isCompact_univ_pi fun _ => hSc)
  rw [hlat]
  exact ⟨isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hTo,
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hTc⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
