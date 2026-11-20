import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFacts

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphStd

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Establish `h1` using `h (-x) (neg_mem hx)`. Rewrite `h1` using `[AddChar.inv_apply, neg_neg]`. Then use the resulting hypothesis. Introduce `h x hx`.

Rewrite using `[AddChar.inv_apply]`. Conclude with `h (-x) (neg_mem hx)`.
-/
theorem isTrivialOn_inv_iff {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (ψ : AddChar F Circle) (n : ℤ) :
    IsTrivialOn ψ⁻¹ n ↔ IsTrivialOn ψ n := by
  constructor
  · intro h x hx
    have h1 := h (-x) (neg_mem hx)
    rwa [AddChar.inv_apply, neg_neg] at h1
  · intro h x hx
    rw [AddChar.inv_apply]
    exact h (-x) (neg_mem hx)

/- English proof (translation)
Unfold `addCharConductor`. Use `congr 1`. Use extensionality with `n`. Conclude with `isTrivialOn_inv_iff ψ n`.
-/
theorem addCharConductor_inv {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (ψ : AddChar F Circle) :
    addCharConductor ψ⁻¹ = addCharConductor ψ := by
  unfold addCharConductor
  congr 1
  ext n
  exact isTrivialOn_inv_iff ψ n

/- English proof (translation)
Use `⟨?_, inv_ne_one.2 hψ.2.1, ?_⟩` and prove the remaining obligations. Conclude with `(hψ.1.comp continuous_neg).congr fun x => (AddChar.inv_apply ψ x).symm`. Rewrite using `[addCharConductor_inv]`. Conclude with `hψ.2.2`.
-/
theorem isStd_inv {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {ψ : AddChar F Circle} (hψ : IsStd ψ) : IsStd ψ⁻¹ := by
  refine ⟨?_, inv_ne_one.2 hψ.2.1, ?_⟩
  · exact (hψ.1.comp continuous_neg).congr fun x => (AddChar.inv_apply ψ x).symm
  · rw [addCharConductor_inv]
    exact hψ.2.2

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.RankinQ.isStd_local v`.
-/
theorem isStd_psiF (v : Ad3.Pl) : Ad3.IsStd (Ad3.GP.psiF v) :=
  GlobalTheory.CompanionTheory.RankinQ.isStd_local v

/- English proof (translation)
Introduce `v` and use `isStd_inv (isStd_psiF v)`.
-/
theorem isStd_psiF_inv : ∀ v : Ad3.Pl, Ad3.IsStd (Ad3.GP.psiF v)⁻¹ :=
  fun v => isStd_inv (isStd_psiF v)

end GlobalTheory.CompanionTheory.SphStd
