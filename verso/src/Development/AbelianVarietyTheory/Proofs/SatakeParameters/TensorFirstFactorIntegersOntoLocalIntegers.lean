import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

/- English proof (translation)
Introduce `F E _ _ _ _ _ n p G A hA v`. Establish `h1 : ∀ y : (A.pl v).1.adicCompletion F, A.ph v ((1 : E) ⊗ₜ[F] y) = y`. Introduce `y`. Use `show ((A.spl v) ((1 : E) ⊗ₜ[F] y)).1 = y`. Rewrite using `[hA v y]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `s hs`. Establish `hle : intV E (A.pl v).1 ≤ ((A.pl v).1.adicCompletionIntegers F).toSubring.comap (A.ph v)`. Use `(Subring.closure_le).2 ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)`.

Take `⟨r, rfl⟩` from `hx show A.ph v ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F)) ∈ (A.pl v).1.adicCompletionIntegers F`. Establish `h0 : IsIntegral ℤ (algebraMap (𝓞 E) E r)` using `(RingOfIntegers.isIntegral r).map (IsScalarTower.toAlgHom ℤ (𝓞 E) E)`. Take `⟨q, hq, hev⟩` from `h0`. Set `f : E →+* (A.pl v).1.adicCompletion F` to `(A.ph v).comp (Algebra.TensorProduct.includeLeftRingHom)`. Establish `hf : f (algebraMap (𝓞 E) E r) = A.ph v ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F))` using `rfl`.

Establish `hint' : IsIntegral ((A.pl v).1.adicCompletionIntegers F) (A.ph v ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F)))`. Use `⟨q.map (Int.castRingHom _), hq.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map, ← hf]`. Use `congrArg f hev` as an intermediate fact. Rewrite `this` using `[map_zero, Polynomial.hom_eval₂]`.

Establish `e : (algebraMap ((A.pl v).1.adicCompletionIntegers F) ((A.pl v).1.adicCompletion F)).comp (Int.castRingHom ((A.pl v).1.adicCompletionIntegers F)) = f.comp (algebraMap ℤ E)` using `RingHom.ext_int _ _`. Rewrite using `[e]`. Conclude with `this`. Take `⟨z, hz⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hint'`. Rewrite using `[← hz]`.

Conclude with `z.2`. Use `show A.ph v ((1 : E) ⊗ₜ[F] y) ∈ (A.pl v).1.adicCompletionIntegers F`. Rewrite using `[h1]`. Conclude with `hy`. Conclude with `hle hs`.

Introduce `x hx`. Use `⟨(1 : E) ⊗ₜ[F] x, ?_, h1 x⟩` and prove the remaining obligations. Conclude with `Subring.subset_closure (Or.inr ⟨⟨x, hx⟩, rfl⟩)`.
-/
theorem ph_tensInt_onto : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G), SplAlg A → ∀ v, (∀ s ∈ intV E (A.pl v).1, A.ph v s ∈ (A.pl v).1.adicCompletionIntegers F) ∧ ∀ x ∈ (A.pl v).1.adicCompletionIntegers F, ∃ s ∈ intV E (A.pl v).1, A.ph v s = x := by
  intro F E _ _ _ _ _ n p G A hA v
  have h1 : ∀ y : (A.pl v).1.adicCompletion F, A.ph v ((1 : E) ⊗ₜ[F] y) = y := by
    intro y
    show ((A.spl v) ((1 : E) ⊗ₜ[F] y)).1 = y
    rw [hA v y]
  refine ⟨?_, ?_⟩
  · intro s hs
    have hle : intV E (A.pl v).1 ≤ ((A.pl v).1.adicCompletionIntegers F).toSubring.comap (A.ph v) := by
      refine (Subring.closure_le).2 ?_
      rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
      · obtain ⟨r, rfl⟩ := hx
        show A.ph v ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F)) ∈ (A.pl v).1.adicCompletionIntegers F
        have h0 : IsIntegral ℤ (algebraMap (𝓞 E) E r) := (RingOfIntegers.isIntegral r).map (IsScalarTower.toAlgHom ℤ (𝓞 E) E)
        obtain ⟨q, hq, hev⟩ := h0
        let f : E →+* (A.pl v).1.adicCompletion F := (A.ph v).comp (Algebra.TensorProduct.includeLeftRingHom)
        have hf : f (algebraMap (𝓞 E) E r) = A.ph v ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F)) := rfl
        have hint' : IsIntegral ((A.pl v).1.adicCompletionIntegers F) (A.ph v ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : (A.pl v).1.adicCompletion F))) := by
          refine ⟨q.map (Int.castRingHom _), hq.map _, ?_⟩
          rw [Polynomial.eval₂_map, ← hf]
          have := congrArg f hev
          rw [map_zero, Polynomial.hom_eval₂] at this
          have e : (algebraMap ((A.pl v).1.adicCompletionIntegers F) ((A.pl v).1.adicCompletion F)).comp
              (Int.castRingHom ((A.pl v).1.adicCompletionIntegers F)) = f.comp (algebraMap ℤ E) := RingHom.ext_int _ _
          rw [e]
          exact this
        obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
        rw [← hz]
        exact z.2
      · show A.ph v ((1 : E) ⊗ₜ[F] y) ∈ (A.pl v).1.adicCompletionIntegers F
        rw [h1]
        exact hy
    exact hle hs
  · intro x hx
    refine ⟨(1 : E) ⊗ₜ[F] x, ?_, h1 x⟩
    exact Subring.subset_closure (Or.inr ⟨⟨x, hx⟩, rfl⟩)

end GlobalTheory.TwV
