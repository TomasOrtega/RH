import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTracePairingBilinearNondegenerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiFinRat

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical
open GlobalTheory.BoxLattice GlobalTheory.EvAdm

noncomputable section

namespace GlobalTheory.PsiSplit

/- English proof (translation)
Introduce `F _ _ κ _ ψ hψ x z`. Use `set y := x ⬝ᵥ fun i => algebraMap F (AF F) (z i) with hy`. Establish `hsplit : y = pairA F y.1 0 + pairA F 0 y.2` using `Prod.ext (add_zero _).symm (zero_add _).symm`. Establish `h1 : y.1 = ∑ i, (x i).1 * algebraMap F (Ainf F) (z i)`. Rewrite using `[hy, dotProduct]`.

Express the relevant statement in the definitionally equal form `fstA F (∑ i, x i * algebraMap F (AF F) (z i)) = _`. Rewrite using `[map_sum]`. Both sides reduce to the same expression. Establish `h2 : y.2 = (fun i => (x i).2) ⬝ᵥ ratFin F κ z`. Rewrite using `[hy, dotProduct, dotProduct]`.

Express the relevant statement in the definitionally equal form `sndA F (∑ i, x i * algebraMap F (AF F) (z i)) = _`. Rewrite using `[map_sum]`. Both sides reduce to the same expression. Establish `hev : evI F (pairA F y.1 0) = ∑ i, evI F (x i) * ratInf F κ z i`. Express the relevant statement in the definitionally equal form `InfiniteAdeleRing.ringEquiv_mixedSpace F y.1 = _`.

Rewrite using `[h1, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Use `congr 1`. Conclude with `(InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := F)).symm`.

Rewrite using `[hsplit, AddChar.map_add_eq_mul, hψ.2.2 _ (GlobalTheory.PsiNontriv.at_pairA_zero _), hev, h2, GlobalTheory.VacLn.trPair_apply]`.
-/
theorem psi_split : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (x : κ → AF F) (z : κ → F), ψ (x ⬝ᵥ fun i => algebraMap F (AF F) (z i)) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (GlobalTheory.VacLn.trPair F κ (fun i => evI F (x i)) (ratInf F κ z) : ℂ)) *
        ψ (pairA F 0 ((fun i => (x i).2) ⬝ᵥ ratFin F κ z)) := by
  intro F _ _ κ _ ψ hψ x z
  set y := x ⬝ᵥ fun i => algebraMap F (AF F) (z i) with hy
  have hsplit : y = pairA F y.1 0 + pairA F 0 y.2 := Prod.ext (add_zero _).symm (zero_add _).symm
  have h1 : y.1 = ∑ i, (x i).1 * algebraMap F (Ainf F) (z i) := by
    rw [hy, dotProduct]
    change fstA F (∑ i, x i * algebraMap F (AF F) (z i)) = _
    rw [map_sum]
    rfl
  have h2 : y.2 = (fun i => (x i).2) ⬝ᵥ ratFin F κ z := by
    rw [hy, dotProduct, dotProduct]
    change sndA F (∑ i, x i * algebraMap F (AF F) (z i)) = _
    rw [map_sum]
    rfl
  have hev : evI F (pairA F y.1 0) = ∑ i, evI F (x i) * ratInf F κ z i := by
    change InfiniteAdeleRing.ringEquiv_mixedSpace F y.1 = _
    rw [h1, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    congr 1
    exact (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := F)).symm
  rw [hsplit, AddChar.map_add_eq_mul, hψ.2.2 _ (GlobalTheory.PsiNontriv.at_pairA_zero _), hev, h2,
    GlobalTheory.VacLn.trPair_apply]

end GlobalTheory.PsiSplit

end
