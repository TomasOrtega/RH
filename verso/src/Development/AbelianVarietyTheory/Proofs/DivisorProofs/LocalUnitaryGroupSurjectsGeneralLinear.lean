import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SurjAtPlaceV

open GlobalTheory.LeviAtPlace

/- English proof (translation)
Introduce `_ F E _ _ _ _ _ σ B a a' G X om om' hTr v _ t g'`. Establish `h` using `hTr.base.cm`. Establish `hJ : IsUnit (G.V.J.map t).det`. Take `⟨φ⟩ : Nonempty (F →+* ℂ)` from `inferInstance`. Establish `h0` using `det_ne_zero_of_sig (hTr.geo.hV.sig (InfinitePlace.mk φ))`.

Establish `h1 : G.V.J.det ≠ 0` using `fun e => h0 (by`. Rewrite using `[show G.V.J.map _ = RingHom.mapMatrix _ G.V.J from rfl, ← RingHom.map_det, e, map_zero])`. Rewrite using `[show G.V.J.map t = (t : E →+* Fv F v).mapMatrix G.V.J from rfl, ← RingHom.map_det]`. Conclude with `isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)`. Use `⟨leviHom h t G.V.J hJ hTr.geo.hV.herm g', lift_sub_one_at v _, ?_⟩` and prove the remaining obligations.

Rewrite using `[leviHom_map_piW, GlobalTheory.LeviAtPlace.locMat, pairMat_fst]`.
-/
theorem surj_at_place : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∀ (t : E →ₐ[F] Fv F v) (g' : GL (Fin a) (Fv F v)), ∃ g ∈ UAt σ G.V (evFin F v), (mat g).map (piW t) = g'.1 := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v _ t g'
  have h := hTr.base.cm
  have hJ : IsUnit (G.V.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := det_ne_zero_of_sig (hTr.geo.hV.sig (InfinitePlace.mk φ))
    have h1 : G.V.J.det ≠ 0 := fun e => h0 (by
      rw [show G.V.J.map _ = RingHom.mapMatrix _ G.V.J from rfl, ← RingHom.map_det, e, map_zero])
    rw [show G.V.J.map t = (t : E →+* Fv F v).mapMatrix G.V.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  refine ⟨leviHom h t G.V.J hJ hTr.geo.hV.herm g', lift_sub_one_at v _, ?_⟩
  rw [leviHom_map_piW, GlobalTheory.LeviAtPlace.locMat, pairMat_fst]

end GlobalTheory.SurjAtPlaceV
