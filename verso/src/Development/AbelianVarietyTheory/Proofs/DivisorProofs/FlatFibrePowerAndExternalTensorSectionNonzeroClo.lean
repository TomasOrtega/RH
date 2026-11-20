import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusProdSec

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels

namespace GlobalTheory.BoxNonzeroClosed

/- English proof (translation)
The claim follows from `| 0 => inferInstanceAs (Flat (𝟙 S)) | n + 1 => by have := flat_powObj G n exact inferInstanceAs (Flat (pullback.fst G.hom (Out.powObj G n).hom ≫ G.hom))`.
-/
theorem flat_powObj {S : Scheme.{0}} (G : Over S) [Flat G.hom] : ∀ n : ℕ, Flat (Out.powObj G n).hom
  | 0 => inferInstanceAs (Flat (𝟙 S))
  | n + 1 => by
    have := flat_powObj G n
    exact inferInstanceAs (Flat (pullback.fst G.hom (Out.powObj G n).hom ≫ G.hom))

/- English proof (translation)
Use `flat_powObj G N` as an intermediate fact. Set `e : pow G N ≅ Out.powObj G N` to `(productIsProduct (fun _ : Fin N => G)).conePointUniqueUpToIso (Out.powIsLimit G N)`. Establish `: IsIso e.hom.left` using `inferInstanceAs (IsIso ((Over.forget S).map e.hom))`. Rewrite using `[← Over.w e.hom]`. Use `infer_instance`.
-/
theorem flat_pow {S : Scheme.{0}} (G : Over S) [Flat G.hom] (N : ℕ) : Flat (pow G N).hom := by
  have := flat_powObj G N
  let e : pow G N ≅ Out.powObj G N :=
    (productIsProduct (fun _ : Fin N => G)).conePointUniqueUpToIso (Out.powIsLimit G N)
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  rw [← Over.w e.hom]
  infer_instance

/- English proof (translation)
Introduce and unpack `V _ _ G _ L θ ⟨g, hg, hθ⟩ N`. Use `⟨flat_pow G N, ?_⟩` and prove the remaining obligations. Take `⟨y, hy, hy'⟩` from `GlobalTheory.BoxSection.exists_point (fun k => Pi.π (fun _ : Fin N => G) k) (productIsProduct (fun _ : Fin N => G)) _ (fun _ => g) (fun _ => hg)`. Conclude with `⟨y, hy, GlobalTheory.BoxSection.mem_nonzeroLocus_prodSec L (pr G N) (fun _ => θ) y fun i => (hy' i).symm ▸ hθ⟩`.
-/
theorem main : ∀ (V : Type) [CommRing V] [IsLocalRing V] (G : Over (Sp V)) [Flat G.hom] (L : LB G.left) (θ : L.Sec),
    NonzeroClosed (X := G) θ → ∀ N : ℕ, Flat (pow G N).hom ∧ NonzeroClosed (X := pow G N) (boxSec G θ N) := by
  rintro V _ _ G _ L θ ⟨g, hg, hθ⟩ N
  refine ⟨flat_pow G N, ?_⟩
  obtain ⟨y, hy, hy'⟩ := GlobalTheory.BoxSection.exists_point (fun k => Pi.π (fun _ : Fin N => G) k)
    (productIsProduct (fun _ : Fin N => G)) _ (fun _ => g) (fun _ => hg)
  exact ⟨y, hy, GlobalTheory.BoxSection.mem_nonzeroLocus_prodSec L (pr G N) (fun _ => θ) y
    fun i => (hy' i).symm ▸ hθ⟩

end GlobalTheory.BoxNonzeroClosed
