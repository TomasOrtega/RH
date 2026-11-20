import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootOfUnityPrimeToTeichmullerLift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSumRootsOfUnityStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage

/- English proof (translation)
Introduce `l _ P AI T K c hc`. Take `⟨n, z, ω, hω, hsum⟩` from `GlobalTheory.T.exists_eq_sum_padicInt_mul_rootsOfUnity l K c c.2 hc`. Establish `h1 : ∀ i, ∃ w : Ainf l, Lifts AI K w ⟨ω i, (hω i).1⟩`. Introduce `i`. Take `⟨hK, m, hm, hl, hx⟩` from `hω i`.

Take `⟨xb, hxb⟩` from `GlobalTheory.MemLoc.exists_isTiltOf (ω i) m hm hl hx`. Conclude with `⟨_, AI.ιA_teich ⟨ω i, hK.2⟩ m hm hl hx xb hxb⟩`. Use `choose w hw using h1`. Establish `h2 : c = ∑ i, algebraMap ℚ_[l] ↥(K0 K) (z i : ℚ_[l]) * ⟨ω i, (hω i).1⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hsum]`. Use `push_cast`. Both sides reduce to the same expression. Use `⟨∑ i, algebraMap ℤ_[l] (Ainf l) (z i) * w i, ?_⟩` and prove the remaining obligations. Unfold `Lifts at hw ⊢`.

Rewrite using `[h2, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, hw, ιA_zl AI T, ← IsScalarTower.algebraMap_apply]`.
-/
theorem exists_lifts_of_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (c : ↥(K0 K)), ‖(c : Om l)‖ ≤ 1 → ∃ w : Ainf l, Lifts AI K w c := by
  intro l _ P AI T K c hc
  obtain ⟨n, z, ω, hω, hsum⟩ := GlobalTheory.T.exists_eq_sum_padicInt_mul_rootsOfUnity l K c c.2 hc
  have h1 : ∀ i, ∃ w : Ainf l, Lifts AI K w ⟨ω i, (hω i).1⟩ := by
    intro i
    obtain ⟨hK, m, hm, hl, hx⟩ := hω i
    obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf (ω i) m hm hl hx
    exact ⟨_, AI.ιA_teich ⟨ω i, hK.2⟩ m hm hl hx xb hxb⟩
  choose w hw using h1
  have h2 : c = ∑ i, algebraMap ℚ_[l] ↥(K0 K) (z i : ℚ_[l]) * ⟨ω i, (hω i).1⟩ := by
    apply Subtype.ext
    rw [hsum]
    push_cast
    rfl
  refine ⟨∑ i, algebraMap ℤ_[l] (Ainf l) (z i) * w i, ?_⟩
  unfold Lifts at hw ⊢
  rw [h2, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, hw, ιA_zl AI T, ← IsScalarTower.algebraMap_apply]

end GlobalTheory.ExpImage
